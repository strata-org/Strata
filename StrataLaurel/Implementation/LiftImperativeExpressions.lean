/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

import Strata.Util.Tactics
public import StrataLaurel.Implementation.LaurelPass
public import StrataLaurel.Implementation.Resolution
import StrataLaurel.Implementation.LaurelTypes
import StrataLaurel.Implementation.MapStmtExpr

namespace Strata
namespace Laurel

public section

/-
Transform assignments that appear in expression contexts into preceding statements.

When we see expressions, we traverse them right to left, pushing what we lift onto the
prependStatements stack, so every statement on the stack runs after the occurrences
still to be visited. An assignment is replaced by a read of its target and pushed.
When a variable is read while a statement on the stack assigns it, a snapshot of the
variable is pushed above that statement and read instead (`readVar`); the substitution
map keeps it for the occurrences that follow.

When we encounter an if-then-else, we rerun our algorithm from scratch on both branches,
so nested assignments are moved to the start of each branch.
If any assignments were discovered in the branches,
lift the entire if-then-else by putting it on the prependStatements stack.
Introduce a fresh variable and for each branch,
assign the last statement in that branch to the fresh variable.

Example 1 — Assignments in expression position:
  var y: int := x + (x := 1;) + x + (x := 2;);

Becomes:
  var $x_1 := x;              -- before snapshot 1
  x := 1;                     -- lifted first assignment
  var $x_0 := x;              -- before snapshot 0
  x := 2;                     -- lifted second assignment
  var y: int := $x_1 + $x_0 + $x_0 + x;

Example 2 — Conditional (if-then-else) inside an expression position:
  y := x + (if b then { x := x + 1; x } else { x := x + 2; x });

Becomes:
  var $x_0: int := x;          -- read by the left operand, which runs before the if
  var $cndtn_0: int;
  if b then {
    x := x + 1;
    $cndtn_0 := x;
  } else {
    x := x + 2;
    $cndtn_0 := x;
  }
  y := $x_0 + $cndtn_0;
-/

/-- Substitution map: variable uniqueId → replacement identifier -/
private abbrev SubstMap := Std.HashMap Nat Identifier

structure LiftState where
  /-- Statements to prepend (in reverse order — newest first) -/
  prependedStmts : List StmtExprMd := []
  /-- Counter for generating unique temp names per variable -/
  varCounters : List (String × Nat) := []
  /-- Substitution map: variable name → name to use.

      Mutable state on purpose: a mutation must stay visible to the
      *following, sequential* computations. Arguments are walked in reverse
      evaluation order, so a snapshot `readVar` takes in a later argument is
      read while traversing the earlier ones — a sideways flow that
      Reader-style `local` scoping cannot express.

      Lifetime: entries are statement-local (`withStatementScope` clears at
      statement boundaries); a region lifted out of expression position starts
      without the enclosing expression's entries, which are restored after it
      (`inFreshScope`). -/
  private subst : SubstMap := {}
  /-- Variables, by `uniqueId`, that a statement in `prependedStmts` assigns and that
      have not been snapshotted above it. An occurrence visited now is evaluated
      before that statement, so `readVar` snapshots the variable first. Scoped like
      `prependedStmts`. -/
  private dirty : Std.HashSet Nat := {}
  /-- Type environment -/
  model : SemanticModel
  /-- Global counter for fresh conditional variables -/
  condCounter : Nat := 0
  /-- All procedures in the program, used to look up return types of imperative calls -/
  procedures : List Procedure := []
  /-- Names of callees whose calls should be treated as imperative (lifted) -/
  imperativeCallees : List String := []
  /-- Variable uniqueIds referenced by lifted statements. When a `Var (.Declare ...)`
      is encountered for a variable whose uniqueId is in this set, it is also lifted
      so the declaration remains in scope for the lifted statements that use it.

      Unlike `subst` and `prependedStmts`, this is *not* saved and restored around
      nested scopes — it accumulates across the whole procedure and is only reset
      per procedure. That is sound because of a precondition on the input:
      Resolution assigns a program-globally-unique `uniqueId` to every `Declare`,
      so an entry for uniqueId `N` names exactly one declaration site and can
      never cause an unrelated one to hoist.

      A pass that duplicates a `Declare` node while keeping its `uniqueId` breaks
      this. `defineName` preserves an already-set `uniqueId`, so simply re-running
      Resolution does not repair such a duplicate — the pass must clear the copy's
      `uniqueId` and let re-resolution mint a fresh one. `TransparencyPass`'s
      quantifier proof block does exactly that for its havoc variable. -/
  liftedVarRefs : Std.HashSet Nat := {}

abbrev LiftM := ExceptT String (StateM LiftState)

private def freshTempFor (varName : Identifier) : LiftM Identifier := do
  let counters := (← get).varCounters
  let counter := counters.find? (·.1 == varName.text) |>.map (·.2) |>.getD 0
  modify fun s => { s with varCounters := (varName.text, counter + 1) :: s.varCounters.filter (·.1 != varName.text) }
  return mkId s!"${varName.text}_{counter}"

private def freshTempVar : LiftM Identifier := do
  let n := (← get).condCounter
  modify fun s => { s with condCounter := n + 1 }
  return s!"$cndtn_{n}"

/-- Record what lifted statements use, by `uniqueId`: every variable they read or
    assign goes into `liftedVarRefs`, and every variable they assign becomes `dirty`. -/
private def recordLifted (stmts : List StmtExprMd) : LiftM Unit := do
  let (refs, writes) := stmts.foldl (init := ([], [])) fun acc stmt =>
    foldStmtExpr (fun e (refs, writes) => match e.val with
      | .Var (.Local name) => (name.uniqueId.toList ++ refs, writes)
      | .Assign targets _ =>
        let ids := targets.filterMap fun t => match t.val with
          | .Local name => name.uniqueId
          | _ => none
        (ids ++ refs, ids ++ writes)
      | _ => (refs, writes)) acc stmt
  modify fun s => { s with
    liftedVarRefs := refs.foldl (·.insert ·) s.liftedVarRefs
    dirty := writes.foldl (·.insert ·) s.dirty }

private def prepend (stmt : StmtExprMd) : LiftM Unit := do
  modify fun s => { s with prependedStmts := stmt :: s.prependedStmts }
  recordLifted [stmt]

private def prependList (stmts : List StmtExprMd) : LiftM Unit := do
  modify fun s => { s with prependedStmts := stmts ++ s.prependedStmts }
  recordLifted stmts

private def onlyKeepSideEffectStmtsAndLast (stmts : List StmtExprMd) : LiftM (List StmtExprMd) := do
  match stmts with
  | [] => return []
  | _ =>
    -- return stmts
    let last := stmts.getLast!
    let nonLast ← stmts.dropLast.flatMapM (fun s =>
      match s.val with
      | .Var (.Declare ..) => do
          pure [s]

      /-
      Any other impure StmtExpr, like .Assign, .Exit or .Return,
      should already have been processed by translateExpr,
      so we can assume this StmtExpr is pure and can be dropped.
      TODO: currently .Exit and .Return are not processed by translateExpr, this is a bug
      -/
      | _ => pure []
    )
    return nonLast ++ [last]

private def takePrepends : LiftM (List StmtExprMd) := do
  let stmts := (← get).prependedStmts
  modify fun s => { s with prependedStmts := [] }
  return stmts

/-- Run `body` in a fresh statement-local substitution scope.

A snapshot substitution only stands in for occurrences evaluated *before* the
assignment it was taken for, within the same statement. Once the statement ends
every remaining occurrence must read the live variable again — including
occurrences in a nested statement the current one guards, such as a branch body.
Clearing on entry is what enforces that; clearing on exit is redundant given the
entry clear, and is kept so the property still holds for any arm added later.

Sub-regions within a single statement are not scoped here. They are traversed in
reverse evaluation order, or run in `inFreshScope` when they are lifted out of the
expression. -/
private def withStatementScope { t : Type } (body : LiftM t) : LiftM t := do
  modify fun s => { s with subst := {}, dirty := {} }
  let result ← body
  modify fun s => { s with subst := {}, dirty := {} }
  return result

private def computeType (expr : StmtExprMd) : LiftM HighTypeMd := do
  let s ← get
  return computeExprType s.model expr

/-- The name an occurrence of `varName` visited now reads. If a lifted statement that
    assigns it has not been snapshotted above, that statement runs after this
    occurrence, so snapshot the variable at the top of `prependedStmts` first. -/
private def readVar (varName : Identifier) (source : FileRange) : LiftM Identifier := do
  let some uid := varName.uniqueId | return varName
  if !(← get).dirty.contains uid then
    return (← get).subst.getD uid varName
  let snapshotName ← freshTempFor varName
  let varType ← computeType ⟨.Var (.Local varName), source⟩
  prepend ⟨.Assign [⟨.Declare ⟨snapshotName, some varType⟩, source⟩]
    ⟨.Var (.Local varName), source⟩, source⟩
  modify fun s => { s with dirty := s.dirty.erase uid, subst := s.subst.insert uid snapshotName }
  return snapshotName

/-- Run `body` as a region lifted out of the enclosing expression: it lands above
    everything lifted so far, so it starts with an empty stack and no snapshots or
    dirty variables of the enclosing scope. Returns what it lifted with its result,
    and restores the enclosing scope. The name counters are deliberately not
    restored: names minted inside escape into the output, and a restored counter
    would mint them again. -/
private def inFreshScope {t : Type} (body : LiftM t) : LiftM (List StmtExprMd × t) := do
  let saved ← get
  modify fun s => { s with prependedStmts := [], subst := {}, dirty := {} }
  let result ← body
  let lifted := (← get).prependedStmts
  modify fun s => { s with
    prependedStmts := saved.prependedStmts, subst := saved.subst, dirty := saved.dirty }
  return (lifted, result)

/-- Check if an expression contains any assignments or imperative calls
(recursively). When `liftsAssertsAssumes` is set, asserts and assumes also
count — these are lifted into statement position by `transformExpr`, so an
if-then-else whose branch contains one must itself be lifted to keep the
statement guarded by the condition.

Recursion is delegated to the generic `anyStmtExpr` traversal; this predicate only
classifies a single node. `imperativeCallees`/`liftsAssertsAssumes` are constant for a
call, so the closure captures them. A `while` always counts: the expression-position
`.While` arm lifts the loop whole, so an if-then-else holding one must itself be
lifted, or the loop would be hoisted out of its guard. -/
def containsAssignmentOrImperativeCall (imperativeCallees : List String) (expr : StmtExprMd)
    (liftsAssertsAssumes : Bool := false) : Bool :=
  anyStmtExpr (fun e => match e.val with
    | .Assign .. | .IncrDecr .. | .CompoundAssign .. | .While .. => true
    | .StaticCall name _ _ => imperativeCallees.contains name.text
    | .Assert .. | .Assume .. => liftsAssertsAssumes
    | _ => false) expr

mutual

/-- Lift `expr` whole, as a statement: transform it in a fresh scope and push what it
    becomes. -/
def transformLiftedStmt (expr : StmtExprMd) : LiftM Unit := do
  let (_, stmts) ← inFreshScope (transformStmt expr)
  prependList stmts
  termination_by (sizeOf expr, 1)

/--
Process an expression in expression context, traversing arguments right to left.
Assignments are lifted to prependedStmts and replaced with snapshot variable references.
With `discard` set the caller drops the result, so none is computed.
-/
def transformExpr (expr : StmtExprMd) (discard : Bool := false) : LiftM StmtExprMd := do
  match h_node : expr with
  | AstNode.mk val source =>
  match h_val : val with
  | .Var (.Local name) =>
      if discard then return ⟨.Hole, source⟩
      return ⟨.Var (.Local (← readVar name source)), source⟩

  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ => return expr

  | .Hole false (some holeType) =>
      -- Nondeterministic typed hole: lift to a fresh variable with no initializer (havoc)
      let holeVar ← freshTempVar
      prepend ⟨ .Var (.Declare ⟨holeVar, some holeType⟩), source⟩
      return ⟨ .Var (.Local holeVar), source ⟩

  | .Assign targets value =>
      let firstTarget ← match targets with
        | head :: _ => pure head
        | _ => return expr
      let target ← match firstTarget.val with
        | .Local varName => pure varName
        | .Declare param => pure param.name
        | _ =>
          dbg_trace "Strata bug: non-identifier targets should have been removed before the lift expression phase";
          return expr
      -- The result reads the target just after this assignment, which is before
      -- whatever has been lifted so far: read it now, before lifting the assignment.
      let resultExpr ← if discard then pure ⟨.Hole, source⟩
        else pure ⟨.Var (.Local (← readVar target source)), source⟩
      transformLiftedStmt expr
      return resultExpr

  | .StaticCall callee args tyArgs =>
    let imperativeCallees := (← get).imperativeCallees
    if !imperativeCallees.contains callee.text then
      let seqArgs ← args.reverse.mapM (transformExpr · discard)
      let seqCall := ⟨.StaticCall callee seqArgs.reverse tyArgs, source⟩
      return seqCall
    else if discard then
      transformLiftedStmt expr
      return ⟨.Hole, source⟩
    else
      let callResultVar ← freshTempVar
      let callResultTypeFull ← computeType expr
      -- The temp var holds the call's value; drop the maybe-except output from its type.
      let callResultType := stripTrailingErrors callResultTypeFull

      let (_, prepends) ← inFreshScope (transformStmtAssignImperativeCall
        [⟨ .Declare ⟨callResultVar, some callResultType⟩, source⟩] callee args tyArgs source source)
      prependList prepends
      return ⟨.Var (.Local callResultVar), source⟩

  | .IfThenElse cond thenBranch elseBranch =>
      let imperativeCallees := (← get).imperativeCallees
      -- A branch must be lifted if it contains anything `transformExpr` would
      -- hoist: assignments, imperative calls, asserts, or assumes. (Asserts and
      -- assumes matter because hoisting them out of the branch would drop the
      -- condition's guard — see `liftsAssertsAssumes`.)
      let thenHasAssign := containsAssignmentOrImperativeCall imperativeCallees thenBranch (liftsAssertsAssumes := true)
      let elseHasAssign := match elseBranch with
        | some e => containsAssignmentOrImperativeCall imperativeCallees e (liftsAssertsAssumes := true)
        | none => false
      if thenHasAssign || elseHasAssign then

        -- Infer type from the ORIGINAL then-branch (not the transformed one),
        -- because the transformed expression may reference freshly generated
        -- variables (e.g. $c_2) that don't exist in the SemanticModel yet.
        let condType ← computeType thenBranch
        let needsCondVar := !discard && !condType.val matches .TVoid

        -- Lift the entire if-then-else. Introduce a fresh variable for the result.
        let condVar ← freshTempVar
        -- The condition and each branch are lifted with the `if`, so each is traversed
        -- in a scope of its own.
        let (condPrepends, seqCond) ← inFreshScope (transformExpr cond)
        let (thenPrepends, seqThen) ← inFreshScope (transformExpr thenBranch)
        let assignStmts := if needsCondVar then [⟨.Assign [⟨ .Local condVar, source⟩] seqThen, source⟩] else [seqThen]
        let thenBlock := ⟨.Block (thenPrepends ++ assignStmts) none, source ⟩
        let seqElse ← match elseBranch with
          | some e => do
              let (elsePrepends, se) ← inFreshScope (transformExpr e)
              let assignStmts: List StmtExprMd := if needsCondVar then [⟨.Assign [⟨ .Local condVar, source⟩] se, source⟩] else [se];
              pure (some (⟨.Block (elsePrepends ++ assignStmts) none, source ⟩))
          | none => pure none
        -- IfThenElse added first (cons puts it deeper), then declaration (cons puts it on top)
        -- Output order: declaration, then if-then-else
        prepend (⟨.IfThenElse seqCond thenBlock seqElse, source⟩)
        let result ←
          if needsCondVar then do
            prepend ⟨.Var (.Declare ⟨condVar, some condType⟩), source ⟩
            pure ⟨.Var (.Local condVar), source⟩
          else
            -- Unused value
            pure ⟨ .Hole, expr.source ⟩
        prependList condPrepends
        return result
      else
        -- No liftable statements in branches — recurse normally, but in reverse
        -- evaluation order, as elsewhere in this traversal: the branches run
        -- after the condition, so they must read live variables rather than a
        -- snapshot the condition took. Visiting the condition last also keeps its
        -- substitutions available to occurrences evaluated before it.
        let seqThen ← transformExpr thenBranch
        let seqElse ← match elseBranch with
          | some e => pure (some (← transformExpr e))
          | none => pure none
        let seqCond ← transformExpr cond
        return ⟨.IfThenElse seqCond seqThen seqElse, source⟩

  | .Block stmts labelOption =>
      -- Only the last element's value is the block's.
      let newStmts := (← stmts.attach.reverse.mapIdxM fun i ⟨s, _⟩ =>
        transformExpr s (discard := discard || i != 0)).reverse
      let filtered ← onlyKeepSideEffectStmtsAndLast newStmts
      return ⟨ .Block filtered labelOption, source⟩

  | .Var (.Declare param) =>
      -- Lift the declaration if a lifted statement reads or assigns the variable, so
      -- that it stays declared above them.
      match param.name.uniqueId with
      | some paramUid =>
        if (← get).liftedVarRefs.contains paramUid then
          prepend (⟨.Var (.Declare param), expr.source⟩)
          return ⟨.Var (.Local param.name), expr.source⟩
        else
          return expr
      | none => throw s!"Var (.Declare {param.name.text}) has no uniqueId"

  | .Assume cond =>
      let (argPrepends, newCond) ← inFreshScope (transformExpr cond)
      prepend ⟨ .Assume newCond, source⟩
      prependList argPrepends
      pure default

  | .Assert cond summary =>
      let (argPrepends, newCond) ← inFreshScope (transformExpr cond)
      prepend ⟨ .Assert newCond summary, source⟩
      prependList argPrepends
      pure default

  | .Return (some retExpr) =>
      let seqRet ← transformExpr retExpr
      return ⟨.Return (some seqRet), source⟩

  | .While .. =>
      -- A loop only occurs as a statement of a block; lift it whole, as a statement.
      -- Traversed as an expression, its body's statements would be hoisted out of it.
      transformLiftedStmt expr
      return ⟨.Hole, source⟩

  | .PureFieldUpdate target fieldName newValue =>
      let seqTarget ← transformExpr target
      let seqNewValue ← transformExpr newValue
      return ⟨.PureFieldUpdate seqTarget fieldName seqNewValue, source⟩

  | .ReferenceEquals lhs rhs =>
      let seqRhs ← transformExpr rhs
      let seqLhs ← transformExpr lhs
      return ⟨.ReferenceEquals seqLhs seqRhs, source⟩

  | .AsType target ty =>
      let seqTarget ← transformExpr target
      return ⟨.AsType seqTarget ty, source⟩

  | .IsType target ty =>
      let seqTarget ← transformExpr target
      return ⟨.IsType seqTarget ty, source⟩

  | .InstanceCall target callee args =>
      let seqArgs ← args.reverse.mapM transformExpr
      let seqTarget ← transformExpr target
      return ⟨.InstanceCall seqTarget callee seqArgs.reverse, source⟩

  | .Quantifier .. =>
      -- The body and trigger are *spec* positions under a binder, like a loop
      -- invariant, and are deliberately left untransformed: nothing may be
      -- hoisted out of a quantifier.
      --
      -- Hoisting is unsound here for two separate reasons. Scope: the binder is
      -- in scope only inside the quantifier, so a lifted statement mentioning it
      -- lands where its name is not declared — `forall(x: int) => { var t: int
      -- := x * x; t >= 0 }` would hoist `var t: int := x * x` above the
      -- `forall`, leaving `x` free and turning a valid program into one that
      -- fails to resolve. Multiplicity: the body is re-evaluated per
      -- instantiation, once for every value of the binder, so even a statement
      -- that mentions no bound variable would be evaluated exactly once, before
      -- the quantifier, freezing what should vary — silently changing what the
      -- quantifier says rather than just making it harder to prove.
      --
      -- Nothing is left behind that needs lifting. `TransparencyPass` runs first
      -- (it removes `Pseudo.statementExpression`) and rewrites every
      -- quantifier body: `functionalize` removes its proof steps and calls
      -- become their `$asFunction` twins, so a body reaching this pass holds no
      -- assert, assume, or Core-procedure call. A proof procedure's steps are
      -- moved by that pass into an ordinary `if $proof_N then { .. }` statement
      -- *preceding* the quantifier, where the binder is replaced by a locally
      -- declared `$havoc_N`; that block is reached through the normal statement
      -- path and lifted there, under its own declaration.
      --
      -- A declaration written inside a body, as in the example above, therefore
      -- stays where it is, evaluated per instantiation and still meaning what
      -- was written. `InlineLocalVariables` folds it back into the expression
      -- afterwards — it opens a scope per quantifier, shadowing the binder —
      -- since a Core quantifier can no more carry a declaration than an
      -- invariant can.
      return expr

  | .Old value label? =>
      let seqValue ← transformExpr value
      return ⟨.Old seqValue label?, source⟩

  | .Fresh value =>
      let seqValue ← transformExpr value
      return ⟨.Fresh seqValue, source⟩

  | .Assigned name =>
      let seqName ← transformExpr name
      return ⟨.Assigned seqName, source⟩

  | .ProveBy value proof =>
      let seqValue ← transformExpr value
      let seqProof ← transformExpr proof
      return ⟨.ProveBy seqValue seqProof, source⟩

  | .ContractOf ty func =>
      let seqFunc ← transformExpr func
      return ⟨.ContractOf ty seqFunc, source⟩

  | _ => return expr
  termination_by (sizeOf expr, 2)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.left; (try have := Condition.sizeOf_condition_lt ‹_›); term_by_mem)
      | (apply Prod.Lex.left; simp <;> omega)
      | (try subst h_node; try subst h_val; apply Prod.Lex.right; omega)

def transformStmtAssignImperativeCall
    (targets : List (AstNode Variable))
    (callee: Identifier)
    (args: List StmtExprMd)
    (typeArgs: List HighTypeMd)
    (source: FileRange)
    (callSource: FileRange): LiftM (List StmtExprMd) := do
  let seqArgs ← args.reverse.mapM transformExpr
  let argPrepends ← takePrepends
  -- `typeArgs` carried onto the rebuilt call: lifting reorders and renames arguments but does
  -- not change the callee's instantiation.
  return argPrepends ++ [⟨.Assign targets ⟨.StaticCall callee seqArgs.reverse typeArgs, callSource⟩, source⟩]
  termination_by (sizeOf args, 0)
  decreasing_by
    all_goals try (apply Prod.Lex.right; omega)
    all_goals (try simp_all; try have := Condition.sizeOf_condition_lt ‹_›; try term_by_mem)
    all_goals (try (apply Prod.Lex.left); try term_by_mem; try omega)

/--
Process a statement, handling any assignments in its sub-expressions.
Returns a list of statements (the original may expand into multiple).

Runs in a fresh `withStatementScope`, so it neither inherits snapshot
substitutions from the preceding statement nor leaks its own to the next one.
-/
def transformStmt (stmt : StmtExprMd) : LiftM (List StmtExprMd) := withStatementScope do
  match stmt with
  | AstNode.mk val source =>
  match val with
  | .Assert cond summary =>
      -- Do not transform assert conditions with assignments — they must be rejected.
      -- But nondeterministic holes need to be lifted.
      -- if containsNondetHole cond.condition && !containsAssignmentOrImperativeCall (← get).model cond.condition then
        let seqCond ← transformExpr cond
        let prepends ← takePrepends
        return prepends ++ [⟨.Assert seqCond summary, source⟩]
      -- else
      --   return [stmt]

  | .Assume cond =>
      -- if containsNondetHole cond && !containsAssignmentOrImperativeCall (← get).model cond then
        let seqCond ← transformExpr cond
        let prepends ← takePrepends
        return prepends ++ [⟨.Assume seqCond, source⟩]
      -- else
      --   return [stmt]

  | .Block stmts metadata =>
      let seqStmts ← stmts.mapM transformStmt
      return [⟨.Block seqStmts.flatten metadata, source⟩]

  | .Var (.Declare _) =>
      return [stmt]

  | .Assign targets valueMd =>
      -- If the RHS is a direct imperative StaticCall, don't lift it —
      -- translateStmt handles Assign + StaticCall directly as a call statement.
      match _: valueMd with
      | AstNode.mk value callSource =>
      match _: value with
      | .StaticCall callee args tyArgs =>
          let imperativeCallees := (← get).imperativeCallees
          if imperativeCallees.contains callee.text then
            transformStmtAssignImperativeCall targets callee args tyArgs source callSource
          else
            let seqValue ← transformExpr valueMd
            let prepends ← takePrepends
            return prepends ++ [⟨.Assign targets seqValue, source⟩]
      | _ =>
          let seqValue ← transformExpr valueMd
          let prepends ← takePrepends
          return prepends ++ [⟨.Assign targets seqValue, source⟩]

  | .IfThenElse cond thenBranch elseBranch =>
      let seqCond ← transformExpr cond
      let condPrepends ← takePrepends
      let seqThen ← do
        let stmts ← transformStmt thenBranch
        pure ⟨ .Block stmts none, source ⟩
      let seqElse ← match elseBranch with
        | some e => do
            let se ← transformStmt e
            pure (some (⟨.Block se none, source ⟩))
        | none => pure none
      return condPrepends ++ [⟨.IfThenElse seqCond seqThen seqElse, source⟩]

  | .While cond invs dec body postTest =>
      let seqCond ← transformExpr cond
      let condPrepends ← takePrepends
      -- Invariants and `decreases` are *spec* positions, like a `requires` or an
      -- `ensures`, and are deliberately left untransformed. They are re-evaluated at
      -- the loop head on entry and after every iteration, so hoisting a statement out
      -- of one would evaluate it exactly once, before the loop, freezing every
      -- loop-varying operand at its pre-loop value — silently changing what the
      -- invariant says rather than just making it harder to prove.
      --
      -- Anything the contract pass left inside an invariant (e.g. the `var $cp_… :=`
      -- argument temporaries of a call to a `requires`-bearing procedure such as the
      -- `$div` wrapper behind `/`) therefore stays in place, where it is evaluated per
      -- iteration and still means what was written. `InlineLocalVariables` folds those
      -- declarations back into the expression afterwards, since a Core invariant can no
      -- more carry a declaration than a function body can.
      --
      -- This also means a nondeterministic hole in an invariant is no longer
      -- havoc-lifted here. That lifting could never have been correct in a loop head:
      -- it emits an uninitialized `var` before the loop, so the hole would take one
      -- fixed (if arbitrary) value for every iteration instead of being re-havoced.
      --
      -- Leaving them alone also means an invariant cannot inherit a snapshot the
      -- condition took, because no substitution is applied to it at all.
      let seqBody ← do
        let stmts ← transformStmt body
        pure ⟨.Block stmts none, source⟩
      return condPrepends ++
        [⟨.While seqCond invs dec seqBody postTest, source⟩]

  | .StaticCall name args tyArgs =>
      -- Right-to-left, like the expression-position `.StaticCall` arm: a snapshot
      -- created for an assignment argument must be visible to the arguments to its
      -- *left* in source order (those are the ones that have to read the old
      -- value), so they must be traversed after it.
      let seqArgs ← args.reverse.mapM transformExpr
      let prepends ← takePrepends
      -- `subst` is scoped to a single statement: it maps a variable to the
      -- snapshot holding its pre-assignment value while that statement's
      -- arguments are being traversed. Leaking it into the next statement would
      -- rewrite that statement's reads to the stale snapshot, so clear it here
      -- as every sibling statement arm does.
      modify fun s => { s with subst := {} }
      return prepends ++ [⟨.StaticCall name seqArgs.reverse tyArgs, source⟩]

  | .Return (some retExpr) =>
      let seqRet ← transformExpr retExpr
      let prepends ← takePrepends
      return prepends ++ [⟨.Return (some seqRet), source⟩]

  -- No `.Throw` / `.Try` arms: `EliminateExceptions` runs earlier in the
  -- pipeline, so by the time expression-lifting runs the exceptional channel has
  -- already been lowered to ordinary control flow and those constructors can no
  -- longer occur. They fall through to the identity case below.
  | _ =>
      return [stmt]
  termination_by (sizeOf stmt, 0)
  decreasing_by
    all_goals try (apply Prod.Lex.right; omega)
    all_goals (try have := CatchClause.sizeOf_body_lt ‹_›)
    all_goals (try have := CatchClause.sizeOf_predicate_lt ‹_›)
    all_goals (try simp_all; try have := Condition.sizeOf_condition_lt ‹_›; try term_by_mem)
    all_goals (try (apply Prod.Lex.left); try term_by_mem; try omega)
end

def transformProcedureBody (source: FileRange) (body : StmtExprMd) : LiftM StmtExprMd := do
  let stmts ← transformStmt body
  match stmts with
  | [single] => pure single
  | multiple => pure ⟨.Block multiple none, source ⟩

def transformProcedure (proc : Procedure) : LiftM Procedure := do
  modify fun s => { s with subst := {}, dirty := {}, prependedStmts := [], varCounters := [], liftedVarRefs := {} }
  match proc.body with
  | .Transparent bodyExpr =>
      let seqBody ← transformProcedureBody proc.name.source bodyExpr
      pure { proc with body := .Transparent seqBody }
  | .Opaque postconds impl modif =>
      let impl' ← impl.mapM (transformProcedureBody proc.name.source)
      pure { proc with body := .Opaque postconds impl' modif }
  | .Abstract _ =>
      pure proc
  | .External =>
      pure proc

/--
Transform a program to lift all assignments that occur in an expression context.
When `procedureNames` is non-empty, only procedures whose name appears in the
list are transformed; all others are left unchanged. When `procedureNames` is
empty, no procedures are transformed.
-/
def liftExpressionAssignments (program : Program)
    (model : SemanticModel) (imperativeCallees : List String) : Except String Program :=
  let initState : LiftState := { model := model, imperativeCallees := imperativeCallees }
  let transform := program.staticProcedures.mapM transformProcedure
  let (result, _) := (ExceptT.run transform).run initState
  match result with
  | .ok seqProcedures => .ok { program with staticProcedures := seqProcedures }
  | .error e => .error e

end -- public section

/--
Apply `liftExpressionAssignments` to the core (non-functional) procedures in an
`UnorderedCoreWithLaurelTypes`. Only procedures whose names appear in the core
procedure list are transformed; functions are left unchanged.
-/
def liftImperativeExpressionsInCore (uc : UnorderedCoreWithLaurelTypes)
    (model : SemanticModel) : Except String UnorderedCoreWithLaurelTypes := do
  let imperativeCallees := uc.coreProcedures.map (·.name.text)
  let liftedProgram ← liftExpressionAssignments
    { staticProcedures := uc.coreProcedures, staticFields := [], types := [], constants := [] }
    model imperativeCallees
  pure { uc with
    functions := uc.functions
    coreProcedures := liftedProgram.staticProcedures
  }

public def liftImperativeExpressionsPass : LaurelPass UnorderedCoreWithLaurelTypes UnorderedCoreWithLaurelTypes where
  name := "LiftImperativeExpressions"
  creates := [NodeKind.StmtExpr.Var, NodeKind.StmtExpr.Assign, NodeKind.StmtExpr.Block]
  removes := [NodeKind.Pseudo.statementExpression]
  -- Hoisting an imperative call out of a short-circuited operand would run it
  -- unconditionally, so `DesugarShortCircuit` must have guarded those first.
  unsupported := [NodeKind.Pseudo.imperativeShortCircuit,
    NodeKind.StmtExpr.IncrDecr, NodeKind.StmtExpr.CompoundAssign]
  documentation := "Lifts assignments, assertions, assumptions and calls to a configurable list of procedures, that appear in expression contexts, to preceding statements. Lifting is necessary because Strata Core does not support assignments, assumes, asserts and calls to Core procedures within expressions. The pass introduces fresh temporary variables where needed. Lifting expressions that occur in conditional control flow that is also in an expression, can require duplicating some of that control flow. If we do not encode the heap before the lifting pass, we will need to lift any calls to heap mutating procedures, since they are implicitly mutating. The Laurel resolver should be able to tell us which procedures are heap mutating, so this is simple."
  needsResolves := true
  run := fun _ p m =>
    match liftImperativeExpressionsInCore p m with
    | .ok p' => (p', [], {})
    | .error e => (p, [Message.fromString s!"Internal error in LiftImperativeExpressions: {e}" .strataBug], {})

end Laurel
