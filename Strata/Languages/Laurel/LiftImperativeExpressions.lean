/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Util.Tactics
public import Strata.Languages.Laurel.Resolution
import Strata.Languages.Laurel.LaurelTypes

namespace Strata
namespace Laurel

public section

/-
Transform assignments that appear in expression contexts into preceding statements.

When we see expressions, we traverse them right to left.
For each variable, we maintain a substitution map, which is initially filled with the actual variable.
If we encounter an assignment, we replace it with the current substitution for that variable. We then come up with a new snapshot variable name, and push that to the subsitution map.
We also push both the assignment and an assignment to the snapshot variable to a stack over prependStatements.

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
  var z: bool := (if (b) { b := false; } else (b := true;)) || b;

Becomes:
  var $c_0: bool;
  if (b) {
    var $b_0 := b;
    b := false;
    $c_0 := b;
  } else {
    var $b_0 := b;
    b := true;
    $c_0 := b;
  }
  var z: bool := $c_0 || b;

Example 3 — Statement-level assignment:
  x := expr;

Becomes:
  var $x_0 := x;               -- before-snapshot of x
  x := expr;                   -- original assignment
-/

/-- Substitution map: variable name → name to use in expressions -/
private abbrev SubstMap := Map Identifier Identifier

structure LiftState where
  /-- Statements to prepend (in reverse order — newest first) -/
  prependedStmts : List StmtExprMd := []
  /-- Counter for generating unique temp names per variable -/
  varCounters : List (Identifier × Nat) := []
  /-- Substitution map: variable name → name to use -/
  private subst : SubstMap := []
  /-- Type environment -/
  model : SemanticModel
  /-- Global counter for fresh conditional variables -/
  condCounter : Nat := 0
  /-- All procedures in the program, used to look up return types of imperative calls -/
  procedures : List Procedure := []
  /-- Names of callees whose calls should be treated as imperative (lifted) -/
  imperativeCallees : List String := []

@[expose] abbrev LiftM := StateM LiftState

private def emptyMd : Option String := none

private def freshTempFor (varName : Identifier) : LiftM Identifier := do
  let counters := (← get).varCounters
  let counter := counters.find? (·.1 == varName) |>.map (·.2) |>.getD 0
  modify fun s => { s with varCounters := (varName, counter + 1) :: s.varCounters.filter (·.1 != varName) }
  return s!"${varName.text}_{counter}"

private def freshCondVar : LiftM Identifier := do
  let n := (← get).condCounter
  modify fun s => { s with condCounter := n + 1 }
  return s!"$cndtn_{n}"

private def prepend (stmt : StmtExprMd) : LiftM Unit :=
  modify fun s => { s with prependedStmts := stmt :: s.prependedStmts }

private def onlyKeepSideEffectStmtsAndLast (stmts : List StmtExprMd) : LiftM (List StmtExprMd) := do
  match stmts with
  | [] => return []
  | _ =>
    -- return stmts
    let last := stmts.getLast!
    let nonLast ← stmts.dropLast.flatMapM (fun s =>
      match s.val with
      | .Var (.Declare ..) | .Assign ([⟨.Declare .., _⟩]) _ => do
          pure [s]
      -- | .Assert _ => do
      --     pure [s]
      -- | .Assume _ => do
      --     pure [s]

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

private def getSubst (varName : Identifier) : LiftM Identifier := do
  match (← get).subst.lookup varName with
  | some mapped => return mapped
  | none => return varName

private def setSubst (varName : Identifier) (value : Identifier) : LiftM Unit :=
  modify fun s => { s with subst := ⟨ varName, value ⟩ :: s.subst }

private def computeType (expr : StmtExprMd) : LiftM HighTypeMd := do
  let s ← get
  return computeExprType s.model expr

/-- Check if an expression contains any assignments or imperative calls
(recursively). When `liftsAssertsAssumes` is set, asserts and assumes also
count — these are lifted into statement position by `transformExpr`, so an
if-then-else whose branch contains one must itself be lifted to keep the
statement guarded by the condition. -/
def containsAssignmentOrImperativeCall (imperativeCallees : List String) (expr : StmtExprMd)
    (liftsAssertsAssumes : Bool := false) : Bool :=
  match expr with
  | AstNode.mk val _ =>
  match val with
  | .Assign .. => true
  | .StaticCall name args1 =>
    imperativeCallees.contains name.text ||
      args1.attach.any (fun x => containsAssignmentOrImperativeCall imperativeCallees x.val liftsAssertsAssumes)
  | .PrimitiveOp _ args2 _ => args2.attach.any (fun x => containsAssignmentOrImperativeCall imperativeCallees x.val liftsAssertsAssumes)
  | .Block stmts _ => stmts.attach.any (fun x => containsAssignmentOrImperativeCall imperativeCallees x.val liftsAssertsAssumes)
  | .IfThenElse cond th el =>
      containsAssignmentOrImperativeCall imperativeCallees cond liftsAssertsAssumes ||
      containsAssignmentOrImperativeCall imperativeCallees th liftsAssertsAssumes ||
      match el with | some e => containsAssignmentOrImperativeCall imperativeCallees e liftsAssertsAssumes | none => false
  | .Assume cond => liftsAssertsAssumes || containsAssignmentOrImperativeCall imperativeCallees cond liftsAssertsAssumes
  | .Assert cond => liftsAssertsAssumes || containsAssignmentOrImperativeCall imperativeCallees cond.condition liftsAssertsAssumes
  | .InstanceCall target _ args =>
      containsAssignmentOrImperativeCall imperativeCallees target liftsAssertsAssumes ||
      args.attach.any (fun x => containsAssignmentOrImperativeCall imperativeCallees x.val liftsAssertsAssumes)
  | .Quantifier _ _ trigger body =>
      containsAssignmentOrImperativeCall imperativeCallees body liftsAssertsAssumes ||
      match trigger with | some t => containsAssignmentOrImperativeCall imperativeCallees t liftsAssertsAssumes | none => false
  | .Old value => containsAssignmentOrImperativeCall imperativeCallees value liftsAssertsAssumes
  | .Fresh value => containsAssignmentOrImperativeCall imperativeCallees value liftsAssertsAssumes
  | .ProveBy value proof =>
      containsAssignmentOrImperativeCall imperativeCallees value liftsAssertsAssumes ||
      containsAssignmentOrImperativeCall imperativeCallees proof liftsAssertsAssumes
  | .ReferenceEquals lhs rhs =>
      containsAssignmentOrImperativeCall imperativeCallees lhs liftsAssertsAssumes ||
      containsAssignmentOrImperativeCall imperativeCallees rhs liftsAssertsAssumes
  | .PureFieldUpdate target _ newValue =>
      containsAssignmentOrImperativeCall imperativeCallees target liftsAssertsAssumes ||
      containsAssignmentOrImperativeCall imperativeCallees newValue liftsAssertsAssumes
  | .AsType target _ => containsAssignmentOrImperativeCall imperativeCallees target liftsAssertsAssumes
  | .IsType target _ => containsAssignmentOrImperativeCall imperativeCallees target liftsAssertsAssumes
  | .Assigned name => containsAssignmentOrImperativeCall imperativeCallees name liftsAssertsAssumes
  | .ContractOf _ func => containsAssignmentOrImperativeCall imperativeCallees func liftsAssertsAssumes
  | .Return (some v) => containsAssignmentOrImperativeCall imperativeCallees v liftsAssertsAssumes
  | _ => false
  termination_by expr
  decreasing_by
    all_goals (try cases x)
    all_goals (try simp_all)
    all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
    all_goals (try term_by_mem)
    all_goals omega

/--
Shared logic for lifting an assignment in expression position:
prepends the assignment, creates before-snapshots for all targets,
and updates substitutions. The value should already be transformed by the caller.
-/
private def liftAssignExpr (targets : List VariableMd) (seqValue : StmtExprMd)
    (source : Option FileRange) : LiftM Unit := do
  -- Prepend the assignment itself
  prepend (⟨.Assign targets seqValue, source⟩)
  -- Create a before-snapshot for each target and update substitutions
  for target in targets do
    match target.val with
    | .Local varName =>
        let snapshotName ← freshTempFor varName
        let varType ← computeType ⟨ .Var (.Local varName), source ⟩
        -- Snapshot goes before the assignment (cons pushes to front)
        prepend (⟨.Assign [⟨.Declare ⟨snapshotName, varType⟩, source⟩] (⟨.Var (.Local varName), source⟩), source⟩)
        setSubst varName snapshotName
    | _ => pure ()

mutual
/--
Process an expression in expression context, traversing arguments right to left.
Assignments are lifted to prependedStmts and replaced with snapshot variable references.
-/
def transformExpr (expr : StmtExprMd) : LiftM StmtExprMd := do
  match expr with
  | AstNode.mk val source =>
  match val with
  | .Var (.Local name) =>
      return ⟨.Var (.Local (← getSubst name)), source⟩

  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ => return expr

  | .Hole false (some holeType) =>
      -- Nondeterministic typed hole: lift to a fresh variable with no initializer (havoc)
      let holeVar ← freshCondVar
      prepend ⟨ .Var (.Declare ⟨holeVar, holeType⟩), source⟩
      return ⟨ .Var (.Local holeVar), source ⟩

  | .Assign targets value =>
      -- The expression result is the current substitution for the first target
      -- (we already know what it maps to AFTER this assignment from right-to-left traversal)
      let firstTarget ← match targets with
        | head :: _ => pure head
        | _ => return expr

      let resultExpr ← match firstTarget.val with
        | .Local varName => pure (⟨.Var (.Local (← getSubst varName)), source⟩)
        | .Declare param =>
          -- Declaration with initializer: check if substitution exists
          let hasSubst := (← get).subst.lookup param.name |>.isSome
          if hasSubst then
            pure (⟨.Var (.Local (← getSubst param.name)), source⟩)
          else
            pure (⟨.Var (.Local param.name), source⟩)
        | _ =>
          dbg_trace "Strata bug: non-identifier targets should have been removed before the lift expression phase";
          return expr

      -- Use the original value (not seqValue) for the prepended assignment,
      -- because prepended statements execute in program order and don't need substitutions.
      liftAssignExpr targets value source

      return resultExpr

  | .PrimitiveOp op args _ =>
      -- Process arguments right to left
      let seqArgs ← args.reverse.mapM transformExpr
      return ⟨.PrimitiveOp op seqArgs.reverse, source⟩

  | .StaticCall callee args =>
    let model := (← get).model
    let imperativeCallees := (← get).imperativeCallees
    if !imperativeCallees.contains callee.text then
      let seqArgs ← args.reverse.mapM transformExpr
      let seqCall := ⟨.StaticCall callee seqArgs.reverse, source⟩
      return seqCall
    else
      let startingPrepend ← takePrepends
      let seqArgs ← args.reverse.mapM transformExpr
      let argsPepends ← takePrepends
      let seqCall := ⟨.StaticCall callee seqArgs.reverse, source⟩
      -- Imperative call in expression position: lift to an assignment.
      -- Only valid for single-output procedures (or unresolved ones where we
      -- fall back to a single target). Multi-output procedures in expression
      -- position are a bug in the upstream translation — Resolution should
      -- emit a diagnostic for that case.
      let outputs := match model.get callee with
        | .staticProcedure proc => proc.outputs
        | .instanceProcedure _ proc => proc.outputs
        | _ => []
      let callResultVar ← freshCondVar
      let callResultType ← match outputs with
        | [single] => pure single.type
        | _ => computeType expr
      let liftedCall := [
        ⟨ (.Var (.Declare ⟨callResultVar, callResultType⟩)), source ⟩,
        ⟨.Assign [⟨ .Local callResultVar, source⟩] seqCall, source⟩
      ]
      modify fun s => { s with prependedStmts := argsPepends ++ liftedCall ++ startingPrepend}
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
        let needsCondVar := condType.val != .TVoid

        -- Lift the entire if-then-else. Introduce a fresh variable for the result.
        let condVar ← freshCondVar
        -- Save outer state
        let savedSubst := (← get).subst
        let savedPrepends := (← get).prependedStmts

        let seqCond ← transformExpr cond
        let condPrepends := (← get).prependedStmts
        -- Process then-branch from scratch
        modify fun s => { s with prependedStmts := [], subst := [] }
        let seqThen ← transformExpr thenBranch
        let thenPrepends ← takePrepends
        let assignStmts := if needsCondVar then [⟨.Assign [⟨ .Local condVar, source⟩] seqThen, source⟩] else [seqThen]
        let thenBlock := ⟨.Block (thenPrepends ++ assignStmts) none, source ⟩
        -- Process else-branch from scratch
        modify fun s => { s with prependedStmts := [], subst := [] }
        let seqElse ← match elseBranch with
          | some e => do
              let se ← transformExpr e
              let elsePrepends ← takePrepends
              let assignStmts: List StmtExprMd := if needsCondVar then [⟨.Assign [⟨ .Local condVar, source⟩] se, source⟩] else [se];
              pure (some (⟨.Block (elsePrepends ++ assignStmts) none, source ⟩))
          | none => pure none
        -- Restore outer state
        modify fun s => { s with subst := savedSubst, prependedStmts := savedPrepends }
        -- IfThenElse added first (cons puts it deeper), then declaration (cons puts it on top)
        -- Output order: declaration, then if-then-else
        prepend (⟨.IfThenElse seqCond thenBlock seqElse, source⟩)
        if needsCondVar then
          prepend ⟨.Var (.Declare ⟨condVar, condType⟩), source ⟩
          modify fun s => { s with prependedStmts := condPrepends ++ s.prependedStmts }
          return ⟨.Var (.Local condVar), source⟩
        else
          modify fun s => { s with prependedStmts := condPrepends ++ s.prependedStmts }
          return default
      else
        -- No liftable statements in branches — recurse normally.
        let seqCond ← transformExpr cond
        let seqThen ← transformExpr thenBranch
        let seqElse ← match elseBranch with
          | some e => pure (some (← transformExpr e))
          | none => pure none
        return ⟨.IfThenElse seqCond seqThen seqElse, source⟩

  | .Block stmts labelOption =>
      let newStmts := (← stmts.reverse.mapM transformExpr).reverse
      -- Flatten generated multi-output call wrappers BEFORE onlyKeepSideEffectStmtsAndLast
      -- which would drop the multi-target assign. Pattern: [VarDecl, MultiAssign, VarRef].
      match newStmts with
      | [decl, assign, last] =>
        match decl.val, assign.val with
        | .Assign [t] _, .Assign targets _ =>
          match t.val with
          | .Declare _ =>
            if targets.length ≥ 2 then
              prepend assign
              prepend decl
              return last
            else
              let filtered ← onlyKeepSideEffectStmtsAndLast newStmts
              return ⟨ .Block filtered labelOption, source⟩
          | _ =>
            let filtered ← onlyKeepSideEffectStmtsAndLast newStmts
            return ⟨ .Block filtered labelOption, source⟩
        | _, _ =>
          let filtered ← onlyKeepSideEffectStmtsAndLast newStmts
          return ⟨ .Block filtered labelOption, source⟩
      | _ =>
        let filtered ← onlyKeepSideEffectStmtsAndLast newStmts
        return ⟨ .Block filtered labelOption, source⟩

  | .Var (.Declare param) =>
      -- If the substitution map has an entry for this variable, it was
      -- assigned to the right and we need to lift this declaration so it
      -- appears before the snapshot that references it.
      let hasSubst := (← get).subst.lookup param.name |>.isSome
      if hasSubst then
        prepend (⟨.Var (.Declare param), expr.source⟩)
        return ⟨.Var (.Local (← getSubst param.name)), expr.source⟩
      else
        return expr

  | .Assume cond =>
      let prepends ← takePrepends
      let seqCond ← transformExpr cond
      let argPrepends ← takePrepends
      modify fun s => { s with prependedStmts := argPrepends ++ [⟨.Assume seqCond, source⟩] ++ prepends }
      default

  | .Assert cond =>
      let prepends ← takePrepends
      let seqCond ← transformExpr cond.condition
      let argPrepends ← takePrepends
      modify fun s => { s with prependedStmts := argPrepends ++ [⟨.Assert { cond with condition := seqCond }, source⟩] ++ prepends }
      default

  | .Return (some retExpr) =>
      let seqRet ← transformExpr retExpr
      return ⟨.Return (some seqRet), source⟩

  | .While cond invs dec body =>
      let seqCond ← transformExpr cond
      let seqInvs ← invs.mapM transformExpr
      let seqDec ← match dec with
        | some d => pure (some (← transformExpr d))
        | none => pure none
      let seqBody ← transformExpr body
      return ⟨.While seqCond seqInvs seqDec seqBody, source⟩

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

  | .Quantifier mode param trigger body =>
      let seqBody ← transformExpr body
      let seqTrigger ← match trigger with
        | some t => pure (some (← transformExpr t))
        | none => pure none
      return ⟨.Quantifier mode param seqTrigger seqBody, source⟩

  | .Old value =>
      let seqValue ← transformExpr value
      return ⟨.Old seqValue, source⟩

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
  termination_by (sizeOf expr, 0)
  decreasing_by
    all_goals (simp_all; try have := Condition.sizeOf_condition_lt ‹_›; try term_by_mem)
    all_goals (apply Prod.Lex.left; try term_by_mem; try omega)

/--
Process a statement, handling any assignments in its sub-expressions.
Returns a list of statements (the original may expand into multiple).
-/
def transformStmt (stmt : StmtExprMd) : LiftM (List StmtExprMd) := do
  match stmt with
  | AstNode.mk val source =>
  match val with
  | .Assert cond =>
      -- Do not transform assert conditions with assignments — they must be rejected.
      -- But nondeterministic holes need to be lifted.
      -- if containsNondetHole cond.condition && !containsAssignmentOrImperativeCall (← get).model cond.condition then
        let seqCond ← transformExpr cond.condition
        let prepends ← takePrepends
        modify fun s => { s with subst := [] }
        return prepends ++ [⟨.Assert { cond with condition := seqCond }, source⟩]
      -- else
      --   return [stmt]

  | .Assume cond =>
      -- if containsNondetHole cond && !containsAssignmentOrImperativeCall (← get).model cond then
        let seqCond ← transformExpr cond
        let prepends ← takePrepends
        modify fun s => { s with subst := [] }
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
      | AstNode.mk value _ =>
      match _: value with
      | .StaticCall callee args =>
          let imperativeCallees := (← get).imperativeCallees
          if !imperativeCallees.contains callee.text then
            let seqValue ← transformExpr valueMd
            let prepends ← takePrepends
            modify fun s => { s with subst := [] }
            return prepends ++ [⟨.Assign targets seqValue, source⟩]
          else
            let seqArgs ← args.reverse.mapM transformExpr
            let argPrepends ← takePrepends
            modify fun s => { s with subst := [] }
            return argPrepends ++ [⟨.Assign targets ⟨.StaticCall callee seqArgs.reverse, source⟩, source⟩]
      | _ =>
          let seqValue ← transformExpr valueMd
          let prepends ← takePrepends
          modify fun s => { s with subst := [] }
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

  | .While cond invs dec body =>
      let seqCond ← transformExpr cond
      let condPrepends ← takePrepends
      -- Process invariants and decreases through transformExpr for nondet holes
      let seqInvs ← invs.mapM transformExpr
      let invPrepends ← takePrepends
      let seqDec ← match dec with
        | some d => pure (some (← transformExpr d))
        | none => pure none
      let decPrepends ← takePrepends
      let seqBody ← do
        let stmts ← transformStmt body
        pure ⟨.Block stmts none, source⟩
      return condPrepends ++ invPrepends ++ decPrepends ++
        [⟨.While seqCond seqInvs seqDec seqBody, source⟩]

  | .StaticCall name args =>
      let seqArgs ← args.mapM transformExpr
      let prepends ← takePrepends
      return prepends ++ [⟨.StaticCall name seqArgs, source⟩]

  | .Return (some retExpr) =>
      let seqRet ← transformExpr retExpr
      let prepends ← takePrepends
      modify fun s => { s with subst := [] }
      return prepends ++ [⟨.Return (some seqRet), source⟩]

  | .PrimitiveOp name args _ =>
      let seqArgs ← args.mapM transformExpr
      let prepends ← takePrepends
      return prepends ++ [⟨.PrimitiveOp name seqArgs, source⟩]
  | _ =>
      return [stmt]
  termination_by (sizeOf stmt, 0)
  decreasing_by
    all_goals (try term_by_mem)
    all_goals (apply Prod.Lex.left; try term_by_mem)
end

def transformProcedureBody (source: Option FileRange) (body : StmtExprMd) : LiftM StmtExprMd := do
  let stmts ← transformStmt body
  match stmts with
  | [single] => pure single
  | multiple => pure ⟨.Block multiple none, source ⟩

def transformProcedure (proc : Procedure) : LiftM Procedure := do
  modify fun s => { s with subst := [], prependedStmts := [], varCounters := [] }
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
    (model : SemanticModel) (imperativeCallees : List String) : Program :=
  let initState : LiftState := { model := model, imperativeCallees := imperativeCallees }
  let transform := program.staticProcedures.mapM transformProcedure
  let (seqProcedures, _) := transform.run initState
  { program with staticProcedures := seqProcedures }

end -- public section
end Laurel
