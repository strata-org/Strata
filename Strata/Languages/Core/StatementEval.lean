/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Statement
import all Strata.Languages.Core.Statement
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Env
public import Strata.Languages.Core.CmdEval
public import Strata.Languages.Core.Statistics
public import Strata.DL.Lambda.LTyUnify
public import Strata.DL.Lambda.LExprT
public import Strata.DL.Imperative.StmtEval
public import Strata.Languages.Core.StatementSemantics
import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.CmdEval

---------------------------------------------------------------------

public section

namespace Core

namespace Statement

open Std (ToFormat Format format)
open Lambda

---------------------------------------------------------------------

inductive CondType where
  | Requires
  | Ensures

instance : ToString CondType where
  toString c := match c with
  | .Requires => "Requires"
  | .Ensures => "Ensures"

private abbrev VarSubst := List ((Expression.Ident × Option Lambda.LMonoTy) × Expression.Expr)

/--
Create proof obligations and path conditions originating from
a `.call` statement.
-/
private def callConditions (proc : Procedure)
    (condType : CondType) (conditions : ListMap String Procedure.Check)
    (subst :  VarSubst) :
    ListMap String Procedure.Check :=
  let names := List.map
               (fun k => s!"(Origin_{proc.header.name.name}_{condType}){k}")
               conditions.keys
  -- The replacement expressions must be closed (no dangling bvars).
  let sm := subst.map (fun (x, v) => (x.fst, v))
  let exprs := List.map
                (fun p =>
                  { p with expr := LExpr.substFvars p.expr sm })
                conditions.values
  List.zip names exprs

/--
Create substitution mapping from formal parameters to actual arguments.
-/
private def mkFormalArgSubst (proc : Procedure) (args : List Expression.Expr) (E : Env) : VarSubst :=
  let args' := args.map (fun a => E.exprEval a)
  let formal_tys := proc.header.inputs.keys.map
                      (fun k => ((k, none) : (Lambda.IdentT Lambda.LMonoTy Unit)))
  List.zip formal_tys args'

/--
Create fresh variables for return and LHS mapping.

Return mapping is used for postcondition substitution, i.e., to map procedure's
return parameter names to fresh variables.

LHS mapping is used for environment updates, i.e., to map caller's LHS variable
names to the _same_ fresh variables as above.

For example, if we have `call x := Inc(8)` where `Inc` returns a variable named `ret`:
Return mapping: `[("ret", fresh_var)]`
LHS mapping: `[("x", fresh_var)]`
-/
private def mkReturnSubst (proc : Procedure) (lhs : List Expression.Ident) (E : Env) :
    VarSubst × VarSubst × Env :=
  let lhs_tys := lhs.map (fun l => (E.exprEnv.state.findD l (none, .fvar () l none)).fst)
  let lhs_typed := lhs.zip lhs_tys
  let (lhs_fvars, E') := E.genFVars lhs_typed
  let return_tys := proc.header.outputs.keys.map
      (fun k => ((k, none) : (Lambda.IdentT Lambda.LMonoTy Unit)))
  let return_lhs_subst := List.zip return_tys lhs_fvars
  let lhs_post_subst := List.zip lhs_typed lhs_fvars
  (return_lhs_subst, lhs_post_subst, E')


/--
Extract the type from an expression that has already been typechecked (so e.g.
`.fvar` and `.op` nodes have their types stored in the `Option LMonoTy` field).
-/
private def getExprType (e : Expression.Expr) : Option LMonoTy :=
  match e with
  | .fvar _ _ ty => ty
  | .op _ _ ty => ty
  | .const _ c => some c.ty
  | .app _ fn _ =>
    -- For application, get the return type from the function type
    match getExprType fn with
    | some (.tcons "arrow" [_, ret]) => some ret
    | _ => none
  | .eq _ _ _ => some .bool
  | .quant _ _ _ _ _ _ => some .bool
  | .abs _ _ ty e =>
    match ty, getExprType e with
    | some ty1, some ty2 => some (.arrow ty1 ty2)
    | _, _ => none
  | .ite _ _ e1 e2 =>
    let ty1 := getExprType e1
    if ty1 == getExprType e2 then ty1 else none
  | .bvar _ _ => none

/--
Compute type substitution by unifying actual argument types with input types
and LHS types with output types.
-/
private def computeTypeSubst (input_tys output_tys: List LMonoTy)
  (args : List Expression.Expr) (lhs : List Expression.Ident) (E : Env) :
  Subst :=
  let actual_tys := args.filterMap getExprType
  let lhs_tys := lhs.filterMap (fun l =>
    (E.exprEnv.state.findD l (none, .fvar () l none)).fst)
  let input_constraints := actual_tys.zip input_tys
  let output_constraints := lhs_tys.zip output_tys
  let constraints := input_constraints ++ output_constraints
  match Constraints.unify constraints SubstInfo.empty with
  | .ok substInfo => substInfo.subst
  | .error _ => Subst.empty

/--
Evaluate a procedure call by inlining its contract.
`args` and `lhs` are matched positionally against
`proc.header.inputs` and `proc.header.outputs` respectively.
-/
def Command.inlineCallContract (E : Env)
    (lhs : List Expression.Ident) (pname : String) (args : List Expression.Expr)
    (md : Imperative.MetaData Expression) : Command × Env :=
  match Program.Procedure.find? E.program pname with
  | some proc =>
    let tySubst := computeTypeSubst proc.header.inputs.values
      proc.header.outputs.values args lhs E

    -- positional: formal_arg_subst zips header.inputs.keys with args
    let formal_arg_subst := mkFormalArgSubst proc args E
    -- positional: return_lhs_subst zips header.outputs.keys with lhs
    let (return_lhs_subst, lhs_post_subst, E) := mkReturnSubst proc lhs E

    -- Apply type substitution to preconditions to instantiate type variables.
    let preconditions_typed := proc.spec.preconditions.map
        (fun (l, c) => (l, { c with expr := c.expr.applySubst tySubst }))
    -- Generate precondition proof obligations.
    let preconditions := callConditions proc .Requires preconditions_typed formal_arg_subst
    let preconditions := preconditions.map
        (fun (l, e) => (l, Procedure.Check.mk (E.exprEval e.expr) e.attr e.md))
    let deferred_pre := ProofObligations.createAssertions E.pathConditions preconditions
    let E := { E with deferred := E.deferred ++ deferred_pre }

    -- Apply type substitution to postconditions to instantiate type variables.
    let postconditions_typed := proc.spec.postconditions.map
        (fun (l, c) => (l, { c with expr := c.expr.applySubst tySubst }))
    -- For inout parameters (in both inputs and outputs), the output mapping
    -- to a fresh post-call variable is the correct one; remove the duplicate
    -- input mapping so there is no ambiguity.
    let outputNames := proc.header.outputs.keys
    let formal_arg_subst_filtered := formal_arg_subst.filter fun ((id, _), _) =>
      !outputNames.contains id
    let postcond_subst := return_lhs_subst ++ formal_arg_subst_filtered
    let postconditions := callConditions proc .Ensures postconditions_typed postcond_subst

    -- Add postconditions to path conditions.
    let postconditions := (postconditions.keys.zip (Procedure.Spec.getCheckExprs postconditions)).map
      fun (label, e) => Imperative.PathConditionEntry.assumption label e
    let E := { E with pathConditions := (E.pathConditions.addInNewest postconditions)}

    -- Update environment with post-call state.
    let post_vars_mdata := lhs_post_subst.map
        (fun ((old, _), new) => Imperative.MetaDataElem.mk (.var old) (.expr new))
    let md' := md ++ post_vars_mdata.toArray
    let callArgs := args.map .inArg ++ lhs.map .outArg
    let c' := CmdExt.call pname callArgs md'
    let E := E.addToContext lhs_post_subst
    (c', E)
  | _ =>
    let callArgs := args.map .inArg ++ lhs.map .outArg
    let c' := CmdExt.call pname callArgs md
    let E := { E with error := some (.Misc f!"Procedure {pname} not found!") }
    (c', E)

def Command.eval (E : Env) (old_var_subst : SubstMap) (c : Command) : Command × Env :=
  match c with
  | .cmd c =>
    let (c, E) := Imperative.Cmd.eval { E with substMap := old_var_subst } c
    (.cmd c, E)
  | .call pname callArgs md =>
    let lhs := CallArg.getLhs callArgs
    let inArgs := CallArg.getInputExprs callArgs
    Command.inlineCallContract E lhs pname inArgs md

---------------------------------------------------------------------

mutual
/--
Generic function to check if a statement contains a specific command type.
-/
def Statement.containsCmd (predicate : Imperative.Cmd Expression → Bool) (s : Statement) : Bool :=
  match s with
  | .cmd (.cmd c) => predicate c
  | .cmd _ => false
  | .block _ inner_ss _ => Statements.containsCmds predicate inner_ss
  | .ite _ then_ss else_ss _ => Statements.containsCmds predicate then_ss ||
                                Statements.containsCmds predicate else_ss
  | .loop _ _ _ body_ss _ => Statements.containsCmds predicate body_ss
  | .funcDecl _ _ | .exit _ _ | .typeDecl _ _ => false  -- Function/type declarations and exits don't contain commands
  termination_by Imperative.Stmt.sizeOf s

/--
Generic function to check if statements contain a specific command type.
-/
def Statements.containsCmds (predicate : Imperative.Cmd Expression → Bool) (ss : Statements) : Bool :=
  match ss with
  | [] => false
  | s :: ss =>
    Statement.containsCmd predicate s || Statements.containsCmds predicate ss
  termination_by Imperative.Block.sizeOf ss
end

/--
Detect if statements contain any `cover` commands.
-/
def Statements.containsCovers (ss : Statements) : Bool :=
  Statements.containsCmds
    (fun c => match c with | .cover _ _ _ => true | _ => false) ss

/--
Detect if statements contain any `assert` commands.
-/
def Statements.containsAsserts (ss : Statements) : Bool :=
  Statements.containsCmds
    (fun c => match c with | .assert _ _ _ => true | _ => false) ss

mutual
/--
Collect all `cover` commands from a statement `s` with their labels and metadata.
-/
def Statement.collectCovers (s : Statement) : List (String × Imperative.MetaData Expression) :=
  match s with
  | .cmd (.cmd (.cover label _expr md)) => [(label, md)]
  | .cmd _ => []
  | .block _ inner_ss _ => Statements.collectCovers inner_ss
  | .ite _ then_ss else_ss _ => Statements.collectCovers then_ss ++ Statements.collectCovers else_ss
  | .loop _ _ _ body_ss _ => Statements.collectCovers body_ss
  | .funcDecl _ _ | .exit _ _ | .typeDecl _ _ => []  -- Function/type declarations and exits don't contain cover commands
  termination_by Imperative.Stmt.sizeOf s
/--
Collect all `cover` commands from statements `ss` with their labels and metadata.
-/
def Statements.collectCovers (ss : Statements) : List (String × Imperative.MetaData Expression) :=
  match ss with
  | [] => []
  | s :: ss =>
    Statement.collectCovers s ++ Statements.collectCovers ss
  termination_by Imperative.Block.sizeOf ss
end

mutual
/--
Collect all `assert` commands from a statement `s` with their labels and metadata.
-/
def Statement.collectAsserts (s : Statement) : List (String × Imperative.MetaData Expression) :=
  match s with
  | .cmd (.cmd (.assert label _expr md)) => [(label, md)]
  | .cmd _ => []
  | .block _ inner_ss _ => Statements.collectAsserts inner_ss
  | .ite _ then_ss else_ss _ => Statements.collectAsserts then_ss ++ Statements.collectAsserts else_ss
  | .loop _ _ _ body_ss _ => Statements.collectAsserts body_ss
  | .funcDecl _ _ | .exit _ _ | .typeDecl _ _ => []  -- Function/type declarations and exits don't contain assert commands
  termination_by Imperative.Stmt.sizeOf s
/--
Collect all `assert` commands from statements `ss` with their labels and metadata.
-/
def Statements.collectAsserts (ss : Statements) : List (String × Imperative.MetaData Expression) :=
  match ss with
  | [] => []
  | s :: ss =>
    Statement.collectAsserts s ++ Statements.collectAsserts ss
  termination_by Imperative.Block.sizeOf ss
end

/--
Create cover obligations for covers in an unreachable (dead) branch, including
the current path conditions so that a reachability check can detect unreachability.
The obligation expression is `false` (a cover that trivially fails).
-/
private def createUnreachableCoverObligations
    (pathConditions : Imperative.PathConditions Expression)
    (covers : List (String × Imperative.MetaData Expression)) :
    Imperative.ProofObligations Expression :=
  covers.toArray.map
    (fun (label, md) =>
      (Imperative.ProofObligation.mk label .cover pathConditions (LExpr.false ()) md))

/--
Create assert obligations for asserts in an unreachable (dead) branch, including
the current path conditions so that a reachability check can detect unreachability.
The obligation expression is `true` (an assert that trivially passes).
-/
private def createUnreachableAssertObligations
    (pathConditions : Imperative.PathConditions Expression)
    (asserts : List (String × Imperative.MetaData Expression)) :
    Imperative.ProofObligations Expression :=
  asserts.toArray.map
    (fun (label, md) =>
      let propType := match md.getPropertyType with
        | some s => if s == Imperative.MetaData.divisionByZero then .divisionByZero
                    else if s == Imperative.MetaData.arithmeticOverflow then .arithmeticOverflow
                    else if s == Imperative.MetaData.outOfBoundsAccess then .outOfBoundsAccess
                    else .assert
        | _ => .assert
      (Imperative.ProofObligation.mk label propType pathConditions (LExpr.true ()) md))

/--
Substitute free variables in an expression with their current values from the environment,
excluding the given parameter names (which are bound by the function, not free).
This implements value capture semantics for local function declarations (`funcDecl`).

Unlike global functions (which are evaluated at the top level with no local state),
local functions capture the values of free variables at the point of declaration.
Parameters are excluded because they are bound by the function definition and should
not be substituted with values from the enclosing scope.
-/
def captureFreevars (env : Env) (paramNames : List CoreIdent) (e : Expression.Expr) : Expression.Expr :=
  let freeVars := Lambda.LExpr.freeVars e
  let freeVarsToCapture := freeVars.filter (fun fv => fv.fst ∉ paramNames)
  -- The replacement expressions must be closed (no dangling bvars).
  let sm := freeVarsToCapture.filterMap (fun fv =>
    match env.exprEnv.state.find? fv.fst with
    | some (_, val) => some (fv.fst, val)
    | none => none)
  Lambda.LExpr.substFvars e sm

/--
An environment with an optional exit label.
-/
structure EnvWithNext where
  env  : Env
  /-- `none` = no exit active; `some none` = exit nearest block; `some (some l)` = exit block `l` -/
  exitLabel : Option (Option String) := .none
  /-- Stack of unmerged split conditions. Each entry is
      `(splitId, cond, side)` where `splitId` uniquely identifies the
      split origin (both paths from the same split get the same
      `splitId`), `cond` is the branch condition expression, and
      `side` distinguishes the branches (`true` = then, `false` = else
      for ITE splits). Last element is the most recent (innermost)
      unmerged split.

      Key invariant: both sides of a split always share the same
      `splitId` and `cond`; only `side` differs. Entries are only
      pushed in `processIteBranches` when `pathCap` is active.
      `mergeCondPairs` relies on this to correctly pair and merge
      paths. -/
  splitConds : Array (Nat × Expression.Expr × Bool) := #[]

/--
Collect proof obligations for an unreachable (dead) branch.
All covers in the dead branch fail (unreachable), and all asserts pass
(unsatisfiable path conditions).
-/
private def collectDeadBranchDeferred
    (ss_f : Statements) (cond : Expression.Expr)
    (pathConditions : Imperative.PathConditions Expression) :
    Imperative.ProofObligations Expression :=
  if Statements.containsCovers ss_f || Statements.containsAsserts ss_f then
    let deadLabel := toString (f!"<dead_branch: {cond.eraseTypes}>")
    let deadPathConds := pathConditions.push [.assumption deadLabel (LExpr.false ())]
    createUnreachableCoverObligations deadPathConds (Statements.collectCovers ss_f) ++
    createUnreachableAssertObligations deadPathConds (Statements.collectAsserts ss_f)
  else
    #[]

private def noStats : Statistics := {}

/--
Extract the first element from `pool` whose most recent `splitConds`
entry has the given `splitId`. Returns `(matched_element, remaining_pool)`
or `none`.
-/
private def extractMatchingSplitId (splitId : Nat)
    (pool acc : List EnvWithNext) :
    Option (EnvWithNext × List EnvWithNext) :=
  match pool with
  | [] => none
  | e :: rest =>
    match e.splitConds.back? with
    | some (sid, _, _) =>
      if sid == splitId then some (e, acc.reverse ++ rest)
      else extractMatchingSplitId splitId rest (e :: acc)
    | none => extractMatchingSplitId splitId rest (e :: acc)

private theorem extractMatchingSplitId_length (splitId : Nat)
    (pool acc : List EnvWithNext) (e : EnvWithNext) (rest : List EnvWithNext)
    (h : extractMatchingSplitId splitId pool acc = some (e, rest)) :
    rest.length + 1 = pool.length + acc.length := by
  induction pool generalizing acc with
  | nil => simp [extractMatchingSplitId] at h
  | cons e_t ts' ih =>
    simp only [extractMatchingSplitId] at h
    split at h
    · next sid _ _ =>
      split at h
      · simp at h; obtain ⟨_, rfl⟩ := h
        simp [List.length_reverse, List.length_append]; omega
      · have := ih (e_t :: acc) h; simp [List.length] at this ⊢; omega
    · have := ih (e_t :: acc) h; simp [List.length] at this ⊢; omega

private structure CondPairsResult where
  paired      : List EnvWithNext
  unmatched_t : List EnvWithNext
  unmatched_f : List EnvWithNext

/--
Find pairs of paths from opposite sides of the same split. Iterates
over `ts` (true-branch paths), searching `remaining_f` for a
false-branch path with a matching most-recent `splitId`. Matched pairs
are merged via `Env.merge` and collected in `paired`.

Invariant: every input path appears in exactly one output list.
Called only from `mergeCondPairs` on continuing paths (all have
`exitLabel = .none`), so the merged result inherits `e_t.exitLabel`
without loss.
-/
private def findCondPairs
    (ts unmatched_t remaining_f paired : List EnvWithNext) : CondPairsResult :=
  match ts with
  | [] => ⟨paired.reverse, unmatched_t.reverse, remaining_f⟩
  | e_t :: rest_ts =>
    match e_t.splitConds.back? with
    | some (splitId, split_cond, _) =>
      match extractMatchingSplitId splitId remaining_f [] with
      | some (e_f, remaining_f') =>
        let merged : EnvWithNext := {
          env := Env.merge split_cond e_t.env e_f.env,
          exitLabel := .none,
          splitConds := e_t.splitConds.pop }
        findCondPairs rest_ts unmatched_t remaining_f' (merged :: paired)
      | none =>
        findCondPairs rest_ts (e_t :: unmatched_t) remaining_f paired
    | none =>
      findCondPairs rest_ts (e_t :: unmatched_t) remaining_f paired

/-- Each match consumes one from `ts` and one from `remaining_f` but
    adds only one to `paired` — a net loss of one element per match.
    The `2 *` on `paired` counts each paired element twice: once as
    itself in the output, and once for the input it consumed. With
    empty accumulators (`findCondPairs ts [] fs []`), this simplifies
    to `output_total + r.paired.length = ts.length + fs.length`,
    i.e., `output_total = input_total - num_matches`. -/
private theorem findCondPairs_length
    (ts unmatched_t remaining_f paired : List EnvWithNext) :
    let r := findCondPairs ts unmatched_t remaining_f paired
    2 * r.paired.length + r.unmatched_t.length + r.unmatched_f.length =
      ts.length + unmatched_t.length + remaining_f.length + 2 * paired.length := by
  induction ts generalizing unmatched_t remaining_f paired with
  | nil => simp [findCondPairs, List.length_reverse]; omega
  | cons e_t rest ih =>
    unfold findCondPairs
    split
    · next splitId split_cond _ _ =>
      split
      · next e_f remaining_f' heq =>
        have hlen := extractMatchingSplitId_length splitId remaining_f [] e_f remaining_f' heq
        simp only [List.length_nil, Nat.add_zero] at hlen
        have ih := ih unmatched_t remaining_f' ({
          env := Env.merge split_cond e_t.env e_f.env,
          exitLabel := .none,
          splitConds := e_t.splitConds.pop } :: paired)
        simp only [List.length_cons] at ih ⊢
        omega
      · have ih := ih (e_t :: unmatched_t) remaining_f paired
        simp only [List.length_cons] at ih ⊢; omega
    · have ih := ih (e_t :: unmatched_t) remaining_f paired
      simp only [List.length_cons] at ih ⊢; omega


/--
Merge paths by matching splitId pairs from `splitConds`.
Each round finds at least one pair (when `paired` is non-empty),
strictly reducing the path count. Terminates by `ewns.length`.
Stops when the path count is at or below `target`.
-/
private def mergeCondPairs (ewns : List EnvWithNext)
    (target : Nat) : List EnvWithNext :=
  if ewns.length <= target then ewns
  else
  let p := (fun e : EnvWithNext =>
    match e.splitConds.back? with
    | some (_, _, b) => b
    | none => true)
  let parts := ewns.partition p
  let r := findCondPairs parts.1 [] parts.2 []
  -- processIteBranches always tags both sides of a split with the same
  -- splitId, so findCondPairs always finds at least one pair when paths
  -- from opposite sides exist. This guard prevents an infinite loop if
  -- that invariant were ever violated.
  if h_nonempty : r.paired.isEmpty then
    ewns
  else
    have h_part : parts.1.length + parts.2.length = ewns.length :=
      List.partition_length ewns p
    have h_fcpl : 2 * r.paired.length + r.unmatched_t.length + r.unmatched_f.length =
        parts.1.length + parts.2.length := by
      have h := findCondPairs_length parts.1 [] parts.2 []
      simp at h; exact h
    have h_pos : r.paired.length ≥ 1 := by
      cases h : r.paired
      · simp [h, List.isEmpty] at h_nonempty
      · simp
    have : (r.paired ++ r.unmatched_t ++ r.unmatched_f).length < ewns.length := by
      simp only [List.length_append]
      omega
    mergeCondPairs (r.paired ++ r.unmatched_t ++ r.unmatched_f) target
  termination_by ewns.length
  decreasing_by assumption

/-- Apply the path cap between statements. Continuing paths (no active
    exit) are merged down to the cap via `mergeCondPairs`. Exiting paths
    are not merged — they skip remaining statements so they don't
    contribute to exponential blowup.
    `pathCap` is read from the first path's `Env`, where it is set once
    at initialization and never modified during evaluation. -/
private def enforcePathCap (ewns : List EnvWithNext) (stats : Statistics) :
    List EnvWithNext × Statistics :=
  match ewns with
  | [] => ([], stats)
  | ewn :: _ =>
    match ewn.env.pathCap with
    | .some cap =>
      -- CLI rejects 0, but clamp defensively: cap 0 would needlessly
      -- attempt to merge a single remaining path below the target.
      let cap := max cap 1
      let (noExit, hasExit) :=
        ewns.partition (fun (e : EnvWithNext) => e.exitLabel.isNone)
      if noExit.length > cap then
        let merged := mergeCondPairs noExit cap
        (merged ++ hasExit,
         stats.increment s!"{Evaluator.Stats.betweenStmt_capMerged}")
      else (ewns, stats)
    | .none => (ewns, stats)

/-- Evaluate a single statement. `evalSub` and `processBranches` are
    the recursive calls from `evalAuxGo` and `processIteBranches`,
    threaded as parameters to break the mutual recursion. -/
private def evalOneStmt (old_var_subst : SubstMap)
    (Ewn : EnvWithNext) (s : Statement) (nextSplitId : Nat)
    (evalSub : EnvWithNext → Statements → Nat → List EnvWithNext × Statistics × Nat)
    (processBranches : EnvWithNext → Expression.Expr → Expression.Expr →
      Statements → Statements → Nat → List EnvWithNext × Statistics × Nat) :
    List EnvWithNext × Statistics × Nat :=
  match s with
  | .cmd c =>
    let (_, E) := Command.eval Ewn.env old_var_subst c
    ([{ Ewn with env := E, exitLabel := .none }], noStats, nextSplitId)
  | .block label ss _ =>
    let Ewn := { Ewn with env := Ewn.env.pushEmptyScope }
    let (Ewns, blockStats, nextSplitId) := evalSub Ewn ss nextSplitId
    let Ewns := Ewns.map
                    (fun (ewn : EnvWithNext) =>
                         let exitLabel := match ewn.exitLabel with
                           | .some .none => .none
                           | .some (.some l) => if l == label then .none else .some (.some l)
                           | other => other
                         { ewn with env := ewn.env.popScope,
                                    exitLabel := exitLabel })
    (Ewns, blockStats, nextSplitId)
  | .ite cond then_ss else_ss _ =>
    match cond with
    | .nondet =>
      let freshName : CoreIdent := ⟨s!"$__nondet_cond_{Ewn.env.pathConditions.length}", ()⟩
      let freshVar : Expression.Expr := .fvar () freshName none
      let initStmt := Statement.init freshName (.forAll [] (.tcons "bool" [])) .nondet Imperative.MetaData.empty
      let iteStmt := Imperative.Stmt.ite (.det freshVar) then_ss else_ss Imperative.MetaData.empty
      evalSub Ewn [initStmt, iteStmt] nextSplitId
    | .det c =>
      let cond' := Ewn.env.exprEval c
      match cond' with
      | .true _ | .false _ =>
        let (ss_live, ss_dead) :=
          if cond'.isTrue then (then_ss, else_ss) else (else_ss, then_ss)
        let deadDeferred := collectDeadBranchDeferred ss_dead c Ewn.env.pathConditions
        let (Ewns, liveStats, nextSplitId) := evalSub Ewn ss_live nextSplitId
        match Ewns with
        | [] => ([], liveStats, nextSplitId)
        | first :: restEwns =>
          ({ first with env.deferred :=
              deadDeferred ++ first.env.deferred } :: restEwns, liveStats, nextSplitId)
      | _ => processBranches Ewn c cond' then_ss else_ss nextSplitId
  | .loop _ _ _ _ _ =>
    panic! "Cannot evaluate `loop` statement. \
            Please transform your program to eliminate loops before \
            calling Core.Statement.evalAux"
  | .funcDecl decl _ =>
    let paramNames := decl.inputs.map (·.1)
    let func : Lambda.LFunc CoreLParams := {
      name := decl.name,
      typeArgs := decl.typeArgs,
      isConstr := decl.isConstr,
      inputs := decl.inputs.map (fun (id, ty) => (id, Lambda.LTy.toMonoTypeUnsafe ty)),
      output := Lambda.LTy.toMonoTypeUnsafe decl.output,
      body := decl.body.map (captureFreevars Ewn.env paramNames),
      attr := decl.attr,
      concreteEval := decl.concreteEval,
      axioms := decl.axioms.map (captureFreevars Ewn.env paramNames)
    }
    match Ewn.env.addFactoryFunc func with
    | .ok env' => ([{ Ewn with env := env' }], noStats, nextSplitId)
    | .error e =>
      ([{ Ewn with env := { Ewn.env with error := some (.Misc f!"{e}") } }], noStats, nextSplitId)
  | .typeDecl _ _ => ([Ewn], noStats, nextSplitId)
  | .exit l _ => ([{ Ewn with exitLabel := .some l}], noStats, nextSplitId)

mutual
/-- Batch symbolic evaluator: evaluates a statement list for all input
    paths simultaneously. Between each statement, enforces the path cap
    by merging continuing (.none exit) paths. -/
def evalAuxGo (steps : Nat) (old_var_subst : SubstMap)
    (Ewns : List EnvWithNext) (ss : Statements) (nextSplitId : Nat) :
    List EnvWithNext × Statistics × Nat :=
  let (errors, good) := Ewns.partition (fun (ewn : EnvWithNext) => ewn.env.error.isSome)
  if good.isEmpty then (Ewns, noStats, nextSplitId)
  else
  match steps with
  | 0 => (good.map (fun ewn =>
      { ewn with env := { ewn.env with error := some .OutOfFuel }, exitLabel := .none })
      ++ errors,
      noStats.increment s!"{Evaluator.Stats.simulatingStmtHitOutOfFuel}" good.length,
      nextSplitId)
  | steps' + 1 =>
    have _htermination_lemma : wfParam steps' < steps' + 1 := by simp [wfParam]
    match ss with
    | [] => (Ewns, noStats, nextSplitId)
    | s :: rest =>
      let (continuing, exiting) :=
        good.partition (fun (ewn : EnvWithNext) => ewn.exitLabel.isNone)
      let (resultsRev, stmtStats, nextSplitId) := continuing.foldl
        (fun (acc, statsAcc, nId) (ewn : EnvWithNext) =>
          let (res, stmtS, nId) := evalOneStmt old_var_subst ewn s nId
            (fun e ss nId => evalAuxGo steps' old_var_subst [e] ss nId)
            (fun e c c' t f nId => processIteBranches steps' old_var_subst e c c' t f nId)
          (res.reverse ++ acc, statsAcc.merge stmtS, nId))
        ([], noStats, nextSplitId)
      let results := resultsRev.reverse
      let stmtStats := stmtStats.increment
        s!"{Evaluator.Stats.simulatedStmts}" continuing.length
      let (results, stmtStats) := enforcePathCap results stmtStats
      -- Exiting paths first to preserve source order: they were set
      -- to exit before this statement, so their obligations precede
      -- obligations generated by continuing paths.
      let allPaths := exiting ++ results ++ errors
      let (finalResults, restStats, nextSplitId) :=
        evalAuxGo steps' old_var_subst allPaths rest nextSplitId
      (finalResults, stmtStats.merge restStats, nextSplitId)
  termination_by (steps, Imperative.Block.sizeOf ss)

def processIteBranches (steps : Nat) (old_var_subst : SubstMap) (Ewn : EnvWithNext)
    (cond cond' : Expression.Expr) (then_ss else_ss : Statements)
    (nextSplitId : Nat) : List EnvWithNext × Statistics × Nat :=
  let splitId := nextSplitId
  let nextSplitId := nextSplitId + 1
  let Ewn := { Ewn with env := Ewn.env.pushEmptyScope }
  let label_true := toString (f!"<label_ite_cond_true: {cond.eraseTypes}>")
  let label_false := toString (f!"<label_ite_cond_false: !({cond.eraseTypes})>")
  let path_conds_true := Ewn.env.pathConditions.push [.assumption label_true cond']
  let path_conds_false := Ewn.env.pathConditions.push
                            [.assumption label_false (Lambda.LExpr.ite () cond' (LExpr.false ()) (LExpr.true ()))]
  have : 1 <= Imperative.Block.sizeOf then_ss := by
   unfold Imperative.Block.sizeOf; split <;> omega
  have : 1 <= Imperative.Block.sizeOf else_ss := by
   unfold Imperative.Block.sizeOf; split <;> omega
  have : Imperative.Block.sizeOf then_ss < Imperative.Block.sizeOf then_ss +
                                          Imperative.Block.sizeOf else_ss := by
    omega
  have : Imperative.Block.sizeOf else_ss < Imperative.Block.sizeOf then_ss +
                                          Imperative.Block.sizeOf else_ss := by
   omega
  let (Ewns_t, stats_t, nextSplitId) := evalAuxGo steps old_var_subst
                  [{Ewn with env := {Ewn.env with pathConditions := path_conds_true}}]
                  then_ss nextSplitId
  let (Ewns_f, stats_f, nextSplitId) := evalAuxGo steps old_var_subst
                  [{Ewn with env := {Ewn.env with pathConditions := path_conds_false,
                                                  deferred := #[]}}]
                  else_ss nextSplitId
  let branchStats := stats_t.merge stats_f
  match Ewns_t, Ewns_f with
  | [{ env := E_t, exitLabel := .none, ..}],
    [{ env := E_f, exitLabel := .none, ..}] =>
    ([{ env := (Env.merge cond' E_t E_f).popScope, exitLabel := .none }],
     branchStats.increment s!"{Evaluator.Stats.processIteBranches_merged}",
     nextSplitId)
  | _, _ =>
    let popAll (ewns : List EnvWithNext) :=
      ewns.map (fun ewn => { ewn with env := ewn.env.popScope })
    match Ewn.env.pathCap with
    | .some _ =>
      let tagSplit (ewns : List EnvWithNext) (side : Bool) : List EnvWithNext :=
        ewns.map (fun ewn =>
          { ewn with splitConds := ewn.splitConds.push (splitId, cond', side) })
      let Ewns_tagged := tagSplit Ewns_t true ++ tagSplit Ewns_f false
      (popAll Ewns_tagged,
       branchStats.increment s!"{Evaluator.Stats.processIteBranches_diverged}",
       nextSplitId)
    | .none =>
      (popAll (Ewns_t ++ Ewns_f),
       branchStats.increment s!"{Evaluator.Stats.processIteBranches_diverged}",
       nextSplitId)
  termination_by (steps, Imperative.Block.sizeOf then_ss + Imperative.Block.sizeOf else_ss)

end

def evalAux (E : Env) (old_var_subst : SubstMap) (ss : Statements) (optExit : Option (Option String)) :
  List EnvWithNext × Statistics :=
  let ewn : EnvWithNext := { env := E, exitLabel := optExit }
  let (result, stats, _) := evalAuxGo (Imperative.Block.sizeOf ss) old_var_subst [ewn] ss 0
  (result, stats)

def exitToError : EnvWithNext → Env
  | { env, exitLabel := .none, .. } => env
  | { env, exitLabel := .some (.some l), .. } => ({ env with error := some (.LabelNotExists l) })
  | { env, exitLabel := .some .none, .. } => ({ env with error := some (.Misc "exit outside of any block") })

/--
A symbolic simulator for statements yielding a list of resulting environments.

The argument `old_var_subst` below is a substitution map from global variables
to their pre-state value in the enclosing procedure of `ss`.
-/
def eval (E : Env) (old_var_subst : SubstMap) (ss : Statements) : List Env × Statistics :=
  let (ewns, stats) := evalAux E old_var_subst ss .none
  (ewns.map exitToError, stats)

/--
A symbolic simulator for statements yielding one environment.
-/
def evalOne (E : Env) (old_var_subst : SubstMap) (ss : Statements) : Env :=
  match (eval E old_var_subst ss).fst with
  | [E'] => E'
  | _ => ({ E with error := some (.Misc "More than one result environment") })

---------------------------------------------------------------------

mutual

/--
Interpret a single procedure call.

Importantly, this creates a separate Env to execute the body of the procedure with,
which initially only contains input/output variables.
The resulting Env is the original passed in Env with the output variables copied back into it.
-/
def Command.runCall (lhs : List Expression.Ident) (procName : String) (args : List Expression.Expr)
    (fuel : Nat) (E : Env) : Env :=
    match fuel with
    | 0 => { E with error := some .OutOfFuel }
    | fuel' + 1 =>
    match Program.Procedure.find? E.program ⟨procName, ()⟩ with
    | none => CmdEval.updateError E (.Misc s!"procedure '{procName}' not found")
    | some proc =>
      if proc.body.isEmpty then CmdEval.updateError E (.Misc s!"procedure '{proc.header.name}' has no body")
      else
        match args.mapM (LExpr.run E.exprEnv) with
        | .error s => CmdEval.updateError E (.Misc s)
        | .ok argVals =>
          let formalBindings : List (CoreIdent × (Option LMonoTy × Expression.Expr)) :=
            proc.header.inputs.keys.zip proc.header.inputs.values |>.zip argVals
            |>.map fun ((name, ty), val) => (name, (some ty, val))
          if argVals.length != proc.header.inputs.keys.length then
            CmdEval.updateError E (.Misc s!"procedure '{procName}': expected {proc.header.inputs.keys.length} arguments, got {argVals.length}")
          else
            let outputBindings : List (CoreIdent × (Option LMonoTy × Expression.Expr)) :=
              proc.header.outputs.keys.zip proc.header.outputs.values
              |>.map fun (name, ty) => (name, (some ty, LExpr.fvar () name none))
            let callEnv : Env := { E with
              exprEnv := { E.exprEnv with
                state := [formalBindings ++ outputBindings] } }
            let ops : Imperative.RunOps Expression Command Env := {
              evalExpr := fun E e =>
                some (e.eval E.exprEnv.config.fuel E.exprEnv)
              evalCmd := Command.run fuel'
              extendEval := fun E decl =>
                match E.addFactoryFunc {
                  name := decl.name
                  typeArgs := decl.typeArgs
                  isConstr := decl.isConstr
                  inputs := decl.inputs.map (fun (id, ty) => (id, Lambda.LTy.toMonoTypeUnsafe ty))
                  output := Lambda.LTy.toMonoTypeUnsafe decl.output
                  body := decl.body
                  attr := decl.attr
                  concreteEval := decl.concreteEval
                  axioms := decl.axioms
                } with
                | .ok E' => E'
                | .error _ => E
              pushScope := fun E => E.pushEmptyScope
              popScope := fun E => E.popScope
              hasError := fun E => E.error.isSome
              addError := fun E msg => CmdEval.updateError E (.Misc msg)
            }
            let config : Imperative.RunConfig Expression Command Env :=
              .stmts proc.body callEnv
            let configAfter := Imperative.runStmt ops fuel' config
            match configAfter with
            | .terminal callEnv' =>
              match callEnv'.error with
              | some _ => { E with error := callEnv'.error }
              | none =>
                if lhs.length != proc.header.outputs.keys.length then
                  CmdEval.updateError E (.Misc s!"procedure '{procName}': expected {proc.header.outputs.keys.length} output arguments, got {lhs.length}")
                else
                  let outputVals := proc.header.outputs.keys.map fun name =>
                    (callEnv'.exprEnv.state.findD name (none, LExpr.fvar () name none)).snd
                  lhs.zip outputVals |>.foldl (fun env (name, val) =>
                    env.insertInContext (name, none) val) E
            | _ => CmdEval.updateError E (.Misc "failed to terminate")

def Command.run (fuel : Nat) (E : Env) (c : Command) : Env :=
  match c with
  | .cmd c =>
    Imperative.Cmd.run E c
  | .call pname args _md =>
    Command.runCall (CallArg.getLhs args) pname (CallArg.getInArgs args) fuel E

end

end Statement
end Core

end -- public section

---------------------------------------------------------------------
