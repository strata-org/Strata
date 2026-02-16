/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelFormat
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Core.Verifier
import Strata.Util.Tactics

namespace Strata
namespace Laurel

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
  subst : SubstMap := []
  /-- Type environment -/
  env : TypeEnv := []
  /-- Type definitions from the program -/
  types : List TypeDefinition := []
  /-- Global counter for fresh conditional variables -/
  condCounter : Nat := 0

abbrev LiftM := StateM LiftState

private def emptyMd : Imperative.MetaData Core.Expression := #[]

/-- Wrap a StmtExpr value with empty metadata -/
private def bare (v : StmtExpr) : StmtExprMd := ⟨v, emptyMd⟩

/-- Wrap a HighType value with empty metadata -/
private def bareType (v : HighType) : HighTypeMd := ⟨v, emptyMd⟩

private def freshTempFor (varName : Identifier) : LiftM Identifier := do
  let counters := (← get).varCounters
  let counter := counters.find? (·.1 == varName) |>.map (·.2) |>.getD 0
  modify fun s => { s with varCounters := (varName, counter + 1) :: s.varCounters.filter (·.1 != varName) }
  return s!"${varName}_{counter}"

private def freshCondVar : LiftM Identifier := do
  let n := (← get).condCounter
  modify fun s => { s with condCounter := n + 1 }
  return s!"$c_{n}"

private def addPrepend (stmt : StmtExprMd) : LiftM Unit :=
  modify fun s => { s with prependedStmts := stmt :: s.prependedStmts }

private def takePrepends : LiftM (List StmtExprMd) := do
  let stmts := (← get).prependedStmts
  modify fun s => { s with prependedStmts := [] }
  return stmts

private def getVarType (varName : Identifier) : LiftM HighTypeMd := do
  let env := (← get).env
  match env.find? (fun (n, _) => n == varName) with
  | some (_, ty) => return ty
  | none => panic s!"Could not find {varName} in environment."

private def addToEnv (varName : Identifier) (ty : HighTypeMd) : LiftM Unit :=
  modify fun s => { s with env := (varName, ty) :: s.env }

private def getSubst (varName : Identifier) : LiftM Identifier := do
  match (← get).subst.find? varName with
  | some mapped => return mapped
  | none => return varName

private def setSubst (varName : Identifier) (value : Identifier) : LiftM Unit :=
  modify fun s => { s with subst := s.subst.insert varName value }

private def computeType (expr : StmtExprMd) : LiftM HighTypeMd := do
  let s ← get
  return computeExprType s.env s.types expr

/-- Check if an expression contains any assignments (recursively). -/
private def containsAssignment (expr : StmtExprMd) : Bool :=
  match expr with
  | WithMetadata.mk val _ =>
  match val with
  | .Assign .. => true
  | .StaticCall _ args1 => args1.attach.any (fun x => containsAssignment x.val)
  | .PrimitiveOp _ args2 => args2.attach.any (fun x => containsAssignment x.val)
  | .Block stmts _ => stmts.attach.any (fun x => containsAssignment x.val)
  | .IfThenElse cond th el =>
      containsAssignment cond || containsAssignment th ||
      match el with | some e => containsAssignment e | none => false
  | _ => false
  termination_by expr
  decreasing_by
    all_goals ((try cases x); simp_all; try term_by_mem)

/--
Shared logic for lifting an assignment in expression position:
prepends the assignment, creates before-snapshots for all targets,
and updates substitutions. The value should already be transformed by the caller.
-/
private def liftAssignExpr (targets : List StmtExprMd) (seqValue : StmtExprMd)
    (md : Imperative.MetaData Core.Expression) : LiftM Unit := do
  -- Prepend the assignment itself
  addPrepend (⟨.Assign targets seqValue, md⟩)
  -- Create a before-snapshot for each target and update substitutions
  for target in targets do
    match target.val with
    | .Identifier varName =>
        let snapshotName ← freshTempFor varName
        let varType ← getVarType varName
        -- Snapshot goes before the assignment (cons pushes to front)
        addPrepend (⟨.LocalVariable snapshotName varType (some (⟨.Identifier varName, md⟩)), md⟩)
        setSubst varName snapshotName
    | _ => pure ()

mutual
/--
Process an expression in expression context, traversing arguments right to left.
Assignments are lifted to prependedStmts and replaced with snapshot variable references.
-/
def transformExpr (expr : StmtExprMd) : LiftM StmtExprMd := do
  match expr with
  | WithMetadata.mk val md =>
  match val with
  | .Identifier name =>
      return ⟨.Identifier (← getSubst name), md⟩

  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ => return expr

  | .Assign targets value =>
      -- The expression result is the current substitution for the first target
      -- (we already know what it maps to AFTER this assignment from right-to-left traversal)
      let firstTarget := targets.head?.getD (panic "Assign must have non-empty targets")
      let resultExpr ← match firstTarget.val with
        | .Identifier varName => pure (⟨.Identifier (← getSubst varName), md⟩)
        | _ => panic "Non-identifier targets not supported in the lift expression phase"

      -- Use the original value (not seqValue) for the prepended assignment,
      -- because prepended statements execute in program order and don't need substitutions.
      liftAssignExpr targets value md

      return resultExpr

  | .PrimitiveOp op args =>
      -- Process arguments right to left
      let seqArgs ← args.reverse.mapM transformExpr
      return ⟨.PrimitiveOp op seqArgs.reverse, md⟩

  | .StaticCall name args =>
      let seqArgs ← args.reverse.mapM transformExpr
      return ⟨.StaticCall name seqArgs.reverse, md⟩

  | .IfThenElse cond thenBranch elseBranch =>
      let thenHasAssign := containsAssignment thenBranch
      let elseHasAssign := match elseBranch with
        | some e => containsAssignment e
        | none => false
      if thenHasAssign || elseHasAssign then
        -- Lift the entire if-then-else. Introduce a fresh variable for the result.
        let condVar ← freshCondVar
        let seqCond ← transformExpr cond
        -- Save outer state
        let savedSubst := (← get).subst
        let savedPrepends := (← get).prependedStmts
        -- Process then-branch from scratch
        modify fun s => { s with prependedStmts := [], subst := [] }
        let seqThen ← transformExpr thenBranch
        let thenPrepends ← takePrepends
        let thenBlock := bare (.Block (thenPrepends ++ [⟨.Assign [bare (.Identifier condVar)] seqThen, md⟩]) none)
        -- Process else-branch from scratch
        modify fun s => { s with prependedStmts := [], subst := [] }
        let seqElse ← match elseBranch with
          | some e => do
              let se ← transformExpr e
              let elsePrepends ← takePrepends
              pure (some (bare (.Block (elsePrepends ++ [⟨.Assign [bare (.Identifier condVar)] se, md⟩]) none)))
          | none => pure none
        -- Restore outer state
        modify fun s => { s with subst := savedSubst, prependedStmts := savedPrepends }
        -- Infer type from the then-branch result
        let condType ← computeType seqThen
        -- IfThenElse added first (cons puts it deeper), then declaration (cons puts it on top)
        -- Output order: declaration, then if-then-else
        addPrepend (⟨.IfThenElse seqCond thenBlock seqElse, md⟩)
        addPrepend (bare (.LocalVariable condVar condType none))
        return bare (.Identifier condVar)
      else
        -- No assignments in branches — recurse normally
        let seqCond ← transformExpr cond
        let seqThen ← transformExpr thenBranch
        let seqElse ← match elseBranch with
          | some e => pure (some (← transformExpr e))
          | none => pure none
        return ⟨.IfThenElse seqCond seqThen seqElse, md⟩

  | .Block stmts metadata =>
      -- Block in expression position: lift all but last to prepends
      match h_last : stmts.getLast? with
      | none => return bare (.Block [] metadata)
      | some last => do
          have := List.mem_of_getLast? h_last

          -- Pre-populate the environment with all LocalVariable declarations
          -- so that getVarType works when creating snapshots
          for s in stmts do
            match s with
            | WithMetadata.mk val _ =>
            match val with
            | .LocalVariable name ty _ => addToEnv name ty
            | _ => pure ()
          -- Process all-but-last right to left using transformExprDiscarded
          for nonLastStatement in stmts.dropLast.reverse.attach do
            transformExprDiscarded nonLastStatement
          -- Last element is the expression value
          transformExpr last

  | .LocalVariable name ty initializer =>
      -- Add the variable to the environment
      addToEnv name ty
      -- If the substitution map has an entry for this variable, it was
      -- assigned to the right and we need to lift this declaration so it
      -- appears before the snapshot that references it.
      let hasSubst := (← get).subst.find? name |>.isSome
      if hasSubst then
        match initializer with
        | some initExpr =>
            let seqInit ← transformExpr initExpr
            addPrepend (⟨.LocalVariable name ty (some seqInit), expr.md⟩)
        | none =>
            addPrepend (⟨.LocalVariable name ty none, expr.md⟩)
        return ⟨.Identifier (← getSubst name), expr.md⟩
      else
        return expr

  | _ => return expr
  termination_by (sizeOf expr, 0)
  decreasing_by
    all_goals (simp_all; try term_by_mem)
    have := List.dropLast_subset stmts
    have stmtInStmts : nonLastStatement.val ∈ stmts := by grind
    -- term_by_mem gets a type error here, so we do it manually
    have xSize := List.sizeOf_lt_of_mem stmtInStmts
    omega

/--
Transform an expression whose result value is discarded (e.g. non-last elements in a block). All side-effects in Laurel are represented as assignments, so we only need to lift assignments, anything else can be forgotten.
-/
def transformExprDiscarded (expr2 : StmtExprMd) : LiftM Unit := do
  match _hExpr: expr2 with
  | WithMetadata.mk val md =>
  match _h: val with
  | .Assign targets value =>
      -- Transform value to process nested assignments (side-effect only),
      -- but use original value for the prepended assignment (no substitutions needed).
      let _ ← transformExpr value
      liftAssignExpr targets value md
  | _ =>
      let result ← transformExpr expr2
      addPrepend result
  termination_by (sizeOf expr2, 1)
  decreasing_by
    simp_all; omega
    rw [<- _hExpr]; omega

/--
Process a statement, handling any assignments in its sub-expressions.
Returns a list of statements (the original may expand into multiple).
-/
def transformStmt (stmt : StmtExprMd) : LiftM (List StmtExprMd) := do
  match stmt with
  | WithMetadata.mk val md =>
  match val with
  | .Assert cond =>
      let seqCond ← transformExpr cond
      let prepends ← takePrepends
      return prepends ++ [⟨.Assert seqCond, md⟩]

  | .Assume cond =>
      let seqCond ← transformExpr cond
      let prepends ← takePrepends
      return prepends ++ [⟨.Assume seqCond, md⟩]

  | .Block stmts metadata =>
      let seqStmts ← stmts.mapM transformStmt
      return [bare (.Block seqStmts.flatten metadata)]

  | .LocalVariable name ty initializer =>
      addToEnv name ty
      match initializer with
      | some initExpr =>
          let seqInit ← transformExpr initExpr
          let prepends ← takePrepends
          modify fun s => { s with subst := [] }
          return prepends ++ [⟨.LocalVariable name ty (some seqInit), md⟩]
      | none =>
          return [stmt]

  | .Assign targets value =>
      let seqValue ← transformExpr value
      let prepends ← takePrepends
      modify fun s => { s with subst := [] }
      return prepends ++ [⟨.Assign targets seqValue, md⟩]

  | .IfThenElse cond thenBranch elseBranch =>
      let seqCond ← transformExpr cond
      let condPrepends ← takePrepends
      let seqThen ← do
        let stmts ← transformStmt thenBranch
        pure (bare (.Block stmts none))
      let seqElse ← match elseBranch with
        | some e => do
            let se ← transformStmt e
            pure (some (bare (.Block se none)))
        | none => pure none
      return condPrepends ++ [⟨.IfThenElse seqCond seqThen seqElse, md⟩]

  | .While cond invs dec body =>
      let seqCond ← transformExpr cond
      let condPrepends ← takePrepends
      let seqBody ← do
        let stmts ← transformStmt body
        pure (bare (.Block stmts none))
      return condPrepends ++ [⟨.While seqCond invs dec seqBody, md⟩]

  | .StaticCall name args =>
      let seqArgs ← args.mapM transformExpr
      let prepends ← takePrepends
      return prepends ++ [⟨.StaticCall name seqArgs, md⟩]

  | _ =>
      return [stmt]
  termination_by (sizeOf stmt, 0)
  decreasing_by
    all_goals term_by_mem
end

def transformProcedureBody (body : StmtExprMd) : LiftM StmtExprMd := do
  let stmts ← transformStmt body
  match stmts with
  | [single] => pure single
  | multiple => pure (bare (.Block multiple none))

def transformProcedure (proc : Procedure) : LiftM Procedure := do
  let initEnv : TypeEnv :=
    proc.inputs.map (fun p => (p.name, p.type)) ++
    proc.outputs.map (fun p => (p.name, p.type))
  modify fun s => { s with subst := [], prependedStmts := [], varCounters := [], env := initEnv }
  match proc.body with
  | .Transparent bodyExpr =>
      let seqBody ← transformProcedureBody bodyExpr
      pure { proc with body := .Transparent seqBody }
  | _ => pure proc

/--
Transform a program to lift all assignments that occur in an expression context.
-/
def liftExpressionAssignments (program : Program) : Program :=
  let initState : LiftState := { types := program.types }
  let (seqProcedures, _) := (program.staticProcedures.mapM transformProcedure).run initState
  { program with staticProcedures := seqProcedures }

end Laurel
