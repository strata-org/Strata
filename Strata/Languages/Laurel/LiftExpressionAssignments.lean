/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelFormat
import Strata.Languages.Core.Verifier

namespace Strata
namespace Laurel

/-
Transform assignments that appear in expression contexts into preceding statements.

Example 1 — Assignments in expression position:
  var y: int := x + (x := 1;) + x + (x := 2;);

Becomes:
  var $t_0 := x;
  x := 1;
  var $t_1 := x;
  var $t_2 := x;
  x := 2;
  var $t_3 := x;


  var $x_0 := x;              -- before snapshot 0
  x := 1;                     -- lifted first assignment
  var $x_1 := x;              -- before snapshot 1
  x := 2;                     -- lifted second assignment
  var y: int := $x_0 + $x_1 + $x_1 + x;

Example 2 — Conditional (if-then-else) inside an expression position:
  var z: bool := (if (b) { b := false; } else (b := true;)) || b;

Becomes:
  var $c_0: bool;
  if (b) {
    b := false;
    $c_0 := b;
  } else {
    b := true;
    $c_0 := b;
  }
  var z: bool := #c_0 || b;

Example 3 — Statement-level assignment:
  x := expr;

Becomes:
  var $x_0 := x;               -- before-snapshot of x
  x := expr;                   -- original assignment
-/

private abbrev TypeEnv := List (Identifier × HighType)

private def lookupType (env : TypeEnv) (name : Identifier) : HighType :=
  match env.find? (fun (n, _) => n == name) with
  | some (_, ty) => ty
  | none => .TInt  -- Default fallback

structure SequenceState where
  -- Stack of conditions we've entered (for wrapping lifted assignments)
  -- When entering a then-branch, we push the condition
  -- When entering an else-branch, we push the negated condition
  conditionStack : List StmtExpr := []
  prependedStmts : List StmtExpr := []
  diagnostics : List DiagnosticModel
  -- Maps variable names to their counter for generating unique temp names
  varCounters : List (Identifier × Nat) := []
  -- Forward snapshots: maps variable names to their current (post-assignment) snapshot.
  -- Used by Identifier lookups so that references AFTER an assignment use the after-snapshot.
  forwardSnapshots : List (Identifier × Identifier) := []
  -- Retroactive snapshots: maps variable names to their before-assignment snapshot.
  -- Used by applySnapshots to fix earlier sibling expressions that were processed
  -- before the assignment was encountered.
  retroactiveSnapshots : List (Identifier × Identifier) := []
  -- Type environment mapping variable names to their types
  env : TypeEnv := []

abbrev SequenceM := StateM SequenceState

def SequenceM.addPrependedStmt (stmt : StmtExpr) : SequenceM Unit :=
  modify fun s => { s with prependedStmts := stmt :: s.prependedStmts }

def SequenceM.addDiagnostic (d : DiagnosticModel) : SequenceM Unit :=
  modify fun s => { s with diagnostics := d :: s.diagnostics }

/-- Push a condition onto the stack (entering a conditional branch) -/
def SequenceM.pushCondition (cond : StmtExpr) : SequenceM Unit :=
  modify fun s => { s with conditionStack := cond :: s.conditionStack }

/-- Pop a condition from the stack (leaving a conditional branch) -/
def SequenceM.popCondition : SequenceM Unit :=
  modify fun s => { s with conditionStack := s.conditionStack.drop 1 }

/-- Get the current condition stack -/
def SequenceM.getConditionStack : SequenceM (List StmtExpr) := do
  return (← get).conditionStack

/-- Negate a condition expression -/
def negateCondition (cond : StmtExpr) : StmtExpr :=
  .PrimitiveOp .Not [cond]

/-- Execute action with a condition pushed onto the stack -/
def SequenceM.withCondition (cond : StmtExpr) (m : SequenceM α) : SequenceM α := do
  SequenceM.pushCondition cond
  let result ← m
  SequenceM.popCondition
  return result

/-- Wrap a statement in conditionals based on the condition stack.
    If conditionStack = [c1, c2, c3], we wrap as:
    if c3 { if c2 { if c1 { stmt } } }
    (innermost condition is first in the list) -/
def wrapInConditions (stmt : StmtExpr) (conditions : List StmtExpr) : StmtExpr :=
  conditions.foldl (fun inner cond => .IfThenElse cond inner none) stmt

def SequenceM.takePrependedStmts : SequenceM (List StmtExpr) := do
  let stmts := (← get).prependedStmts
  modify fun s => { s with prependedStmts := [] }
  return stmts.reverse

def SequenceM.freshTempFor (varName : Identifier) : SequenceM Identifier := do
  let counters := (← get).varCounters
  let counter := counters.find? (·.1 == varName) |>.map (·.2) |>.getD 0
  modify fun s => { s with varCounters := (varName, counter + 1) :: s.varCounters.filter (·.1 != varName) }
  return s!"${varName}_{counter}"

/-- Get the forward (post-assignment) snapshot for a variable -/
def SequenceM.getForwardSnapshot (varName : Identifier) : SequenceM (Option Identifier) := do
  return (← get).forwardSnapshots.find? (·.1 == varName) |>.map (·.2)

/-- Get the retroactive (pre-assignment) snapshot for a variable -/
def SequenceM.getRetroactiveSnapshot (varName : Identifier) : SequenceM (Option Identifier) := do
  return (← get).retroactiveSnapshots.find? (·.1 == varName) |>.map (·.2)

/-- Set the forward snapshot for a variable (used after an assignment) -/
def SequenceM.setForwardSnapshot (varName : Identifier) (snapshotName : Identifier) : SequenceM Unit := do
  modify fun s => { s with forwardSnapshots := (varName, snapshotName) :: s.forwardSnapshots.filter (·.1 != varName) }

/-- Set the retroactive snapshot for a variable (used to fix earlier siblings) -/
def SequenceM.setRetroactiveSnapshot (varName : Identifier) (snapshotName : Identifier) : SequenceM Unit := do
  modify fun s => { s with retroactiveSnapshots := (varName, snapshotName) :: s.retroactiveSnapshots.filter (·.1 != varName) }

/-- Clear both forward and retroactive snapshots for a variable -/
def SequenceM.clearSnapshots (varName : Identifier) : SequenceM Unit := do
  modify fun s => { s with
    forwardSnapshots := s.forwardSnapshots.filter (·.1 != varName)
    retroactiveSnapshots := s.retroactiveSnapshots.filter (·.1 != varName) }

def SequenceM.getVarType (varName : Identifier) : SequenceM HighType := do
  return lookupType (← get).env varName

def SequenceM.addToEnv (varName : Identifier) (ty : HighType) : SequenceM Unit := do
  modify fun s => { s with env := (varName, ty) :: s.env }

/-- Save the current snapshot state (both forward and retroactive) -/
def SequenceM.saveSnapshots : SequenceM (List (Identifier × Identifier) × List (Identifier × Identifier)) := do
  let s ← get
  return (s.forwardSnapshots, s.retroactiveSnapshots)

/-- Restore a previously saved snapshot state -/
def SequenceM.restoreSnapshots (saved : List (Identifier × Identifier) × List (Identifier × Identifier)) : SequenceM Unit := do
  modify fun s => { s with forwardSnapshots := saved.1, retroactiveSnapshots := saved.2 }

/-- Apply retroactive snapshot substitutions to an already-processed expression.
    This handles the case where a later assignment created a before-snapshot
    that should retroactively apply to earlier sibling expressions.
    Uses retroactiveSnapshots (before-snapshots), NOT forwardSnapshots. -/
partial def applyRetroactiveSnapshots (expr : StmtExpr) : SequenceM StmtExpr := do
  match expr with
  | .Identifier varName =>
      match ← SequenceM.getRetroactiveSnapshot varName with
      | some snapshotName => return .Identifier snapshotName
      | none => return expr
  | .PrimitiveOp op args =>
      let newArgs ← args.mapM applyRetroactiveSnapshots
      return .PrimitiveOp op newArgs
  | .IfThenElse cond thenBr elseBr =>
      let newCond ← applyRetroactiveSnapshots cond
      let newThen ← applyRetroactiveSnapshots thenBr
      let newElse ← match elseBr with
        | some e => pure (some (← applyRetroactiveSnapshots e))
        | none => pure none
      return .IfThenElse newCond newThen newElse
  | .StaticCall name args =>
      let newArgs ← args.mapM applyRetroactiveSnapshots
      return .StaticCall name newArgs
  | _ => return expr

def transformTarget (expr : StmtExpr) : SequenceM StmtExpr := do
  match expr with
  | .PrimitiveOp op args =>
      let seqArgs ← args.mapM transformTarget
      return .PrimitiveOp op seqArgs
  | .StaticCall name args =>
      let seqArgs ← args.mapM transformTarget
      return .StaticCall name seqArgs
  | _ => return expr  -- Identifiers and other targets stay as-is (no snapshot substitution)

/-- Ensure a retroactive snapshot exists for a variable before an assignment.
    If a forward snapshot already exists (from a prior assignment), reuse it
    as the retroactive target. Otherwise, create a new before-snapshot. -/
def SequenceM.ensureRetroactiveSnapshot (varName : Identifier) : SequenceM Unit := do
  -- If there's already a forward snapshot, use it as the retroactive target
  match ← SequenceM.getForwardSnapshot varName with
  | some existingSnapshot =>
      SequenceM.setRetroactiveSnapshot varName existingSnapshot
  | none =>
      -- No prior snapshot exists — create a before-snapshot
      let beforeName ← SequenceM.freshTempFor varName
      let varType ← SequenceM.getVarType varName
      let beforeDecl := StmtExpr.LocalVariable beforeName varType (some (.Identifier varName))
      SequenceM.addPrependedStmt beforeDecl
      SequenceM.setRetroactiveSnapshot varName beforeName

/-- Create an after-snapshot for a variable, set forward snapshot, return snapshot name -/
def SequenceM.afterSnapshot (varName : Identifier) : SequenceM Identifier := do
  let afterName ← SequenceM.freshTempFor varName
  let varType ← SequenceM.getVarType varName
  let afterDecl := StmtExpr.LocalVariable afterName varType (some (.Identifier varName))
  SequenceM.addPrependedStmt afterDecl
  -- Set forward snapshot so subsequent Identifier references use the after-snapshot
  SequenceM.setForwardSnapshot varName afterName
  return afterName

mutual
/-
Process an expression, extracting any assignments to preceding statements.
Returns the transformed expression with assignments replaced by variable references.
-/
def transformExpr (expr : StmtExpr) : SequenceM StmtExpr := do
  match expr with
  | .Assign targets value md =>
      -- This is an assignment in expression context
      let seqValue ← transformExpr value
      let condStack ← SequenceM.getConditionStack
      -- For each target: ensure retroactive snapshot exists, then execute the assignment
      for target in targets do
        match target with
        | .Identifier varName =>
            SequenceM.ensureRetroactiveSnapshot varName
        | _ => pure ()
      -- Wrap the assignment in conditionals if we're inside conditional branches
      let assignStmt := StmtExpr.Assign targets seqValue md
      let wrappedAssign := wrapInConditions assignStmt condStack
      SequenceM.addPrependedStmt wrappedAssign
      -- After-snapshot: captures value after the assignment
      -- This becomes the expression value of the assignment
      let firstTarget := targets.head?.getD (.Identifier "__unknown")
      match firstTarget with
      | .Identifier varName =>
          let afterName ← SequenceM.afterSnapshot varName
          return .Identifier afterName
      | _ => return firstTarget

  | .PrimitiveOp op args =>
      let seqArgs ← args.mapM transformExpr
      -- Apply retroactive snapshots to handle cases where a later arg's assignment
      -- created a before-snapshot that earlier args should use
      let finalArgs ← seqArgs.mapM applyRetroactiveSnapshots
      return .PrimitiveOp op finalArgs

  | .IfThenElse cond thenBranch elseBranch =>
      let seqCond ← transformExpr cond
      -- Snapshot the condition if it's a variable that might be modified by branches
      let stableCond ← match seqCond with
        | .Identifier varName =>
            -- Snapshot the condition variable to stabilize it
            let condSnapshotName ← SequenceM.freshTempFor varName
            let condType ← SequenceM.getVarType varName
            let condDecl := StmtExpr.LocalVariable condSnapshotName condType (some seqCond)
            SequenceM.addPrependedStmt condDecl
            -- Register as forward snapshot so branches can reuse it as retroactive target
            SequenceM.setForwardSnapshot varName condSnapshotName
            pure (.Identifier condSnapshotName)
        | _ => pure seqCond
      -- Save snapshot state so both branches start from the same state
      let savedSnapshots ← SequenceM.saveSnapshots
      -- Process then-branch with condition pushed onto stack
      let seqThen ← SequenceM.withCondition stableCond (transformExpr thenBranch)
      -- Restore snapshot state before processing else-branch
      -- so the else-branch doesn't see snapshots created by the then-branch
      SequenceM.restoreSnapshots savedSnapshots
      -- Process else-branch with negated condition pushed onto stack
      let seqElse ← match elseBranch with
        | some e => SequenceM.withCondition (negateCondition stableCond) (transformExpr e >>= (pure ∘ some))
        | none => pure none
      -- After both branches, we don't know which branch ran, so clear all snapshots.
      -- The IfThenElse expression itself already captures the branch results via
      -- the after-snapshot variables in seqThen/seqElse.
      -- Subsequent references should use the actual variable.
      modify fun s => { s with retroactiveSnapshots := [], forwardSnapshots := [] }
      return .IfThenElse stableCond seqThen seqElse

  | .StaticCall name args =>
      let seqArgs ← args.mapM transformExpr
      let finalArgs ← seqArgs.mapM applyRetroactiveSnapshots
      return .StaticCall name finalArgs

  | .Block stmts metadata =>
      -- Block in expression position: move all but last statement to prepended
      let rec processBlock (remStmts : List StmtExpr) : SequenceM StmtExpr := do
        match _: remStmts with
        | [] => return .Block [] metadata
        | [last] => transformExpr last
        | head :: tail =>
            match head with
            | .Assign targets value md =>
                let seqTargets ← targets.mapM transformTarget
                let seqValue ← transformExpr value
                -- Ensure retroactive snapshot exists before the assignment
                for target in seqTargets do
                  match target with
                  | .Identifier varName =>
                      SequenceM.ensureRetroactiveSnapshot varName
                  | _ => pure ()
                let assignStmt := StmtExpr.Assign seqTargets seqValue md
                SequenceM.addPrependedStmt assignStmt
                -- Clear snapshots after statement-level assignment
                -- (no retroactive fixing needed for statement-level assignments)
                for target in seqTargets do
                  match target with
                  | .Identifier varName => SequenceM.clearSnapshots varName
                  | _ => pure ()
            | _ =>
                let seqStmt ← transformStmt head
                for s in seqStmt do
                  SequenceM.addPrependedStmt s
            processBlock tail
        termination_by SizeOf.sizeOf remStmts
        decreasing_by
        all_goals (simp_wf; try omega)
        subst_vars; rename_i heq; cases heq; omega
      processBlock stmts

  -- Base cases: no assignments to extract
  | .LiteralBool _ => return expr
  | .LiteralInt _ => return expr
  | .Identifier varName => do
      -- If this variable has a forward snapshot (from a preceding assignment),
      -- use the after-snapshot. Otherwise return the variable as-is.
      match ← SequenceM.getForwardSnapshot varName with
      | some snapshotName => return .Identifier snapshotName
      | none => return expr
  | .LocalVariable _ _ _ => return expr
  | _ => return expr  -- Other cases
  termination_by SizeOf.sizeOf expr

/-
Process a statement, handling any assignments in its sub-expressions.
Returns a list of statements (the original one may be split into multiple).
-/
def transformStmt (stmt : StmtExpr) : SequenceM (List StmtExpr) := do
  match stmt with
  | @StmtExpr.Assert cond md =>
      let seqCond ← transformExpr cond
      SequenceM.addPrependedStmt <| StmtExpr.Assert seqCond md
      SequenceM.takePrependedStmts

  | @StmtExpr.Assume cond md =>
      let seqCond ← transformExpr cond
      SequenceM.addPrependedStmt <| StmtExpr.Assume seqCond md
      SequenceM.takePrependedStmts

  | .Block stmts metadata =>
      let seqStmts ← stmts.mapM transformStmt
      return [.Block (seqStmts.flatten) metadata]

  | .LocalVariable name ty initializer =>
      SequenceM.addToEnv name ty
      match initializer with
      | some initExpr => do
          let seqInit ← transformExpr initExpr
          -- Clear snapshots after processing the initializer so they don't leak
          -- into subsequent statements
          modify fun s => { s with forwardSnapshots := [], retroactiveSnapshots := [] }
          SequenceM.addPrependedStmt <| .LocalVariable name ty (some seqInit)
          SequenceM.takePrependedStmts
      | none =>
          return [stmt]

  | .Assign targets value md =>
      let seqTargets ← targets.mapM transformTarget
      let seqValue ← transformExpr value
      -- Snapshot BEFORE the assignment to preserve the old value
      for target in seqTargets do
        match target with
        | .Identifier varName =>
            let snapshotName ← SequenceM.freshTempFor varName
            let snapshotType ← SequenceM.getVarType varName
            let snapshotDecl := StmtExpr.LocalVariable snapshotName snapshotType (some (.Identifier varName))
            SequenceM.addPrependedStmt snapshotDecl
        | _ => pure ()
      SequenceM.addPrependedStmt <| .Assign seqTargets seqValue md
      -- Clear snapshots after statement-level assignment
      modify fun s => { s with forwardSnapshots := [], retroactiveSnapshots := [] }
      SequenceM.takePrependedStmts

  | .IfThenElse cond thenBranch elseBranch =>
      let seqCond ← transformExpr cond
      let seqThen ← do
        let stmts ← transformStmt thenBranch
        pure (.Block stmts none)
      let seqElse ← match elseBranch with
        | some e => do
            let se ← transformStmt e
            pure (some (.Block se none))
        | none => pure none
      SequenceM.addPrependedStmt <| .IfThenElse seqCond seqThen seqElse
      SequenceM.takePrependedStmts

  | .StaticCall name args =>
      let seqArgs ← args.mapM transformExpr
      SequenceM.addPrependedStmt <| .StaticCall name seqArgs
      SequenceM.takePrependedStmts

  | _ =>
      return [stmt]
  termination_by SizeOf.sizeOf stmt

end

def transformProcedureBody (body : StmtExpr) : SequenceM StmtExpr := do
  let seqStmts ← transformStmt body
  match seqStmts with
  | [single] => pure single
  | multiple => pure <| .Block multiple none

def transformProcedure (proc : Procedure) : SequenceM Procedure := do
  -- Initialize environment with procedure parameters
  let initEnv : TypeEnv := proc.inputs.map (fun p => (p.name, p.type)) ++
                           proc.outputs.map (fun p => (p.name, p.type))
  -- Reset state for each procedure to avoid cross-procedure contamination
  modify fun s => { s with conditionStack := [], forwardSnapshots := [], retroactiveSnapshots := [], varCounters := [], env := initEnv }
  match proc.body with
  | .Transparent bodyExpr =>
      let seqBody ← transformProcedureBody bodyExpr
      pure { proc with body := .Transparent seqBody }
  | _ => pure proc  -- Opaque and Abstract bodies unchanged

/--
Transform a program to lift all assignments that occur in an expression context.
-/
def liftExpressionAssignments (program : Program) : Except (Array DiagnosticModel) Program :=
  let (seqProcedures, afterState) := (program.staticProcedures.mapM transformProcedure).run
    { conditionStack := [], diagnostics := [] }
  if !afterState.diagnostics.isEmpty then
    .error afterState.diagnostics.toArray
  else
    .ok { program with staticProcedures := seqProcedures }

end Laurel
