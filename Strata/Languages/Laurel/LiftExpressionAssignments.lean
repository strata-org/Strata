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

For example:
  if ((x := x + 1) == (y := x)) { ... }

Becomes:
  var x1 := x + 1;
  x := x1;
  var y1 := x;
  y := y1;
  if (x1 == y1) { ... }
-/

private abbrev TypeEnv := List (Identifier × HighType)

private def lookupType (env : TypeEnv) (name : Identifier) : HighType :=
  match env.find? (fun (n, _) => n == name) with
  | some (_, ty) => ty
  | none => .TInt  -- Default fallback

structure SequenceState where
  insideCondition : Bool
  prependedStmts : List StmtExpr := []
  diagnostics : List DiagnosticModel
  -- Maps variable names to their counter for generating unique temp names
  varCounters : List (Identifier × Nat) := []
  -- Maps variable names to their current snapshot variable name
  -- When an assignment is lifted, we create a snapshot and record it here
  -- Subsequent references to the variable should use the snapshot
  varSnapshots : List (Identifier × Identifier) := []
  -- Type environment mapping variable names to their types
  env : TypeEnv := []

abbrev SequenceM := StateM SequenceState

def SequenceM.addPrependedStmt (stmt : StmtExpr) : SequenceM Unit :=
  modify fun s => { s with prependedStmts := stmt :: s.prependedStmts }

def SequenceM.addDiagnostic (d : DiagnosticModel) : SequenceM Unit :=
  modify fun s => { s with diagnostics := d :: s.diagnostics }

def checkOutsideCondition(md: Imperative.MetaData Core.Expression): SequenceM Unit := do
  let state <- get
  if state.insideCondition then
    let fileRange := (Imperative.getFileRange md).get!
    SequenceM.addDiagnostic {
        fileRange := fileRange,
        message := "Could not lift assigment in expression that is evaluated conditionally"
    }

def SequenceM.setInsideCondition : SequenceM Unit := do
  modify fun s => { s with insideCondition := true }

def SequenceM.withInsideCondition (m : SequenceM α) : SequenceM α := do
  let oldInsideCondition := (← get).insideCondition
  modify fun s => { s with insideCondition := true }
  let result ← m
  modify fun s => { s with insideCondition := oldInsideCondition }
  return result

def SequenceM.takePrependedStmts : SequenceM (List StmtExpr) := do
  let stmts := (← get).prependedStmts
  modify fun s => { s with prependedStmts := [] }
  return stmts.reverse

def SequenceM.freshTempFor (varName : Identifier) : SequenceM Identifier := do
  let counters := (← get).varCounters
  let counter := counters.find? (·.1 == varName) |>.map (·.2) |>.getD 0
  modify fun s => { s with varCounters := (varName, counter + 1) :: s.varCounters.filter (·.1 != varName) }
  return s!"${varName}_{counter}"

def SequenceM.getSnapshot (varName : Identifier) : SequenceM (Option Identifier) := do
  return (← get).varSnapshots.find? (·.1 == varName) |>.map (·.2)

def SequenceM.setSnapshot (varName : Identifier) (snapshotName : Identifier) : SequenceM Unit := do
  modify fun s => { s with varSnapshots := (varName, snapshotName) :: s.varSnapshots.filter (·.1 != varName) }

def SequenceM.getVarType (varName : Identifier) : SequenceM HighType := do
  return lookupType (← get).env varName

def SequenceM.addToEnv (varName : Identifier) (ty : HighType) : SequenceM Unit := do
  modify fun s => { s with env := (varName, ty) :: s.env }

def transformTarget (expr : StmtExpr) : SequenceM StmtExpr := do
  match expr with
  | .PrimitiveOp op args =>
      let seqArgs ← args.mapM transformTarget
      return .PrimitiveOp op seqArgs
  | .StaticCall name args =>
      let seqArgs ← args.mapM transformTarget
      return .StaticCall name seqArgs
  | _ => return expr  -- Identifiers and other targets stay as-is (no snapshot substitution)

mutual
/-
Process an expression, extracting any assignments to preceding statements.
Returns the transformed expression with assignments replaced by variable references.
-/
def transformExpr (expr : StmtExpr) : SequenceM StmtExpr := do
  match expr with
  | .Assign targets value md =>
      checkOutsideCondition md
      -- This is an assignment in expression context
      -- We need to: 1) execute the assignment, 2) capture the value in a temporary
      -- This prevents subsequent assignments to the same variable from changing the value
      let seqValue ← transformExpr value
      let assignStmt := StmtExpr.Assign targets seqValue md
      SequenceM.addPrependedStmt assignStmt
      -- For each target, create a snapshot variable so subsequent references
      -- to that variable will see the value after this assignment
      for target in targets do
        match target with
        | .Identifier varName =>
            let snapshotName ← SequenceM.freshTempFor varName
            let snapshotType ← SequenceM.getVarType varName
            let snapshotDecl := StmtExpr.LocalVariable snapshotName snapshotType (some (.Identifier varName))
            SequenceM.addPrependedStmt snapshotDecl
            SequenceM.setSnapshot varName snapshotName
        | _ => pure ()
      -- Create a temporary variable to capture the assigned value (for expression result)
      -- Use TInt as the type (could be refined with type inference)
      -- For multi-target assigns, use the first target
      let firstTarget := targets.head?.getD (.Identifier "__unknown")
      let tempName ← match firstTarget with
        | .Identifier name => SequenceM.freshTempFor name
        | _ => SequenceM.freshTempFor "__expr"
      let tempDecl := StmtExpr.LocalVariable tempName .TInt (some firstTarget)
      SequenceM.addPrependedStmt tempDecl
      -- Return the temporary variable as the expression value
      return .Identifier tempName

  | .PrimitiveOp op args =>
      let seqArgs ← args.mapM transformExpr
      return .PrimitiveOp op seqArgs

  | .IfThenElse cond thenBranch elseBranch =>
      let seqCond ← transformExpr cond
      SequenceM.withInsideCondition do
        let seqThen ← transformExpr thenBranch
        let seqElse ← match elseBranch with
          | some e => transformExpr e >>= (pure ∘ some)
          | none => pure none
        return .IfThenElse seqCond seqThen seqElse

  | .StaticCall name args =>
      let seqArgs ← args.mapM transformExpr
      return .StaticCall name seqArgs

  | .Block stmts metadata =>
      -- Block in expression position: move all but last statement to prepended
      -- Process statements in order, handling assignments specially to set snapshots
      let rec processBlock (remStmts : List StmtExpr) : SequenceM StmtExpr := do
        match _: remStmts with
        | [] => return .Block [] metadata
        | [last] => transformExpr last
        | head :: tail =>
            match head with
            | .Assign targets value md =>
                /-
                Because we are lifting all assignments
                and the last one will overwrite the previous one
                We need to store the current value after each assignment
                Which we do using a snapshot variable
                We will use transformTarget (no snapshot substitution) for targets
                and transformExpr (with snapshot substitution) for values
                -/
                let seqTargets ← targets.mapM transformTarget
                let seqValue ← transformExpr value
                let assignStmt := StmtExpr.Assign seqTargets seqValue md
                SequenceM.addPrependedStmt assignStmt
                -- Create snapshot for variables so subsequent reads
                -- see the value after this assignment (not after later assignments)
                for target in seqTargets do
                  match target with
                  | .Identifier varName =>
                      let snapshotName ← SequenceM.freshTempFor varName
                      let snapshotType ← SequenceM.getVarType varName
                      let snapshotDecl := StmtExpr.LocalVariable snapshotName snapshotType (some (.Identifier varName))
                      SequenceM.addPrependedStmt snapshotDecl
                      SequenceM.setSnapshot varName snapshotName
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
      -- If this variable has a snapshot (from a lifted assignment), use the snapshot
      match ← SequenceM.getSnapshot varName with
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
      -- Process the condition, extracting any assignments
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
          SequenceM.addPrependedStmt <| .LocalVariable name ty (some seqInit)
          SequenceM.takePrependedStmts
      | none =>
          return [stmt]

  | .Assign targets value md =>
      let seqTargets ← targets.mapM transformTarget
      let seqValue ← transformExpr value
      SequenceM.addPrependedStmt <| .Assign seqTargets seqValue md
      SequenceM.takePrependedStmts

  | .IfThenElse cond thenBranch elseBranch =>
      let seqCond ← transformExpr cond
      SequenceM.withInsideCondition do
        let seqThen ← transformStmt thenBranch
        let thenBlock := .Block seqThen none

        let seqElse ← match elseBranch with
          | some e =>
              let se ← transformStmt e
              pure (some (.Block se none))
          | none => pure none

        SequenceM.addPrependedStmt <| .IfThenElse seqCond thenBlock seqElse
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
  | multiple => pure <| .Block multiple.reverse none

def transformProcedure (proc : Procedure) : SequenceM Procedure := do
  -- Initialize environment with procedure parameters
  let initEnv : TypeEnv := proc.inputs.map (fun p => (p.name, p.type)) ++
                           proc.outputs.map (fun p => (p.name, p.type))
  -- Reset state for each procedure to avoid cross-procedure contamination
  modify fun s => { s with insideCondition := false, varSnapshots := [], varCounters := [], env := initEnv }
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
    { insideCondition := false, diagnostics := [] }
  if !afterState.diagnostics.isEmpty then
    .error afterState.diagnostics.toArray
  else
    .ok { program with staticProcedures := seqProcedures }

end Laurel
