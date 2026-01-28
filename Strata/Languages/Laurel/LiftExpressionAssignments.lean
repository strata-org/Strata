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

structure SequenceState where
  insideCondition : Bool
  prependedStmts : List StmtExpr := []
  diagnostics : List DiagnosticModel
  tempCounter : Nat := 0

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

def SequenceM.freshTemp : SequenceM Identifier := do
  let counter := (← get).tempCounter
  modify fun s => { s with tempCounter := s.tempCounter + 1 }
  return s!"__t{counter}"

mutual
/-
Process an expression, extracting any assignments to preceding statements.
Returns the transformed expression with assignments replaced by variable references.
-/
def transformExpr (expr : StmtExpr) : SequenceM StmtExpr := do
  match expr with
  | .Assign target value md =>
      checkOutsideCondition md
      -- This is an assignment in expression context
      -- We need to: 1) execute the assignment, 2) capture the value in a temporary
      -- This prevents subsequent assignments to the same variable from changing the value
      let seqValue ← transformExpr value
      let assignStmt := StmtExpr.Assign target seqValue md
      SequenceM.addPrependedStmt assignStmt
      -- Create a temporary variable to capture the assigned value
      -- Use TInt as the type (could be refined with type inference)
      let tempName ← SequenceM.freshTemp
      let tempDecl := StmtExpr.LocalVariable tempName .TInt (some target)
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
      let rec next (remStmts: List StmtExpr) := match remStmts with
        | [last] => transformExpr last
        | head :: tail => do
            let seqStmt ← transformStmt head
            for s in seqStmt do
              SequenceM.addPrependedStmt s
            next tail
        | [] => return .Block [] metadata

      next stmts

  -- Base cases: no assignments to extract
  | .LiteralBool _ => return expr
  | .LiteralInt _ => return expr
  | .Identifier _ => return expr
  | .LocalVariable _ _ _ => return expr
  | _ => return expr  -- Other cases

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
      match initializer with
      | some initExpr => do
          let seqInit ← transformExpr initExpr
          SequenceM.addPrependedStmt <| .LocalVariable name ty (some seqInit)
          SequenceM.takePrependedStmts
      | none =>
          return [stmt]

  | .Assign target value md =>
      let seqTarget ← transformExpr target
      let seqValue ← transformExpr value
      SequenceM.addPrependedStmt <| .Assign seqTarget seqValue md
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

end

def transformProcedureBody (body : StmtExpr) : SequenceM StmtExpr := do
  let seqStmts ← transformStmt body
  match seqStmts with
  | [single] => pure single
  | multiple => pure <| .Block multiple.reverse none

def transformProcedure (proc : Procedure) : SequenceM Procedure := do
  -- Reset insideCondition for each procedure to avoid cross-procedure contamination
  modify fun s => { s with insideCondition := false }
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
