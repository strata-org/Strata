/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel

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
  prependedStmts : List StmtExpr := []
  tempCounter : Nat := 0

abbrev SequenceM := StateM SequenceState

def SequenceM.addPrependedStmt (stmt : StmtExpr) : SequenceM Unit :=
  modify fun s => { s with prependedStmts := stmt :: s.prependedStmts }

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
  | .Assign target value =>
      -- This is an assignment in expression context
      -- We need to: 1) execute the assignment, 2) capture the value in a temporary
      -- This prevents subsequent assignments to the same variable from changing the value
      let seqValue ← transformExpr value
      let assignStmt := StmtExpr.Assign target seqValue
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

  | .Assign target value =>
      -- Top-level assignment (statement context)
      let seqTarget ← transformExpr target
      let seqValue ← transformExpr value
      SequenceM.addPrependedStmt <| .Assign seqTarget seqValue
      SequenceM.takePrependedStmts

  | .IfThenElse cond thenBranch elseBranch =>
      let seqThen ← transformStmt thenBranch
      let thenBlock := .Block seqThen none

      let seqElse ← match elseBranch with
        | some e =>
            let se ← transformStmt e
            pure (some (.Block se none))
        | none => pure none

      let seqCond ← transformExpr cond
      SequenceM.addPrependedStmt <| .IfThenElse seqCond thenBlock seqElse
      SequenceM.takePrependedStmts

  | .StaticCall name args =>
      let seqArgs ← args.mapM transformExpr
      SequenceM.addPrependedStmt <| .StaticCall name seqArgs
      SequenceM.takePrependedStmts

  | _ =>
      return [stmt]

end

def transformProcedureBody (body : StmtExpr) : StmtExpr :=
  let (seqStmts, _) := transformStmt body |>.run {}
  match seqStmts with
  | [single] => single
  | multiple => .Block multiple.reverse none

def transformProcedure (proc : Procedure) : Procedure :=
  match proc.body with
  | .Transparent bodyExpr =>
      let seqBody := transformProcedureBody bodyExpr
      { proc with body := .Transparent seqBody }
  | _ => proc  -- Opaque and Abstract bodies unchanged

/--
Transform a program to lift all assignments that occur in an expression context.
-/
def liftExpressionAssignments (program : Program) : Program :=
  let seqProcedures := program.staticProcedures.map transformProcedure
  { program with staticProcedures := seqProcedures }

end Laurel
