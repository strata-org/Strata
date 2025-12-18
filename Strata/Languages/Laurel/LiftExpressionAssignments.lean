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
  -- Accumulated statements to be prepended
  prependedStmts : List StmtExpr := []
  -- Counter for generating unique temporary variable names
  tempCounter : Nat := 0

abbrev SequenceM := StateM SequenceState

def SequenceM.addPrependedStmt (stmt : StmtExpr) : SequenceM Unit :=
  modify fun s => { s with prependedStmts := s.prependedStmts ++ [stmt] }

def SequenceM.getPrependedStmts : SequenceM (List StmtExpr) := do
  let stmts := (← get).prependedStmts
  modify fun s => { s with prependedStmts := [] }
  return stmts

def SequenceM.freshTemp : SequenceM Identifier := do
  let counter := (← get).tempCounter
  modify fun s => { s with tempCounter := s.tempCounter + 1 }
  return s!"__t{counter}"

mutual
/-
Process an expression, extracting any assignments to preceding statements.
Returns the transformed expression with assignments replaced by variable references.
-/
partial def sequenceExpr (expr : StmtExpr) : SequenceM StmtExpr := do
  match expr with
  | .Assign target value =>
      -- This is an assignment in expression context
      -- We need to: 1) execute the assignment, 2) capture the value in a temporary
      -- This prevents subsequent assignments to the same variable from changing the value
      let seqValue ← sequenceExpr value
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
      -- Process arguments, which might contain assignments
      let seqArgs ← args.mapM sequenceExpr
      return .PrimitiveOp op seqArgs

  | .IfThenElse cond thenBranch elseBranch =>
      -- Process condition first (assignments here become preceding statements)
      let seqCond ← sequenceExpr cond
      -- For if-expressions, branches should be processed as expressions
      -- If a branch is a block, extract all but the last statement, then use the last as the value
      let seqThen ← sequenceExpr thenBranch
      let seqElse ← match elseBranch with
        | some e => sequenceExpr e >>= (pure ∘ some)
        | none => pure none
      return .IfThenElse seqCond seqThen seqElse

  | .StaticCall name args =>
      -- Process arguments
      let seqArgs ← args.mapM sequenceExpr
      return .StaticCall name seqArgs

  | .Block stmts metadata =>
      -- Block in expression position: move all but last statement to prepended
      match stmts.reverse with
      | [] =>
          -- Empty block, return as-is
          return .Block [] metadata
      | lastStmt :: restReversed =>
          -- Process all but the last statement and add to prepended
          let priorStmts := restReversed.reverse
          for stmt in priorStmts do
            let seqStmt ← sequenceStmt stmt
            for s in seqStmt do
              SequenceM.addPrependedStmt s
          -- Process and return the last statement as an expression
          sequenceExpr lastStmt

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
partial def sequenceStmt (stmt : StmtExpr) : SequenceM (List StmtExpr) := do
  match stmt with
  | @StmtExpr.Assert cond md =>
      -- Process the condition, extracting any assignments
      let seqCond ← sequenceExpr cond
      let prepended ← SequenceM.getPrependedStmts
      return prepended ++ [StmtExpr.Assert seqCond md]

  | @StmtExpr.Assume cond md =>
      let seqCond ← sequenceExpr cond
      let prepended ← SequenceM.getPrependedStmts
      return prepended ++ [StmtExpr.Assume seqCond md]

  | .Block stmts metadata =>
      -- Process each statement in the block
      let seqStmts ← stmts.mapM sequenceStmt
      return [.Block (seqStmts.flatten) metadata]

  | .LocalVariable name ty initializer =>
      match initializer with
      | some initExpr => do
          let seqInit ← sequenceExpr initExpr
          let prepended ← SequenceM.getPrependedStmts
          return prepended ++ [.LocalVariable name ty (some seqInit)]
      | none =>
          return [stmt]

  | .Assign target value =>
      -- Top-level assignment (statement context)
      let seqTarget ← sequenceExpr target
      let seqValue ← sequenceExpr value
      let prepended ← SequenceM.getPrependedStmts
      return prepended ++ [.Assign seqTarget seqValue]

  | .IfThenElse cond thenBranch elseBranch =>
      -- Process condition (extract assignments)
      let seqCond ← sequenceExpr cond
      let prependedCond ← SequenceM.getPrependedStmts

      -- Process branches
      let seqThen ← sequenceStmt thenBranch
      let thenBlock := .Block seqThen none

      let seqElse ← match elseBranch with
        | some e =>
            let se ← sequenceStmt e
            pure (some (.Block se none))
        | none => pure none

      let ifStmt := .IfThenElse seqCond thenBlock seqElse
      return prependedCond ++ [ifStmt]

  | .StaticCall name args =>
      let seqArgs ← args.mapM sequenceExpr
      let prepended ← SequenceM.getPrependedStmts
      return prepended ++ [.StaticCall name seqArgs]

  | _ =>
      -- Other statements pass through
      return [stmt]

end

def liftInProcedureBody (body : StmtExpr) : StmtExpr :=
  let (seqStmts, _) := sequenceStmt body |>.run {}
  match seqStmts with
  | [single] => single
  | multiple => .Block multiple none

def liftInProcedure (proc : Procedure) : Procedure :=
  match proc.body with
  | .Transparent bodyExpr =>
      let seqBody := liftInProcedureBody bodyExpr
      { proc with body := .Transparent seqBody }
  | _ => proc  -- Opaque and Abstract bodies unchanged

/-
Transform a program to lift all assignments that occur in an expression context.
-/
def liftExpressionAssignments (program : Program) : Program :=
  let seqProcedures := program.staticProcedures.map liftInProcedure
  { program with staticProcedures := seqProcedures }

end Laurel
