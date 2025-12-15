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
  x := x + 1;
  y := x;
  if (x == y) { ... }
-/

structure SequenceState where
  -- Accumulated statements to be prepended
  prependedStmts : List StmtExpr := []

abbrev SequenceM := StateM SequenceState

def SequenceM.addPrependedStmt (stmt : StmtExpr) : SequenceM Unit :=
  modify fun s => { s with prependedStmts := s.prependedStmts ++ [stmt] }

def SequenceM.getPrependedStmts : SequenceM (List StmtExpr) := do
  let stmts := (← get).prependedStmts
  modify fun s => { s with prependedStmts := [] }
  return stmts

mutual
/-
Process an expression, extracting any assignments to preceding statements.
Returns the transformed expression with assignments replaced by variable references.
-/
partial def sequenceExpr (expr : StmtExpr) : SequenceM StmtExpr := do
  match expr with
  | .Assign target value =>
      -- This is an assignment in expression context
      -- Extract it to a statement and return just the target variable
      let seqValue ← sequenceExpr value
      let assignStmt := StmtExpr.Assign target seqValue
      SequenceM.addPrependedStmt assignStmt
      -- Return the target as the expression value
      return target

  | .PrimitiveOp op args =>
      -- Process arguments, which might contain assignments
      let seqArgs ← args.mapM sequenceExpr
      return .PrimitiveOp op seqArgs

  | .IfThenElse cond thenBranch elseBranch =>
      -- Process condition first (assignments here become preceding statements)
      let seqCond ← sequenceExpr cond
      -- Then process branches as statements (not expressions)
      let seqThen ← sequenceStmt thenBranch
      let thenBlock := .Block seqThen none
      let seqElse ← match elseBranch with
        | some e =>
            let se ← sequenceStmt e
            pure (some (.Block se none))
        | none => pure none
      return .IfThenElse seqCond thenBlock seqElse

  | .StaticCall name args =>
      -- Process arguments
      let seqArgs ← args.mapM sequenceExpr
      return .StaticCall name seqArgs

  | .Block stmts metadata =>
      -- Process block as a statement context
      let seqStmts ← stmts.mapM sequenceStmt
      return .Block (seqStmts.flatten) metadata

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

/-
Transform a procedure body to sequence all assignments.
-/
def sequenceProcedureBody (body : StmtExpr) : StmtExpr :=
  let (seqStmts, _) := sequenceStmt body |>.run {}
  match seqStmts with
  | [single] => single
  | multiple => .Block multiple none

/-
Transform a procedure to sequence all assignments in its body.
-/
def sequenceProcedure (proc : Procedure) : Procedure :=
  match proc.body with
  | .Transparent bodyExpr =>
      let seqBody := sequenceProcedureBody bodyExpr
      { proc with body := .Transparent seqBody }
  | _ => proc  -- Opaque and Abstract bodies unchanged

/-
Transform a program to sequence all assignments.
-/
def sequenceProgram (program : Program) : Program :=
  let seqProcedures := program.staticProcedures.map sequenceProcedure
  { program with staticProcedures := seqProcedures }

end Laurel