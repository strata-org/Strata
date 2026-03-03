/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelFormat

/-!
# Division-by-Zero Check Insertion

A Laurel-to-Laurel transformation that inserts `assert divisor != 0` before
every division or modulo operation (`Div`, `Mod`, `DivT`, `ModT`).
-/

namespace Strata.Laurel

private def emptyMd : Imperative.MetaData Core.Expression := #[]
private def bare (v : StmtExpr) : StmtExprMd := ⟨v, emptyMd⟩

/-- Returns true for operations that require a non-zero divisor. -/
private def isDivisionOp : Operation → Bool
  | .Div | .Mod | .DivT | .ModT => true
  | _ => false

/-- Build `assert arg != 0` for a given expression. -/
private def mkDivByZeroAssert (divisor : StmtExprMd) : StmtExprMd :=
  ⟨.Assert ⟨.PrimitiveOp .Neq [divisor, ⟨.LiteralInt 0, divisor.md⟩], divisor.md⟩, divisor.md⟩

/--
Collect division-by-zero assertions needed for an expression.
Returns the list of assertions that should be prepended before the expression
is evaluated.
-/
partial def collectDivChecks (expr : StmtExprMd) : List StmtExprMd :=
  match expr.val with
  | .PrimitiveOp op args =>
    let childChecks := args.flatMap collectDivChecks
    if isDivisionOp op then
      match args with
      | [_, divisor] => childChecks ++ [mkDivByZeroAssert divisor]
      | _ => childChecks
    else childChecks
  | .IfThenElse cond thenBr elseBr =>
    collectDivChecks cond ++
    collectDivChecks thenBr ++
    (elseBr.map collectDivChecks |>.getD [])
  | .Block stmts _ => stmts.flatMap collectDivChecks
  | .Assign _ value => collectDivChecks value
  | .StaticCall _ args => args.flatMap collectDivChecks
  | .InstanceCall target _ args =>
    collectDivChecks target ++ args.flatMap collectDivChecks
  | .FieldSelect target _ => collectDivChecks target
  | .PureFieldUpdate target _ newVal =>
    collectDivChecks target ++ collectDivChecks newVal
  | .LocalVariable _ _ init => init.map collectDivChecks |>.getD []
  | .While cond invs _ body =>
    collectDivChecks cond ++
    invs.flatMap collectDivChecks ++
    collectDivChecks body
  | .Assert cond => collectDivChecks cond
  | .Assume cond => collectDivChecks cond
  | .Forall _ _ body => collectDivChecks body
  | .Exists _ _ body => collectDivChecks body
  | .Old v => collectDivChecks v
  | .Fresh v => collectDivChecks v
  | .ProveBy v p => collectDivChecks v ++ collectDivChecks p
  | .ReferenceEquals l r => collectDivChecks l ++ collectDivChecks r
  | .AsType target _ => collectDivChecks target
  | .IsType target _ => collectDivChecks target
  | .Return (some v) => collectDivChecks v
  | .Assigned name => collectDivChecks name
  | _ => []

/--
Transform a statement by inserting division-by-zero assertions.
For each statement that contains a division, the assertion is inserted
immediately before the statement.
-/
partial def insertDivChecksStmt (stmt : StmtExprMd) : List StmtExprMd :=
  match stmt.val with
  | .Block stmts label =>
    let transformed := stmts.flatMap insertDivChecksStmt
    [⟨.Block transformed label, stmt.md⟩]
  | .IfThenElse cond thenBr elseBr =>
    let condChecks := collectDivChecks cond
    let thenStmts := insertDivChecksStmt thenBr
    let thenBr' := match thenStmts with
      | [single] => single
      | multiple => ⟨.Block multiple none, thenBr.md⟩
    let elseBr' := elseBr.map fun e =>
      let elseStmts := insertDivChecksStmt e
      match elseStmts with
      | [single] => single
      | multiple => ⟨.Block multiple none, e.md⟩
    condChecks ++ [⟨.IfThenElse cond thenBr' elseBr', stmt.md⟩]
  | .While cond invs dec body =>
    let condChecks := collectDivChecks cond
    let bodyStmts := insertDivChecksStmt body
    let body' := match bodyStmts with
      | [single] => single
      | multiple => ⟨.Block multiple none, body.md⟩
    condChecks ++ [⟨.While cond invs dec body', stmt.md⟩]
  | _ =>
    let checks := collectDivChecks stmt
    checks ++ [stmt]

/-- Transform a procedure body by inserting division-by-zero checks. -/
def insertDivChecksProcedure (proc : Procedure) : Procedure :=
  match proc.body with
  | .Transparent body =>
    let stmts := insertDivChecksStmt body
    let body' := match stmts with
      | [single] => single
      | multiple => ⟨.Block multiple none, body.md⟩
    { proc with body := .Transparent body' }
  | .Opaque postconds (some impl) modif =>
    let stmts := insertDivChecksStmt impl
    let impl' := match stmts with
      | [single] => single
      | multiple => ⟨.Block multiple none, impl.md⟩
    { proc with body := .Opaque postconds (some impl') modif }
  | _ => proc

/-- Insert division-by-zero checks into all procedures of a Laurel program. -/
def insertDivisionByZeroChecks (program : Program) : Program :=
  { program with staticProcedures := program.staticProcedures.map insertDivChecksProcedure }

end Strata.Laurel
