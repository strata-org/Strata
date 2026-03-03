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

/-- Returns true for operations that require a non-zero divisor. -/
private def isDivisionOp : Operation → Bool
  | .Div | .Mod | .DivT | .ModT => true
  | _ => false

/-- Build `divisor != 0` condition for a given expression. -/
private def mkDivByZeroCondition (divisor : StmtExprMd) : StmtExprMd :=
  ⟨.PrimitiveOp .Neq [divisor, ⟨.LiteralInt 0, divisor.md⟩], divisor.md⟩

/-- Build `assert arg != 0` for a given expression. -/
private def mkDivByZeroAssert (divisor : StmtExprMd) : StmtExprMd :=
  ⟨.Assert (mkDivByZeroCondition divisor), divisor.md⟩

/--
Collect `divisor != 0` conditions from an expression (not wrapped in Assert).
Does not recurse into IfThenElse branches, While bodies, or quantifiers.
-/
partial def collectDivConditions (expr : StmtExprMd) : List StmtExprMd :=
  match expr.val with
  | .PrimitiveOp op args =>
    let childConds := args.flatMap collectDivConditions
    if isDivisionOp op then
      match args with
      | [_, divisor] => childConds ++ [mkDivByZeroCondition divisor]
      | _ => childConds
    else childConds
  | .IfThenElse cond _ _ => collectDivConditions cond
  | .Block stmts _ => stmts.flatMap collectDivConditions
  | .Assign _ value => collectDivConditions value
  | .StaticCall _ args => args.flatMap collectDivConditions
  | .InstanceCall target _ args =>
    collectDivConditions target ++ args.flatMap collectDivConditions
  | .FieldSelect target _ => collectDivConditions target
  | .PureFieldUpdate target _ newVal =>
    collectDivConditions target ++ collectDivConditions newVal
  | .LocalVariable _ _ init => init.map collectDivConditions |>.getD []
  | .While cond _ _ _ => collectDivConditions cond
  | .Assert cond => collectDivConditions cond
  | .Assume cond => collectDivConditions cond
  | .Forall _ _ _ | .Exists _ _ _ => []
  | .Old v => collectDivConditions v
  | .Fresh v => collectDivConditions v
  | .ProveBy v p => collectDivConditions v ++ collectDivConditions p
  | .ReferenceEquals l r => collectDivConditions l ++ collectDivConditions r
  | .AsType target _ => collectDivConditions target
  | .IsType target _ => collectDivConditions target
  | .Return (some v) => collectDivConditions v
  | .Assigned name => collectDivConditions name
  | _ => []

/-- Conjoin a list of conditions with `&&`. -/
private def conjoinConditions (conds : List StmtExprMd) (md : Imperative.MetaData Core.Expression) : StmtExprMd :=
  match conds with
  | [] => ⟨.LiteralBool true, md⟩
  | [c] => c
  | c :: cs => cs.foldl (fun acc x => ⟨.PrimitiveOp .And [acc, x], md⟩) c

/--
Collect ALL `divisor != 0` conditions from an expression, recursing into
all branches. Used for functional procedures where preconditions must cover
every execution path. Does not recurse into quantifiers.
-/
partial def collectAllDivConditions (expr : StmtExprMd) : List StmtExprMd :=
  match expr.val with
  | .PrimitiveOp op args =>
    let childConds := args.flatMap collectAllDivConditions
    if isDivisionOp op then
      match args with
      | [_, divisor] => childConds ++ [mkDivByZeroCondition divisor]
      | _ => childConds
    else childConds
  | .IfThenElse cond thenBr elseBr =>
    collectAllDivConditions cond ++
    collectAllDivConditions thenBr ++
    (elseBr.map collectAllDivConditions |>.getD [])
  | .Block stmts _ => stmts.flatMap collectAllDivConditions
  | .StaticCall _ args => args.flatMap collectAllDivConditions
  | .Forall _ _ _ | .Exists _ _ _ => []
  | _ => []

/--
Rewrite an expression to insert division-by-zero guards inside quantifiers.
For `∀x, body` with divisions, rewrites to `∀x, (divisor != 0) → body`.
For `∃x, body` with divisions, rewrites to `∃x, (divisor != 0) ∧ body`.
-/
partial def insertDivChecksExpr (expr : StmtExprMd) : StmtExprMd :=
  match expr.val with
  | .Forall name ty body =>
    let body' := insertDivChecksExpr body
    let conds := collectDivConditions body'
    let guardedBody := if conds.isEmpty then body'
      else ⟨.PrimitiveOp .Implies [conjoinConditions conds body'.md, body'], body'.md⟩
    ⟨.Forall name ty guardedBody, expr.md⟩
  | .Exists name ty body =>
    let body' := insertDivChecksExpr body
    let conds := collectDivConditions body'
    let guardedBody := if conds.isEmpty then body'
      else ⟨.PrimitiveOp .And [conjoinConditions conds body'.md, body'], body'.md⟩
    ⟨.Exists name ty guardedBody, expr.md⟩
  | .Assert cond => ⟨.Assert (insertDivChecksExpr cond), expr.md⟩
  | .Assume cond => ⟨.Assume (insertDivChecksExpr cond), expr.md⟩
  | .PrimitiveOp op args =>
    ⟨.PrimitiveOp op (args.map insertDivChecksExpr), expr.md⟩
  | .IfThenElse cond thenBr elseBr =>
    ⟨.IfThenElse (insertDivChecksExpr cond) (insertDivChecksExpr thenBr)
      (elseBr.map insertDivChecksExpr), expr.md⟩
  | .Block stmts label =>
    ⟨.Block (stmts.map insertDivChecksExpr) label, expr.md⟩
  | _ => expr

/--
Collect division-by-zero assertions needed for an expression.
Returns the list of assertions that should be prepended before the expression
is evaluated. Does not recurse into quantifiers (those are handled by
`insertDivChecksExpr`).
-/
partial def collectDivChecks (expr : StmtExprMd) : List StmtExprMd :=
  (collectDivConditions expr).map fun cond => ⟨.Assert cond, cond.md⟩

/--
Transform a statement by inserting division-by-zero assertions.
For each statement that contains a division, the assertion is inserted
immediately before the statement. Quantifier bodies are rewritten in-place
by `insertDivChecksExpr`.
-/
partial def insertDivChecksStmt (stmt : StmtExprMd) : List StmtExprMd :=
  match stmt.val with
  | .Block stmts label =>
    let transformed := stmts.flatMap insertDivChecksStmt
    [⟨.Block transformed label, stmt.md⟩]
  | .IfThenElse cond thenBr elseBr =>
    let cond := insertDivChecksExpr cond
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
    let cond := insertDivChecksExpr cond
    let condChecks := collectDivChecks cond
    let bodyStmts := insertDivChecksStmt body
    let body' := match bodyStmts with
      | [single] => single
      | multiple => ⟨.Block multiple none, body.md⟩
    condChecks ++ [⟨.While cond invs dec body', stmt.md⟩]
  | _ =>
    -- Rewrite quantifier bodies, then collect remaining div checks
    let stmt := insertDivChecksExpr stmt
    let checks := collectDivChecks stmt
    checks ++ [stmt]

/-- Transform a procedure body by inserting division-by-zero checks.
For functional (pure) procedures, adds `requires divisor != 0` preconditions
instead of inserting assert statements (which would break purity). -/
def insertDivChecksProcedure (proc : Procedure) : Procedure :=
  if proc.isFunctional then
    -- For functional procedures: add preconditions and rewrite quantifier bodies
    let body' := match proc.body with
      | .Transparent body => .Transparent (insertDivChecksExpr body)
      | other => other
    let newPreconds := match proc.body with
      | .Transparent body => (collectAllDivConditions body).map fun cond => cond
      | _ => []
    { proc with
      preconditions := proc.preconditions ++ newPreconds
      body := body' }
  else
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
