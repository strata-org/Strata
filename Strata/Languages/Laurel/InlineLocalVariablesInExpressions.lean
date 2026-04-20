/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
import Strata.Util.Tactics

/-!
# Inline Local Variables in Expression Position

Replaces local variable declarations in functional procedure bodies with
direct substitution of the initializer into the remaining statements of
the block. This eliminates `LocalVariable` nodes from expression contexts
so the Core translator does not need to handle let-bindings in expressions.

Example:
```
function f() returns (r: int) {
  var x: int := 1;
  var y: int := x + 1;
  y
}
```
becomes:
```
function f() returns (r: int) {
  0 + 1
}
```
-/

namespace Strata.Laurel

public section

/-- Substitute all occurrences of identifier `name` with `replacement` in `expr`. -/
private def substIdentifier (name : Identifier) (replacement : StmtExprMd) (expr : StmtExprMd)
    : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Identifier n => if n == name then replacement else e
    | _ => e) expr

/-- Inline initialized local variables in a block, substituting their
    initializers into the remaining statements. Non-LocalVariable
    statements are kept as-is. -/
private def inlineLocalsInStmts (stmts : List StmtExprMd) : List StmtExprMd :=
  match stmts with
  | [] => []
  | ⟨.LocalVariable name _ty (some initializer), _, _⟩ :: rest =>
    let rest' := rest.map (substIdentifier name initializer)
    inlineLocalsInStmts rest'
  | s :: rest => s :: inlineLocalsInStmts rest
termination_by stmts.length

/-- Rewrite a single node: if it is a Block, inline any LocalVariable
    declarations. Recursion into children is handled by `mapStmtExpr`. -/
private def inlineLocalsNode (expr : StmtExprMd) : StmtExprMd :=
  match expr.val with
  | .Block stmts label =>
    let stmts' := inlineLocalsInStmts stmts
    match stmts' with
    | [single] => single
    | _ => ⟨.Block stmts' label, expr.source, expr.md⟩
  | _ => expr

/-- Apply local-variable inlining to all functional procedure bodies. -/
def inlineLocalVariablesInExpressions (program : Program) : Program :=
  { program with staticProcedures := program.staticProcedures.map fun proc =>
    if !proc.isFunctional then proc
    else
      match proc.body with
      | .Transparent body =>
        { proc with body := .Transparent (mapStmtExpr inlineLocalsNode body) }
      | .Opaque postconds (some impl) modif =>
        { proc with body := .Opaque postconds (some (mapStmtExpr inlineLocalsNode impl)) modif }
      | _ => proc }

end -- public section
end Strata.Laurel
