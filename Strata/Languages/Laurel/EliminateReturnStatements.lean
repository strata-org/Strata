/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr

/-!
# Eliminate Return Statements

Replaces `return` statements in imperative procedure bodies with assignments
to the output parameters followed by an `exit` to a labelled block that wraps
the entire body. This ensures that code placed after the body block (e.g.,
postcondition assertions inserted by the contract pass) is always reached.

This pass should run after `EliminateReturnsInExpression` (which handles
functional/expression-position returns) and before the contract pass.
-/

namespace Strata.Laurel

public section

private def returnLabel : String := "$return"

private def emptyMd : MetaData := .empty

private def mkMd (e : StmtExpr) : StmtExprMd := { val := e, source := none }

/-- Replace `Return val` with `output := val; exit "$return"` (or just `exit`
    for valueless returns). Uses `mapStmtExpr` for bottom-up traversal. -/
private def replaceReturn (outputs : List Parameter) (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Return (some val) =>
      match outputs with
      | [out] =>
        let assign := mkMd (.Assign [mkMd (.Identifier out.name)] val)
        let exit := mkMd (.Exit returnLabel)
        ⟨.Block [assign, exit] none, e.source, e.md⟩
      | _ => mkMd (.Exit returnLabel)
    | .Return none => mkMd (.Exit returnLabel)
    | _ => e) expr

/-- Transform a single procedure: wrap body in a labelled block and replace returns. -/
private def eliminateReturnStmts (proc : Procedure) : Procedure :=
  match proc.body with
  | .Opaque postconds (some impl) mods =>
    let impl' := replaceReturn proc.outputs impl
    let wrapped := mkMd (.Block [impl'] (some returnLabel))
    { proc with body := .Opaque postconds (some wrapped) mods }
  | .Transparent body =>
    let body' := replaceReturn proc.outputs body
    let wrapped := mkMd (.Block [body'] (some returnLabel))
    { proc with body := .Transparent wrapped }
  | _ => proc

/-- Transform a program by eliminating return statements in all procedure bodies. -/
def eliminateReturnStatements (program : Program) : Program :=
  { program with staticProcedures := program.staticProcedures.map eliminateReturnStmts }

end -- public section

end Strata.Laurel
