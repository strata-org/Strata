/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.LaurelPass

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




/-- Transform a single procedure: wrap body in a labelled block and replace returns. -/
private def eliminateReturnStmts (proc : Procedure) : Procedure :=
  match proc.body with
  | .Opaque postconds (some impl) mods =>
    let impl' := replaceReturn proc.outputs impl
    let wrapped := match impl'.val with
      | .Block stmts none => ⟨.Block stmts (some returnLabel), impl'.source⟩
      | _ => ⟨ .Block [impl'] (some returnLabel), proc.name.source ⟩
    { proc with body := .Opaque postconds (some wrapped) mods }
  | .Transparent body =>
    let body' := replaceReturn proc.outputs body
    let wrapped := match body'.val with
      | .Block stmts none => ⟨.Block stmts (some returnLabel), body'.source⟩
      | _ => ⟨ .Block [body'] (some returnLabel), proc.name.source ⟩
    { proc with body := .Transparent wrapped }
  | _ => proc
where

  /-- Replace `Return val` with `output := val; exit "$return"` (or just `exit`
    for valueless returns). Uses `mapStmtExpr` for bottom-up traversal. -/
  replaceReturn (outputs : List Parameter) (expr : StmtExprMd) : StmtExprMd :=
    mapStmtExpr (fun e =>
      match e.val with
      | .Return (some val) =>
        /- Handling valued return is required because the heap param pass introduces valued return in
        Strata/Languages/Laurel/HeapParameterizationConstants.lean
        We should change that so we can remove this case.
        -/
        match outputs with
        | [out] =>
          let assign := ⟨ .Assign [⟨ .Local out.name, expr.source ⟩] val, expr.source ⟩
          let exit := ⟨ .Exit returnLabel, expr.source ⟩
          ⟨.Block [assign, exit] none, e.source⟩
        | _ => ⟨ .Exit returnLabel, expr.source ⟩
      | .Return none => ⟨ .Exit returnLabel, expr.source ⟩
      | _ => e) expr

/-- Transform a program by eliminating return statements in all procedure bodies. -/
def eliminateReturnStatements (program : Program) : Program :=
  { program with staticProcedures := program.staticProcedures.map eliminateReturnStmts }

public def eliminateReturnStatementsPass : LoweringPass where
  name := "EliminateReturnStatements"
  documentation := "Lower return statements to exit statements. Wrap each procedure body with a 'return' block"
  run := fun p _m =>
    let p' := eliminateReturnStatements p
    (p', [], {})
  -- comesBefore := [contractPass]

end -- public section

end Strata.Laurel
