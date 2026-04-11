/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel

/-!
# Eliminate Value Returns

Rewrites `return expr` into `outParam := expr; return` for imperative
(non-functional) procedures that have an output parameter. This decouples
the return-value assignment from the `LaurelToCoreTranslator`, which no
longer needs to know about output parameters when translating returns.

The pass is a Laurel-to-Laurel rewrite that runs before Core translation.
-/

namespace Strata.Laurel

/-- Rewrite `Return (some value)` → `Block [Assign [Identifier outParam] value, Return none]`
    throughout a statement tree. -/
partial def eliminateValueReturn (outParam : Identifier) (stmt : StmtExprMd) : StmtExprMd :=
  let md := stmt.md
  match stmt.val with
  | .Return (some value) =>
    let target : StmtExprMd := ⟨.Identifier outParam, value.md⟩
    let assign : StmtExprMd := ⟨.Assign [target] value, md⟩
    let ret : StmtExprMd := ⟨.Return none, md⟩
    ⟨.Block [assign, ret] none, md⟩
  | .Block stmts label =>
    ⟨.Block (stmts.map (eliminateValueReturn outParam)) label, md⟩
  | .IfThenElse cond thenBr elseBr =>
    ⟨.IfThenElse cond
      (eliminateValueReturn outParam thenBr)
      (elseBr.map (eliminateValueReturn outParam)), md⟩
  | .While cond invs decr body =>
    ⟨.While cond invs decr (eliminateValueReturn outParam body), md⟩
  | _ => stmt

/-- Apply value-return elimination to a single procedure. Only applies to
    non-functional procedures with exactly one output parameter. -/
def eliminateValueReturnsInProc (proc : Procedure) : Procedure :=
  if proc.isFunctional then proc
  else match proc.outputs.head? with
  | none => proc
  | some outParam =>
    let rewrite := eliminateValueReturn outParam.name
    match proc.body with
    | .Transparent body =>
      { proc with body := .Transparent (rewrite body) }
    | .Opaque postconds (some impl) modif =>
      { proc with body := .Opaque postconds (some (rewrite impl)) modif }
    | _ => proc

public section

/-- Transform a program by eliminating value returns in all imperative procedures. -/
def eliminateValueReturnsTransform (program : Program) : Program :=
  { program with staticProcedures := program.staticProcedures.map eliminateValueReturnsInProc }

end -- public section

end Laurel
