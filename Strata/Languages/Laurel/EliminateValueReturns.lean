/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr

/-!
# Eliminate Value Returns

Rewrites `return expr` into `outParam := expr; return` for imperative
(non-functional) procedures that have an output parameter. This decouples
the return-value assignment from the `LaurelToCoreTranslator`, which no
longer needs to know about output parameters when translating returns.

The pass is a Laurel-to-Laurel rewrite that runs before Core translation.
-/

namespace Strata.Laurel

/-- Rewrite a single `Return (some value)` node into
    `Block [Assign [Identifier outParam] value, Return none]`.
    Recursion into children is handled by `mapStmtExpr`. -/
private def eliminateValueReturnNode (outParam : Identifier) (stmt : StmtExprMd) : StmtExprMd :=
  match stmt.val with
  | .Return (some value) =>
    -- Synthesized nodes use default metadata since no diagnostics should be reported on them
    let target : StmtExprMd := { val := .Identifier outParam, source := none }
    let assign : StmtExprMd := { val := .Assign [target] value, source := none }
    let ret : StmtExprMd := { val := .Return none, source := stmt.source }
    { val := .Block [assign, ret] none, source := none }
  | _ => stmt

/-- Check whether a statement tree contains any `Return (some _)`. -/
def hasValuedReturn (stmt : StmtExprMd) : Bool :=
  match _h : stmt.val with
  | .Return (some _) => true
  | .Block stmts _ => stmts.attach.any fun ⟨s, _⟩ => hasValuedReturn s
  | .IfThenElse _ thenBr (some elseBr) =>
    hasValuedReturn thenBr || hasValuedReturn elseBr
  | .IfThenElse _ thenBr none => hasValuedReturn thenBr
  | .While _ _ _ body => hasValuedReturn body
  | _ => false
  termination_by sizeOf stmt
  decreasing_by
    all_goals simp_wf
    all_goals (try have := AstNode.sizeOf_val_lt stmt)
    all_goals (try term_by_mem)
    all_goals omega

/-- Apply value-return elimination to a single procedure. Only applies to
    non-functional procedures with exactly one output parameter.
    Emits an error if a valued return is used with multiple output parameters. -/
def eliminateValueReturnsInProc (proc : Procedure) : Procedure × Array DiagnosticModel :=
  if proc.isFunctional then (proc, #[])
  else match proc.outputs with
  | [outParam] =>
    let rewrite := mapStmtExpr (eliminateValueReturnNode outParam.name)
    match proc.body with
    | .Transparent body =>
      ({ proc with body := .Transparent (rewrite body) }, #[])
    | .Opaque postconds (some impl) modif =>
      ({ proc with body := .Opaque postconds (some (rewrite impl)) modif }, #[])
    | _ => (proc, #[])
  | other =>
    let bodyHasValuedReturn := match proc.body with
      | .Transparent body => hasValuedReturn body
      | .Opaque _ (some impl) _ => hasValuedReturn impl
      | _ => false
    if bodyHasValuedReturn then
      let msg := if other.isEmpty then
        "Valued return is not supported for procedures with no output parameters"
      else
        "Valued return is not supported for procedures with multiple output parameters"
      (proc, #[diagnosticFromSource proc.name.source msg DiagnosticType.UserError])
    else (proc, #[])

public section

/-- Transform a program by eliminating value returns in all imperative procedures. -/
def eliminateValueReturnsTransform (program : Program) : Program × Array DiagnosticModel :=
  let (procs, diags) := program.staticProcedures.foldl (fun (ps, ds) proc =>
    let (proc', procDiags) := eliminateValueReturnsInProc proc
    (proc' :: ps, ds ++ procDiags)
  ) ([], #[])
  ({ program with staticProcedures := procs.reverse }, diags)

end -- public section

end Laurel
