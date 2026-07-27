/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
import Strata.DL.Lambda.LExprT
import Strata.Languages.Core.StatementType

---------------------------------------------------------------------

public section

namespace Core

open Std (ToFormat Format format)
open Imperative (MetaData HasVarsImp)
open Strata (DiagnosticModel FileRange)

namespace Procedure

/-- Rewrite fresh instantiation-variable names back to user names in an error message. -/
private def renameTypeVars (userSubst : Lambda.Subst) (msg : String) : String :=
  userSubst.flatten.foldl (fun acc (fresh, v) =>
    match v with
    | .ftvar orig => acc.replace (toString fresh) (toString orig)
    | _ => acc) msg

private def checkNoDuplicates (proc : Procedure) (sourceLoc : FileRange) :
    Except DiagnosticModel Unit := do
  if !proc.header.inputs.keys.Nodup then
    .error <| DiagnosticModel.withRange sourceLoc f!"[{proc.header.name}] Duplicates found in the formals!"
  if !proc.header.outputs.keys.Nodup then
    .error <| DiagnosticModel.withRange sourceLoc f!"[{proc.header.name}] Duplicates found in the return variables!"

/-- Well-formedness of a procedure's type parameters (mirroring `LFunc.type`'s checks
    for functions): `typeArgs` must be distinct, every type variable in an input/output
    type must be declared in `typeArgs`, and no `typeArgs` name may use the reserved
    generator prefix `$__ty` (which instantiation uses for fresh vars, so a collision
    would let the fresh→user back-renaming capture). -/
private def checkTypeArgsWF (proc : Procedure) (sourceLoc : FileRange) :
    Except DiagnosticModel Unit := do
  if !proc.header.typeArgs.Nodup then
    .error <| DiagnosticModel.withRange sourceLoc
      f!"[{proc.header.name}] Duplicates found in the type parameters!\n\
         {proc.header.typeArgs}"
  let genPrefixArgs := proc.header.typeArgs.filter
    (fun ta => Lambda.TState.tyPrefix.toList.isPrefixOf ta.toList)
  if !genPrefixArgs.isEmpty then
    .error <| DiagnosticModel.withRange sourceLoc
      f!"[{proc.header.name}]: type parameters {genPrefixArgs} use the reserved \
         generator-variable prefix '{Lambda.TState.tyPrefix}'; rename them"
  let sigVars := (Lambda.LMonoTys.freeVars proc.header.inputs.values ++
                  Lambda.LMonoTys.freeVars proc.header.outputs.values).eraseDups
  let undeclared := sigVars.filter (· ∉ proc.header.typeArgs)
  if !undeclared.isEmpty then
    .error <| DiagnosticModel.withRange sourceLoc
      f!"[{proc.header.name}]: type variables {undeclared} appear in the \
         signature but are not declared in typeArgs {proc.header.typeArgs}"

private def checkModificationRights (proc : Procedure) (sourceLoc : FileRange) :
    Except DiagnosticModel Unit := do
  let modifiedVars := (HasVarsImp.modifiedVars (P := Expression) proc.body).eraseDups
  let definedVars := (HasVarsImp.definedVars (P := Expression) proc.body false).eraseDups
  -- The `old ` prefix is reserved for pre-state ghost bindings of in-out parameters
  -- (`CoreIdent.mkOld`). A body may READ `old x` but must not MODIFY or DEFINE an
  -- old-prefixed variable. The checks below don't otherwise catch this (the `init`
  -- freshness check misses a fresh `old z`, and an old-named output is permitted), so
  -- both modified and defined vars are guarded explicitly here.
  let oldWritten := (modifiedVars ++ definedVars).filter (fun v => CoreIdent.isOldIdent v)
  if !oldWritten.isEmpty then
    .error <| DiagnosticModel.withRange sourceLoc f!"[{proc.header.name}]: body modifies or defines variables {oldWritten} \
              whose names use the reserved 'old ' prefix; that prefix is reserved for pre-state inout parameter ghosts"
  let allowedVars := proc.header.outputs.keys ++ definedVars
  let disallowed := modifiedVars.filter (fun v => !allowedVars.contains v)
  if !disallowed.isEmpty then
    .error <| DiagnosticModel.withRange sourceLoc f!"[{proc.header.name}]: This procedure modifies variables it \
              is not allowed to!\n\
              Variables actually modified: {modifiedVars}\n\
              Modification allowed for these variables: {allowedVars}"

private def setupInputEnv (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (sourceLoc : FileRange) :
    Except DiagnosticModel (@Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst) := do
  let Env := Env.pushEmptyContext
  let (inp_mty_sig, Env, tyArgSubst) ← Lambda.LMonoTySignature.instantiateWithSubst C Env proc.header.typeArgs
                            proc.header.inputs |>.mapError (fun e => DiagnosticModel.withRange sourceLoc e)
  let inp_lty_sig := Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig
  let Env := Env.addInNewestContext inp_lty_sig
  return (inp_mty_sig, Env, tyArgSubst)

-- Error message prefix for errors in processing procedure pre/post conditions.
def conditionErrorMsgPrefix (procName : CoreIdent) (condName : CoreLabel)
    (md : MetaData Expression) : DiagnosticModel :=
  md.toDiagnosticF f!"[{procName}:{condName}]:"

-- Type checking procedure pre/post conditions. Structured as an explicit tail recursion
-- (`go`) rather than a `for`/`forIn` loop, so soundness proofs can use the generated
-- `go.induct` instead of unfolding a `forIn` desugaring.
open Lambda.LTy.Syntax in
private def typeCheckConditions (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (conditions : ListMap CoreLabel Check) (procName : CoreIdent) :
    Except DiagnosticModel (Array Expression.Expr × Core.Expression.TyEnv) :=
  go C procName conditions #[] Env
where
  go (C : Core.Expression.TyContext) (procName : CoreIdent)
      (conditions : List (CoreLabel × Check)) (results : Array Expression.Expr)
      (currentEnv : Core.Expression.TyEnv) :
      Except DiagnosticModel (Array Expression.Expr × Core.Expression.TyEnv) :=
    match conditions with
    | [] => .ok (results, currentEnv)
    | (name, condition) :: rest => do
      let errorPrefix := conditionErrorMsgPrefix procName name condition.md
      let (annotatedExpr, newEnv) ← Lambda.LExpr.resolve C currentEnv condition.expr
                                      |>.mapError (fun e => { errorPrefix with message := errorPrefix.message ++ " " ++ toString e })
      if annotatedExpr.toLMonoTy != mty[bool] then
        .error { errorPrefix with message := errorPrefix.message ++ s!": Expected condition to be of type Bool, but got {annotatedExpr.toLMonoTy}!" }
      go C procName rest (results.push annotatedExpr.unresolved) newEnv

def typeCheck (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (p : Program)
    (proc : Procedure) (md : MetaData Expression) : Except DiagnosticModel (Procedure × Core.Expression.TyEnv) := do
  let fileRange := Imperative.getFileRange md |>.getD FileRange.unknown

  -- Validate well-formedness of formals and returns.
  checkNoDuplicates proc fileRange
  checkTypeArgsWF proc fileRange
  checkModificationRights proc fileRange

  -- Temporarily add the formals into the context.
  let (inp_mty_sig, envWithInputs, tyArgSubst) ← setupInputEnv C Env proc fileRange

  -- Type check preconditions.
  -- Note: `envWithInputs` does not have the return variables in the context,
  -- which means that the presence of any return variables in the preconditions
  -- will rightfully flag an error.
  let (preconditions, envAfterPreconds) ← typeCheckConditions C envWithInputs
                                            proc.spec.preconditions proc.header.name

  -- Temporarily add returns into the context, reusing the same typeArg substitution
  -- as the inputs so that both share the same fresh vars for each type parameter.
  let out_mtys := proc.header.outputs.values.map (Lambda.LMonoTy.subst tyArgSubst)
  let (out_mtys, envAfterPreconds) ← Lambda.LMonoTys.resolveAliases out_mtys envAfterPreconds
    |>.mapError (fun e => DiagnosticModel.withRange fileRange e)
  let out_mty_sig : @Lambda.LMonoTySignature Unit := proc.header.outputs.keys.zip out_mtys
  let out_lty_sig := Lambda.LMonoTySignature.toTrivialLTy out_mty_sig
  let envWithOutputs := Lambda.TEnv.addInNewestContext (T := CoreLParams) envAfterPreconds out_lty_sig

  -- Add "old" variables for in-out parameters (those in both inputs and outputs) so
  -- postconditions and body can reference `old x`. Use the *instantiated* input signature
  -- `inp_mty_sig` (alias-resolved, type parameters replaced by the shared fresh vars) rather
  -- than the raw declared types, so `old x` has the same type as `x` in the body context.
  let oldInoutBindings : List (CoreIdent × Lambda.LTy) :=
    (inp_mty_sig.filter fun (id, _) => (ListMap.keys proc.header.outputs).contains id).map
      fun (id, ty) => (CoreIdent.mkOld id.name, .forAll [] ty)
  let envWithOldVars := envWithOutputs.addInNewestContext oldInoutBindings

  -- Type check postconditions.
  let (postconditions, envAfterPostconds) ← typeCheckConditions C envWithOldVars
                                              proc.spec.postconditions proc.header.name

  -- Type check body.
  -- Note that `Statement.typeCheck` already reports source locations in
  -- error messages.
  let bodyStmts : List Statement ← match proc.body with
    | .structured ss => pure ss
    | .cfg _ =>
      Except.error (DiagnosticModel.withRange fileRange
        f!"[{proc.header.name}]: CFG procedures not supported yet")
  -- Add the typeArg substitution (e.g. [a → $__ty0]) so that body type annotations
  -- referencing the original names get normalized to the fresh vars by `preprocess`.
  let tyArgConstraints : Lambda.Constraints := tyArgSubst.flatten.map fun (k, v) => (.ftvar k, v)
  let S ← Lambda.Constraints.unify tyArgConstraints envAfterPostconds.stateSubstInfo
          |>.mapError (fun e => DiagnosticModel.withRange fileRange (format e))
  let envForBody := envAfterPostconds.updateSubst S
  -- The rigid type variables are the fresh vars representing the procedure's type
  -- parameters. These must not be refined by unification in the body.
  let rigidVars := tyArgSubst.flatten.filterMap fun (_, v) =>
    match v with | .ftvar id => some id | _ => none
  let C := { C with rigidTypeVars := rigidVars }
  -- The fresh instantiation vars must remain abstract in the body env: a pre/postcondition
  -- (or the tyArg unification) may not refine them to a concrete type. Otherwise, e.g.
  -- `procedure P<a>(x:a) requires 0 < x` would silently pin `a := int` — a soundness gap,
  -- since a caller could instantiate `a := bool`. (Mirrors `Function.typeCheck`'s guard.)
  match rigidVars.find? (fun v =>
      Lambda.LMonoTy.subst envForBody.stateSubstInfo.subst (Lambda.LMonoTy.ftvar v)
        != Lambda.LMonoTy.ftvar v) with
  | some v =>
    let inferred := Lambda.LMonoTy.subst envForBody.stateSubstInfo.subst (Lambda.LMonoTy.ftvar v)
    .error <| DiagnosticModel.withRange fileRange
      f!"[{proc.header.name}]: rigid type variable '{v}' was refined to '{inferred}'; \
         a pre/postcondition or the signature over-constrains a declared type parameter"
  | none => pure ()
  -- Substitution to rename fresh type variables back to user-supplied names.
  let userSubst : Lambda.Subst :=
    [tyArgSubst.flatten.filterMap fun (orig, v) =>
      match v with | .ftvar fresh => some (fresh, .ftvar orig) | _ => none]
  let (annotated_body, finalEnv) ← (Statement.typeCheck C envForBody p (.some proc) bodyStmts)
    |>.mapError (fun e => { e with message := renameTypeVars userSubst e.message })

  -- Remove formals and returns from the context -- they ought to be local to
  -- the procedure body.
  let finalEnv := finalEnv.popContext

  -- Construct final result.
  let finalPreconditions := Procedure.Spec.updateCheckExprs preconditions.toList proc.spec.preconditions
  let finalPostconditions := Procedure.Spec.updateCheckExprs postconditions.toList proc.spec.postconditions
  -- Keep the declared type parameters: `userSubst` renames the signature below back to the
  -- original type-variable names, so it still references `proc.header.typeArgs`. Clearing
  -- them to `[]` would leave a polymorphic signature with undeclared type variables — an
  -- inconsistent procedure the checker would reject on a second pass. (Mirrors `Function.typeCheck`.)
  let new_hdr := { proc.header with typeArgs := proc.header.typeArgs,
                                    inputs := inp_mty_sig.map (fun (id, mty) => (id, Lambda.LMonoTy.subst userSubst mty)),
                                    outputs := out_mty_sig.map (fun (id, mty) => (id, Lambda.LMonoTy.subst userSubst mty)) }
  let new_spec := { proc.spec with preconditions := finalPreconditions,
                                   postconditions := finalPostconditions }
  let annotated_body := annotated_body.map (Core.Statement.Statement.subst userSubst)
  let new_proc := { proc with header := new_hdr, spec := new_spec, body := .structured annotated_body }

  return (new_proc, finalEnv)

---------------------------------------------------------------------

end Procedure
end Core

end -- public section
