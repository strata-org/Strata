/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Core.Procedure
import Strata.DL.Imperative.HasVars
import Strata.Languages.Core.StatementType
import Strata.Languages.Core.OldExpressions

---------------------------------------------------------------------

namespace Core

open Std (ToFormat Format format)
open Imperative (MetaData)
open Strata (DiagnosticModel FileRange)

namespace Procedure

private def checkNoDuplicates (proc : Procedure) (sourceLoc : FileRange) :
    Except DiagnosticModel Unit := do
  if !proc.header.inputs.keys.Nodup then
    .error <| DiagnosticModel.withRange sourceLoc f!"[{proc.header.name}] Duplicates found in the formals!"
  if !proc.header.outputs.keys.Nodup then
    .error <| DiagnosticModel.withRange sourceLoc f!"[{proc.header.name}] Duplicates found in the return variables!"
  if !proc.spec.modifies.Nodup then
    .error <| DiagnosticModel.withRange sourceLoc f!"[{proc.header.name}] Duplicates found in the modifies clause!"

private def checkVariableScoping (proc : Procedure) (sourceLoc : FileRange) :
    Except DiagnosticModel Unit := do
  if proc.spec.modifies.any (fun v => v ∈ proc.header.inputs.keys) then
    .error <| DiagnosticModel.withRange sourceLoc f!"[{proc.header.name}] Variables in the modifies clause must \
              not appear in the formals.\n\
              Modifies: {proc.spec.modifies}\n\
              Formals: {proc.header.inputs.keys}"
  if proc.spec.modifies.any (fun v => v ∈ proc.header.outputs.keys) then
    .error <| DiagnosticModel.withRange sourceLoc f!"[{proc.header.name}] Variables in the modifies clause must \
              not appear in the return values.\n\
              Modifies: {proc.spec.modifies}\n\
              Returns: {proc.header.outputs.keys}"
  if proc.header.inputs.keys.any (fun v => v ∈ proc.header.outputs.keys) then
    .error <| DiagnosticModel.withRange sourceLoc f!"[{proc.header.name}] Variables in the formals must \
              not appear in the return values.\n\
              Formals: {proc.header.inputs.keys}\n\
              Returns: {proc.header.outputs.keys}"

private def checkModifiesClause (proc : Procedure) (Env : Core.Expression.TyEnv)
    (sourceLoc : FileRange) : Except DiagnosticModel Unit := do
  if proc.spec.modifies.any (fun v => (Env.context.types.find? v).isNone) then
    .error <| DiagnosticModel.withRange sourceLoc f!"[{proc.header.name}]: All the variables in the modifies clause \
              must exist in the context!\n\
              Modifies: {proc.spec.modifies}"

private def checkModificationRights (proc : Procedure) (sourceLoc : FileRange) :
    Except DiagnosticModel Unit := do
  let modifiedVars := (Imperative.Block.modifiedVars proc.body).eraseDups
  let definedVars := (Imperative.Block.definedVars proc.body).eraseDups
  let allowedVars := proc.header.outputs.keys ++ proc.spec.modifies ++ definedVars
  if modifiedVars.any (fun v => v ∉ allowedVars) then
    .error <| DiagnosticModel.withRange sourceLoc f!"[{proc.header.name}]: This procedure modifies variables it \
              is not allowed to!\n\
              Variables actually modified: {modifiedVars}\n\
              Modification allowed for these variables: {allowedVars}"

private def setupInputEnv (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (sourceLoc : FileRange) :
    Except DiagnosticModel (@Lambda.LMonoTySignature Visibility × Core.Expression.TyEnv) := do
  let Env := Env.pushEmptyContext
  let (inp_mty_sig, Env) ← Lambda.LMonoTySignature.instantiate C Env proc.header.typeArgs
                            proc.header.inputs |>.mapError (fun e => DiagnosticModel.withRange sourceLoc e)
  let inp_lty_sig := Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig
  let Env := Env.addToContext inp_lty_sig
  return (inp_mty_sig, Env)

-- Error message prefix for errors in processing procedure pre/post conditions.
def conditionErrorMsgPrefix (procName : CoreIdent) (condName : CoreLabel)
    (md : MetaData Expression) : DiagnosticModel :=
  md.toDiagnosticF f!"[{procName}:{condName}]:"

-- Type checking procedure pre/post conditions.
-- We flag occurrences of `old` expressions in the preconditions and normalize
-- them in the postconditions.
open Lambda.LTy.Syntax in
private def typeCheckConditions (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (conditions : ListMap CoreLabel Check) (procName : CoreIdent) (checkOldExprs : Bool) :
    Except DiagnosticModel (Array Expression.Expr × Core.Expression.TyEnv) := do
  let mut results := #[]
  let mut currentEnv := Env
  for (name, condition) in (conditions.keys, conditions.values) do
    let errorPrefix := conditionErrorMsgPrefix procName name condition.md
    if checkOldExprs && OldExpressions.containsOldExpr condition.expr then
      .error { errorPrefix with message := errorPrefix.message ++ " Preconditions cannot contain applications of the `old` function!" }
    let expr := if checkOldExprs then condition.expr else OldExpressions.normalizeOldExpr condition.expr
    let (annotatedExpr, newEnv) ← Lambda.LExpr.resolve C currentEnv expr
                                    |>.mapError (fun e => { errorPrefix with message := errorPrefix.message ++ " " ++ toString e })
    if annotatedExpr.toLMonoTy != mty[bool] then
      .error { errorPrefix with message := errorPrefix.message ++ s!": Expected condition to be of type Bool, but got {annotatedExpr.toLMonoTy}!" }
    results := results.push annotatedExpr.unresolved
    currentEnv := newEnv
  return (results, currentEnv)

def typeCheck (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (p : Program)
    (proc : Procedure) (md : MetaData Expression) : Except DiagnosticModel (Procedure × Core.Expression.TyEnv) := do
  let fileRange := Imperative.getFileRange md |>.getD FileRange.unknown

  -- Validate well-formedness of formals, returns, and modifies clause.
  checkNoDuplicates proc fileRange
  checkVariableScoping proc fileRange
  checkModifiesClause proc Env fileRange
  checkModificationRights proc fileRange

  -- Temporarily add the formals into the context.
  let (inp_mty_sig, envWithInputs) ← setupInputEnv C Env proc fileRange

  -- Type check preconditions.
  -- Note: `envWithInputs` does not have the return variables in the context,
  -- which means that the presence of any return variables in the preconditions
  -- will rightfully flag an error.
  let (preconditions, envAfterPreconds) ← typeCheckConditions C envWithInputs
                                            proc.spec.preconditions proc.header.name
                                            (checkOldExprs := true)

  -- Temporarily add returns into the context.
  let (out_mty_sig, envWithOutputs) ← Lambda.LMonoTySignature.instantiate C
                                        envAfterPreconds proc.header.typeArgs
                                        proc.header.outputs |>.mapError (fun e => DiagnosticModel.withRange fileRange e)
  let out_lty_sig := Lambda.LMonoTySignature.toTrivialLTy out_mty_sig
  let envWithOutputs := envWithOutputs.addToContext out_lty_sig

  -- Type check postconditions.
  let (postconditions, envAfterPostconds) ← typeCheckConditions C envWithOutputs
                                              proc.spec.postconditions proc.header.name
                                              (checkOldExprs := false)

  -- Type check body.
  -- Note that `Statement.typeCheck` already reports source locations in
  -- error messages.
  let (annotated_body, finalEnv) ← Statement.typeCheck C envAfterPostconds p (.some proc) proc.body

  -- Remove formals and returns from the context -- they ought to be local to
  -- the procedure body.
  let finalEnv := finalEnv.popContext

  -- Construct final result.
  let finalPreconditions := Procedure.Spec.updateCheckExprs preconditions.toList proc.spec.preconditions
  let finalPostconditions := Procedure.Spec.updateCheckExprs postconditions.toList proc.spec.postconditions
  -- Type arguments are empty below because we've replaced polytypes with monotypes.
  let new_hdr := { proc.header with typeArgs := [],
                                    inputs := inp_mty_sig,
                                    outputs := out_mty_sig }
  let new_spec := { proc.spec with preconditions := finalPreconditions,
                                   postconditions := finalPostconditions }
  let new_proc := { proc with header := new_hdr, spec := new_spec, body := annotated_body }

  return (new_proc, finalEnv)

---------------------------------------------------------------------

end Procedure
end Core
