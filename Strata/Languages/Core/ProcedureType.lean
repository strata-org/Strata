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

namespace Procedure

-- Error message prefix for errors in processing procedure pre/post conditions.
def conditionErrorMsgPrefix (procName : CoreIdent) (condName : CoreLabel)
    (md : MetaData Expression) : Format :=
  let sourceLoc := MetaData.formatFileRangeD md (includeEnd? := true)
  f!"{sourceLoc} [{procName}:{condName}]:"

open Lambda.LTy.Syntax in
-- Type checking procedure pre/post conditions.
def conditionTypeCheck (C: Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (expr : Expression.Expr) (errorMsgPrefix : Format) :
    Except Format (Expression.Expr × Core.Expression.TyEnv) := do
  let (condAnnotated, newEnv) ← Lambda.LExpr.resolve C Env expr
                         |>.mapError (fun e => f!"{errorMsgPrefix} {e}")
  if condAnnotated.toLMonoTy != mty[bool] then
    .error f!"{errorMsgPrefix}: Expected condition to be of type Bool,\
              but got {condAnnotated.toLMonoTy}!"
  return (condAnnotated.unresolved, newEnv)

def typeCheck (C: Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (p : Program)
  (proc : Procedure) (md : MetaData Expression) : Except Format (Procedure × Core.Expression.TyEnv) :=
  let sourceLoc := MetaData.formatFileRangeD md (includeEnd? := false)
  let sourceLoc := if sourceLoc.isEmpty then sourceLoc else f!"{sourceLoc} "
  let errorWithSourceLoc := fun e => if sourceLoc.isEmpty then e else f!"{sourceLoc} {e}"
  if !proc.header.inputs.keys.Nodup then
    .error f!"{sourceLoc}[{proc.header.name}] Duplicates found in the formals!"
  else if !proc.header.outputs.keys.Nodup then
    .error f!"{sourceLoc}[{proc.header.name}] Duplicates found in the return variables!"
  else if !proc.spec.modifies.Nodup then
    .error f!"{sourceLoc}[{proc.header.name}] Duplicates found in the modifies clause!"
  else if proc.spec.modifies.any (fun v => v ∈ proc.header.inputs.keys) then
    .error f!"{sourceLoc}[{proc.header.name}] Variables in the modifies clause must \
              not appear in the formals.\n\
              Modifies: {proc.spec.modifies}\n
              Formals: {proc.header.inputs.keys}"
  else if proc.spec.modifies.any (fun v => v ∈ proc.header.outputs.keys) then
    .error f!"{sourceLoc}[{proc.header.name}] Variables in the modifies clause must \
              not appear in the return values.\n\
              Modifies: {proc.spec.modifies}\n
              Returns: {proc.header.outputs.keys}"
  else if proc.header.inputs.keys.any (fun v => v ∈ proc.header.outputs.keys) then
    .error f!"{sourceLoc}[{proc.header.name}] Variables in the formals must not appear \
              in the return values.\n\
              Formals: {proc.header.inputs.keys}\n
              Returns: {proc.header.outputs.keys}"
  else if proc.spec.modifies.any (fun v => (Env.context.types.find? v).isNone) then
    .error f!"{sourceLoc}[{proc.header.name}]: All the variables in the modifies \
              clause must exist in the context! \
              Modifies: {proc.spec.modifies}"
  else do
    let modifiedVars := (Imperative.Block.modifiedVars proc.body).eraseDups
    let definedVars := (Imperative.Block.definedVars proc.body).eraseDups
    let allowedVars := proc.header.outputs.keys ++ proc.spec.modifies ++ definedVars
    if modifiedVars.any (fun v => v ∉ allowedVars) then
      .error f!"{sourceLoc}[{proc.header.name}]: This procedure modifies variables it is not allowed to!\n\
                Variables actually modified: {modifiedVars}\n\
                Modification allowed for these variables: {allowedVars}"
    else
      -- 1. Temporarily add the formals into the context.
      let Env := Env.pushEmptyContext
      let (inp_mty_sig, Env) ← Lambda.LMonoTySignature.instantiate C Env proc.header.typeArgs
                            proc.header.inputs
                            |>.mapError errorWithSourceLoc
      let inp_lty_sig := Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig
      let Env := Env.addToContext inp_lty_sig
      -- 2. Type check preconditions under `Env` -- note: `Env` does not have
      --    the return variables in the context, which means that the presence
      --    of any return variables in the preconditions will flag an error.
      let mut preconditions := (#[] : Array Expression.Expr)
      let mut precondEnv := Env
      for (name, precond) in (proc.spec.preconditions.keys, proc.spec.preconditions.values) do
        let precondErrorMsgPfx := conditionErrorMsgPrefix proc.header.name name precond.md
        if OldExpressions.containsOldExpr precond.expr then
          .error f!"{precondErrorMsgPfx} Preconditions cannot contain applications of \
                    the `old` function!"
        let (precond, newEnv) ← conditionTypeCheck C precondEnv precond.expr precondErrorMsgPfx
        preconditions := preconditions.push precond
        precondEnv := newEnv
        -- End of for loop.
      -- 3. Temporarily add the returns into the context.
      let Env := precondEnv
      let (out_mty_sig, Env) ← Lambda.LMonoTySignature.instantiate C Env proc.header.typeArgs
                            proc.header.outputs
                            |>.mapError errorWithSourceLoc
      let out_lty_sig := Lambda.LMonoTySignature.toTrivialLTy out_mty_sig
      let Env := Env.addToContext out_lty_sig
      -- 4. Type check postconditions.
      let mut postconditions := (#[] : Array Expression.Expr)
      let mut postcondEnv := Env
      for (name, postcond) in (proc.spec.postconditions.keys, proc.spec.postconditions.values) do
        -- Normalize the old expressions in the postconditions. The evaluator
        -- depends on this step! See also note in `OldExpressions.lean`.
        let postcondNormalizedExpr := OldExpressions.normalizeOldExpr postcond.expr
        let postcondErrorMsgPfx := conditionErrorMsgPrefix proc.header.name name postcond.md
        let (postcond, newEnv) ← conditionTypeCheck C postcondEnv postcondNormalizedExpr postcondErrorMsgPfx
        postconditions := postconditions.push postcond
        postcondEnv := newEnv
        -- End of for loop.
      let Env := postcondEnv
      -- 5. Typecheck the body of the procedure.
      -- Note that `Statement.typeCheck` already reports source locations in
      -- error messages.
      let (annotated_body, Env) ← Statement.typeCheck C Env p (.some proc) proc.body
      -- 6. Remove formals and returns from the `Env`.
      let Env := Env.popContext
      let finalPreconds := Procedure.Spec.updateCheckExprs preconditions.toList proc.spec.preconditions
      let finalPostConds := Procedure.Spec.updateCheckExprs postconditions.toList proc.spec.postconditions
      -- Type arguments are empty below because we've replaced polytypes with monotypes.
      let new_hdr := { proc.header with typeArgs := [],
                                        inputs := inp_mty_sig,
                                        outputs := out_mty_sig }
      let new_spec := { proc.spec with preconditions := finalPreconds, postconditions := finalPostConds }
      let new_proc := { proc with header := new_hdr, spec := new_spec, body := annotated_body }
      .ok (new_proc, Env)

---------------------------------------------------------------------
end Procedure
end Core
