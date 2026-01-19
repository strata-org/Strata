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
     let preconditions := Procedure.Spec.getCheckExprs proc.spec.preconditions
     dbg_trace f!"MetaData: {proc.spec.preconditions.values.map (fun v => v.md)}"
     if preconditions.any (fun p => OldExpressions.containsOldExpr p) then
      .error f!"{sourceLoc}[{proc.header.name}]: Preconditions cannot contain applications of\
                the `old` function!"
     else
      -- 1. Temporarily add the formals into the context.
      let Env := Env.pushEmptyContext
      let (inp_mty_sig, Env) ← Lambda.LMonoTySignature.instantiate C Env proc.header.typeArgs
                            proc.header.inputs
                            |>.mapError errorWithSourceLoc
      let lty_sig := Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig
      let Env := Env.addToContext lty_sig
      -- 2. Type check preconditions under `Env` -- note: `Env` does not have
      --    the return variables in the context, which means that the presence
      --    of any return variables in the preconditions will flag an error.
      let (preconditions_a, Env) ← Lambda.LExpr.resolves C Env preconditions |>.mapError errorWithSourceLoc
      let pre_tys := preconditions_a.map Lambda.LExpr.toLMonoTy
      let preconditions := preconditions_a.map Lambda.LExpr.unresolved
      for (pre, ty) in proc.spec.preconditionNames.zip pre_tys do
        if ty != .tcons "bool" [] then
          .error f!"{sourceLoc}[{proc.header.name}]: Expected precondition {pre} to be of type Bool, but got {ty}!"
      -- 3. Normalize the old expressions in the postconditions. The evaluator
      --    depends on this step! See also note in `OldExpressions.lean`.
      let postcondition_checks := OldExpressions.normalizeOldChecks proc.spec.postconditions
      -- 4. Type check postconditions, after adding returns to `Env`.
      let (out_mty_sig, Env) ← Lambda.LMonoTySignature.instantiate C Env proc.header.typeArgs
                            proc.header.outputs
                            |>.mapError errorWithSourceLoc
      let lty_sig := Lambda.LMonoTySignature.toTrivialLTy out_mty_sig
      let Env := Env.addToContext lty_sig
      let postconditions := postcondition_checks.map (fun (_, c) => c.expr)
      let (postconditions_a, Env) ← Lambda.LExpr.resolves C Env postconditions |>.mapError errorWithSourceLoc
      let post_tys := postconditions_a.map Lambda.LExpr.toLMonoTy
      let postconditions := postconditions_a.map Lambda.LExpr.unresolved
      for (post, ty) in proc.spec.postconditionNames.zip post_tys do
        if ty != .tcons "bool" [] then
          .error f!"{sourceLoc}[{proc.header.name}]: Expected postcondition {post} to be of type Bool, but got {ty}!"
      -- 5. Typecheck the body of the procedure.
      -- Note that `Statement.typeCheck` already reports source locations in
      -- error messages.
      let (annotated_body, Env) ← Statement.typeCheck C Env p (.some proc) proc.body
      -- 6. Remove formals and returns from the `Env`.
      let Env := Env.popContext
      let preconditions := Procedure.Spec.updateCheckExprs preconditions proc.spec.preconditions
      let postconditions := Procedure.Spec.updateCheckExprs postconditions proc.spec.postconditions
      -- Type arguments are empty below because we've replaced polytypes with monotypes.
      let new_hdr := { proc.header with typeArgs := [],
                                        inputs := inp_mty_sig,
                                        outputs := out_mty_sig }
      let new_spec := { proc.spec with preconditions := preconditions, postconditions := postconditions }
      let new_proc := { proc with header := new_hdr, spec := new_spec, body := annotated_body }
      .ok (new_proc, Env)

---------------------------------------------------------------------
end Procedure
end Core
