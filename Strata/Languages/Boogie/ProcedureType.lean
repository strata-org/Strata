/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Boogie.Procedure
import Strata.DL.Imperative.HasVars
import Strata.Languages.Boogie.StatementType
import Strata.Languages.Boogie.OldExpressions

---------------------------------------------------------------------

namespace Boogie

open Std (ToFormat Format format)
open Imperative (MetaData)

namespace Procedure

def typeCheck (C: Boogie.Expression.TyContext) (Env : Boogie.Expression.TyEnv) (p : Program)
  (proc : Procedure) (md : MetaData Expression) : Except Format (Procedure × Boogie.Expression.TyEnv) :=
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
     if preconditions.any (fun p => OldExpressions.containsOldExpr p) then
      .error f!"{sourceLoc}[{proc.header.name}]: Preconditions cannot contain applications of\
                the `old` function!"
     else
      -- 1. Temporarily add the formals and returns into the context.
      let Env := Env.pushEmptyContext
      let (mty_sig, Env) ← Lambda.LMonoTySignature.instantiate C Env proc.header.typeArgs
                            (proc.header.inputs ++ proc.header.outputs)
                            |>.mapError errorWithSourceLoc
      let lty_sig := Lambda.LMonoTySignature.toTrivialLTy mty_sig
      let Env := Env.addToContext lty_sig
      -- 2. Normalize the old expressions in the postconditions. The evaluator
      --    depends on this step! See also note in `OldExpressions.lean`.
      let postcondition_checks := OldExpressions.normalizeOldChecks proc.spec.postconditions
      -- 3. Ensure that the preconditions and postconditions are of type boolean.
      let postconditions := postcondition_checks.map (fun (_, c) => c.expr)
      let (preconditions_a, Env) ← Lambda.LExpr.resolves C Env preconditions |>.mapError errorWithSourceLoc
      let pre_tys := preconditions_a.map Lambda.LExpr.toLMonoTy
      let preconditions := preconditions_a.map Lambda.LExpr.unresolved
      let (postconditions_a, Env) ← Lambda.LExpr.resolves C Env postconditions |>.mapError errorWithSourceLoc
      let post_tys := postconditions_a.map Lambda.LExpr.toLMonoTy
      let postconditions := postconditions_a.map Lambda.LExpr.unresolved
      if (pre_tys ++ post_tys).any (fun ty => ty != .tcons "bool" []) then
        .error f!"{sourceLoc}[{proc.header.name}]: Expected pre- and post-conditions to be of type Bool!"
      else
        -- 4. Typecheck the body of the procedure.
        -- Note that `Statement.typeCheck` already reports source locations in
        -- error messages.
        let (annotated_body, Env) ← Statement.typeCheck C Env p (.some proc) proc.body
        -- Remove formals and returns from the context.
        let Env := Env.popContext
        let preconditions := Procedure.Spec.updateCheckExprs preconditions proc.spec.preconditions
        let postconditions := Procedure.Spec.updateCheckExprs postconditions proc.spec.postconditions
        let new_hdr := { proc.header with typeArgs := [],
                                          inputs := mty_sig.take proc.header.inputs.length,
                                          outputs := mty_sig.drop proc.header.inputs.length }
        let new_spec := { proc.spec with preconditions := preconditions, postconditions := postconditions }
        let new_proc := { proc with header := new_hdr, spec := new_spec, body := annotated_body }
        .ok (new_proc, Env)

---------------------------------------------------------------------
end Procedure
end Boogie
