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

private def checkNoDuplicates (proc : Procedure) (sourceLoc : FileRange) :
    Except DiagnosticModel Unit := do
  if !proc.header.inputs.keys.Nodup then
    .error <| DiagnosticModel.withRange sourceLoc f!"[{proc.header.name}] Duplicates found in the formals!"
  if !proc.header.outputs.keys.Nodup then
    .error <| DiagnosticModel.withRange sourceLoc f!"[{proc.header.name}] Duplicates found in the return variables!"

private def checkModificationRights (proc : Procedure) (sourceLoc : FileRange) :
    Except DiagnosticModel Unit := do
  let modifiedVars := (HasVarsImp.modifiedVars (P := Expression) proc.body).eraseDups
  let definedVars := (HasVarsImp.definedVars (P := Expression) proc.body false).eraseDups
  let allowedVars := proc.header.outputs.keys ++ definedVars
  let disallowed := modifiedVars.filter (fun v => !allowedVars.contains v)
  if !disallowed.isEmpty then
    .error <| DiagnosticModel.withRange sourceLoc f!"[{proc.header.name}]: This procedure modifies variables it \
              is not allowed to!\n\
              Variables actually modified: {modifiedVars}\n\
              Modification allowed for these variables: {allowedVars}"

private def setupInputEnv (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (sourceLoc : FileRange) :
    Except DiagnosticModel (@Lambda.LMonoTySignature Unit × Core.Expression.TyEnv) := do
  let Env := Env.pushEmptyContext
  let (inp_mty_sig, Env) ← Lambda.LMonoTySignature.instantiate C Env proc.header.typeArgs
                            proc.header.inputs |>.mapError (fun e => DiagnosticModel.withRange sourceLoc e)
  let inp_lty_sig := Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig
  let Env := Env.addInNewestContext inp_lty_sig
  return (inp_mty_sig, Env)

private def checkUniqueLabels (procName : CoreIdent) (cfg : DetCFG) (sourceLoc : FileRange) :
    Except DiagnosticModel Unit := do
  let labels := cfg.blocks.map (·.1)
  if !labels.Nodup then
    let dups := labels.filter (fun l => labels.countP (· == l) > 1) |>.eraseDups
    .error <| DiagnosticModel.withRange sourceLoc
      f!"[{procName}]: Duplicate block labels in CFG: {dups}"

private def checkEntryExists (procName : CoreIdent) (cfg : DetCFG) (sourceLoc : FileRange) :
    Except DiagnosticModel Unit := do
  let labels := cfg.blocks.map (·.1)
  if !labels.contains cfg.entry then
    .error <| DiagnosticModel.withRange sourceLoc
      f!"[{procName}]: Entry label \"{cfg.entry}\" not found in CFG blocks. \
         Available labels: {labels}"

private def checkTargetLabels (procName : CoreIdent) (cfg : DetCFG) (sourceLoc : FileRange) :
    Except DiagnosticModel Unit := do
  let labels := cfg.blocks.map (·.1)
  for (lbl, blk) in cfg.blocks do
    match blk.transfer with
    | .condGoto _ lt lf _ =>
      if !labels.contains lt then
        .error <| DiagnosticModel.withRange sourceLoc
          f!"[{procName}]: Block \"{lbl}\" branches to unknown label \"{lt}\". \
             Available labels: {labels}"
      if !labels.contains lf then
        .error <| DiagnosticModel.withRange sourceLoc
          f!"[{procName}]: Block \"{lbl}\" branches to unknown label \"{lf}\". \
             Available labels: {labels}"
    | .finish _ => pure ()

-- Type environment flows sequentially through all blocks in list order,
-- regardless of control-flow reachability.  This is a sound over-approximation:
-- it may accept a program that uses an uninitialized variable at runtime (the
-- verifier will still catch the error), but it never misses a real type error.
-- Per-block scoping would require a dataflow fixpoint over the CFG.
open Lambda Lambda.LTy.Syntax in
private def typeCheckCFG (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (P : Program) (proc : Procedure) (cfg : DetCFG) (sourceLoc : FileRange) :
    Except DiagnosticModel (DetCFG × Core.Expression.TyEnv) := do
  checkUniqueLabels proc.header.name cfg sourceLoc
  checkEntryExists proc.header.name cfg sourceLoc
  checkTargetLabels proc.header.name cfg sourceLoc
  let mut currentEnv := Env
  let mut annotatedBlocks : List (String × Imperative.DetBlock String Command Expression) := []
  for (lbl, blk) in cfg.blocks do
    let mut cmds' := []
    for cmd in blk.cmds do
      let (cmd', newEnv) ← Statement.typeCheckCmd C currentEnv P cmd
      currentEnv := newEnv
      cmds' := cmds' ++ [cmd']
    let transfer' ← match blk.transfer with
      | .condGoto p lt lf md =>
        let (pa, newEnv) ← LExpr.resolve C currentEnv p
          |>.mapError DiagnosticModel.fromFormat
        currentEnv := newEnv
        if pa.toLMonoTy != mty[bool] then
          .error <| DiagnosticModel.withRange sourceLoc
            f!"[{proc.header.name}]: Branch condition in block \"{lbl}\" \
               is not of type bool, got {pa.toLMonoTy}"
        pure (Imperative.DetTransferCmd.condGoto pa.unresolved lt lf md)
      | .finish md => pure (.finish md)
    annotatedBlocks := annotatedBlocks ++ [(lbl, { cmds := cmds', transfer := transfer' })]
  let annotatedCFG : DetCFG := { entry := cfg.entry, blocks := annotatedBlocks }
  return (annotatedCFG, currentEnv)

-- Error message prefix for errors in processing procedure pre/post conditions.
def conditionErrorMsgPrefix (procName : CoreIdent) (condName : CoreLabel)
    (md : MetaData Expression) : DiagnosticModel :=
  md.toDiagnosticF f!"[{procName}:{condName}]:"

-- Type checking procedure pre/post conditions.
open Lambda.LTy.Syntax in
private def typeCheckConditions (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (conditions : ListMap CoreLabel Check) (procName : CoreIdent) :
    Except DiagnosticModel (Array Expression.Expr × Core.Expression.TyEnv) := do
  let mut results := #[]
  let mut currentEnv := Env
  for (name, condition) in (conditions.keys, conditions.values) do
    let errorPrefix := conditionErrorMsgPrefix procName name condition.md
    let (annotatedExpr, newEnv) ← Lambda.LExpr.resolve C currentEnv condition.expr
                                    |>.mapError (fun e => { errorPrefix with message := errorPrefix.message ++ " " ++ toString e })
    if annotatedExpr.toLMonoTy != mty[bool] then
      .error { errorPrefix with message := errorPrefix.message ++ s!": Expected condition to be of type Bool, but got {annotatedExpr.toLMonoTy}!" }
    results := results.push annotatedExpr.unresolved
    currentEnv := newEnv
  return (results, currentEnv)

def typeCheck (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (p : Program)
    (proc : Procedure) (md : MetaData Expression) : Except DiagnosticModel (Procedure × Core.Expression.TyEnv) := do
  let fileRange := Imperative.getFileRange md |>.getD FileRange.unknown

  -- Validate well-formedness of formals and returns.
  checkNoDuplicates proc fileRange
  checkModificationRights proc fileRange

  -- Temporarily add the formals into the context.
  let (inp_mty_sig, envWithInputs) ← setupInputEnv C Env proc fileRange

  -- Type check preconditions.
  -- Note: `envWithInputs` does not have the return variables in the context,
  -- which means that the presence of any return variables in the preconditions
  -- will rightfully flag an error.
  let (preconditions, envAfterPreconds) ← typeCheckConditions C envWithInputs
                                            proc.spec.preconditions proc.header.name

  -- Temporarily add returns into the context.
  let (out_mty_sig, envWithOutputs) ← Lambda.LMonoTySignature.instantiate C
                                        envAfterPreconds proc.header.typeArgs
                                        proc.header.outputs |>.mapError (fun e => DiagnosticModel.withRange fileRange e)
  let out_lty_sig := Lambda.LMonoTySignature.toTrivialLTy out_mty_sig
  let envWithOutputs := envWithOutputs.addInNewestContext out_lty_sig

  -- Add "old" variables for in-out parameters (those in both inputs and outputs)
  -- so that postconditions and body can reference `old x`.
  let oldInoutBindings : List (CoreIdent × Lambda.LTy) :=
    proc.header.getInoutParams.toList.map fun (id, ty) =>
      (CoreIdent.mkOld id.name, .forAll [] ty)
  let envWithOldVars := envWithOutputs.addInNewestContext oldInoutBindings

  -- Type check postconditions.
  let (postconditions, envAfterPostconds) ← typeCheckConditions C envWithOldVars
                                              proc.spec.postconditions proc.header.name

  -- Type check body.
  -- Note that `Statement.typeCheck` already reports source locations in
  -- error messages.
  let (annotated_body, annotated_cfg, finalEnv) ← match proc.body with
    | .structured ss =>
      let (ss', env') ← Statement.typeCheck C envAfterPostconds p (.some proc) ss
      pure (ss', none, env')
    | .cfg cfgBody =>
      let (cfg', env') ← typeCheckCFG C envAfterPostconds p proc cfgBody fileRange
      pure ([], some cfg', env')

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
  let new_body := match annotated_cfg with
    | some cfg' => .cfg cfg'
    | none => .structured annotated_body
  let new_proc := { proc with header := new_hdr, spec := new_spec, body := new_body }

  return (new_proc, finalEnv)

---------------------------------------------------------------------

end Procedure
end Core

end -- public section
