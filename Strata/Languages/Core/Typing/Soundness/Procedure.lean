/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.ProcedureType
public import Strata.Languages.Core.Typing.Spec.ProcedureTypeSpec
public import Strata.Languages.Core.Typing.Soundness.TypingAssumptions
public import Strata.Languages.Core.Typing.Soundness.Statement
public import Strata.Languages.Core.Typing.Soundness.StatementOutput
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.LExprTypeSpecProps
public import Strata.DL.Lambda.LExprT
public import Strata.DL.Lambda.FactoryWF
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.LTyProps
public import Strata.Util.ExceptProps
public import Strata.Util.ListMapProps
public import Strata.Util.ListUtils
public import Strata.Util.ListUtilsProps
public import Strata.Util.Tactics
public import Strata.Languages.Core.Typing.Props.TypeSkolemProps
public import Strata.Languages.Core.Typing.Props.SourceExprResolveProps
public import Strata.Languages.Core.Typing.Props.SkolemScopeProps
public import Strata.Languages.Core.Typing.Props.SkolemizerProps
public import Strata.Languages.Core.Typing.Props.FunctionTypeProps
import all Strata.Languages.Core.ProcedureType
import Strata.Languages.Core.StatementType
import Strata.Languages.Core.Typing.Props.ProcedureTypeProps
public import Strata.Languages.Core.ProcedureProps
import Strata.Languages.Core.ProcedureTypeProps
import Strata.Languages.Core.Typing.Props.StatementEraseProps
import Strata.Languages.Core.CallWFProps
import Strata.Languages.Core.FunctionType
import all Strata.Languages.Core.Typing.Props.FunctionTypeProps
import all Strata.Languages.Core.Typing.Spec.ProcedureTypeSpec
import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import Strata.Languages.Core.Procedure
import Strata.DL.Imperative.Procedure
import Strata.DL.Lambda.LExprAnnotRel
import all Strata.Languages.Core.Typing.Soundness.StatementOutput
import Strata.Languages.Core.TypeSkolem
import Strata.Languages.Core.Typing.Soundness.Command
import Strata.Languages.Core.Typing.Props.StatementTypeProps
import Strata.Languages.Core.Typing.Props.TypingSpecProps
import Strata.Languages.Core.Typing.Props.NamesWFProps

/-! # Soundness of the procedure typechecker

The checker renames reserved type parameters (`Procedure.renameReservedTypeArgs`) and runs
`Procedure.typeCheckCore` on the result; most lemmas are about the core checker.

Key theorems:
* `Procedure.typeCheck_sound`: an accepted procedure satisfies `ProcHasType`.
* `Procedure.typeCheck_sound_output`: the returned procedure is well typed with valid names.
* `Procedure.typeCheckIn_sound`, `Procedure.typeCheckIn_sound_output`: the same for the checker
  run against given sets of type names that cover those in scope and in the procedure
  signatures of the program.
* `ProcSigResolved.instOf_renameTypeArgs`: calls typed against a procedure stay typed against
  its elaborated form. -/

public section

namespace Core

open Lambda Imperative
open TypeSpec
open Strata.Util (HMap HMaps)

variable {sc ps : Thunk (Std.HashSet String)} {tn : Unit → List String}

/-- A successful check means the substitution fixes every ambient rigid variable. -/
private theorem Procedure.ensureAmbientRigidVarsFixed_ok (procName : CoreIdent)
    (rigidVars : List TyIdentifier) (S : Subst) {u : Unit}
    (h : Procedure.ensureAmbientRigidVarsFixed procName rigidVars S = .ok u) :
    Procedure.ambientRigidVarsFixed rigidVars S = true := by
  unfold Procedure.ensureAmbientRigidVarsFixed at h
  elim_err h
  assumption

/-- A command with no error mentions no type variable outside the type parameters in a local's
    declared type or a call type argument. -/
private theorem Procedure.cmdUnboundTyVars_of_msg_none
    (typeArgs : List TyIdentifier) (c : Command)
    (h : Procedure.cmdUnboundMsg? typeArgs c = none) :
    Procedure.cmdUnboundTyVars typeArgs c = [] := by
  unfold Procedure.cmdUnboundMsg? at h
  split at h
  · rename_i hnil
    exact hnil
  · simp at h

/-- A successful check means every type variable that the body mentions in a local's declared
    type or in a call type argument is one of the procedure's type parameters. -/
private theorem Procedure.declTyVarsBound_of_check (procName : CoreIdent)
    (md : MetaData Expression) (typeArgs : List TyIdentifier) (body : Procedure.Body)
    (h : Procedure.checkDeclTyVarsBound procName md typeArgs body = .ok ()) :
    ∀ v ∈ bodyCollect (fun _ => []) LMonoTy.freeVars body, v ∈ typeArgs := by
  intro v hv
  rw [Procedure.bodyCollect_noExprs_eq_cmds, List.mem_flatMap] at hv
  obtain ⟨c, hc, hvc⟩ := hv
  unfold Procedure.checkDeclTyVarsBound at h
  split at h
  · rename_i hnone
    have hcnone : Procedure.cmdUnboundMsg? typeArgs c = none :=
      List.filterMap_eq_nil_iff.mp hnone c hc
    have hnil := Procedure.cmdUnboundTyVars_of_msg_none typeArgs c hcnone
    by_cases hin : v ∈ typeArgs
    · exact hin
    · have hmem : v ∈ Procedure.cmdUnboundTyVars typeArgs c := by
        unfold Procedure.cmdUnboundTyVars
        have hnotin : decide (v ∉ typeArgs) = true := by simpa using hin
        rw [List.mem_eraseDups, List.mem_filter]
        exact ⟨hvc, hnotin⟩
      rw [hnil] at hmem
      exact absurd hmem (List.not_mem_nil)
  · simp at h

/-- The signature the body scope is built from. -/
def bodySig (hdr : Procedure.Header) : @LMonoTySignature Unit :=
  oldInoutSig hdr.getInoutParams.toList ++ hdr.outputs ++ hdr.inputs

/-- When a `mapM` that checks each labeled condition with `f` succeeds, `f` accepts every source
    condition and produces every returned one. -/
private theorem Procedure.conditionsMapM_ok
    {f : CoreLabel → Procedure.Check → Except Strata.Message Procedure.Check}
    {g : CoreLabel × Procedure.Check → Except Strata.Message (CoreLabel × Procedure.Check)}
    {conds conds' : ListMap CoreLabel Procedure.Check}
    (hg : ∀ q r, g q = .ok r → ∃ chk', f q.1 q.2 = .ok chk' ∧ r = (q.1, chk'))
    (h : conds.mapM g = .ok conds') :
    (∀ c ∈ conds.values, ∃ lbl chk', f lbl c = .ok chk') ∧
      (∀ c ∈ conds'.values, ∃ lbl c₀, c₀ ∈ conds.values ∧ f lbl c₀ = .ok c) := by
  constructor
  · intro c hc
    obtain ⟨lbl, hmem⟩ := ListMap.mem_values _ c hc
    obtain ⟨r, -, hr⟩ := mapM_except_mem_left g conds conds' h (lbl, c) hmem
    obtain ⟨chk', hf, -⟩ := hg _ _ hr
    exact ⟨lbl, chk', hf⟩
  · intro c hc
    obtain ⟨lbl, hmem⟩ := ListMap.mem_values _ c hc
    obtain ⟨q, hqmem, hq⟩ := mapM_except_mem_right g conds conds' h (lbl, c) hmem
    obtain ⟨chk', hf, hr⟩ := hg _ _ hq
    simp only [Prod.mk.injEq] at hr
    rw [hr.2]
    have hq2 : q.2 ∈ conds.values := by
      rw [ListMap.values_eq_map_snd]
      exact List.mem_map_of_mem hqmem
    exact ⟨q.1, q.2, hq2, hf⟩

/-- What a successful `Procedure.typeCheckCore` run establishes about the source procedure `proc`
    and the returned `proc'`; `insR` and `outsR` are the resolved input and output types. -/
private structure Procedure.CheckRun (sc ps : Thunk (Std.HashSet String))
    (tn : Unit → List String) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (p : Program) (proc : Procedure) (md : MetaData Expression) (proc' : Procedure)
    (insR outsR : LMonoTys) : Prop where
  /-- The input parameter names are distinct. -/
  inputsNodup : proc.header.inputs.keys.Nodup
  /-- The output parameter names are distinct. -/
  outputsNodup : proc.header.outputs.keys.Nodup
  /-- No parameter name collides with the `old` name of an in-out parameter. -/
  oldNamesFresh : proc.header.oldNamesFresh
  /-- Each resolved input type is registered. -/
  insKnown : List.Rel₂ (fun _ ty' => isInstanceOfKnownType ty' C = true)
    proc.header.inputs.values insR
  /-- Each resolved output type is registered. -/
  outsKnown : List.Rel₂ (fun _ ty' => isInstanceOfKnownType ty' C = true)
    proc.header.outputs.values outsR
  /-- Resolving the aliases of the input types gives `insR` and keeps the environment. -/
  insResolve : LMonoTys.resolveAliases proc.header.inputs.values Env = .ok (insR, Env)
  /-- Resolving the aliases of the output types gives `outsR` and keeps the environment. -/
  outsResolve : LMonoTys.resolveAliases proc.header.outputs.values Env = .ok (outsR, Env)
  /-- Every variable the body modifies is an output or a variable the body defines. -/
  modRights : ∀ v ∈ HasVarsImp.modifiedVars (P := Expression) proc.body,
    v ∈ proc.header.outputs.keys ++ HasVarsImp.definedVars (P := Expression) proc.body false
  /-- The returned header pairs the parameter names with their resolved types. -/
  header : proc'.header = { proc.header with
    inputs := proc.header.inputs.keys.zip insR, outputs := proc.header.outputs.keys.zip outsR }
  /-- Every source precondition passes the condition check in the input scope. -/
  preconditionsChecked : ∀ c ∈ proc.spec.preconditions.values, ∃ lbl chk',
    Procedure.checkCondition (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn))
      (Function.formalsEnv Env (Procedure.rigidNames sc ps C proc tn) proc'.header.inputs)
      proc.header.name (Procedure.rigidNames sc ps C proc tn) lbl c = .ok chk'
  /-- Every returned precondition is the result of checking a source one in the input scope. -/
  preconditionsStored : ∀ c ∈ proc'.spec.preconditions.values, ∃ lbl c₀,
    c₀ ∈ proc.spec.preconditions.values ∧
    Procedure.checkCondition (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn))
      (Function.formalsEnv Env (Procedure.rigidNames sc ps C proc tn) proc'.header.inputs)
      proc.header.name (Procedure.rigidNames sc ps C proc tn) lbl c₀ = .ok c
  /-- Every source postcondition passes the condition check in the body scope. -/
  postconditionsChecked : ∀ c ∈ proc.spec.postconditions.values, ∃ lbl chk',
    Procedure.checkCondition (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn))
      (Function.formalsEnv Env (Procedure.rigidNames sc ps C proc tn) (bodySig proc'.header))
      proc.header.name (Procedure.rigidNames sc ps C proc tn) lbl c = .ok chk'
  /-- Every returned postcondition is the result of checking a source one in the body scope. -/
  postconditionsStored : ∀ c ∈ proc'.spec.postconditions.values, ∃ lbl c₀,
    c₀ ∈ proc.spec.postconditions.values ∧
    Procedure.checkCondition (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn))
      (Function.formalsEnv Env (Procedure.rigidNames sc ps C proc tn) (bodySig proc'.header))
      proc.header.name (Procedure.rigidNames sc ps C proc tn) lbl c₀ = .ok c
  /-- The returned preconditions are the checked source ones, with the same labels in the same
      order. -/
  preconditionsRel : List.Rel₂ (fun (a b : CoreLabel × Procedure.Check) =>
    b.1 = a.1 ∧
    Procedure.checkCondition (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn))
      (Function.formalsEnv Env (Procedure.rigidNames sc ps C proc tn) proc'.header.inputs)
      proc.header.name (Procedure.rigidNames sc ps C proc tn) a.1 a.2 = .ok b.2)
    proc.spec.preconditions proc'.spec.preconditions
  /-- The returned postconditions are the checked source ones, with the same labels in the same
      order. -/
  postconditionsRel : List.Rel₂ (fun (a b : CoreLabel × Procedure.Check) =>
    b.1 = a.1 ∧
    Procedure.checkCondition (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn))
      (Function.formalsEnv Env (Procedure.rigidNames sc ps C proc tn) (bodySig proc'.header))
      proc.header.name (Procedure.rigidNames sc ps C proc tn) a.1 a.2 = .ok b.2)
    proc.spec.postconditions proc'.spec.postconditions
  /-- The returned body mentions only type parameters in the declared types of its locals and in
      its call type arguments. -/
  declTyVarsBound : Procedure.checkDeclTyVarsBound proc.header.name md proc.header.typeArgs
    proc'.body = .ok ()
  /-- A CFG body, skolemized, passes the CFG checker in the body scope, and the returned body is
      the deskolemized result. -/
  bodyCfg : ∀ c o, proc.body = .cfg c o → ∃ loc cOut EnvX,
    CFG.typeCheck (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn))
        (Function.formalsEnv Env (Procedure.rigidNames sc ps C proc tn) (bodySig proc'.header))
        p proc
        (DetCFG.mapCmdsGuards c (skolemizeCmd none (Procedure.rigidNames sc ps C proc tn))
          (skolemizeBody none (Procedure.rigidNames sc ps C proc tn))) loc = .ok (cOut, EnvX) ∧
    proc'.body = .cfg (DetCFG.mapCmdsGuards cOut
      (mapCmdTys (deskolemizeTy (Procedure.rigidNames sc ps C proc tn)))
      (mapExprTys (deskolemizeTy (Procedure.rigidNames sc ps C proc tn)))) o
  /-- A structured body, skolemized, checks in the body scope with every rigid type variable
      fixed, and the returned body is the deskolemized result. -/
  bodyStructured : ∀ ss o, proc.body = .structured ss o → ∃ ssOut EnvX,
    Statement.typeCheck
        (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn))
        (Function.formalsEnv Env (Procedure.rigidNames sc ps C proc tn) (bodySig proc'.header))
        p (some proc) (skolemizeStmts none (Procedure.rigidNames sc ps C proc tn) ss)
      = .ok (ssOut, EnvX) ∧
    (∀ v ∈ (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn)).rigidTypeVars,
      LMonoTy.subst EnvX.stateSubstInfo.subst (.ftvar v) = .ftvar v) ∧
    proc'.body = .structured
      (mapStmtsTys (deskolemizeTy (Procedure.rigidNames sc ps C proc tn)) ssOut) o
  /-- An abstract body is returned abstract. -/
  bodyAbstract : proc.body = .abstract → proc'.body = .abstract

/-- Skipping skolemization of a control-flow graph when `σ` is empty agrees with skolemizing it. -/
private theorem cfg_skolemize_unless_isEmpty (σ : RigidNames) (c : DetCFG) :
    (if σ.isEmpty then c
      else DetCFG.mapCmdsGuards c (skolemizeCmd none σ) (skolemizeBody none σ)) =
      DetCFG.mapCmdsGuards c (skolemizeCmd none σ) (skolemizeBody none σ) := by
  refine ite_isEmpty_eq_of_nil fun hσ => ?_
  rw [hσ, DetCFG.mapCmdsGuards_id (skolemizeCmd_nil none) (skolemizeBody_nil none)]

/-- Skipping deskolemization of a control-flow graph when `σ` is empty agrees with
    deskolemizing it. -/
private theorem cfg_deskolemize_unless_isEmpty (σ : RigidNames) (c : DetCFG) :
    (if σ.isEmpty then c
      else DetCFG.mapCmdsGuards c (mapCmdTys (deskolemizeTy σ)) (mapExprTys (deskolemizeTy σ))) =
      DetCFG.mapCmdsGuards c (mapCmdTys (deskolemizeTy σ)) (mapExprTys (deskolemizeTy σ)) := by
  refine ite_isEmpty_eq_of_nil fun hσ => ?_
  rw [hσ, funext deskolemizeTy_nil]
  exact (DetCFG.mapCmdsGuards_id mapCmdTys_id (congrFun mapExprTys_id) c).symm

/-- Skipping skolemization of a statement list when `σ` is empty agrees with skolemizing it. -/
private theorem stmts_skolemize_unless_isEmpty (σ : RigidNames) (ss : List Statement) :
    (if σ.isEmpty then ss else skolemizeStmts none σ ss) = skolemizeStmts none σ ss := by
  refine ite_isEmpty_eq_of_nil fun hσ => ?_
  rw [hσ, skolemizeStmts_nil]

/-- Skipping deskolemization of a statement list when `σ` is empty agrees with deskolemizing
    it. -/
private theorem stmts_deskolemize_unless_isEmpty (σ : RigidNames) (ss : List Statement) :
    (if σ.isEmpty then ss else mapStmtsTys (deskolemizeTy σ) ss) =
      mapStmtsTys (deskolemizeTy σ) ss := by
  refine ite_isEmpty_eq_of_nil fun hσ => ?_
  rw [hσ, funext deskolemizeTy_nil]
  exact (mapStmtsTys_id ss).symm

/-- A successful procedure check returns the incoming environment and yields a `CheckRun` for
    some resolved input and output types. -/
private theorem Procedure.typeCheckCore_ok_inv
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {p : Program}
    {proc proc' : Procedure} {md : MetaData Expression}
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    Env' = Env ∧ ∃ insR outsR, Procedure.CheckRun sc ps tn C Env p proc md proc' insR outsR := by
  have hfresh := Procedure.typeCheckCore_oldNamesFresh h
  unfold Procedure.typeCheckCore at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  elim_err h with hinNd
  elim_err h with houtNd
  elim_err h
  elim_err h with vIn hInMap
  obtain ⟨insR, EnvA⟩ := vIn
  obtain ⟨hEA, hInsRes, hIns⟩ := resolveKnownTys_ok_inv C _
    proc.header.inputs.values Env EnvA insR (Except.mapError_ok_h' hInMap)
  subst EnvA
  elim_err h with vOut hOutMap
  obtain ⟨outsR, EnvB⟩ := vOut
  obtain ⟨hEB, hOutsRes, hOuts⟩ := resolveKnownTys_ok_inv C _
    proc.header.outputs.values Env EnvB outsR (Except.mapError_ok_h' hOutMap)
  subst EnvB
  elim_err h with hmod
  elim_err h with preconds' hPre
  elim_err h with postconds' hPost
  have hbody : ∃ body' : Procedure.Body,
      (∀ c o, proc.body = .cfg c o → ∃ loc cOut EnvX,
        CFG.typeCheck (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn))
            (Function.formalsEnv Env (Procedure.rigidNames sc ps C proc tn)
              (bodySig { proc.header with inputs := proc.header.inputs.keys.zip insR,
                                          outputs := proc.header.outputs.keys.zip outsR }))
            p proc
            (DetCFG.mapCmdsGuards c (skolemizeCmd none (Procedure.rigidNames sc ps C proc tn))
              (skolemizeBody none (Procedure.rigidNames sc ps C proc tn))) loc = .ok (cOut, EnvX) ∧
        body' = .cfg (DetCFG.mapCmdsGuards cOut
          (mapCmdTys (deskolemizeTy (Procedure.rigidNames sc ps C proc tn)))
          (mapExprTys (deskolemizeTy (Procedure.rigidNames sc ps C proc tn)))) o) ∧
      (∀ ss o, proc.body = .structured ss o → ∃ ssOut EnvX,
        Statement.typeCheck
            (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn))
            (Function.formalsEnv Env (Procedure.rigidNames sc ps C proc tn)
              (bodySig { proc.header with inputs := proc.header.inputs.keys.zip insR,
                                          outputs := proc.header.outputs.keys.zip outsR }))
            p (some proc) (skolemizeStmts none (Procedure.rigidNames sc ps C proc tn) ss)
          = .ok (ssOut, EnvX) ∧
        (∀ v ∈ (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn)).rigidTypeVars,
          LMonoTy.subst EnvX.stateSubstInfo.subst (.ftvar v) = .ftvar v) ∧
        body' = .structured
          (mapStmtsTys (deskolemizeTy (Procedure.rigidNames sc ps C proc tn)) ssOut) o) ∧
      Procedure.checkDeclTyVarsBound proc.header.name md proc.header.typeArgs body' = .ok () ∧
      (proc.body = .abstract → body' = .abstract) ∧
      ({ proc with
          header :=
            { proc.header with inputs := proc.header.inputs.keys.zip insR,
                               outputs := proc.header.outputs.keys.zip outsR },
          spec := { preconditions := preconds', postconditions := postconds' },
          body := body' }, Env) = (proc', Env') := by
    split_ns at h
    · rename_i c o hc
      elim_err h with vC hC
      obtain ⟨cOut, EnvX⟩ := vC
      elim_err h
      elim_err h with hchk
      refine ⟨_, fun c' o' hc' => ?_, fun ss o' hss => ?_, hchk, fun ha => ?_, Except.ok.inj h⟩
      · rw [hc] at hc'
        cases hc'
        have hC' := Except.mapError_ok_h' hC
        rw [cfg_skolemize_unless_isEmpty] at hC'
        exact ⟨_, cOut, EnvX, hC', congrArg (Procedure.Body.cfg · o)
          (cfg_deskolemize_unless_isEmpty _ _)⟩
      · rw [hc] at hss
        cases hss
      · rw [hc] at ha
        cases ha
    · rename_i ss o hss
      elim_err h with vB hBMap
      obtain ⟨ssOut, EnvX⟩ := vB
      elim_err h with hrig
      elim_err h with hchk
      refine ⟨_, fun c o' hc => ?_, fun ss' o' hss' => ?_, hchk, fun ha => ?_, Except.ok.inj h⟩
      · rw [hss] at hc
        cases hc
      · rw [hss] at hss'
        cases hss'
        have hB := Except.mapError_ok_h' hBMap
        rw [stmts_skolemize_unless_isEmpty] at hB
        exact ⟨ssOut, EnvX, hB,
          (Procedure.ambientRigidVarsFixed_iff _ _).mp
            (Procedure.ensureAmbientRigidVarsFixed_ok _ _ _ hrig),
          congrArg (Procedure.Body.structured · o) (stmts_deskolemize_unless_isEmpty _ _)⟩
      · rw [hss] at ha
        cases ha
    · rename_i ha
      elim_err h with hchk
      refine ⟨_, fun c o hc => ?_, fun ss o hss => ?_, hchk, fun _ => rfl, Except.ok.inj h⟩
      · rw [ha] at hc
        cases hc
      · rw [ha] at hss
        cases hss
  obtain ⟨body', hbodyCfg, hbodyStructured, hbodyChk, hbodyAbstract, hret⟩ := hbody
  simp only [Prod.mk.injEq] at hret
  obtain ⟨rfl, rfl⟩ := hret
  have hpreRun := Procedure.conditionsMapM_ok
    (f := Procedure.checkCondition (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn))
      (Function.formalsEnv Env (Procedure.rigidNames sc ps C proc tn)
        (proc.header.inputs.keys.zip insR))
      proc.header.name (Procedure.rigidNames sc ps C proc tn)) ?gPre hPre
  have hpostRun := Procedure.conditionsMapM_ok
    (f := Procedure.checkCondition (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn))
      (Function.formalsEnv Env (Procedure.rigidNames sc ps C proc tn)
        (bodySig { proc.header with inputs := proc.header.inputs.keys.zip insR,
                                    outputs := proc.header.outputs.keys.zip outsR }))
      proc.header.name (Procedure.rigidNames sc ps C proc tn)) ?gPost hPost
  rotate_left
  all_goals
    try
      intro q r hq
      elim_err hq with chk' hcc
      exact ⟨chk', hcc, (Except.ok.inj hq).symm⟩
  obtain ⟨hpreChecked, hpreStored⟩ := hpreRun
  obtain ⟨hpostChecked, hpostStored⟩ := hpostRun
  refine ⟨rfl, insR, outsR,
    { inputsNodup := by simpa using hinNd
      outputsNodup := by simpa using houtNd
      oldNamesFresh := hfresh
      insKnown := hIns.imp fun _ _ hr => hr.2.2
      outsKnown := hOuts.imp fun _ _ hr => hr.2.2
      insResolve := hInsRes
      outsResolve := hOutsRes
      modRights := ?_
      header := rfl
      preconditionsChecked := hpreChecked
      preconditionsStored := hpreStored
      postconditionsChecked := hpostChecked
      postconditionsStored := hpostStored
      preconditionsRel := (mapM_except_rel₂ _ _ _ hPre).imp ?preRel
      postconditionsRel := (mapM_except_rel₂ _ _ _ hPost).imp ?postRel
      declTyVarsBound := hbodyChk
      bodyCfg := hbodyCfg
      bodyStructured := hbodyStructured
      bodyAbstract := hbodyAbstract }⟩
  case preRel =>
    intro a b hab
    elim_err hab with chk' hcc
    obtain rfl := (Except.ok.inj hab).symm
    exact ⟨rfl, hcc⟩
  case postRel =>
    intro a b hab
    elim_err hab with chk' hcc
    obtain rfl := (Except.ok.inj hab).symm
    exact ⟨rfl, hcc⟩
  · intro v hv
    have hc := forIn_guard_all _ _ (HasVarsImp.modifiedVars proc.body) PUnit.unit _ hmod v hv
    rw [List.contains_eq_mem, decide_eq_true_eq, List.mem_append] at hc
    rw [List.mem_append]
    rcases hc with hc | hc
    · left
      rw [ListMap.keys_eq_map_fst (List.zip _ _), List.mem_map] at hc
      obtain ⟨pp, hpp, hpp2⟩ := hc
      exact hpp2 ▸ (List.of_mem_zip hpp).1
    · exact Or.inr hc

/-- The CFG that `CFG.typeCheck` returns erases to the erasure of its source: the checker only
    adds type annotations to the commands and branch guards, and keeps the entry, the labels, the
    targets and the metadata. -/
theorem CFG.typeCheck_eraseAnnots_eq {C : Expression.TyContext} {Env : Expression.TyEnv}
    {P : Program} {proc : Procedure} {cfg : DetCFG} {sourceLoc : Strata.FileRange}
    {res : DetCFG × Expression.TyEnv}
    (hrun : CFG.typeCheck C Env P proc cfg sourceLoc = .ok res) :
    DetCFG.eraseAnnots res.1 = DetCFG.eraseAnnots cfg := by
  have hrel : DetCFG.BlocksRel (fun x y => Command.eraseAnnots y = Command.eraseAnnots x)
      (fun p q => q.eraseTypes = p.eraseTypes) cfg res.1 :=
    CFG.typeCheck_blocksRel_aliases _ _
      (fun _ _ _ _ _ hc => Statement.typeCheckCmd_eraseAnnots_eq _ _ _ _ _ _ hc)
      (fun _ y S hq => (Command.eraseAnnots_subst S y).trans hq)
      (fun _ _ _ _ hr => SourceExpr.resolve_unresolved_eraseTypes _ _ _ _ _ hr)
      (fun _ q S hq => (LExpr.eraseTypes_applyTypeSubst q S).trans hq) hrun
  unfold DetCFG.eraseAnnots
  exact DetCFG.mapCmdsGuards_eq_of_blocksRel _ _ (fun _ _ hxy => hxy) (fun _ _ hxy => hxy) hrel

/-- A CFG body that `Procedure.typeCheckCore` accepts comes back as a CFG whose blocks match the
    source's one to one: each returned command modifies and defines the variables of the source
    command at the same position, and each of its calls is well formed in the program. -/
private theorem Procedure.CheckRun.cfgCmdsRel {C : Expression.TyContext}
    {Env : Expression.TyEnv} {p : Program} {proc proc' : Procedure} {md : MetaData Expression}
    {insR outsR : LMonoTys}
    (run : Procedure.CheckRun sc ps tn C Env p proc md proc' insR outsR) {c : DetCFG} {o : Bool}
    (hb : proc.body = .cfg c o) :
    ∃ c', proc'.body = .cfg c' o ∧ DetCFG.CmdsRel (fun x y =>
      Command.modifiedVars y = Command.modifiedVars x ∧
      Command.definedVars y = Command.definedVars x ∧
      ∀ cs ∈ Command.callSites y, WF.WFcallProp p cs.procName cs.args) c c' := by
  obtain ⟨loc, cOut, EnvX, hrun, hout⟩ := run.bodyCfg c o hb
  refine ⟨_, hout, ?_⟩
  have hchecked := CFG.typeCheck_cmdsRel (fun x y =>
      Command.modifiedVars y = Command.modifiedVars x ∧
      Command.definedVars y = Command.definedVars x ∧
      ∀ cs ∈ Command.callSites y, WF.WFcallProp p cs.procName cs.args) ?hQ ?hsubst hrun
  case hQ =>
    intro E E' x y hc
    obtain ⟨hm, hd⟩ := Statement.typeCheckCmd_vars_eq _ _ _ _ _ _ hc
    exact ⟨hm, hd, Statement.typeCheckCmd_callsWellFormed _ _ _ _ _ _ hc⟩
  case hsubst =>
    intro x y S hq
    exact ⟨(Command.modifiedVars_subst S y).trans hq.1,
      (Command.definedVars_subst S y).trans hq.2.1,
      Command.callsWellFormed_mapInput _ (fun t => t.map (·.map (LTy.subst S)))
        (Command.callSites_subst S y) hq.2.2⟩
  have hsk := DetCFG.cmdsRel_mapCmdsGuards c
    (skolemizeCmd none (Procedure.rigidNames sc ps C proc tn))
    (skolemizeBody none (Procedure.rigidNames sc ps C proc tn))
  have hdesk := DetCFG.cmdsRel_mapCmdsGuards cOut
    (mapCmdTys (deskolemizeTy (Procedure.rigidNames sc ps C proc tn)))
    (mapExprTys (deskolemizeTy (Procedure.rigidNames sc ps C proc tn)))
  refine DetCFG.CmdsRel.imp ?_ (DetCFG.CmdsRel.comp (DetCFG.CmdsRel.comp hsk hchecked) hdesk)
  rintro x w ⟨z, ⟨y, rfl, hq⟩, rfl⟩
  refine ⟨?_, ?_, Command.callsWellFormed_mapInput _
    (fun t => t.map (·.map (mapLTyTys (deskolemizeTy (Procedure.rigidNames sc ps C proc tn)))))
    (Command.callSites_mapCmdTys _ z) hq.2.2⟩
  · rw [Command.modifiedVars_mapCmdTys, hq.1, Command.modifiedVars_skolemizeCmd]
  · rw [Command.definedVars_mapCmdTys, hq.2.1, Command.definedVars_skolemizeCmd]

/-- A successful condition check: its annotations' type variables are among the parameters named
    in `σ`, its skolemized form resolves at `bool` to `et` fixing the ambient rigid variables,
    and the stored condition is `et` with the final substitution applied and deskolemized. -/
private theorem Procedure.checkCondition_ok_inv
    {C : Expression.TyContext} {Env : Expression.TyEnv} {nm : CoreIdent} {σ : RigidNames}
    {label : CoreLabel} {chk chk' : Procedure.Check}
    (h : Procedure.checkCondition C Env nm σ label chk = .ok chk') :
    ∃ et EnvR,
      resolveWithType C Env (skolemizeBody none σ chk.expr) LMonoTy.bool = .ok (et, EnvR) ∧
      Procedure.ambientRigidVarsFixed C.rigidTypeVars EnvR.stateSubstInfo.subst = true ∧
      chk' = { chk with
        expr := finishDeskolemized σ EnvR.stateSubstInfo.subst et } ∧
      WrittenTyVarScope.unboundAnnotVar? false (σ.map Prod.fst) [] chk.expr = none := by
  unfold Procedure.checkCondition at h
  simp only [bind, Except.bind] at h
  elim_err h with r hprop
  obtain ⟨expr, stored, EnvR⟩ := r
  by_cases hfix : Procedure.ambientRigidVarsFixed C.rigidTypeVars EnvR.stateSubstInfo.subst = true
  · obtain ⟨et, hscope, hres, rfl, -⟩ :=
      Function.checkBoolProp_ok_inv (Except.mapError_ok_h' hprop)
    simp only [hfix, ite_true] at h
    exact ⟨et, EnvR, hres, hfix, (Except.ok.inj h).symm, hscope⟩
  · simp only [hfix] at h
    contradiction

/-- The header a successful procedure check returns keeps the declared name, type parameters and
    parameter names, and its parameter types are the resolved ones. -/
private theorem Procedure.CheckRun.signature
    {C : Expression.TyContext} {Env : Expression.TyEnv} {p : Program}
    {proc proc' : Procedure} {md : MetaData Expression}
    {insR outsR : LMonoTys}
    (run : Procedure.CheckRun sc ps tn C Env p proc md proc' insR outsR) :
    proc'.header.inputs.keys = proc.header.inputs.keys ∧
      proc'.header.outputs.keys = proc.header.outputs.keys ∧
      proc'.header.inputs.values = insR ∧ proc'.header.outputs.values = outsR ∧
      proc'.header.name = proc.header.name ∧ proc'.header.typeArgs = proc.header.typeArgs := by
  obtain ⟨hik, hiv⟩ := listMap_keys_zip_values proc.header.inputs insR
    (List.Rel₂.length_eq run.insKnown)
  obtain ⟨hok, hov⟩ := listMap_keys_zip_values proc.header.outputs outsR
    (List.Rel₂.length_eq run.outsKnown)
  rw [run.header]
  exact ⟨hik, hok, hiv, hov, rfl, rfl⟩

/-- The parameter types a successful procedure check returns are pointwise alias-equivalent to the
    declared ones. -/
private theorem Procedure.CheckRun.aliasEquiv
    {C : Expression.TyContext} {Env : Expression.TyEnv} {p : Program}
    {proc proc' : Procedure} {md : MetaData Expression}
    {insR outsR : LMonoTys}
    (run : Procedure.CheckRun sc ps tn C Env p proc md proc' insR outsR) :
    AliasEquivList Env.context.aliases proc.header.inputs.values proc'.header.inputs.values ∧
      AliasEquivList Env.context.aliases proc.header.outputs.values
        proc'.header.outputs.values := by
  obtain ⟨-, -, hiv, hov, -⟩ := run.signature
  rw [hiv, hov]
  have hins := LMonoTys.resolveAliases_sourceTysResolve (T := CoreLParams) _ Env _ Env
    run.insResolve
  have houts := LMonoTys.resolveAliases_sourceTysResolve (T := CoreLParams) _ Env _ Env
    run.outsResolve
  exact ⟨hins.aliasEquiv, houts.aliasEquiv⟩

/-! ### Variables of the elaborated body -/

/-- `Procedure.typeCheckCore` preserves the body's modified and defined variables. -/
private theorem Procedure.typeCheckCore_body_vars_eq
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    HasVarsImp.modifiedVars (P := Expression) proc'.body =
        HasVarsImp.modifiedVars (P := Expression) proc.body ∧
    ∀ b, HasVarsImp.definedVars (P := Expression) proc'.body b =
        HasVarsImp.definedVars (P := Expression) proc.body b := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  cases hb : proc.body with
  | cfg c o =>
    obtain ⟨c', hc', hrel⟩ := run.cfgCmdsRel hb
    rw [hc']
    exact ⟨DetCFG.CmdsRel.flatMap_eq _ (fun _ _ hq => hq.1) hrel,
      fun _ => DetCFG.CmdsRel.flatMap_eq _ (fun _ _ hq => hq.2.1) hrel⟩
  | abstract =>
    rw [run.bodyAbstract hb]
    exact ⟨rfl, fun _ => rfl⟩
  | structured ss o =>
    obtain ⟨ssOut, EnvX, hr, -, hbody'⟩ := run.bodyStructured ss o hb
    obtain ⟨hm, hd⟩ := Statement.typeCheck_vars_eq _ _ _ _ _ _ _ hr
    rw [hbody']
    refine ⟨?_, ?_⟩
    · show Block.modifiedVars _ = Block.modifiedVars _
      rw [mapStmtsTys_modifiedVars, hm, skolemizeStmts_modifiedVars]
    · intro b
      show Block.definedVars _ _ = Block.definedVars _ _
      rw [mapStmtsTys_definedVars, hd b, skolemizeStmts_definedVars]

/-! ### Signature and environment returned by `Procedure.typeCheckCore` -/

/-- The returned signature has no free type variable that the declared signature lacks. -/
private theorem Procedure.typeCheckCore_signatureFreeVars_subset
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    ∀ v, v ∈ LMonoTys.freeVars proc'.header.inputs.values ++
            LMonoTys.freeVars proc'.header.outputs.values →
        v ∈ LMonoTys.freeVars proc.header.inputs.values ++
            LMonoTys.freeVars proc.header.outputs.values := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  obtain ⟨hins, houts⟩ := run.aliasEquiv
  intro v hv
  rw [List.mem_append] at hv ⊢
  rcases hv with hvi | hvo
  · exact Or.inl ((AliasEquivList.freeVars_iff h_aw.mem hins v).mpr hvi)
  · exact Or.inr ((AliasEquivList.freeVars_iff h_aw.mem houts v).mpr hvo)

/-- `Procedure.typeCheckCore` preserves output parameter names. -/
private theorem Procedure.typeCheckCore_outputsKeys_eq
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    proc'.header.outputs.keys = proc.header.outputs.keys := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  exact run.signature.2.1

/-- `Procedure.typeCheckCore` preserves input parameter names. -/
private theorem Procedure.typeCheckCore_inputsKeys_eq
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    proc'.header.inputs.keys = proc.header.inputs.keys := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  exact run.signature.1

/-- `Procedure.typeCheckCore` preserves the procedure's declared type parameters. -/
private theorem Procedure.typeCheckCore_typeArgs_eq
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    proc'.header.typeArgs = proc.header.typeArgs := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  exact run.signature.2.2.2.2.2

/-- The returned parameter types are the alias resolutions of the declared ones, both at the
    incoming environment. -/
private theorem Procedure.typeCheckCore_resolveAliases
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    LMonoTys.resolveAliases proc.header.inputs.values Env
        = .ok (proc'.header.inputs.values, Env) ∧
      LMonoTys.resolveAliases proc.header.outputs.values Env
        = .ok (proc'.header.outputs.values, Env) := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  obtain ⟨-, -, hiv, hov, -⟩ := run.signature
  rw [hiv, hov]
  exact ⟨run.insResolve, run.outsResolve⟩

/-- The returned procedure has the declared parameter names, with the declared parameter types
    alias-resolved against the incoming scope. -/
private theorem Procedure.typeCheckCore_sigResolved
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    ProcSigResolved Env.context.aliases proc proc' := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  obtain ⟨hik, hok, -⟩ := run.signature
  obtain ⟨hins, houts⟩ := Procedure.typeCheckCore_resolveAliases C Env Env' p proc proc' md h
  have hres : Env.context.resolveTy
      = ({ aliases := Env.context.aliases } : TContext Unit).resolveTy :=
    TContext.resolveTy_congr (T := CoreLParams) rfl
  refine ⟨(Procedure.typeCheckCore_typeArgs_eq C Env Env' p proc proc' md h).symm, hik.symm,
    hok.symm, ?_, ?_⟩
  · rw [← hres]
    exact TContext.resolveTys_of_resolveAliases (T := CoreLParams) hins
  · rw [← hres]
    exact TContext.resolveTys_of_resolveAliases (T := CoreLParams) houts

/-- `Procedure.typeCheckCore` returns a signature with the same parameter names and pointwise
    alias-equivalent parameter types. -/
private theorem Procedure.typeCheckCore_sigAgree
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    ProcSigAgree Env.context.aliases proc proc' :=
  (Procedure.typeCheckCore_sigResolved C Env Env' p proc proc' md h).sigAgree

/-- On success, `Procedure.typeCheckCore` returns the incoming environment and keeps the procedure
    name. -/
private theorem Procedure.typeCheckCore_env_eq_and_name_eq
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    Env' = Env ∧ proc'.header.name = proc.header.name := by
  obtain ⟨henv, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  exact ⟨henv, run.signature.2.2.2.2.1⟩

/-- `callError?` accepts, against the program the procedure is checked in, every call of a CFG
    body the procedure checker returns. -/
private theorem Procedure.typeCheckCore_cfgCallsChecked
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {p : Program}
    {proc proc' : Procedure} {md : MetaData Expression} {g : DetCFG} {o : Bool}
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hg : proc'.body = .cfg g o) :
    ∀ cs ∈ proc'.callSites, callError? p cs.procName cs.args = none := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  cases hb : proc.body with
  | cfg c o =>
    obtain ⟨c', hc', hrel⟩ := run.cfgCmdsRel hb
    intro cs hcs
    rw [Procedure.callSites, hc'] at hcs
    obtain ⟨⟨lbl, blk⟩, hlb, hcs⟩ := List.mem_flatMap.mp hcs
    obtain ⟨y, hy, hcs⟩ := List.mem_flatMap.mp hcs
    obtain ⟨x, hq⟩ := DetCFG.CmdsRel.exists_of_mem hrel hlb hy
    exact (callError?_eq_none_iff _ _ _).mpr (hq.2.2 cs hcs)
  | structured ss o =>
    obtain ⟨_, _, _, _, hout⟩ := run.bodyStructured ss o hb
    rw [hout] at hg
    cases hg
  | abstract =>
    rw [run.bodyAbstract hb] at hg
    cases hg

/-- Checking a procedure keeps a registered substitution range registered. -/
private theorem Procedure.typeCheckCore_RangeKnown
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression) (ks : Lambda.KnownTypes)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hS : Lambda.Subst.RangeKnown Env.stateSubstInfo.subst ks) :
    Lambda.Subst.RangeKnown Env'.stateSubstInfo.subst ks := by
  rw [(Procedure.typeCheckCore_env_eq_and_name_eq C Env Env' p proc proc' md h).1]
  exact hS

/-! ### Signature checks an accepted source procedure passes -/

/-- If `Procedure.typeCheckCore` succeeds, the procedure's input parameter names are distinct. -/
private theorem Procedure.typeCheckCore_inputsNodup
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    proc.header.inputs.keys.Nodup := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  exact run.inputsNodup

/-- If `Procedure.typeCheckCore` succeeds, the procedure's output parameter names are distinct. -/
private theorem Procedure.typeCheckCore_outputsNodup
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    proc.header.outputs.keys.Nodup := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  exact run.outputsNodup

/-- When a procedure's type parameters are allowed names, every rigid name generated for it
    stands for a type parameter that the type-variable policy for user-written types admits. -/
private theorem Procedure.rigidNames_admissible (sc ps : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (proc : Procedure) (tn : Unit → List String)
    (hta : ∀ a ∈ proc.header.typeArgs, isAllowedName a = true) :
    ∀ q ∈ Procedure.rigidNames sc ps C proc tn,
      TyVarAdmissibility.notGeneratedOrRigid q.1 = true := by
  intro q hq
  have hmem := List.mem_map_of_mem (f := Prod.fst) hq
  rw [(Procedure.rigidNames_fresh _ _ _ _ _).2.2.2.1] at hmem
  exact TyVarAdmissibility.notGeneratedOrRigid_of_isAllowedName (hta _ hmem)

/-! ### Type variables of the returned signature -/

/-- If `Procedure.typeCheckCore` succeeds on a procedure whose declared signature uses only its
    type parameters, and the aliases are well formed, every type variable of the returned
    signature is a type argument. -/
private theorem Procedure.typeCheckCore_noUndeclaredVars
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hdecl : proc.header.SigDeclared) (h_aw : TContext.AliasesWF Env.context) :
    ∀ v, v ∈ LMonoTys.freeVars proc'.header.inputs.values ++
            LMonoTys.freeVars proc'.header.outputs.values →
        v ∈ proc'.header.typeArgs := by
  intro v hv
  have hsub :=
    Procedure.typeCheckCore_signatureFreeVars_subset C Env Env' p proc proc' md h h_aw v hv
  have hin := hdecl v hsub
  rw [Procedure.typeCheckCore_typeArgs_eq C Env Env' p proc proc' md h]
  exact hin

/-- If `Procedure.typeCheckCore` succeeds on a procedure whose declared signature uses only its
    type parameters, and the aliases are well formed, every type variable of the returned
    signature has a rigid name. -/
private theorem Procedure.typeCheckCore_signatureFreeVars_rigid
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hdecl : proc.header.SigDeclared)
    (h_aw : TContext.AliasesWF Env.context) :
    ∀ v, v ∈ LMonoTys.freeVars proc'.header.inputs.values ++
            LMonoTys.freeVars proc'.header.outputs.values →
        v ∈ (Procedure.rigidNames sc ps C proc tn).map Prod.fst := by
  rw [(Procedure.rigidNames_fresh _ _ _ _ _).2.2.2.1, ← Procedure.typeCheckCore_typeArgs_eq C Env
      Env' p proc proc' md h]
  exact Procedure.typeCheckCore_noUndeclaredVars C Env Env' p proc proc' md h hdecl h_aw

/-! ### Variables the body may modify -/

/-- If `Procedure.typeCheckCore` succeeds, every variable the input body modifies is an output
    parameter or a variable the body defines. -/
private theorem Procedure.typeCheckCore_modRights_input
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    ∀ v, v ∈ HasVarsImp.modifiedVars (P := Expression) proc.body →
        v ∈ proc.header.outputs.keys ++
            HasVarsImp.definedVars (P := Expression) proc.body false := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  exact run.modRights

/-- If `Procedure.typeCheckCore` succeeds, every variable the elaborated body modifies is an output
    parameter or a variable the body defines. -/
private theorem Procedure.typeCheckCore_modRights_output
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    ∀ v, v ∈ HasVarsImp.modifiedVars (P := Expression) proc'.body →
        v ∈ proc'.header.outputs.keys ++
            HasVarsImp.definedVars (P := Expression) proc'.body false := by
  intro v hv
  obtain ⟨hmod, hdef⟩ := Procedure.typeCheckCore_body_vars_eq C Env Env' p proc proc' md h
  have hkeys := Procedure.typeCheckCore_outputsKeys_eq C Env Env' p proc proc' md h
  rw [hmod] at hv
  rw [hkeys, hdef]
  exact Procedure.typeCheckCore_modRights_input C Env Env' p proc proc' md h v hv

/-! ### Condition typing in the skolemized parameter scope -/

/-- The scope stack of the skolemized parameter-scope environment is nonempty. -/
private theorem skolemScopeEnv_types_ne (σ : RigidNames) (Env : Expression.TyEnv)
    (sig : @LMonoTySignature Unit) :
    (Function.formalsEnv Env σ sig).context.types ≠ [] := by
  rw [formalsEnv_types]
  exact List.cons_ne_nil _ _

/-- A successful `checkCondition` in a closed skolemized scope gives an annotated `bool` judgment
    for the returned condition, with registered binder annotations, when `C` registers no rigid
    constant. -/
private theorem Procedure.checkCondition_output
    (C : Expression.TyContext) (Env : Expression.TyEnv) (nm : CoreIdent)
    (σ : RigidNames) (scope : HMap CoreIdent LTy) (label : CoreLabel)
    (hpfx : RigidNamesPrefixed σ)
    (chk chk' : Procedure.Check)
    (h : Procedure.checkCondition (addSkolemTypes C σ)
            ((Env.pushEmptyContext).addInNewestContext (T := CoreLParams) scope)
            nm σ label chk = .ok chk')
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_scope : ∀ ty ∈ scope.values, LTy.freeVars ty = [] ∧ LTy.boundVars ty = [])
    (h_fresh : RigidNamesFresh C.knownTypes σ)
    (h_arrow : C.knownTypes["arrow"]? = some 2)
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty C.knownTypes = true)
    (h_substRange : Lambda.Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes)
    (h_lits : ConstTysFixed σ chk.expr) :
    LExpr.HasTypeA (T := CoreLParams) [] chk'.expr LMonoTy.bool ∧
      BinderAnnotsKnown C chk'.expr := by
  obtain ⟨et, EnvR, hres, -, rfl, -⟩ := Procedure.checkCondition_ok_inv h
  have hwf : LExpr.TEnvWF (T := CoreLParams)
      ((Env.pushEmptyContext).addInNewestContext (T := CoreLParams) scope) :=
    pushEmptyContext_addInNewestContext_preserves_TEnvWF (T := CoreLParams) Env scope h_env h_scope
  have hares : TContext.AliasesResolved
      ((Env.pushEmptyContext).addInNewestContext (T := CoreLParams) scope).context := by
    intro al hal
    exact h_resolved al hal
  have hfac' := FactorySigWF.addSkolemTypes C σ h_fac
  have hext := KnownTypesExtends_addSkolemTypes C h_fresh
  have hrefl := Subst.absorbs_refl _ EnvR.stateSubstInfo.isWF
  have hA := resolveWithType_HasTypeA_ground_absorbing (addSkolemTypes C σ) _ EnvR _ et
    LMonoTy.bool hres rfl hwf h_fac hares _ hrefl
  have hD := HasTypeA_replaceUserProvidedType_deskolemizeTy hpfx [] _ LMonoTy.bool
    (ConstTysFixed_resolveWithType (addSkolemTypes C σ) _ EnvR (skolemizeBody none σ chk.expr) et
      LMonoTy.bool hres _ (ConstTysFixed_skolemizeBody none h_lits)) hA
  have hrange0 : Lambda.Subst.RangeKnown
      ((Env.pushEmptyContext).addInNewestContext (T := CoreLParams) scope).stateSubstInfo.subst
      (addSkolemTypes C σ).knownTypes :=
    Subst.RangeKnown_mono _ _ _ hext h_substRange
  have hboolK : LMonoTy.knownInstance LMonoTy.bool (addSkolemTypes C σ).knownTypes = true :=
    knownInstance_mono _ _ _ hext (h_lit (.boolConst true) rfl)
  have hRK := resolveWithType_RangeKnown (addSkolemTypes C σ) _ EnvR _ et LMonoTy.bool hres hwf
    hfac' (hext "arrow" 2 h_arrow) (hext "bool" 0 (knownTypes_bool_of_literalTys h_lit))
    (fun c hp _ => knownInstance_mono _ _ _ hext (h_lit c hp)) hboolK hrange0
  have hk := resolveWithType_binderAnnotations_known_absorbing (addSkolemTypes C σ) _ EnvR _ et
    LMonoTy.bool hres hwf hfac' _ hrefl hRK
  refine ⟨?_, binderAnnotations_known_deskolemize (Csk := addSkolemTypes C σ) (Crig := C)
    (knownTypes_contains_of_getElem?_addSkolemTypes (fun _ => rfl)) _ hk⟩
  simpa only [List.map_nil, deskolemizeTy_bool hpfx] using hD

/-! ### The declarative body scope -/

/-- The procedure input context pushes the input declaration scope onto the ambient context. -/
private theorem procInputContext_eq (Γ : TContext Unit) (proc : Procedure) :
    procInputContext Γ proc
      = { Γ with types := Γ.types.push (formalsScope proc.header.inputs) } := by
  unfold procInputContext
  rfl

/-- The procedure body context pushes the formal declaration scope onto the ambient context. -/
private theorem procBodyContext_eq (Γ : TContext Unit) (proc : Procedure) :
    procBodyContext Γ proc
      = { Γ with types := Γ.types.push (formalsScope (bodySig proc.header)) } := by
  unfold bodySig procBodyContext procBodyScopes
  rfl

/-- A condition accepted under a resolved, skolemized signature has type `bool` in the declared
    parameter scope. -/
private theorem Procedure.checkCondition_HasType_bool
    (C : Expression.TyContext) (Env : Expression.TyEnv) (nm : CoreIdent)
    (σ : RigidNames) (sig sigR : @LMonoTySignature Unit) (label : CoreLabel)
    (hpfx : RigidNamesPrefixed σ) (hnd : (σ.map Prod.snd).Nodup)
    (chk chk' : Procedure.Check)
    (h : Procedure.checkCondition (addSkolemTypes C σ)
            (Function.formalsEnv Env σ sigR) nm σ label chk = .ok chk')
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_sigR_nud : ∀ v ∈ LMonoTys.freeVars sigR.values, v ∈ σ.map Prod.fst)
    (h_keys : sig.keys = sigR.keys)
    (h_vals : AliasEquivList Env.context.aliases sig.values sigR.values)
    (h_amb : NoSkolemAmbient C Env.context σ)
    (h_mono : MonoScope Env.context)
    (h_rt_sig : ∀ q ∈ ListMap.toList sigR,
        deskolemizeTy σ (skolemizeTy σ q.2) = q.2)
    (h_allowed : allExprTys (mtyAllTyConsNames (notRigidConst σ)) chk.expr = true)
    (h_lits : ConstTysFixed σ chk.expr) :
    LExpr.HasType (T := CoreLParams) C
      { Env.context with types := Env.context.types.push (formalsScope sig) }
      chk.expr (.forAll [] LMonoTy.bool) := by
  obtain ⟨et, EnvR, hres, -, -, -⟩ := Procedure.checkCondition_ok_inv h
  have h_ws := resolveWithType_WellScoped _ _ _ _ _ _ hres
  have hrtv : ∀ mty ∈ sigR.values, deskolemizeTy σ (skolemizeTy σ mty) = mty := by
    intro mty hm
    obtain ⟨k, hk⟩ := ListMap.mem_values _ mty hm
    exact h_rt_sig (k, mty) hk
  have hdesk := funcPosition_HasType C Env EnvR σ hpfx hnd none sigR chk.expr LMonoTy.bool et
    hres h_ws h_env h_closed h_fac h_amb h_mono h_sigR_nud hrtv h_allowed h_lits rfl
  rw [deskolemizeTy_bool hpfx] at hdesk
  exact LExpr.HasType_pushScope_aliasEquiv C Env.context sig sigR chk.expr LMonoTy.bool
    h_env.aliasesWF h_keys h_vals hdesk

/-! ### Deskolemizing the skolemized parameter scope -/

/-- The skolemized parameter scope deskolemizes to the declared scope when deskolemization
    fixes the ambient types and each declared parameter type round-trips. -/
private theorem skolemScope_deskolemizes (σ : RigidNames) (Env : Expression.TyEnv)
    (sig : @LMonoTySignature Unit)
    (h_ambient : ∀ z ty, Env.context.types.find? z = some ty →
        mapLTyTys (deskolemizeTy σ) ty = ty)
    (h_rt : ∀ mty ∈ sig.values, deskolemizeTy σ (skolemizeTy σ mty) = mty) :
    DeskolemizesScope σ
      (Function.formalsEnv Env σ sig).context
      { Env.context with types := Env.context.types.push (formalsScope sig) } := by
  have htys := formalsEnv_types Env σ sig
  have hal := formalsEnv_aliases Env σ sig
  refine ⟨by rw [hal], fun x => ?_⟩
  rw [htys]
  show HMaps.find? (formalsScope sig :: Env.context.types) x
      = (HMaps.find?
          ((skolemScope σ sig).union HMap.empty :: Env.context.types) x).map
            (mapLTyTys (deskolemizeTy σ))
  cases hd : (formalsScope sig).find? x with
  | none =>
    simp only [HMaps.find?, HMap.union_empty, find?_skolemScope, hd, Option.map_none]
    cases hamb : HMaps.find? Env.context.types x with
    | none => simp only [Option.map_none]
    | some ty => simp only [Option.map_some, h_ambient x ty hamb]
  | some t =>
    obtain ⟨mty, hmty, rfl⟩ := formalsScope_find?_mem sig x t hd
    have hrt : mapLTyTys (deskolemizeTy σ)
        (mapLTyTys (skolemizeTy σ) (LTy.forAll [] mty)) = LTy.forAll [] mty := by
      show LTy.forAll [] (deskolemizeTy σ (skolemizeTy σ mty)) = LTy.forAll [] mty
      rw [h_rt mty hmty]
    simp only [HMaps.find?, HMap.union_empty, find?_skolemScope, hd, Option.map_some, hrt]

/-! ### Signature side conditions of the body scope -/

/-- Every type the body scope binds a parameter at is a signature type of the header. -/
private theorem bodySig_values_subset (hdr : Procedure.Header) :
    ∀ mty ∈ (bodySig hdr).values, mty ∈ hdr.inputs.values ++ hdr.outputs.values := by
  intro mty hm
  unfold bodySig at hm
  rcases (ListMap.mem_values_append _ _ mty).mp hm with h12 | h3
  · rcases (ListMap.mem_values_append _ _ mty).mp h12 with h1 | h2
    · unfold oldInoutSig at h1
      have h1' := ListMap.mem_values_map_of_snd_eq
        (fun x => (CoreIdent.mkOld x.1.name, x.2)) (fun x => rfl) _ mty h1
      simp only [Procedure.Header.getInoutParams, Core.getInoutParams] at h1'
      exact List.mem_append_left _ (ListMap.mem_values_filter _ _ mty h1')
    · exact List.mem_append_right _ h2
  · exact List.mem_append_left _ h3

/-- The body scope's free type variables are in `σ` when the header parameters' are. -/
private theorem bodySig_freeVars_mem (hdr : Procedure.Header) (σ : RigidNames)
    (hnud : ∀ v, v ∈ LMonoTys.freeVars hdr.inputs.values ++
        LMonoTys.freeVars hdr.outputs.values → v ∈ σ.map Prod.fst) :
    ∀ v ∈ LMonoTys.freeVars (bodySig hdr).values, v ∈ σ.map Prod.fst := by
  intro v hv
  obtain ⟨mty, hmty, hvm⟩ := LMonoTys.freeVars_exists hv
  refine hnud v ?_
  rcases List.mem_append.mp (bodySig_values_subset hdr mty hmty) with hi | ho
  · exact List.mem_append_left _ (LMonoTys.freeVars_mem_subset hi hvm)
  · exact List.mem_append_right _ (LMonoTys.freeVars_mem_subset ho hvm)

/-! ### The body check binds no type mentioning a type parameter -/

/-- The body check of an accepted procedure ends with a substitution that binds no type
    mentioning a type parameter, when the incoming substitution mentions none and every
    procedure's signature type variables are its type parameters. -/
private theorem Procedure.typeCheckCore_bodyNoParamRange
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hdecl : proc.header.SigDeclared)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (hsigs : ProcSigsDeclared p)
    (hS : Subst.VarsAvoid Env.stateSubstInfo.subst proc.header.typeArgs)
    (hta : ∀ a ∈ proc.header.typeArgs, isAllowedName a = true)
    (ss : List Statement) (ssOut : List Statement) (EnvX : Expression.TyEnv)
    (hrun : Statement.typeCheck
        (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn))
        (Function.formalsEnv Env (Procedure.rigidNames sc ps C proc tn) (bodySig proc'.header))
        p (some proc) (skolemizeStmts none (Procedure.rigidNames sc ps C proc tn) ss)
      = .ok (ssOut, EnvX)) :
    NoParamRange (Procedure.rigidNames sc ps C proc tn) EnvX.stateSubstInfo.subst := by
  have hps : (Procedure.rigidNames sc ps C proc tn).map Prod.fst = proc.header.typeArgs :=
    (Procedure.rigidNames_fresh sc ps C proc tn).2.2.2.1
  have hsigFV := bodySig_freeVars_mem _ _
    (Procedure.typeCheckCore_signatureFreeVars_rigid C Env Env' p proc proc' md h hdecl
      h_env.aliasesWF)
  have hgen : NoGenName ((Procedure.rigidNames sc ps C proc tn).map Prod.fst) := by
    intro n hn
    rw [hps] at hn
    have hadm := TyVarAdmissibility.notGeneratedOrRigid_not_genTyPrefix
      (TyVarAdmissibility.notGeneratedOrRigid_of_isAllowedName (hta _ hn))
    have htrue : genTyPrefix.toList.isPrefixOf (TState.tyPrefix ++ toString n).toList = true := by
      rw [String.toList_append]
      exact isPrefixOf_append_self _ _
    rw [htrue] at hadm
    exact Bool.noConfusion hadm
  have hctx :
      TContext.VarsAvoid Env.context ((Procedure.rigidNames sc ps C proc tn).map Prod.fst) := by
    intro v hv _
    simp only [TContext.knownTypeVars, List.mem_flatMap] at hv
    obtain ⟨ty, hty, hvty⟩ := hv
    rw [(LExpr.checkContextTypesClosed_iff_values (T := CoreLParams) Env).mp h_closed ty hty]
      at hvty
    exact List.not_mem_nil hvty
  have hfacSk := FactorySigWF.addSkolemTypes C (Procedure.rigidNames sc ps C proc tn) h_fac
  refine fun v hv => Statement.typeCheck_varsAvoid _ _ EnvX p (some proc)
    _ ssOut hrun (formalsEnv_TEnvWF Env _ _ h_env hsigFV) (skolemScopeEnv_types_ne _ Env _)
    hfacSk hgen hsigs ?_
    (Statements.srcAvoid_skolemizeStmts _ ss) ?_ v (Or.inr hv)
  · intro x hx
    exact List.mem_append_right _ hx
  · refine TEnv.VarsAvoid.addInNewestContext (T := CoreLParams)
      (TEnv.VarsAvoid.pushEmptyContext (T := CoreLParams) ⟨hps ▸ hS, hctx⟩) _ ?_
    intro ty hty v hv
    rw [(skolemScope_closed _ _ hsigFV ty hty).1] at hv
    exact absurd hv List.not_mem_nil

/-- Headers with matching parameter names and pointwise alias-equivalent parameter types
    produce body scopes with the same keys and pointwise alias-equivalent values. -/
private theorem bodySig_agree (aliases : List TypeAlias) (hdr hdrR : Procedure.Header)
    (hkeysIn : hdr.inputs.keys = hdrR.inputs.keys)
    (hkeysOut : hdr.outputs.keys = hdrR.outputs.keys)
    (hvalsIn : AliasEquivList aliases hdr.inputs.values hdrR.inputs.values)
    (hvalsOut : AliasEquivList aliases hdr.outputs.values hdrR.outputs.values) :
    (bodySig hdr).keys = (bodySig hdrR).keys ∧
      AliasEquivList aliases (bodySig hdr).values (bodySig hdrR).values := by
  -- Pair names with types so the facts survive the in-out filter and the `old` renaming.
  have hpairIn : List.Rel₂ (fun (q qR : CoreIdent × LMonoTy) =>
      q.1 = qR.1 ∧ AliasEquiv aliases q.2 qR.2) hdr.inputs hdrR.inputs :=
    ListMap.forall₂_pair_of_keys_values _ _ hkeysIn hvalsIn.forall₂
  have hpairOut : List.Rel₂ (fun (q qR : CoreIdent × LMonoTy) =>
      q.1 = qR.1 ∧ AliasEquiv aliases q.2 qR.2) hdr.outputs hdrR.outputs :=
    ListMap.forall₂_pair_of_keys_values _ _ hkeysOut hvalsOut.forall₂
  have hpairInout : List.Rel₂ (fun (q qR : CoreIdent × LMonoTy) =>
      q.1 = qR.1 ∧ AliasEquiv aliases q.2 qR.2)
      hdr.getInoutParams hdrR.getInoutParams := by
    show List.Rel₂ _ (Core.getInoutParams hdr.inputs hdr.outputs)
      (Core.getInoutParams hdrR.inputs hdrR.outputs)
    unfold Core.getInoutParams
    rw [hkeysOut]
    exact ListMap.forall₂_pair_filter _ (fun id => (ListMap.keys hdrR.outputs).contains id)
      _ _ hpairIn
  have hpairOld : List.Rel₂ (fun (q qR : CoreIdent × LMonoTy) =>
      q.1 = qR.1 ∧ AliasEquiv aliases q.2 qR.2) (oldInoutSig hdr.getInoutParams.toList)
        (oldInoutSig hdrR.getInoutParams.toList) := by
    unfold oldInoutSig
    exact ListMap.forall₂_pair_mapKeys _ (fun (id : CoreIdent) => CoreIdent.mkOld id.name)
      _ _ hpairInout
  have hpairBody : List.Rel₂ (fun (q qR : CoreIdent × LMonoTy) =>
      q.1 = qR.1 ∧ AliasEquiv aliases q.2 qR.2) (bodySig hdr) (bodySig hdrR) := by
    unfold bodySig
    unfold instHAppendListMap
    exact List.Rel₂.append (List.Rel₂.append hpairOld hpairOut) hpairIn
  exact ⟨ListMap.keys_eq_of_forall₂_pair _ _ hpairBody,
    AliasEquivList.of_forall₂ (fun _ _ hr => hr)
      (ListMap.forall₂_values_of_forall₂_pair _ _ hpairBody)⟩

/-- Every parameter type of the returned procedure is an instance of registered types. -/
private theorem Procedure.typeCheckCore_paramTypes_knownInstance
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    ∀ mty ∈ proc'.header.inputs.values ++ proc'.header.outputs.values,
      LMonoTy.knownInstance mty C.knownTypes = true := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  obtain ⟨-, -, hiv, hov, -⟩ := run.signature
  intro mty hmem
  rw [hiv, hov] at hmem
  obtain ⟨_, _, hknown⟩ :=
    forall2_exists_left (List.Rel₂.append run.insKnown run.outsKnown) mty hmem
  exact hknown

/-- Every parameter type of the returned header is fixed by alias resolution in the ambient
    context, when no registered type is named like an alias. -/
private theorem Procedure.typeCheckCore_paramTypes_resolved
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (h_aliasNamesFresh : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false) :
    ∀ mty ∈ proc'.header.inputs.values ++ proc'.header.outputs.values,
      Env.context.resolveTy mty = mty := fun mty hm =>
  TContext.resolveTy_of_knownInstance (T := CoreLParams) h_aliasNamesFresh
    (Procedure.typeCheckCore_paramTypes_knownInstance C Env Env' p proc proc' md h mty hm)

/-- Deskolemization absorbs skolemization on every type the returned body scope binds a
    parameter at. -/
private theorem Procedure.typeCheckCore_bodySig_deskolemize_skolemize
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    ∀ mty ∈ (bodySig proc'.header).values,
      deskolemizeTy (Procedure.rigidNames sc ps C proc tn)
        (skolemizeTy (Procedure.rigidNames sc ps C proc tn) mty) = mty := by
  have hnd := (Procedure.rigidNames_fresh sc ps C proc tn).2.1
  intro mty hm
  rw [deskolemizeTy_skolemizeTy_eq_deskolemizeTy hnd]
  exact deskolemizeTy_eq_self_of_knownInstance C
    ((Procedure.rigidNames_fresh sc ps C proc tn).2.2.1) mty
    (Procedure.typeCheckCore_paramTypes_knownInstance C Env Env' p proc proc' md h mty
      (bodySig_values_subset _ mty hm))

/-- No unregistered alias name in scope is registered once a procedure's rigid constants are
    added. -/
private theorem Procedure.aliasNames_notContains_addSkolemTypes
    (sc ps : Thunk (Std.HashSet String)) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (proc : Procedure) (tn : Unit → List String) (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (h_aliasNamesFresh : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false) :
    ∀ al ∈ Env.context.aliases,
      (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn)).knownTypes.containsName al.name
        = false :=
  fun al hal => addSkolemTypes_notContains_of_ne C _ al.name
    ((Procedure.rigidNames_spec sc ps C Env proc tn hcov).aliasNames al hal)
    (h_aliasNamesFresh al hal)

/-- Deskolemizing by a procedure's rigid renaming fixes the signature of every procedure of the
    program a command calls. -/
private theorem Procedure.rigidNames_calledSigsFixed (sc ps : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (p : Program) (proc : Procedure) (tn : Unit → List String)
    (hP : ∀ n ∈ Program.procSigTyNames p, n ∈ ps.get) :
    ∀ c, CalledProcedureSignaturesFixed (Procedure.rigidNames sc ps C proc tn) p c := by
  intro _ pname _ q hf ty hty
  obtain ⟨md, hmem, -⟩ := Program.Procedure.find?_mem_decls p pname q hf
  exact deskolemizeTy_eq_self_of_notRigidConst ty (mtyAllTyConsNames_notRigidConst_of_not_mem
    fun r hr => Procedure.rigidNames_not_programSigs sc ps C p proc tn hP r hr q md hmem ty hty)

/-- Every body-scope parameter type, skolemized, resolves to itself against the ambient aliases
    when no alias name is a registered type of the skolemized table. -/
private theorem Procedure.typeCheckCore_bodySig_skolemize_resolved
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (h_aliasFresh : ∀ al ∈ Env.context.aliases,
      (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn)).knownTypes.containsName al.name
        = false) :
    ∀ mty ∈ (bodySig proc'.header).values,
      Env.context.resolveTy (skolemizeTy (Procedure.rigidNames sc ps C proc tn) mty)
        = skolemizeTy (Procedure.rigidNames sc ps C proc tn) mty := by
  intro mty hm
  exact TContext.resolveTy_of_knownInstance (T := CoreLParams) h_aliasFresh
    (knownInstance_skolemizeTy C ((Procedure.rigidNames_fresh sc ps C proc tn).2.2.1) mty
      (Procedure.typeCheckCore_paramTypes_knownInstance C Env Env' p proc proc' md h mty
        (bodySig_values_subset _ mty hm)))

/-! ### Body typing in the declarative body scope -/

/-- A statement typed by the typechecker spec preserves `DeskolAmbientScope Q σ` and keeps every
    type parameter of `σ` rigid. -/
private theorem DeskolAmbientScope.rigid_step
    {P : Program} {Q : Lambda.Factory CoreLParams → Prop} {σ : RigidNames}
    {C Cfin : LContext CoreLParams} {Γ Γfin : TContext Unit} {Δ Δfin : WrittenEnv}
    {L : List String} {s : Statement}
    (hs : StatementHasType P C Γ Δ L s Cfin Γfin Δfin)
    (hinv : DeskolAmbientScope Q σ C Γ ∧ ∀ q ∈ σ, q.1 ∈ C.rigidTypeVars) :
    DeskolAmbientScope Q σ Cfin Γfin ∧ ∀ q ∈ σ, q.1 ∈ Cfin.rigidTypeVars := by
  refine ⟨StatementHasType_DeskolAmbientScope hs hinv.1, ?_⟩
  intro q hq
  rw [StatementHasType.rigid_eq hs]
  exact hinv.2 q hq

/-- `DeskolAmbientScope` for well-formed factory signatures, with every type parameter of `σ`
    rigid. -/
private abbrev BodyDeskolInv (σ : RigidNames) (Cx : LContext CoreLParams) (Γx : TContext Unit) :
    Prop :=
  DeskolAmbientScope FactorySigWF σ Cx Γx ∧ ∀ q ∈ σ, q.1 ∈ Cx.rigidTypeVars

/-- A checked skolemized body is well typed against the alias-resolved procedures in its resolved,
    substituted scope, and its names are valid. -/
private theorem bodyTyped_skolemized
    (C : Expression.TyContext) (Env EnvX : Expression.TyEnv) (p : Program)
    (proc : Procedure) (σ : RigidNames) (sig : @LMonoTySignature Unit)
    (ssIn ssOut : List Statement)
    (hB : Statement.typeCheck (addSkolemTypes C σ)
            (Function.formalsEnv Env σ sig)
            p (some proc) (skolemizeStmts none σ ssIn) = .ok (ssOut, EnvX))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_mono : MonoScope (IDMeta := Unit) Env.context)
    (h_sigFreeVars : ∀ v ∈ LMonoTys.freeVars sig.values, v ∈ σ.map Prod.fst)
    (h_aliasFresh : ∀ al ∈ Env.context.aliases,
      (addSkolemTypes C σ).knownTypes.containsName al.name = false)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions) :
    (∃ C1 ts1, StatementsWellTyped (p.resolveSigs Env.context.aliases) (addSkolemTypes C σ)
        (TContext.subst (Function.formalsEnv Env σ sig).context.dealias
          EnvX.stateSubstInfo.subst).types [] ssOut C1 ts1) ∧
      StatementsNamesWF (p.resolveSigs Env.context.aliases) (· ∈ C.functions) ssOut := by
  have hwf := formalsEnv_TEnvWF Env σ sig h_env h_sigFreeVars
  have hares := formalsEnv_AliasesResolved Env σ sig h_resolved
  have hfac' := FactorySigWF.addSkolemTypes C σ h_fac
  have hal := formalsEnv_aliases Env σ sig
  have hfreshSk : ∀ al ∈ (Function.formalsEnv Env σ sig).context.aliases,
      (addSkolemTypes C σ).knownTypes.containsName al.name = false :=
    fun al hal' => h_aliasFresh al (hal ▸ hal')
  have hsigSk : FactorySigsFixed (Function.formalsEnv Env σ sig).context.aliases
      (addSkolemTypes C σ).functions := by
    rw [hal]
    simpa only [addSkolemTypes_functions] using h_sigsFixed
  have hwff := Statement.typeCheck_sound_output
      (addSkolemTypes C σ) _ EnvX p
      (some proc) _ ssOut hB hwf hfac' hares (skolemScopeEnv_types_ne σ Env sig)
      (formalsEnv_MonoScope Env σ sig h_mono) hfreshSk hsigSk
  rw [LContext.resolveTable_eq_self hsigSk, hal, addSkolemTypes_functions] at hwff
  exact hwff

/-- A checked skolemized body, deskolemized, is well typed against the alias-resolved procedures in
    the parameter scope over the resolved ambient scope with the parameters rigid, and its names
    are valid. -/
private theorem bodyTyped_output_core
    (C : Expression.TyContext) (Env EnvX : Expression.TyEnv) (p : Program)
    (proc : Procedure) (σ : RigidNames) (sig : @LMonoTySignature Unit)
    (hpfx : RigidNamesPrefixed σ)
    (ssIn ssOut : List Statement)
    (hB : Statement.typeCheck (addSkolemTypes C σ)
            (Function.formalsEnv Env σ sig)
            p (some proc) (skolemizeStmts none σ ssIn) = .ok (ssOut, EnvX))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_frel : FactorySigDeskolemizes σ C.functions C.functions)
    (h_fsafe : FactorySigDeskolSafe σ C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_aliasNoSkolem : AliasesNoSkolem σ Env.context.aliases)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope (IDMeta := Unit) Env.context)
    (h_known : AmbientTypesKnown C.knownTypes Env)
    (h_rt : ∀ mty ∈ sig.values, deskolemizeTy σ (skolemizeTy σ mty) = mty)
    (h_sigFreeVars : ∀ v ∈ LMonoTys.freeVars sig.values, v ∈ σ.map Prod.fst)
    (h_fresh : RigidNamesFresh C.knownTypes σ)
    (h_aliasFresh : ∀ al ∈ Env.context.aliases,
      (addSkolemTypes C σ).knownTypes.containsName al.name = false)
    (h_resSk : ∀ mty ∈ sig.values,
      Env.context.resolveTy (skolemizeTy σ mty) = skolemizeTy σ mty)
    (h_res : ∀ mty ∈ sig.values, Env.context.resolveTy mty = mty)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (hcalled : ∀ c, CalledProcedureSignaturesFixed σ p c)
    (h_litTys : ∀ p ∈ σ, p.2 ∉ stmtsLitTyNames ssIn) :
    (∃ Cout tsOut, StatementsWellTyped (p.resolveSigs Env.context.aliases)
        { C with rigidTypeVars := C.rigidTypeVars ++ σ.map Prod.fst }
        (Env.context.dealias.types.push (formalsScope sig)) []
        (mapStmtsTys (deskolemizeTy σ) ssOut) Cout tsOut) ∧
      StatementsNamesWF (p.resolveSigs Env.context.aliases) (· ∈ C.functions)
        (mapStmtsTys (deskolemizeTy σ) ssOut) := by
  obtain ⟨⟨C1, ts1, hj⟩, hnames⟩ := bodyTyped_skolemized C Env EnvX p proc σ sig ssIn ssOut hB
    h_env h_fac h_resolved h_mono h_sigFreeVars h_aliasFresh h_sigsFixed
  have hsc := formalsEnv_deskolemizes_substDeskolemizedAmbient σ EnvX.stateSubstInfo.subst Env
    sig [] h_sigFreeVars h_rt h_resSk
  have hsc' : DeskolemizesScope σ
      { types := (TContext.subst (Function.formalsEnv Env σ sig).context.dealias
          EnvX.stateSubstInfo.subst).types }
      { types := (substDeskolemizedAmbient σ EnvX.stateSubstInfo.subst Env.context).types.push
          (formalsScope sig) } :=
    ⟨rfl, hsc.2⟩
  have hlitOut : ∀ p ∈ σ, p.2 ∉ stmtsLitTyNames ssOut := by
    rw [Statement.typeCheck_litTyNames_eq _ _ _ p _ _ ssOut hB, stmtsLitTyNames_skolemizeStmts]
    exact h_litTys
  obtain ⟨Cout, tsOut, hd⟩ := TypeSpec.StatementsWellTyped.deskolemize σ hpfx
    (fun c => (hcalled c).resolveSigs h_aliasNoSkolem) C h_fac h_fsafe h_frel hj hsc' hlitOut
  have hEq := (formalsScope_push_dealias_FindEq Env.context sig h_res).symm.trans
    (substDeskolemizedAmbient_push_FindEq σ EnvX.stateSubstInfo.subst C Env sig
      h_env.aliasesWF h_closed h_mono h_known h_fresh h_res)
  obtain ⟨tsOut', hd', -⟩ := hd.of_findEq hEq.1
  exact ⟨⟨Cout, tsOut', hd'⟩, TypeSpec.StatementsNamesWF.mapStmtsTys _ _ hnames⟩

/-! ### Typing of pre- and postconditions -/

/-- Successful checking types each source precondition as `bool` in the input scope, when the
    input types survive the skolem round trip and no annotation names a rigid constant. -/
private theorem Procedure.typeCheckCore_preconditionsTyped_input_of_noSkolemAmbient
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hdecl : proc.header.SigDeclared)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_amb : NoSkolemAmbient C Env.context (Procedure.rigidNames sc ps C proc tn))
    (h_mono : MonoScope Env.context)
    (h_rt_sig : ∀ q ∈ ListMap.toList proc'.header.inputs,
        deskolemizeTy (Procedure.rigidNames sc ps C proc tn)
          (skolemizeTy (Procedure.rigidNames sc ps C proc tn) q.2) = q.2)
    (h_allowed : ∀ c ∈ proc.spec.preconditions.values, allExprTys
        (mtyAllTyConsNames (notRigidConst (Procedure.rigidNames sc ps C proc tn))) c.expr = true)
    (h_lits : ∀ c ∈ proc.spec.preconditions.values,
        ConstTysFixed (Procedure.rigidNames sc ps C proc tn) c.expr) :
    ∀ c ∈ proc.spec.preconditions.values,
        LExpr.HasType C (procInputContext Env.context proc) c.expr
          (.forAll [] .bool) := by
  have hpfx := (Procedure.rigidNames_fresh sc ps C proc tn).1
  have hnd := (Procedure.rigidNames_fresh sc ps C proc tn).2.1
  intro c hc
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  have hσ := Procedure.typeCheckCore_signatureFreeVars_rigid C Env Env' p proc proc' md h hdecl
    h_env.aliasesWF
  have hsig := Procedure.typeCheckCore_sigAgree C Env Env' p proc proc' md h
  obtain ⟨lbl, chk', hcc⟩ := run.preconditionsChecked c hc
  show LExpr.HasType (T := CoreLParams) C
    { Env.context with types := Env.context.types.push (formalsScope proc.header.inputs) } c.expr
    (.forAll [] LMonoTy.bool)
  exact Procedure.checkCondition_HasType_bool C Env proc.header.name
    (Procedure.rigidNames sc ps C proc tn) proc.header.inputs proc'.header.inputs lbl hpfx hnd c
    chk' hcc h_env h_fac h_closed (fun v hv => hσ v (List.mem_append_left _ hv)) hsig.inputsKeys
    hsig.inputsVals h_amb h_mono h_rt_sig (h_allowed c hc) (h_lits c hc)

/-- If the checker accepts a procedure, each source precondition has type `bool` in the input
    scope. -/
private theorem Procedure.typeCheckCore_preconditionsTyped_input
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tn ())
    (hdecl : proc.header.SigDeclared)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) :
    ∀ c ∈ proc.spec.preconditions.values,
        LExpr.HasType C (procInputContext Env.context proc) c.expr
          (.forAll [] .bool) := by
  have hrt := Procedure.typeCheckCore_bodySig_deskolemize_skolemize C Env Env' p proc proc' md h
  refine Procedure.typeCheckCore_preconditionsTyped_input_of_noSkolemAmbient C Env Env' p proc proc'
    md h hdecl h_env h_fac h_closed
    ((Procedure.rigidNames_spec sc ps C Env proc tn hcov).noSkolemAmbient) h_mono ?_
    (Procedure.rigidNames_conditions sc ps C proc tn htn).1
    (Procedure.rigidNames_preconditions_consts sc ps C proc tn htn)
  · intro q hq
    refine hrt q.2 ((ListMap.mem_values_append _ _ q.2).mpr (Or.inr ?_))
    rw [ListMap.values_eq_map_snd]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩

/-- Successful checking types each source postcondition as `bool` in the body scope, when the
    body-scope types survive the skolem round trip and no annotation names a rigid constant. -/
private theorem Procedure.typeCheckCore_postconditionsTyped_input_of_noSkolemAmbient
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hdecl : proc.header.SigDeclared)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_amb : NoSkolemAmbient C Env.context (Procedure.rigidNames sc ps C proc tn))
    (h_mono : MonoScope Env.context)
    (h_rt_sig : ∀ q ∈ ListMap.toList (bodySig proc'.header),
        deskolemizeTy (Procedure.rigidNames sc ps C proc tn)
          (skolemizeTy (Procedure.rigidNames sc ps C proc tn) q.2) = q.2)
    (h_allowed : ∀ c ∈ proc.spec.postconditions.values, allExprTys
        (mtyAllTyConsNames (notRigidConst (Procedure.rigidNames sc ps C proc tn))) c.expr = true)
    (h_lits : ∀ c ∈ proc.spec.postconditions.values,
        ConstTysFixed (Procedure.rigidNames sc ps C proc tn) c.expr) :
    ∀ c ∈ proc.spec.postconditions.values,
        LExpr.HasType C (procBodyContext Env.context proc) c.expr
          (.forAll [] .bool) := by
  have hpfx := (Procedure.rigidNames_fresh sc ps C proc tn).1
  have hnd := (Procedure.rigidNames_fresh sc ps C proc tn).2.1
  intro c hc
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  have hσ := Procedure.typeCheckCore_signatureFreeVars_rigid C Env Env' p proc proc' md h hdecl
    h_env.aliasesWF
  have hsig := Procedure.typeCheckCore_sigAgree C Env Env' p proc proc' md h
  obtain ⟨hkeysB, hvalsB⟩ := bodySig_agree Env.context.aliases proc.header proc'.header
    hsig.inputsKeys hsig.outputsKeys hsig.inputsVals hsig.outputsVals
  obtain ⟨lbl, chk', hcc⟩ := run.postconditionsChecked c hc
  show LExpr.HasType (T := CoreLParams) C (procBodyContext Env.context proc) c.expr
    (.forAll [] LMonoTy.bool)
  rw [procBodyContext_eq]
  exact Procedure.checkCondition_HasType_bool C Env proc.header.name
    (Procedure.rigidNames sc ps C proc tn) (bodySig proc.header) (bodySig proc'.header) lbl hpfx
    hnd c chk' hcc h_env h_fac h_closed (bodySig_freeVars_mem _ _ hσ) hkeysB hvalsB h_amb
    h_mono h_rt_sig (h_allowed c hc) (h_lits c hc)

/-- If the checker accepts a procedure, each source postcondition has type `bool` in the body
    scope. -/
private theorem Procedure.typeCheckCore_postconditionsTyped_input
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tn ())
    (hdecl : proc.header.SigDeclared)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) :
    ∀ c ∈ proc.spec.postconditions.values,
        LExpr.HasType C (procBodyContext Env.context proc) c.expr
          (.forAll [] .bool) := by
  have hrt := Procedure.typeCheckCore_bodySig_deskolemize_skolemize C Env Env' p proc proc' md h
  refine Procedure.typeCheckCore_postconditionsTyped_input_of_noSkolemAmbient C Env Env' p proc
      proc'
    md h hdecl h_env h_fac h_closed
    ((Procedure.rigidNames_spec sc ps C Env proc tn hcov).noSkolemAmbient) h_mono ?_
    (Procedure.rigidNames_conditions sc ps C proc tn htn).2
    (Procedure.rigidNames_postconditions_consts sc ps C proc tn htn)
  · intro q hq
    refine hrt q.2 ?_
    rw [ListMap.values_eq_map_snd]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩

/-- A condition accepted in a skolemized parameter scope agrees with the declared parameter
    context, with its types alias-resolved and no aliases, and the alias-resolved table. -/
private theorem Procedure.checkCondition_annotAgree
    (C : Expression.TyContext) (Env : Expression.TyEnv) (nm : CoreIdent)
    (σ : RigidNames) (sig : @LMonoTySignature Unit) (label : CoreLabel)
    (chk chk' : Procedure.Check)
    (h : Procedure.checkCondition (addSkolemTypes C σ)
            (Function.formalsEnv Env σ sig) nm σ label chk = .ok chk')
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) (h_known : AmbientTypesKnown C.knownTypes Env)
    (h_fresh : RigidNamesFresh C.knownTypes σ)
    (hfixed : ∀ (nm : String) (f : LFunc CoreLParams) (ty : LTy),
      C.functions[nm]? = some f → f.type = .ok ty → mapLTyTys (deskolemizeTy σ) ty = ty)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (h_sigFreeVars : ∀ v ∈ LMonoTys.freeVars sig.values, v ∈ σ.map Prod.fst)
    (h_rt : ∀ mty ∈ sig.values, deskolemizeTy σ (skolemizeTy σ mty) = mty)
    (h_resSk : ∀ mty ∈ sig.values,
      Env.context.resolveTy (skolemizeTy σ mty) = skolemizeTy σ mty)
    (h_res : ∀ mty ∈ sig.values, Env.context.resolveTy mty = mty) :
    ScopesAnnotAgree (C.resolveTable Env.context.aliases)
      { Env.context with types := Env.context.types.push (formalsScope sig) }.dealias.types
      chk'.expr := by
  obtain ⟨et, EnvR, hres, -, rfl, -⟩ := Procedure.checkCondition_ok_inv h
  rw [LContext.resolveTable_eq_self h_sigsFixed]
  exact formalsEnv_resolveWithType_annotAgree C Env Env EnvR σ sig _ _ et _ hres
    (Subst.absorbs_refl _ EnvR.stateSubstInfo.isWF) rfl h_env h_fac h_closed h_mono h_known h_fresh
    hfixed h_sigsFixed h_sigFreeVars h_rt h_resSk h_res

/-- A returned condition of an accepted procedure, checked in the skolemized scope over `sig`, is
    typed `bool` in the resolved `sig` context and table. -/
private theorem Procedure.typeCheckCore_conditionTyped_output
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) (h_known : AmbientTypesKnown C.knownTypes Env)
    (h_aliasNamesFresh : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (h_arrow : C.knownTypes["arrow"]? = some 2)
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty C.knownTypes = true)
    (h_substRange : Lambda.Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes)
    (sig : @LMonoTySignature Unit)
    (h_sub : ∀ mty ∈ sig.values, mty ∈ (bodySig proc'.header).values)
    (h_sigFreeVars : ∀ v ∈ LMonoTys.freeVars sig.values,
      v ∈ (Procedure.rigidNames sc ps C proc tn).map Prod.fst)
    (lbl : CoreLabel) (c₀ c : Procedure.Check)
    (hcc : Procedure.checkCondition (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn))
      (Function.formalsEnv Env (Procedure.rigidNames sc ps C proc tn) sig)
      proc.header.name (Procedure.rigidNames sc ps C proc tn) lbl c₀ = .ok c)
    (h_lits : ConstTysFixed (Procedure.rigidNames sc ps C proc tn) c₀.expr) :
    ExprWellTyped (C.resolveTable Env.context.aliases)
      { Env.context with types := Env.context.types.push (formalsScope sig) }.dealias.types c.expr
      .bool := by
  have hfresh := (Procedure.rigidNames_fresh sc ps C proc tn).2.2.1
  have hA := Procedure.checkCondition_output C Env proc.header.name
    (Procedure.rigidNames sc ps C proc tn) _ lbl ((Procedure.rigidNames_fresh sc ps C proc tn).1)
        c₀ c
    hcc h_env h_fac h_resolved (skolemScope_closed _ _ h_sigFreeVars) hfresh h_arrow
    h_lit h_substRange h_lits
  have hfreshSk := Procedure.aliasNames_notContains_addSkolemTypes sc ps C Env proc tn hcov
    h_aliasNamesFresh
  have hresP := Procedure.typeCheckCore_paramTypes_resolved C Env Env' p proc proc' md h
    h_aliasNamesFresh
  have hrt := Procedure.typeCheckCore_bodySig_deskolemize_skolemize C Env Env' p proc proc' md h
  have hresSk := Procedure.typeCheckCore_bodySig_skolemize_resolved C Env Env' p proc proc' md h
    hfreshSk
  refine ⟨hA.1, ?_, ?_⟩
  · rw [LContext.resolveTable_eq_self h_sigsFixed]
    exact hA.2
  exact Procedure.checkCondition_annotAgree C Env proc.header.name
    (Procedure.rigidNames sc ps C proc tn) sig lbl c₀ c hcc h_env h_fac h_closed h_mono h_known
    hfresh ((Procedure.rigidNames_spec sc ps C Env proc tn hcov).noSkolemAmbient).functions
    h_sigsFixed h_sigFreeVars
    (fun mty hm => hrt mty (h_sub mty hm)) (fun mty hm => hresSk mty (h_sub mty hm))
    (fun mty hm => hresP mty (bodySig_values_subset _ mty (h_sub mty hm)))

/-- If the checker accepts a procedure, each returned precondition is typed `bool` in the
    alias-resolved input context and table. -/
private theorem Procedure.typeCheckCore_preconditionsTyped_output
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tn ())
    (hdecl : proc.header.SigDeclared)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) (h_known : AmbientTypesKnown C.knownTypes Env)
    (h_aliasNamesFresh : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (h_arrow : C.knownTypes["arrow"]? = some 2)
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty C.knownTypes = true)
    (h_substRange : Lambda.Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes) :
    ∀ c ∈ proc'.spec.preconditions.values,
        ExprWellTyped (C.resolveTable Env.context.aliases)
          (procInputContext Env.context proc').dealias.types c.expr .bool := by
  intro c hc
  have hσ := Procedure.typeCheckCore_signatureFreeVars_rigid C Env Env' p proc proc' md h hdecl
    h_env.aliasesWF
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  obtain ⟨lbl, c₀, hc₀, hcc⟩ := run.preconditionsStored c hc
  rw [procInputContext_eq]
  exact Procedure.typeCheckCore_conditionTyped_output C Env Env' p proc proc' md h hcov h_env h_fac
    h_resolved h_closed h_mono h_known h_aliasNamesFresh h_sigsFixed
    h_arrow h_lit h_substRange _
    (fun mty hm => (ListMap.mem_values_append _ _ mty).mpr (Or.inr hm))
    (fun v hv => hσ v (List.mem_append_left _ hv)) lbl c₀ c hcc
    (Procedure.rigidNames_preconditions_consts sc ps C proc tn htn c₀ hc₀)

/-- If the checker accepts a procedure, each returned postcondition is typed `bool` in the
    alias-resolved body context and table. -/
private theorem Procedure.typeCheckCore_postconditionsTyped_output
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tn ())
    (hdecl : proc.header.SigDeclared)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) (h_known : AmbientTypesKnown C.knownTypes Env)
    (h_aliasNamesFresh : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (h_arrow : C.knownTypes["arrow"]? = some 2)
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty C.knownTypes = true)
    (h_substRange : Lambda.Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes) :
    ∀ c ∈ proc'.spec.postconditions.values,
        ExprWellTyped (C.resolveTable Env.context.aliases)
          (procBodyContext Env.context proc').dealias.types c.expr .bool := by
  intro c hc
  have hσ := Procedure.typeCheckCore_signatureFreeVars_rigid C Env Env' p proc proc' md h hdecl
    h_env.aliasesWF
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  obtain ⟨lbl, c₀, hc₀, hcc⟩ := run.postconditionsStored c hc
  rw [procBodyContext_eq]
  exact Procedure.typeCheckCore_conditionTyped_output C Env Env' p proc proc' md h hcov h_env h_fac
    h_resolved h_closed h_mono h_known h_aliasNamesFresh h_sigsFixed
    h_arrow h_lit h_substRange _ (fun _ hm => hm) (bodySig_freeVars_mem _ _ hσ)
    lbl c₀ c hcc (Procedure.rigidNames_postconditions_consts sc ps C proc tn htn c₀ hc₀)

/-! ### Written annotations and body typing -/

/-- When the checker accepts a condition in a parameter scope pushed onto `Env`, its written
    free-variable annotations are valid source types over the ambient aliases that use no reserved
    type-variable name, and its binder annotations use no reserved name. -/
private theorem Procedure.checkCondition_writtenAnnotsOk
    (C : Expression.TyContext) (Env : Expression.TyEnv) (sig : @LMonoTySignature Unit)
    (nm : CoreIdent) (σ : RigidNames) (label : CoreLabel) (chk chk' : Procedure.Check)
    (h : Procedure.checkCondition (addSkolemTypes C σ)
            (Function.formalsEnv Env σ sig) nm σ label chk = .ok chk')
    (hnd : (σ.map Prod.snd).Nodup)
    (h_alias : AliasesNoSkolem σ Env.context.aliases)
    (h_rig : ∀ q ∈ σ, TyVarAdmissibility.notGeneratedOrRigid q.1 = true)
    (h_allowed : allExprTys (mtyAllTyConsNames (notRigidConst σ)) chk.expr = true) :
    FVarAnnotsWF C TyVarAdmissibility.notGeneratedOrRigid Env.context.aliases chk.expr ∧
      BinderAnnotTyVarsAdmissible TyVarAdmissibility.notGeneratedOrRigid chk.expr := by
  obtain ⟨et, EnvR, hres, -, -, -⟩ := Procedure.checkCondition_ok_inv h
  have hsk := resolveWithType_fvarAnnotsWF (addSkolemTypes C σ) _ EnvR
    (skolemizeBody none σ chk.expr) et LMonoTy.bool hres
  rw [formalsEnv_aliases] at hsk
  have hdesk := TypeSpec.FVarAnnotsWF.deskolemize σ (Crig := C) (fun _ => rfl)
    h_alias h_rig hsk
  have hbinder := TypeSpec.BinderAnnotTyVarsAdmissible.deskolemize σ h_rig
    (resolveWithType_binderAnnotTyVarsAdmissible (addSkolemTypes C σ) _ EnvR
      (skolemizeBody none σ chk.expr) et LMonoTy.bool hres)
  rw [mapExprTys_deskolemizeTy_skolemizeBody none hnd chk.expr h_allowed]
    at hdesk hbinder
  exact ⟨hdesk, hbinder⟩

/-- When the checker accepts a procedure, its preconditions' written annotations are valid
    source types using no reserved type-variable name. -/
private theorem Procedure.typeCheckCore_preconditionsAnnots_input
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tn ())
    (hta : ∀ a ∈ proc.header.typeArgs, isAllowedName a = true) :
    ∀ c ∈ proc.spec.preconditions.values,
      WrittenAnnotsOk C (procInputContext Env.context proc) c.expr := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  have hallowed := (Procedure.rigidNames_conditions sc ps C proc tn htn).1
  intro c hc
  obtain ⟨lbl, chk', hcc⟩ := run.preconditionsChecked c hc
  exact Procedure.checkCondition_writtenAnnotsOk C Env _ proc.header.name _ lbl c chk' hcc
    ((Procedure.rigidNames_fresh sc ps C proc tn).2.1)
    ((Procedure.rigidNames_spec sc ps C Env proc tn hcov).noSkolemAmbient).aliases
    (Procedure.rigidNames_admissible sc ps C proc tn hta) (hallowed c hc)

/-- When the checker accepts a procedure, its postconditions' written annotations are valid
    source types using no reserved type-variable name. -/
private theorem Procedure.typeCheckCore_postconditionsAnnots_input
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tn ())
    (hta : ∀ a ∈ proc.header.typeArgs, isAllowedName a = true) :
    ∀ c ∈ proc.spec.postconditions.values,
      WrittenAnnotsOk C (procBodyContext Env.context proc) c.expr := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  have hallowed := (Procedure.rigidNames_conditions sc ps C proc tn htn).2
  intro c hc
  obtain ⟨lbl, chk', hcc⟩ := run.postconditionsChecked c hc
  exact Procedure.checkCondition_writtenAnnotsOk C Env _ proc.header.name _ lbl c chk' hcc
    ((Procedure.rigidNames_fresh sc ps C proc tn).2.1)
    ((Procedure.rigidNames_spec sc ps C Env proc tn hcov).noSkolemAmbient).aliases
    (Procedure.rigidNames_admissible sc ps C proc tn hta) (hallowed c hc)

/-- A condition check succeeds only if every type variable of the condition's annotations is a
    parameter named in `σ`. -/
private theorem Procedure.checkCondition_annotsInScope
    (C : Expression.TyContext) (Env : Expression.TyEnv) (nm : CoreIdent) (σ : RigidNames)
    (label : CoreLabel) (chk chk' : Procedure.Check)
    (h : Procedure.checkCondition (addSkolemTypes C σ) Env nm σ label chk = .ok chk') :
    AnnotsInScope (σ.map Prod.fst) (fun _ => none) chk.expr := by
  obtain ⟨-, -, -, -, -, hscope⟩ := Procedure.checkCondition_ok_inv h
  exact annotsInScope_of_unboundAnnotVar? (fun _ _ hl => by cases hl) hscope

/-- When the checker accepts a procedure, every type variable of an annotation written in each of
    its preconditions is a type parameter of the procedure. -/
private theorem Procedure.typeCheckCore_preconditionsInScope_input
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    ∀ c ∈ proc.spec.preconditions.values,
      AnnotsInScope proc.header.typeArgs (fun _ => none) c.expr := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  intro c hc
  obtain ⟨lbl, chk', hcc⟩ := run.preconditionsChecked c hc
  have hscope := Procedure.checkCondition_annotsInScope C _ _ _ lbl c chk' hcc
  rw [(Procedure.rigidNames_fresh _ _ _ _ _).2.2.2.1] at hscope
  exact hscope

/-- When the checker accepts a procedure, every type variable of an annotation written in each of
    its postconditions is a type parameter of the procedure. -/
private theorem Procedure.typeCheckCore_postconditionsInScope_input
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    ∀ c ∈ proc.spec.postconditions.values,
      AnnotsInScope proc.header.typeArgs (fun _ => none) c.expr := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  intro c hc
  obtain ⟨lbl, chk', hcc⟩ := run.postconditionsChecked c hc
  have hscope := Procedure.checkCondition_annotsInScope C _ _ _ lbl c chk' hcc
  rw [(Procedure.rigidNames_fresh _ _ _ _ _).2.2.2.1] at hscope
  exact hscope

/-- A successful check of the skolemized body in the skolemized parameter scope shows the
    source statements satisfy the typechecker spec in the declarative parameter scope. -/
private theorem bodyTyped_input_core
    (C : Expression.TyContext) (Env EnvX : Expression.TyEnv) (p : Program)
    (proc : Procedure) (σ : RigidNames) (sig : @LMonoTySignature Unit)
    (hpfx : RigidNamesPrefixed σ) (hnd : (σ.map Prod.snd).Nodup)
    (h_rigAdm : ∀ q ∈ σ, TyVarAdmissibility.notGeneratedOrRigid q.1 = true)
    (ssIn ssOut : List Statement)
    (hB : Statement.typeCheck (addSkolemTypes C σ)
            (Function.formalsEnv Env σ sig)
            p (some proc) (skolemizeStmts none σ ssIn) = .ok (ssOut, EnvX))
    (h_rigid : ∀ v ∈ (addSkolemTypes C σ).rigidTypeVars,
      LMonoTy.subst EnvX.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h_np : NoParamRange σ EnvX.stateSubstInfo.subst)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_ambient : ∀ z ty, Env.context.types.find? z = some ty →
        mapLTyTys (deskolemizeTy σ) ty = ty)
    (h_aliasNoSkolem : AliasesNoSkolem σ Env.context.aliases)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_fsig : ∀ (nm : String) (f : LFunc CoreLParams) (fty : LTy),
      C.functions[nm]? = some f → f.type = .ok fty → mapLTyTys (deskolemizeTy σ) fty = fty)
    (h_mono : MonoScope Env.context)
    (h_annotTys : allStmtsTys (mtyAllTyConsNames (notRigidConst σ)) ssIn = true)
    (h_litTys : ∀ p ∈ σ, p.2 ∉ stmtsLitTyNames ssIn)
    (h_rt : ∀ mty ∈ sig.values, deskolemizeTy σ (skolemizeTy σ mty) = mty)
    (h_sigFreeVars : ∀ v ∈ LMonoTys.freeVars sig.values, v ∈ σ.map Prod.fst)
    (h_bodyRoundTrip :
      mapStmtsTys (deskolemizeTy σ) (skolemizeStmts none σ ssIn) = ssIn)
    (hcalled : ∀ c, CalledProcedureSignaturesFixed σ p c) :
    ∃ Cout Γout Δout, StatementsHasType p
      { C with rigidTypeVars := C.rigidTypeVars ++ σ.map Prod.fst }
      { Env.context with types := Env.context.types.push (formalsScope sig) } (fun _ => none) []
      ssIn Cout Γout Δout := by
  obtain ⟨ssA, EnvA, CA, haux, -, hEnv, -⟩ :=
    Statement.typeCheck_ok_inv _ _ _ _ _ _ _ hB
  have hstate : EnvX.stateSubstInfo = Statement.finalSubstInfo
      (Function.formalsEnv Env σ sig).genEnv.genState EnvA := by
    rw [hEnv]; rfl
  have hwf := formalsEnv_TEnvWF Env σ sig h_env h_sigFreeVars
  have hcl := formalsEnv_typesClosed Env σ sig h_closed h_sigFreeVars
  have htys_ne := skolemScopeEnv_types_ne σ Env sig
  have hfac' := FactorySigWF.addSkolemTypes C σ h_fac
  have h_sweep : SweepAt (addSkolemTypes C σ) EnvX.stateSubstInfo.subst ssA := by
    rw [hstate]
    exact typeCheck_sweepAt (addSkolemTypes C σ) _
      EnvX p (some proc) (skolemizeStmts none σ ssIn) ssOut hB _ _ _ haux
  have habs : Subst.absorbs EnvX.stateSubstInfo.subst EnvA.stateSubstInfo.subst := by
    rw [hstate]
    exact Statement.finalSubstInfo_absorbs _ EnvA
  have haliasUnregistered : ∀ al ∈ (Function.formalsEnv Env σ sig).context.aliases,
      (addSkolemTypes C σ).knownTypes.containsName al.name = false := by
    rw [formalsEnv_aliases Env σ sig]
    exact aliasNames_unregistered_addSkolemTypes h_aliasNoSkolem h_aliasNames
  obtain ⟨Γj, Δsrc, hsrcΔ, hsrcΔStrict, -⟩ :=
    Statement.typeCheckAux_sound_visible_withSource σ (addSkolemTypes C σ) CA _ EnvA p
      (some proc) _ ssA EnvX.stateSubstInfo.subst haux habs EnvX.stateSubstInfo.isWF h_np hwf
      hfac' (formalsEnv_MonoScope Env σ sig h_mono) htys_ne
      haliasUnregistered h_sweep h_rigid (List.forall_mem_map.mpr (rigid_mem_addSkolemTypes C σ))
  obtain ⟨Γj0, hsrc0, hsrc0Strict, -⟩ := StatementsSideConditionsΔ.input_ctx_FindEq hsrcΔStrict
    (LExpr.TContext.FindEq_subst_of_closed (T := CoreLParams)
      (Function.formalsEnv Env σ sig).context EnvX.stateSubstInfo.subst
      (LExpr.ctx_closed_of_check (T := CoreLParams)
        (Function.formalsEnv Env σ sig) hcl))
  have hinv0 : BodyDeskolInv σ (addSkolemTypes C σ)
      (Function.formalsEnv Env σ sig).context := by
    refine ⟨
      { factoryWF := hfac'
        signaturesSafe := FactorySigDeskolSafe.of_fixed σ C.functions h_fsig
        monoScope := formalsEnv_MonoScope Env σ sig h_mono
        aliasesWF := hwf.aliasesWF
        aliasesNoSkolem :=
          (formalsEnv_aliases Env σ sig) ▸ h_aliasNoSkolem },
      ?_⟩
    exact rigid_mem_addSkolemTypes C σ
  -- Annotations of the skolemized body avoid rigid-name clashes and survive deskolemization.
  let A := fun t => annotNoRigidClash σ t && deskolKeeps σ t
  have hA : ∀ t, A t = true → annotNoRigidClash σ t = true := by
    intro t ht
    simp only [A, Bool.and_eq_true] at ht
    exact ht.1
  have hvalidD : ∀ (Csk Crig : LContext CoreLParams) (Γsk Γrig : TContext Unit) (ann : LMonoTy),
      BodyDeskolInv σ Csk Γsk → AmbientDeskol σ Csk Crig → DeskolemizesScope σ Γsk Γrig →
      ValidDeclaredTy Csk Γsk.aliases ann →
      ValidDeclaredTy Crig Γrig.aliases (deskolemizeTy σ ann) :=
    fun Csk Crig Γsk Γrig ann hinv hamb hsc hsrc =>
      declaredTy_valid_deskolemize σ Csk Crig Γsk Γrig hamb hsc hinv.1.aliasesNoSkolem
        h_rigAdm ann hsrc
  have hhyps : DeskolHyps p σ (BodyDeskolInv σ) A := by
    refine ⟨hpfx, ?_, fun _ _ hinv => hinv.1.aliasesNoSkolem, h_rigAdm, ?_,
      fun _ _ _ _ _ _ _ _ hs hinv => DeskolAmbientScope.rigid_step hs hinv,
      hcalled, ?_⟩
    · intro Csk Crig Γsk Γrig Δsk Δrig e mty hinv hamb hsc henv hnp hrd hav hann hlit he
      have hclash := allExprTys_mono hA e hann
      have htr : ∀ e', allExprTys (annotNoRigidClash σ) e' = true → ConstTysFixed σ e' →
          LExpr.HasType Csk Γsk e' (.forAll [] mty) →
          LExpr.HasType Crig Γrig (mapExprTys (deskolemizeTy σ) e')
            (.forAll [] (deskolemizeTy σ mty)) := fun e' hclash' hl' he' =>
        exprTyped_deskolemize_polymorphic σ hpfx Csk Crig Γsk Γrig hamb hsc e' mty
          hinv.1.factoryWF hinv.1.signaturesSafe
          hinv.1.monoScope hinv.1.aliasesWF hinv.1.aliasesNoSkolem hclash' hl' he'
      have hread := htr (instAnnots Δsk e) (allExprTys_annotNoRigidClash_instAnnots hrd e hav
        hclash) (ConstTysFixed.instAnnots Δsk hlit) he
      rwa [mapExprTys_deskolemizeTy_instAnnots henv hnp] at hread
    · intro Csk Crig Γsk Γrig _ _ _ ann _ hinv hamb hsc henv hnp hσ _ hdecl
      obtain ⟨hinst, hsrc⟩ := hdecl
      refine ⟨?_, hvalidD Csk Crig Γsk Γrig ann hinv hamb hsc hsrc⟩
      have hinst' := scopedAnnotInst_deskolemizeTy_of_rigid σ hinst hinv.1.aliasesNoSkolem hσ
        henv hnp
      rwa [← hsc.1, hamb.rigidTypeVars_eq] at hinst'
    · intro ann hann
      simp only [A, Bool.and_eq_true] at hann
      exact mem_freeVars_deskolemizeTy_of_deskolKeeps hann.2
  have hannA : allStmtsTys A (skolemizeStmts none σ ssIn) = true := by
    refine allStmtsTys_skolemizeStmts_of_skolemizeTy none σ A ?_ ?_ ssIn h_annotTys
    · intro t h
      simp only [A, Bool.and_eq_true]
      exact ⟨annotNoRigidClash_skolemizeTy σ t,
        deskolKeeps_skolemizeTy_of_sublist (List.Sublist.refl σ) hnd t h⟩
    · intro t h
      simp only [A, Bool.and_eq_true]
      exact ⟨annotNoRigidClash_of_notRigidConst t h, deskolKeeps_of_notRigidConst t h⟩
  obtain ⟨Cout, Γout, Δout, hd, -, -⟩ := StatementsHasTypeΔ_of_deskolemized_outputAgree σ C
    (BodyDeskolInv σ) A hhyps (FactorySigDeskolemizes.refl_of_fixed σ C.functions h_fsig)
    hsrc0 hsrc0Strict hinv0 hannA (Statements.srcAvoid_skolemizeStmts σ ssIn)
    (stmtsLitTyNames_skolemizeStmts none σ ssIn ▸ h_litTys)
    (NoParamBinding.empty σ) _ (fun _ => none)
    (skolemScope_deskolemizes σ Env sig h_ambient h_rt) (EnvDeskol.empty σ)
  rw [h_bodyRoundTrip] at hd
  exact ⟨Cout, Γout, Δout, hd⟩

/-- If the checker accepts a procedure, its source body satisfies the typechecker spec in the
    body scope with the type arguments rigid. -/
private theorem Procedure.typeCheckCore_bodyTyped_input
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tn ())
    (hP : ∀ n ∈ Program.procSigTyNames p, n ∈ ps.get)
    (hdecl : proc.header.SigDeclared)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (hsigs : ProcSigsDeclared p)
    (hS : Subst.VarsAvoid Env.stateSubstInfo.subst proc.header.typeArgs)
    (hta : ∀ a ∈ proc.header.typeArgs, isAllowedName a = true) :
    ProcBodyHasType p
      { C with rigidTypeVars := C.rigidTypeVars ++ proc.header.typeArgs }
      (procBodyContext Env.context proc) proc.body := by
  have hpfx := (Procedure.rigidNames_fresh sc ps C proc tn).1
  have hnd := (Procedure.rigidNames_fresh sc ps C proc tn).2.1
  have hrigAdm := Procedure.rigidNames_admissible sc ps C proc tn hta
  have h_amb := (Procedure.rigidNames_spec sc ps C Env proc tn hcov).noSkolemAmbient
  have hσ := Procedure.typeCheckCore_signatureFreeVars_rigid C Env Env' p proc proc' md h hdecl
    h_env.aliasesWF
  have hrt := Procedure.typeCheckCore_bodySig_deskolemize_skolemize C Env Env' p proc proc' md h
  have hsigAgree := Procedure.typeCheckCore_sigAgree C Env Env' p proc proc' md h
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  cases hbody : proc.body with
  | cfg cfgBody o =>
    exact ProcBodyHasType.cfg _ _
  | abstract =>
    exact ProcBodyHasType.abstract
  | structured ssIn o =>
    obtain ⟨ssOut, EnvX, hB, hRigid, -⟩ := run.bodyStructured ssIn o hbody
    have hbodyAnnot := Procedure.rigidNames_body sc ps C proc tn htn ssIn o hbody
    have hbodyRT : mapStmtsTys (deskolemizeTy (Procedure.rigidNames sc ps C proc tn))
        (skolemizeStmts none (Procedure.rigidNames sc ps C proc tn) ssIn) = ssIn :=
      mapStmtsTys_deskolemizeTy_skolemizeStmts none _ hnd ssIn hbodyAnnot
    obtain ⟨Cout, Γout, Δout, hj⟩ :=
      bodyTyped_input_core C Env EnvX p proc (Procedure.rigidNames sc ps C proc tn) _
        hpfx hnd hrigAdm
        ssIn ssOut hB hRigid
        (Procedure.typeCheckCore_bodyNoParamRange C Env Env' p proc proc' md h hdecl h_env h_fac
          h_closed hsigs hS hta ssIn ssOut EnvX hB)
        h_env h_fac h_closed h_amb.ctxTypes
        h_amb.aliases h_aliasNames h_amb.functions h_mono hbodyAnnot
        (Procedure.rigidNames_body_lits sc ps C proc tn htn ssIn o hbody) hrt
        (bodySig_freeVars_mem _ _ hσ) hbodyRT
        (Procedure.rigidNames_calledSigsFixed sc ps C p proc tn hP)
    obtain ⟨hkeysB, hvalsB⟩ :=
      bodySig_agree Env.context.aliases proc.header _
        hsigAgree.inputsKeys hsigAgree.outputsKeys hsigAgree.inputsVals
        hsigAgree.outputsVals
    obtain ⟨Γout', hj'⟩ :=
      StatementsHasTypeΔ_pushScope_aliasEquiv (P := p) _ Env.context (fun _ => none)
        (bodySig proc.header) _ [] ssIn Cout Γout Δout h_env.aliasesWF hkeysB hvalsB hj
    rw [(Procedure.rigidNames_fresh _ _ _ _ _).2.2.2.1] at hj'
    rw [procBodyContext_eq]
    exact ProcBodyHasType.structured _ Cout Γout' Δout o hj'

/-- A property of every CFG body and of every deskolemized checked structured body, given the side
    conditions of the skolemized body scope, holds of the body an accepted procedure returns. -/
private theorem Procedure.typeCheckCore_body_cases
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (hdecl : proc.header.SigDeclared)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_aliasNamesFresh : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (Q : Procedure.Body → Prop) (hcfg : ∀ c o, Q (.cfg c o)) (habs : Q .abstract)
    (hstr : ∀ (ssIn ssOut : List Statement) (EnvX : Expression.TyEnv) (o : Bool),
      proc.body = .structured ssIn o →
      Statement.typeCheck (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn))
          (Function.formalsEnv Env (Procedure.rigidNames sc ps C proc tn) (bodySig proc'.header))
          p (some proc) (skolemizeStmts none (Procedure.rigidNames sc ps C proc tn) ssIn)
        = .ok (ssOut, EnvX) →
      (Procedure.rigidNames sc ps C proc tn).map Prod.fst = proc'.header.typeArgs →
      RigidNamesPrefixed (Procedure.rigidNames sc ps C proc tn) →
      FactorySigDeskolemizes (Procedure.rigidNames sc ps C proc tn) C.functions C.functions →
      FactorySigDeskolSafe (Procedure.rigidNames sc ps C proc tn) C.functions →
      AliasesNoSkolem (Procedure.rigidNames sc ps C proc tn) Env.context.aliases →
      (∀ mty ∈ (bodySig proc'.header).values, deskolemizeTy (Procedure.rigidNames sc ps C proc tn)
        (skolemizeTy (Procedure.rigidNames sc ps C proc tn) mty) = mty) →
      (∀ v ∈ LMonoTys.freeVars (bodySig proc'.header).values,
        v ∈ (Procedure.rigidNames sc ps C proc tn).map Prod.fst) →
      (∀ al ∈ Env.context.aliases,
        (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn)).knownTypes.containsName al.name
          = false) →
      (∀ mty ∈ (bodySig proc'.header).values,
        Env.context.resolveTy (skolemizeTy (Procedure.rigidNames sc ps C proc tn) mty)
          = skolemizeTy (Procedure.rigidNames sc ps C proc tn) mty) →
      Q (.structured (mapStmtsTys (deskolemizeTy (Procedure.rigidNames sc ps C proc tn)) ssOut)
        o)) :
    Q proc'.body := by
  have hpfx := (Procedure.rigidNames_fresh sc ps C proc tn).1
  have hσ := Procedure.typeCheckCore_signatureFreeVars_rigid C Env Env' p proc proc' md h hdecl
    h_env.aliasesWF
  have hrt := Procedure.typeCheckCore_bodySig_deskolemize_skolemize C Env Env' p proc proc' md h
  have hamb := (Procedure.rigidNames_spec sc ps C Env proc tn hcov).noSkolemAmbient
  have hfixed := hamb.functions
  have hfreshSk := Procedure.aliasNames_notContains_addSkolemTypes sc ps C Env proc tn hcov
    h_aliasNamesFresh
  have hta : (Procedure.rigidNames sc ps C proc tn).map Prod.fst = proc'.header.typeArgs := by
    rw [(Procedure.rigidNames_fresh _ _ _ _ _).2.2.2.1, Procedure.typeCheckCore_typeArgs_eq C Env
        Env' p proc proc' md h]
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  cases hbody : proc.body with
  | cfg cfgBody o =>
    obtain ⟨_, _, _, -, hout⟩ := run.bodyCfg cfgBody o hbody
    rw [hout]
    exact hcfg _ _
  | abstract =>
    rw [run.bodyAbstract hbody]
    exact habs
  | structured ssIn o =>
    obtain ⟨ssOut, EnvX, hB, -, hbody'⟩ := run.bodyStructured ssIn o hbody
    rw [hbody']
    exact hstr ssIn ssOut EnvX o hbody hB hta hpfx (FactorySigDeskolemizes.refl_of_fixed _ _ hfixed)
      (FactorySigDeskolSafe.of_fixed _ _ hfixed) hamb.aliases hrt (bodySig_freeVars_mem _ _ hσ)
      hfreshSk
      (Procedure.typeCheckCore_bodySig_skolemize_resolved C Env Env' p proc proc' md h hfreshSk)

/-- If the checker accepts a procedure, the returned body is well typed in the alias-resolved
    body scopes, table and program, with the type arguments rigid, and the names of a structured
    body are valid. -/
private theorem Procedure.typeCheckCore_bodyTyped_output
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tn ())
    (hP : ∀ n ∈ Program.procSigTyNames p, n ∈ ps.get)
    (hdecl : proc.header.SigDeclared)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope (IDMeta := Unit) Env.context)
    (h_known : AmbientTypesKnown C.knownTypes Env)
    (h_aliasNamesFresh : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions) :
    ProcBodyWellTyped (p.resolveSigs Env.context.aliases)
      { C with rigidTypeVars := C.rigidTypeVars ++ proc'.header.typeArgs }
      (procBodyScopes Env.context.dealias.types proc') proc'.body ∧
    ∀ ss o, proc'.body = .structured ss o →
      StatementsNamesWF (p.resolveSigs Env.context.aliases) (· ∈ C.functions) ss := by
  have hresP := Procedure.typeCheckCore_paramTypes_resolved C Env Env' p proc proc' md h
    h_aliasNamesFresh
  refine Procedure.typeCheckCore_body_cases C Env Env' p proc proc' md h hcov hdecl h_env
    h_aliasNamesFresh
    (fun b => ProcBodyWellTyped (p.resolveSigs Env.context.aliases)
      { C with rigidTypeVars := C.rigidTypeVars ++ proc'.header.typeArgs }
      (procBodyScopes Env.context.dealias.types proc') b ∧
      ∀ ss o, b = .structured ss o →
        StatementsNamesWF (p.resolveSigs Env.context.aliases) (· ∈ C.functions) ss)
    (fun c o => ⟨.cfg c o, fun _ _ hss => nomatch hss⟩) ⟨.abstract, fun _ _ hss => nomatch hss⟩ ?_
  intro ssIn ssOut EnvX o hbodyEq hB hta hpfx hfactoryRel hfactorySafe haliasNoSkolem hrt hσ
    hfreshSk hresSk
  obtain ⟨⟨Cout, tsOut, hj⟩, hnames⟩ :=
    bodyTyped_output_core C Env EnvX p proc (Procedure.rigidNames sc ps C proc tn) _ hpfx
      ssIn ssOut hB h_env h_fac hfactoryRel hfactorySafe h_resolved haliasNoSkolem h_closed h_mono
      h_known hrt hσ ((Procedure.rigidNames_fresh sc ps C proc tn).2.2.1) hfreshSk hresSk
      (fun mty hm => hresP mty (bodySig_values_subset _ mty hm)) h_sigsFixed
      (Procedure.rigidNames_calledSigsFixed sc ps C p proc tn hP)
      (Procedure.rigidNames_body_lits sc ps C proc tn htn ssIn o hbodyEq)
  rw [hta] at hj
  refine ⟨.structured _ Cout tsOut o hj, fun ss _ hss => ?_⟩
  injection hss with hss'
  subst hss'
  exact hnames

/-- When each type of a list resolves through `aliases` to the matching type of a second list,
    and each type of the second list is an instance of a registered type, every type of the first
    list is a valid source type. -/
private theorem sourceTyWF_of_resolve_known {C : Expression.TyContext}
    {aliases : List TypeAlias} :
    ∀ {tys rs : LMonoTys}, SourceTysResolve aliases tys rs →
      List.Rel₂ (fun _ r => isInstanceOfKnownType r C = true) tys rs →
      ∀ ty ∈ tys, ∃ r, SourceTyWF C TyVarAdmissibility.all aliases ty r
  | _, _, .nil, _, _, hty => by cases hty
  | _, _, .cons hhead htail, .cons hk htl, ty, hty => by
    rcases List.mem_cons.mp hty with rfl | hmem
    · exact ⟨_, hhead, ResolvedTyWF.of_knownInstance hk⟩
    · exact sourceTyWF_of_resolve_known htail htl ty hmem

/-! ## Soundness theorems -/

/-- A procedure with allowed type parameters that the checker proper (`typeCheckCore`) accepts
    satisfies `ProcHasTypeExact` in the ambient context, when its header has distinct type
    parameters, declares every type variable of its signature and has no parameter named like a
    function. -/
private theorem Procedure.typeCheckCore_sound
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tn ())
    (hP : ∀ n ∈ Program.procSigTyNames p, n ∈ ps.get)
    (hnd : proc.header.typeArgs.Nodup) (hdecl : proc.header.SigDeclared)
    (hformals : ∀ id ∈ proc.header.inputs.keys ++ proc.header.outputs.keys,
      id.name ∉ C.functions)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (hsigs : ProcSigsDeclared p)
    (hS : Subst.VarsAvoid Env.stateSubstInfo.subst proc.header.typeArgs)
    (hta : ∀ a ∈ proc.header.typeArgs, isAllowedName a = true) :
    ProcHasTypeExact p C Env.context proc :=
  { inputsNodup := Procedure.typeCheckCore_inputsNodup C Env Env' p proc proc' md h
    outputsNodup := Procedure.typeCheckCore_outputsNodup C Env Env' p proc proc' md h
    oldNamesFresh := Procedure.typeCheckCore_oldNamesFresh h
    typeArgsNodup := hnd
    typeArgsNotReserved := hta
    noUndeclaredVars := hdecl
    signatureWellKinded := by
      obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
      intro ty hty
      rcases List.mem_append.mp hty with hin | hout
      · exact sourceTyWF_of_resolve_known
          (LMonoTys.resolveAliases_sourceTysResolve (T := CoreLParams) _ Env _ Env run.insResolve)
          run.insKnown ty hin
      · exact sourceTyWF_of_resolve_known
          (LMonoTys.resolveAliases_sourceTysResolve (T := CoreLParams) _ Env _ Env run.outsResolve)
          run.outsKnown ty hout
    modRights := Procedure.typeCheckCore_modRights_input C Env Env' p proc proc' md h
    preconditionsTyped :=
      Procedure.typeCheckCore_preconditionsTyped_input C Env Env' p proc proc' md h hcov htn hdecl
        h_env h_fac h_closed h_mono
    postconditionsTyped :=
      Procedure.typeCheckCore_postconditionsTyped_input C Env Env' p proc proc' md h hcov htn hdecl
        h_env h_fac h_closed h_mono
    preconditionsAnnots :=
      Procedure.typeCheckCore_preconditionsAnnots_input C Env Env' p proc proc' md h hcov htn hta
    postconditionsAnnots :=
      Procedure.typeCheckCore_postconditionsAnnots_input C Env Env' p proc proc' md h hcov htn hta
    preconditionsInScope :=
      Procedure.typeCheckCore_preconditionsInScope_input C Env Env' p proc proc' md h
    postconditionsInScope :=
      Procedure.typeCheckCore_postconditionsInScope_input C Env Env' p proc proc' md h
    bodyTyped :=
      Procedure.typeCheckCore_bodyTyped_input C Env Env' p proc proc' md h hcov htn hP hdecl h_env
        h_fac h_closed h_mono h_aliasNames hsigs hS hta
    formalsNotFunctions := hformals }

/-- Output soundness for the checker proper (`typeCheckCore`): when the header has distinct type
    parameters, declares every type variable of its signature and has no parameter named like a
    function, the returned procedure is well typed over the alias-resolved variable scopes,
    against the alias-resolved table and program, and its names are valid. -/
private theorem Procedure.typeCheckCore_sound_output
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tn ())
    (hP : ∀ n ∈ Program.procSigTyNames p, n ∈ ps.get)
    (hnd : proc.header.typeArgs.Nodup) (hdecl : proc.header.SigDeclared)
    (hformals : ∀ id ∈ proc.header.inputs.keys ++ proc.header.outputs.keys,
      id.name ∉ C.functions)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_mono : MonoScope (IDMeta := Unit) Env.context)
    (h_aliasNamesFresh : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (h_arrow : C.knownTypes["arrow"]? = some 2)
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty C.knownTypes = true)
    (h_substRange : Lambda.Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_known : AmbientTypesKnown C.knownTypes Env) :
    ProcWellTyped (p.resolveSigs Env.context.aliases) (C.resolveTable Env.context.aliases)
      Env.context.dealias.types proc' ∧
    ProcNamesWF (p.resolveSigs Env.context.aliases) (· ∈ C.functions) proc' := by
  have hresP := Procedure.typeCheckCore_paramTypes_resolved C Env Env' p proc proc' md h
    h_aliasNamesFresh
  have hin : TContext.FindEq (T := CoreLParams) (procInputContext Env.context.dealias proc')
      (procInputContext Env.context proc').dealias := by
    rw [procInputContext_eq, procInputContext_eq]
    exact (formalsScope_push_dealias_FindEq Env.context _
      (fun mty hm => hresP mty (List.mem_append_left _ hm))).symm
  have hbody : TContext.FindEq (T := CoreLParams) (procBodyContext Env.context.dealias proc')
      (procBodyContext Env.context proc').dealias := by
    rw [procBodyContext_eq, procBodyContext_eq]
    exact (formalsScope_push_dealias_FindEq Env.context _
      (fun mty hm => hresP mty (bodySig_values_subset _ mty hm))).symm
  have hpre := Procedure.typeCheckCore_preconditionsTyped_output C Env Env' p proc proc' md h hcov
    htn hdecl h_env h_fac h_resolved h_closed h_mono h_known h_aliasNamesFresh h_sigsFixed
    h_arrow h_lit h_substRange
  have hpost := Procedure.typeCheckCore_postconditionsTyped_output C Env Env' p proc proc' md h
    hcov htn hdecl h_env h_fac h_resolved h_closed h_mono h_known h_aliasNamesFresh h_sigsFixed
    h_arrow h_lit h_substRange
  obtain ⟨hbody', hbnames⟩ := Procedure.typeCheckCore_bodyTyped_output C Env Env' p proc proc' md
    h hcov htn hP hdecl h_env h_fac h_resolved h_closed h_mono h_known h_aliasNamesFresh h_sigsFixed
  have hinKeys := Procedure.typeCheckCore_inputsKeys_eq C Env Env' p proc proc' md h
  have houtKeys := Procedure.typeCheckCore_outputsKeys_eq C Env Env' p proc proc' md h
  have htaEq := Procedure.typeCheckCore_typeArgs_eq C Env Env' p proc proc' md h
  rw [LContext.resolveTable_eq_self h_sigsFixed] at hpre hpost ⊢
  refine ⟨
    { inputsNodup := by
        rw [hinKeys]
        exact Procedure.typeCheckCore_inputsNodup C Env Env' p proc proc' md h
      outputsNodup := by
        rw [houtKeys]
        exact Procedure.typeCheckCore_outputsNodup C Env Env' p proc proc' md h
      oldNamesFresh := by
        have hfresh := Procedure.typeCheckCore_oldNamesFresh h
        unfold Procedure.Header.oldNamesFresh at hfresh ⊢
        intro g hg
        rw [Procedure.Header.mem_keys_getInoutParams] at hg
        rw [hinKeys, houtKeys] at hg ⊢
        have hinout : g ∈ proc.header.getInoutParams.keys :=
          (Procedure.Header.mem_keys_getInoutParams _ g).mpr hg
        exact hfresh g hinout
      typeArgsNodup := by
        rw [htaEq]
        exact hnd
      noUndeclaredVars :=
        Procedure.typeCheckCore_noUndeclaredVars C Env Env' p proc proc' md h hdecl
          h_env.aliasesWF
      declTyVarsBound := by
        obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
        rw [htaEq]
        exact Procedure.declTyVarsBound_of_check _ _ _ _ run.declTyVarsBound
      signatureWellKinded := fun ty hty => (ResolvedTyWF.of_knownInstance
        (Procedure.typeCheckCore_paramTypes_knownInstance C Env Env' p proc proc' md h ty
          hty)).wellKinded
      modRights := Procedure.typeCheckCore_modRights_output C Env Env' p proc proc' md h
      preconditionsTyped := fun c hc => TypeSpec.ExprWellTyped.of_find? hin.1 (hpre c hc)
      postconditionsTyped := fun c hc => TypeSpec.ExprWellTyped.of_find? hbody.1 (hpost c hc)
      bodyTyped := hbody'.withRigid C.rigidTypeVars },
    ?_, ?_⟩
  · rw [hinKeys, houtKeys]
    exact hformals
  · cases hb : proc'.body with
    | structured ss o => exact hbnames ss o hb
    | cfg c o => trivial
    | abstract => trivial

/-- With well-formed aliases, the resolved signature of any renaming of a procedure's type
    parameters has every instantiation of the procedure's resolved signature: a call typed
    against the procedure is typed against the renamed one. -/
theorem ProcSigResolved.instOf_renameTypeArgs {A : List TypeAlias} {q q2 : Procedure}
    {ren : List (String × String)}
    (hA : TContext.AliasesWF ({ aliases := A } : TContext Unit))
    (hren : TypeSpec.TyArgRenamingCore q.header.typeArgs q.mentionedTyVars ren)
    (h : ProcSigResolved A (q.renameTypeArgs ren) q2) :
    ProcSigInstOf (q.resolveSig { aliases := A }) q2 := by
  obtain ⟨hfst, hsnd, hren'⟩ := hren
  obtain ⟨hnmIn, hkIn, hkOut⟩ := Procedure.renameTypeArgs_names q ren
  obtain ⟨hvIn, hvOut⟩ := Procedure.renameTypeArgs_values q ren
  have hext : ∀ (σ : List (TyIdentifier × LMonoTy)) (t : LMonoTy),
      LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ ++ ren.map fun p =>
          (p.2, LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (.ftvar p.1))]) t =
      LMonoTy.subst (Subst.afterRenaming (Strata.Util.HMaps.ofScopes [σ]) ren) t := by
    intro σ t
    refine LMonoTy.subst_ext _ _ _ fun x _ => ?_
    simp only [Subst.afterRenaming, Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil]
    rw [Strata.Util.HMaps.find?_single_scope, HMap.find?_ofList_append]
    cases hx : HMap.find? (HMap.ofList (ren.map fun p =>
        (p.2, LMonoTy.subst [HMap.ofList σ] (.ftvar p.1)))) x with
    | none =>
      rw [Strata.Util.HMaps.find?_push_of_none _ _ x hx, Strata.Util.HMaps.find?_single_scope]
      rfl
    | some v => rw [Strata.Util.HMaps.find?_push_of_some _ _ x v hx]; rfl
  have hkey : ∀ σ : List (TyIdentifier × LMonoTy), ∀ t ∈ q.header.inputs.values ++
      q.header.outputs.values,
      LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ ++ ren.map fun p =>
          (p.2, LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (.ftvar p.1))])
        (({ aliases := A } : TContext Unit).resolveTy (LMonoTy.subst (Subst.ofRenaming ren) t)) =
      LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ])
        (({ aliases := A } : TContext Unit).resolveTy t) := by
    intro σ t ht
    rw [TContext.resolveTy_subst_renaming (T := CoreLParams) hA _ (Subst.ofRenaming_ftvar ren),
      hext σ]
    refine LMonoTy.subst_afterRenaming _ ren hfst hsnd _ fun p hp hv => ?_
    exact (hren' p hp).2
      (Procedure.mem_mentionedTyVars_of_param ht _
        (TContext.resolveTy_freeVars_subset (T := CoreLParams) hA t _ hv))
  refine ⟨?_, ?_, fun σ => ⟨σ ++ ren.map fun p =>
      (p.2, LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (.ftvar p.1)), ?_, ?_, ?_⟩⟩
  · rw [Procedure.resolveSig_inputs, TContext.resolveSig_keys, ← hkIn]
    exact h.inputsKeys
  · rw [Procedure.resolveSig_outputs, TContext.resolveSig_keys, ← hkOut]
    exact h.outputsKeys
  · rw [h.inputsVals, hvIn, Procedure.resolveSig_inputs, TContext.resolveSig_values,
      List.map_map, List.map_map, List.map_map]
    exact List.map_congr_left fun t ht => hkey σ t (List.mem_append_left _ ht)
  · rw [h.outputsVals, hvOut, Procedure.resolveSig_outputs, TContext.resolveSig_values,
      List.map_map, List.map_map, List.map_map]
    exact List.map_congr_left fun t ht => hkey σ t (List.mem_append_right _ ht)
  · rw [← h.typeArgs]
    show (renameTyArgList ren q.header.typeArgs).map _ = q.header.typeArgs.map _
    unfold renameTyArgList
    rw [List.map_map]
    refine List.map_congr_left fun a ha => ?_
    have hfresh : ∀ p ∈ ren, p.2 ∉ LMonoTy.freeVars (LMonoTy.ftvar a) := by
      intro p hp hv
      simp only [LMonoTy.freeVars, List.mem_singleton] at hv
      exact (hren' p hp).2 (hv ▸ Procedure.mem_mentionedTyVars_of_typeArg ha)
    simp only [Function.comp_apply]
    rw [hext σ, ← Subst.ofRenaming_ftvar_lookup hfst a]
    exact LMonoTy.subst_afterRenaming _ ren hfst hsnd _ hfresh

/-- A well-typed procedure body stays well typed against a program giving every procedure it calls
    a signature with every instantiation of the original's, and declaring only type names the
    original program declares. -/
private theorem ProcBodyWellTyped.program_congr_calls {P1 P2 : Program}
    {C : LContext CoreLParams} {ts : TypeScopes} {body : Procedure.Body}
    (hnames : ∀ n ∈ programNamesOfKind P2 .type, n ∈ programNamesOfKind P1 .type)
    (hagree : ProcedureCallsRel ProcSigInstOf P1 P2 (Procedure.Body.calledProcedureNames body))
    (h : ProcBodyWellTyped P1 C ts body) : ProcBodyWellTyped P2 C ts body := by
  cases h with
  | structured ss C' ts' o hss =>
    have hagree' : ProcedureCallsRel ProcSigInstOf P1 P2 (Statements.calledProcedureNames ss) := by
      simpa using hagree
    exact .structured ss C' ts' o
      (TypeSpec.StatementsWellTyped.program_congr_calls hnames hagree' hss)
  | cfg c o => exact .cfg c o
  | abstract => exact .abstract

/-- A well-typed procedure stays well typed against a program giving every procedure it calls a
    signature with every instantiation of the original's, and declaring only type names the
    original program declares. -/
theorem TypeSpec.ProcWellTyped.program_congr_calls {P1 P2 : Program} {C : LContext CoreLParams}
    {ts : TypeScopes} {proc : Procedure}
    (hnames : ∀ n ∈ programNamesOfKind P2 .type, n ∈ programNamesOfKind P1 .type)
    (hagree : ProcedureCallsRel ProcSigInstOf P1 P2 (Procedure.calledProcedureNames proc))
    (h : ProcWellTyped P1 C ts proc) : ProcWellTyped P2 C ts proc where
  inputsNodup := h.inputsNodup
  outputsNodup := h.outputsNodup
  oldNamesFresh := h.oldNamesFresh
  typeArgsNodup := h.typeArgsNodup
  noUndeclaredVars := h.noUndeclaredVars
  declTyVarsBound := h.declTyVarsBound
  signatureWellKinded := h.signatureWellKinded
  modRights := h.modRights
  preconditionsTyped := h.preconditionsTyped
  postconditionsTyped := h.postconditionsTyped
  bodyTyped := by
    have hagree' : ProcedureCallsRel ProcSigInstOf P1 P2
        (Procedure.Body.calledProcedureNames proc.body) := by
      simpa using hagree
    exact ProcBodyWellTyped.program_congr_calls hnames hagree' h.bodyTyped

/-- Procedure body well-typedness does not depend on the context's `idents` field. -/
private theorem ProcBodyWellTyped.withIdents {C : Expression.TyContext} {j : Identifiers Unit}
    {P : Program} {ts : TypeScopes} {body : Procedure.Body}
    (h : ProcBodyWellTyped P { C with idents := j } ts body) : ProcBodyWellTyped P C ts body := by
  cases h with
  | structured ss C' ts' o hss =>
    obtain ⟨Cbase, -, hss'⟩ := TypeSpec.StatementsWellTyped.withIdents hss C j rfl
    exact .structured ss Cbase ts' o hss'
  | cfg c o => exact .cfg c o
  | abstract => exact .abstract

/-- Procedure well-typedness does not depend on the context's `idents` field. -/
theorem TypeSpec.ProcWellTyped.withIdents {C : Expression.TyContext} {j : Identifiers Unit}
    {P : Program} {ts : TypeScopes} {proc : Procedure}
    (h : ProcWellTyped P { C with idents := j } ts proc) : ProcWellTyped P C ts proc where
  inputsNodup := h.inputsNodup
  outputsNodup := h.outputsNodup
  oldNamesFresh := h.oldNamesFresh
  typeArgsNodup := h.typeArgsNodup
  noUndeclaredVars := h.noUndeclaredVars
  declTyVarsBound := h.declTyVarsBound
  signatureWellKinded := h.signatureWellKinded
  modRights := h.modRights
  preconditionsTyped := fun c hc => (h.preconditionsTyped c hc).withIdents
  postconditionsTyped := fun c hc => (h.postconditionsTyped c hc).withIdents
  bodyTyped := ProcBodyWellTyped.withIdents h.bodyTyped

/-! ## Properties of `Procedure.typeCheckCore` -/

/-- `Procedure.typeCheckCore` preserves `TEnvWF`. -/
private theorem Procedure.typeCheckCore_preserves_TEnvWF
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) :
    LExpr.TEnvWF (T := CoreLParams) Env' := by
  rw [(Procedure.typeCheckCore_env_eq_and_name_eq C Env Env' p proc proc' md h).1]
  exact h_env

/-- `Procedure.typeCheckCore` leaves the ambient typing context unchanged. -/
private theorem Procedure.typeCheckCore_context_eq
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    Env'.context = Env.context := by
  rw [(Procedure.typeCheckCore_env_eq_and_name_eq C Env Env' p proc proc' md h).1]

/-- Elaboration does not change which procedures a body can call. -/
private theorem Procedure.typeCheckCore_calledProcedureNames_eq
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckCore sc ps C Env p proc md tn = .ok (proc', Env')) :
    Procedure.calledProcedureNames proc' = Procedure.calledProcedureNames proc := by
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  simp only [Procedure.calledProcedureNames_eq_body]
  cases hpb : proc.body with
  | cfg c o =>
    obtain ⟨_, _, _, -, hout⟩ := run.bodyCfg c o hpb
    rw [hout, Procedure.Body.calledProcedureNames_cfg, Procedure.Body.calledProcedureNames_cfg]
  | abstract => rw [run.bodyAbstract hpb]
  | structured ss o =>
    obtain ⟨ssOut, EnvX, hB, -, hbody'⟩ := run.bodyStructured ss o hpb
    simp only [hbody', Procedure.Body.calledProcedureNames_structured]
    rw [mapStmtsTys_calledProcedureNames,
      Statement.typeCheck_calledProcedureNames_eq _ _ _ _ _ _ _ hB,
      skolemizeStmts_calledProcedureNames]

/-! ### Descending from a procedure's type-check to one of its call sites -/

/-- Every procedure a body checked in the skolemized parameter scope can call has a call site the
    command checker accepted, at the ambient aliases and at a known-types table with no
    program-declared name the skolemized ambient table lacks. -/
private theorem callSite_of_body_typeCheck
    (C : Expression.TyContext) (Env EnvX : Expression.TyEnv) (program : Program)
    (proc : Procedure) (σ : RigidNames) (sig : @LMonoTySignature Unit)
    (nm : String) (ssIn ssOut : List Statement)
    (hB : Statement.typeCheck (addSkolemTypes C σ)
            (Function.formalsEnv Env σ sig)
            program (some proc) (skolemizeStmts none σ ssIn) = .ok (ssOut, EnvX))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_sigFreeVars : ∀ v ∈ LMonoTys.freeVars sig.values, v ∈ σ.map Prod.fst)
    (hmem : nm ∈ Statements.calledProcedureNames ssIn) :
    CallSiteAgreeing program nm (addSkolemTypes C σ) Env := by
  obtain ⟨ssA, EnvA, CA, haux, -, -, -⟩ :=
    Statement.typeCheck_ok_inv _ _ _ _ _ _ _ hB
  have hwf := formalsEnv_TEnvWF Env σ sig h_env h_sigFreeVars
  have hcl := formalsEnv_typesClosed Env σ sig h_closed h_sigFreeVars
  have htys_ne := skolemScopeEnv_types_ne σ Env sig
  have hfac' := FactorySigWF.addSkolemTypes C σ h_fac
  obtain ⟨_, hgo⟩ := typeCheckAux_ok_inv haux
  refine (go_call_descent program (some proc) nm _ _ _ [] [] ssA EnvA CA hgo hwf hfac'
    htys_ne ?_).compose (formalsEnv_aliases Env σ sig) (fun _ _ hx => hx)
  rw [skolemizeStmts_calledProcedureNames]
  exact hmem

/-- Every procedure an accepted procedure can call has a call site the command checker accepted,
    at the caller's aliases and at a known-types table with no program-declared name the caller's
    skolemized table lacks. -/
private theorem Procedure.typeCheckCore_call_descent
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (program : Program)
    (proc proc' : Procedure) (md : MetaData Expression) (nm : String)
    (h : Procedure.typeCheckCore sc ps C Env program proc md tn = .ok (proc', Env'))
    (hdecl : proc.header.SigDeclared)
    (hcalled : nm ∈ Procedure.calledProcedureNames proc)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env) :
    CallSiteAgreeing program nm (addSkolemTypes C (Procedure.rigidNames sc ps C proc tn))
      Env := by
  have hσ := Procedure.typeCheckCore_signatureFreeVars_rigid C Env Env' program proc proc' md h
    hdecl h_env.aliasesWF
  simp only [Procedure.calledProcedureNames_eq_body] at hcalled
  obtain ⟨-, _, _, run⟩ := Procedure.typeCheckCore_ok_inv h
  cases hbody : proc.body with
  | cfg cfgBody o =>
    rw [hbody] at hcalled
    simp only [Procedure.Body.calledProcedureNames_cfg, List.not_mem_nil] at hcalled
  | abstract =>
    rw [hbody] at hcalled
    simp only [Procedure.Body.calledProcedureNames, List.not_mem_nil] at hcalled
  | structured ssIn o =>
    rw [hbody] at hcalled
    simp only [Procedure.Body.calledProcedureNames_structured] at hcalled
    obtain ⟨ssOut, EnvX, hB, -, -⟩ := run.bodyStructured ssIn o hbody
    exact callSite_of_body_typeCheck C Env EnvX program proc
      (Procedure.rigidNames sc ps C proc tn) _ nm ssIn ssOut hB h_env h_fac h_closed
      (bodySig_freeVars_mem _ _ hσ) hcalled

/-- If the checker accepts a caller, and a callee it calls in the form of a renaming of the
    callee's type parameters, the callee's returned signature is the renamed signature
    alias-resolved against the caller's aliases, when the callee's aliases freshly extend the
    caller's with program-declared names the caller does not register. -/
private theorem Procedure.typeCheckCore_forwardCalleeSigResolved
    {scE psE : Thunk (Std.HashSet String)} {tnE : Unit → List String} (program : Program)
    (Ccaller : Expression.TyContext) (Envcaller Envcaller' : Expression.TyEnv)
    (caller caller' : Procedure) (mdcaller : MetaData Expression)
    (Ccallee : Expression.TyContext) (Envcallee Envcallee' : Expression.TyEnv)
    (callee callee' : Procedure) (mdcallee : MetaData Expression)
    (calleeName : String) (ren : List (String × String))
    (hcaller : Procedure.typeCheckCore sc ps Ccaller Envcaller program caller mdcaller tn
                 = .ok (caller', Envcaller'))
    (hP : ∀ n ∈ Program.procSigTyNames program, n ∈ ps.get)
    (hcallerDecl : caller.header.SigDeclared)
    (hcalled : calleeName ∈ Procedure.calledProcedureNames caller)
    (hfind : Program.Procedure.find? program calleeName = some callee)
    (hren : TypeSpec.TyArgRenamingCore callee.header.typeArgs callee.mentionedTyVars ren)
    (hcallee : Procedure.typeCheckCore scE psE Ccallee Envcallee program
                 (callee.renameTypeArgs ren) mdcallee tnE = .ok (callee', Envcallee'))
    (hgrow : TypeAlias.FreshExtension Envcaller.context.aliases Envcallee.context.aliases)
    (hnoCalleeOnlyAliasIsCallerKnownType : ∀ al ∈ Envcallee.context.aliases,
       al ∉ Envcaller.context.aliases →
       Ccaller.knownTypes.containsName al.name = false)
    (hcalleeOnlyAliasDeclared : ∀ al ∈ Envcallee.context.aliases,
       al ∉ Envcaller.context.aliases → DeclaredProgramName program al.name)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Envcaller)
    (h_fac : FactorySigWF Ccaller.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Envcaller) :
    ProcSigResolved Envcaller.context.aliases (callee.renameTypeArgs ren) callee' := by
  obtain ⟨Ccall, Envcall, callArgs, mdc, tyArgs, rc, hcall, halias, hkt⟩ :=
    Procedure.typeCheckCore_call_descent Ccaller Envcaller Envcaller' program caller caller'
        mdcaller
      calleeName hcaller hcallerDecl hcalled h_env h_fac h_closed
  obtain ⟨S, EnvI, EnvR, rtys, hSftvar, hctxI, hres, hknown⟩ :=
    Statement.typeCheckCmd_call_sigResolved Ccall Envcall program calleeName callArgs mdc rc
      callee hcall hfind
  have haliasI : EnvI.context.aliases = Envcaller.context.aliases := by
    rw [hctxI]; exact halias
  rw [List.map_append] at hres
  obtain ⟨insCaller, outsCaller, hinsCaller, houtsCaller, hrtys⟩ :=
    LMonoTys.resolveAliases_append_inv _ _ EnvI EnvR rtys hres
  have hknownIns : ∀ mty ∈ insCaller, isInstanceOfKnownType mty Ccall = true := by
    intro mty hmty
    rw [hrtys] at hknown
    exact hknown mty (List.mem_append_left _ hmty)
  have hknownOuts : ∀ mty ∈ outsCaller, isInstanceOfKnownType mty Ccall = true := by
    intro mty hmty
    rw [hrtys] at hknown
    exact hknown mty (List.mem_append_right _ hmty)
  obtain ⟨hcalleeIns, hcalleeOuts⟩ :=
    Procedure.typeCheckCore_resolveAliases Ccallee Envcallee Envcallee' program _ callee'
      mdcallee hcallee
  have haWF : TContext.AliasesWF EnvI.context := by
    intro a ha
    rw [haliasI] at ha
    exact h_env.aliasesWF.mem a ha
  have hext : TypeAlias.FreshExtension EnvI.context.aliases Envcallee.context.aliases := by
    rw [haliasI]; exact hgrow
  have hnotSig : ∀ q ∈ Procedure.rigidNames sc ps Ccaller caller tn,
      ∀ ty ∈ callee.header.inputs.values ++ callee.header.outputs.values,
        q.2 ∉ getTypeRefs ty := by
    obtain ⟨md, hmem, -⟩ := Program.Procedure.find?_mem_decls program calleeName callee hfind
    exact fun q hq => Procedure.rigidNames_not_programSigs sc ps Ccaller program caller tn hP q hq
      callee md hmem
  obtain ⟨hfst, hsnd, hren'⟩ := hren
  obtain ⟨hvIn, hvOut⟩ := Procedure.renameTypeArgs_values callee ren
  have hS' := Subst.afterRenaming_ftvar ren hSftvar
  have hback : ∀ tys : LMonoTys,
      (∀ ty ∈ tys, ty ∈ callee.header.inputs.values ++ callee.header.outputs.values) →
      (tys.map (LMonoTy.subst (Subst.ofRenaming ren))).map
          (LMonoTy.subst (Subst.afterRenaming S ren)) = tys.map (LMonoTy.subst S) := by
    intro tys hsub
    rw [List.map_map]
    refine List.map_congr_left fun t ht => ?_
    exact LMonoTy.subst_afterRenaming S ren hfst hsnd t fun p hp hv =>
      (hren' p hp).2 (Procedure.mem_mentionedTyVars_of_param (hsub t ht) _ hv)
  have hfresh : ∀ tys : LMonoTys,
      (∀ ty ∈ tys, ty ∈ callee.header.inputs.values ++ callee.header.outputs.values) →
      ∀ al ∈ Envcallee.context.aliases, al ∉ EnvI.context.aliases →
        al.name ∈ tys.flatMap getTypeRefs →
        KnownTypes.containsName Ccall.knownTypes al.name = false := by
    intro tys hsub al hal hnot hn
    rw [haliasI] at hnot
    obtain ⟨ty, hty, hnty⟩ := List.mem_flatMap.mp hn
    refine hkt al.name (hcalleeOnlyAliasDeclared al hal hnot) ?_
    exact addSkolemTypes_notContains_of_ne Ccaller _ al.name
      (fun q hq heq => hnotSig q hq ty (hsub ty hty) (heq ▸ hnty))
      (hnoCalleeOnlyAliasIsCallerKnownType al hal hnot)
  have hIns : LMonoTys.resolveAliases (callee.renameTypeArgs ren).header.inputs.values EnvI
      = .ok (callee'.header.inputs.values, EnvI) := by
    refine LMonoTys.resolveAliases_eq_of_FreshExtension_subst Ccall (Subst.afterRenaming S ren)
      (callee.renameTypeArgs ren).header.inputs.values EnvI Envcallee EnvI Envcallee insCaller
      callee'.header.inputs.values haWF hS' hext ?_ ?_ hcalleeIns hknownIns
    · rw [hvIn, flatMap_getTypeRefs_subst_of_ftvar (Subst.ofRenaming_ftvar ren)]
      exact hfresh _ fun _ hty => List.mem_append_left _ hty
    · rw [hvIn, hback _ fun _ hty => List.mem_append_left _ hty]
      exact hinsCaller
  have hOuts : LMonoTys.resolveAliases (callee.renameTypeArgs ren).header.outputs.values EnvI
      = .ok (callee'.header.outputs.values, EnvI) := by
    refine LMonoTys.resolveAliases_eq_of_FreshExtension_subst Ccall (Subst.afterRenaming S ren)
      (callee.renameTypeArgs ren).header.outputs.values EnvI Envcallee EnvI Envcallee outsCaller
      callee'.header.outputs.values haWF hS' hext ?_ ?_ hcalleeOuts hknownOuts
    · rw [hvOut, flatMap_getTypeRefs_subst_of_ftvar (Subst.ofRenaming_ftvar ren)]
      exact hfresh _ fun _ hty => List.mem_append_right _ hty
    · rw [hvOut, hback _ fun _ hty => List.mem_append_right _ hty]
      exact houtsCaller
  have hres : EnvI.context.resolveTy
      = ({ aliases := Envcaller.context.aliases } : TContext Unit).resolveTy :=
    TContext.resolveTy_congr (T := CoreLParams) haliasI
  refine ⟨(Procedure.typeCheckCore_typeArgs_eq Ccallee Envcallee Envcallee' program _ callee'
      mdcallee hcallee).symm,
    (Procedure.typeCheckCore_inputsKeys_eq Ccallee Envcallee Envcallee' program _ callee'
      mdcallee hcallee).symm,
    (Procedure.typeCheckCore_outputsKeys_eq Ccallee Envcallee Envcallee' program _ callee'
      mdcallee hcallee).symm, ?_, ?_⟩
  · rw [← hres]
    exact TContext.resolveTys_of_resolveAliases (T := CoreLParams) hIns
  · rw [← hres]
    exact TContext.resolveTys_of_resolveAliases (T := CoreLParams) hOuts

/-! ## The checker with reserved type parameters renamed

`Procedure.typeCheckIn` runs `Procedure.typeCheckCore` on the procedure with its reserved type
parameters renamed (`Procedure.renameReservedTypeArgs`). The lemmas below state properties of
`Procedure.typeCheckIn` for any name sets. -/

/-- A procedure `Procedure.typeCheckIn` accepts has distinct type parameters, declares every type
    variable of its signature and has no parameter named like a function. -/
private theorem Procedure.typeCheckIn_headerNames {C : Expression.TyContext}
    {Env Env' : Expression.TyEnv} {p : Program} {proc proc' : Procedure}
    {md : MetaData Expression}
    (h : Procedure.typeCheckIn sc ps C Env p proc md = .ok (proc', Env')) :
    proc.header.typeArgs.Nodup ∧ proc.header.SigDeclared ∧
      ∀ id ∈ proc.header.inputs.keys ++ proc.header.outputs.keys, id.name ∉ C.functions := by
  unfold Procedure.typeCheckIn at h
  obtain ⟨⟨⟩, hnames, -⟩ := (Except.bind_is_ok _ _ _).mp h
  obtain ⟨hnd, hdecl, hformals⟩ := checkSignatureNames_ok (Except.mapError_ok_h' hnames)
  refine ⟨hnd, fun v hv => hdecl v ?_, hformals⟩
  rw [LExpr.LMonoTys.freeVars_append]
  exact hv

/-- The procedure `Procedure.typeCheckIn` checks: `proc` with its reserved type parameters renamed
    to avoid the type variables of the substitution and of the scope. -/
abbrev Procedure.renamedForCheck (C : Expression.TyContext) (Env : Expression.TyEnv)
    (proc : Procedure) : Procedure :=
  proc.renameReservedTypeArgs (fun _ => Statement.substTyVars Env ++ scopeTyVars C Env)
    fun _ => procAnnotTys proc

/-- A procedure `Procedure.typeCheckIn` accepts has distinct type parameters, and the checker's
    renaming of them is a renaming of the procedure (`ProcAlphaVariant`) that captures no type
    variable of the context. -/
private theorem Procedure.typeCheckIn_alphaVariant {C : Expression.TyContext}
    {Env Env' : Expression.TyEnv} {p : Program} {proc proc' : Procedure}
    {md : MetaData Expression}
    (h : Procedure.typeCheckIn sc ps C Env p proc md = .ok (proc', Env')) :
    proc.header.typeArgs.Nodup ∧
      ProcAlphaVariant C Env.context proc
        (Procedure.renamedForCheck C Env proc) := by
  have hnd := (Procedure.typeCheckIn_headerNames h).1
  refine ⟨hnd, Procedure.renameReservedTypeArgs_alphaVariant _ proc hnd fun v hv => ?_⟩
  exact List.mem_append_right _ hv

/-- The renaming of the reserved type parameters of a procedure `Procedure.typeCheckIn` accepts
    has distinct type parameters, declares every type variable of its signature and has no
    parameter named like a function. -/
private theorem Procedure.typeCheckIn_renamed_headerNames {C : Expression.TyContext}
    {Env Env' : Expression.TyEnv} {p : Program} {proc proc' : Procedure}
    {md : MetaData Expression}
    (h : Procedure.typeCheckIn sc ps C Env p proc md = .ok (proc', Env')) :
    (Procedure.renamedForCheck C Env proc).header.typeArgs.Nodup ∧
      (Procedure.renamedForCheck C Env proc).header.SigDeclared ∧
      ∀ id ∈ (Procedure.renamedForCheck C Env proc).header.inputs.keys ++
          (Procedure.renamedForCheck C Env proc).header.outputs.keys,
        id.name ∉ C.functions := by
  obtain ⟨hnd, hdecl, hformals⟩ := Procedure.typeCheckIn_headerNames h
  obtain ⟨-, ren, hren, heq⟩ := Procedure.typeCheckIn_alphaVariant h
  obtain ⟨hnd', hdecl'⟩ := Procedure.renameTypeArgs_sigDeclared hren.1 hnd hdecl
  obtain ⟨-, hkIn, hkOut⟩ := Procedure.renameTypeArgs_names proc ren
  rw [heq]
  refine ⟨hnd', hdecl', ?_⟩
  rw [hkIn, hkOut]
  exact hformals

/-- The type parameters of a procedure `Procedure.typeCheckIn` accepts are distinct. -/
theorem Procedure.typeCheckIn_typeArgs_nodup {scope progSigs : Thunk (Std.HashSet String)}
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {p : Program}
    {proc proc' : Procedure} {md : MetaData Expression}
    (h : Procedure.typeCheckIn scope progSigs C Env p proc md = .ok (proc', Env')) :
    proc.header.typeArgs.Nodup :=
  (Procedure.typeCheckIn_alphaVariant h).1

/-- Every type name of a procedure with its reserved type parameters renamed is a type name of
    the procedure. -/
private theorem Procedure.mem_procTyNames_of_renamed (avoid : Unit → List String)
    (proc : Procedure) (annot : Unit → List LMonoTy) :
    ∀ n ∈ procTyNames (proc.renameReservedTypeArgs avoid annot)
        (procAnnotTys (proc.renameReservedTypeArgs avoid annot)),
      n ∈ procTyNames proc (procAnnotTys proc) := by
  intro n hn
  rw [procTyNames_renameReservedTypeArgs] at hn
  exact hn

/-- Input soundness for procedures checked against given name sets: a procedure
    `Procedure.typeCheckIn` accepts satisfies `ProcHasType` in the ambient context, when `scope`
    holds every type name in scope and `progSigs` every type name in the procedure signatures of
    the program. The environment is well formed with closed monotype schemes; no registered type
    is named like an alias; the factory's function signatures are well formed; every procedure
    signature of the program declares all its type variables as type parameters; and the
    substitution neither binds nor mentions the procedure's type parameters. -/
theorem Procedure.typeCheckIn_sound (scope progSigs : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckIn scope progSigs C Env p proc md = .ok (proc', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ scope.get)
    (hP : ∀ n ∈ Program.procSigTyNames p, n ∈ progSigs.get)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (hsigs : ProcSigsDeclared p)
    (hS : Subst.VarsAvoid Env.stateSubstInfo.subst proc.header.typeArgs) :
    ProcHasType p C Env.context proc := by
  have hSr : Subst.VarsAvoid Env.stateSubstInfo.subst
      (Procedure.renamedForCheck C Env proc).header.typeArgs := by
    intro v hv hmem
    rcases Procedure.renameReservedTypeArgs_typeArgs_mem _ proc _ v hmem with hin | hnot
    · exact hS v hv hin
    · rcases hv with hk | hf
      · exact hnot (List.mem_append_left _ (List.mem_append_left _ hk))
      · exact hnot (List.mem_append_left _ (List.mem_append_right _ hf))
  have htn := Procedure.mem_procTyNames_of_renamed
    (fun _ => Statement.substTyVars Env ++ scopeTyVars C Env) proc (fun _ => procAnnotTys proc)
  obtain ⟨hnd, hdecl, hformals⟩ := Procedure.typeCheckIn_renamed_headerNames h
  exact ⟨_, (Procedure.typeCheckIn_alphaVariant h).2,
    Procedure.typeCheckCore_sound C Env Env' p _ proc' md (Procedure.typeCheckIn_core_ok h) hcov
      htn hP hnd hdecl hformals h_env h_fac h_closed h_mono h_aliasNames hsigs hSr
      (Procedure.renameReservedTypeArgs_typeArgs_allowed _ proc _)⟩

/-- Input soundness for procedures: a procedure the checker accepts satisfies `ProcHasType` in
    the ambient context. The environment is well formed with closed monotype schemes; no
    registered type is named like an alias; the factory's function signatures are well formed;
    every procedure signature of the program declares all its type variables as type parameters;
    and the substitution neither binds nor mentions the procedure's type parameters. -/
theorem Procedure.typeCheck_sound
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env p proc md = .ok (proc', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (hsigs : ProcSigsDeclared p)
    (hS : Subst.VarsAvoid Env.stateSubstInfo.subst proc.header.typeArgs) :
    ProcHasType p C Env.context proc :=
  Procedure.typeCheckIn_sound _ _ C Env Env' p proc proc' md h (scopeTyNameThunk_cover C Env)
    (procSigTyNameThunk_cover p) h_env h_fac h_closed h_mono h_aliasNames hsigs hS

/-- Output soundness for procedures checked against given name sets: the procedure
    `Procedure.typeCheckIn` returns is well typed over the alias-resolved variable scopes,
    against the alias-resolved table and program, and its names are valid, when `scope` holds
    every type name in scope and `progSigs` every type name in the procedure signatures of the
    program. The environment is well formed with closed monotype schemes whose alias-resolved
    types are registered; no alias body mentions an alias, and no registered type is named like
    an alias; the factory's function signatures are well formed and built from registered types;
    and `arrow`, the type of every primitive literal and the range of the substitution are
    registered. -/
theorem Procedure.typeCheckIn_sound_output (scope progSigs : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckIn scope progSigs C Env p proc md = .ok (proc', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ scope.get)
    (hP : ∀ n ∈ Program.procSigTyNames p, n ∈ progSigs.get)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_mono : MonoScope (IDMeta := Unit) Env.context)
    (h_aliasNamesFresh : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (h_arrow : C.knownTypes["arrow"]? = some 2)
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty C.knownTypes = true)
    (h_substRange : Lambda.Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_known : AmbientTypesKnown C.knownTypes Env) :
    ProcWellTyped (p.resolveSigs Env.context.aliases) (C.resolveTable Env.context.aliases)
      Env.context.dealias.types proc' ∧
    ProcNamesWF (p.resolveSigs Env.context.aliases) (· ∈ C.functions) proc' :=
  have hnames := Procedure.typeCheckIn_renamed_headerNames h
  have htn := Procedure.mem_procTyNames_of_renamed
    (fun _ => Statement.substTyVars Env ++ scopeTyVars C Env) proc (fun _ => procAnnotTys proc)
  Procedure.typeCheckCore_sound_output C Env Env' p _ proc' md (Procedure.typeCheckIn_core_ok h)
    hcov htn hP hnames.1 hnames.2.1 hnames.2.2 h_env h_fac h_resolved h_mono h_aliasNamesFresh
    h_sigsFixed h_arrow h_lit h_substRange h_closed h_known

/-- Output soundness for procedures: the returned procedure is well typed over the alias-resolved
    variable scopes, against the alias-resolved table and program, and its names are valid.
    The environment is well formed with
    closed monotype schemes whose alias-resolved types are registered; no alias body mentions
    an alias, and no registered type is named like an alias; the factory's function signatures
    are well formed and built from registered types; and `arrow`, the type of every primitive
    literal and the range of the substitution are registered. -/
theorem Procedure.typeCheck_sound_output
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env p proc md = .ok (proc', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_mono : MonoScope (IDMeta := Unit) Env.context)
    (h_aliasNamesFresh : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (h_arrow : C.knownTypes["arrow"]? = some 2)
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty C.knownTypes = true)
    (h_substRange : Lambda.Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_known : AmbientTypesKnown C.knownTypes Env) :
    ProcWellTyped (p.resolveSigs Env.context.aliases) (C.resolveTable Env.context.aliases)
      Env.context.dealias.types proc' ∧
    ProcNamesWF (p.resolveSigs Env.context.aliases) (· ∈ C.functions) proc' :=
  Procedure.typeCheckIn_sound_output _ _ C Env Env' p proc proc' md h
    (scopeTyNameThunk_cover C Env) (procSigTyNameThunk_cover p) h_env h_fac h_resolved h_mono
    h_aliasNamesFresh h_sigsFixed h_arrow h_lit h_substRange h_closed h_known

/-- A procedure check keeps every type the substitution binds an instance of
    a type `ks` registers. -/
theorem Procedure.typeCheckIn_RangeKnown (scope progSigs : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression) (ks : Lambda.KnownTypes)
    (h : Procedure.typeCheckIn scope progSigs C Env p proc md = .ok (proc', Env'))
    (hS : Lambda.Subst.RangeKnown Env.stateSubstInfo.subst ks) :
    Lambda.Subst.RangeKnown Env'.stateSubstInfo.subst ks :=
  Procedure.typeCheckCore_RangeKnown C Env Env' p _ proc' md ks
    (Procedure.typeCheckIn_core_ok h) hS

/-- A procedure check keeps the procedures the procedure calls. -/
theorem Procedure.typeCheckIn_calledProcedureNames_eq (scope progSigs : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckIn scope progSigs C Env p proc md = .ok (proc', Env')) :
    Procedure.calledProcedureNames proc' = Procedure.calledProcedureNames proc := by
  rw [Procedure.typeCheckCore_calledProcedureNames_eq C Env Env' p _ proc' md
    (Procedure.typeCheckIn_core_ok h), Procedure.renameReservedTypeArgs_eq]
  exact (Procedure.renameTypeArgs_body proc _).1

/-- `callError?` accepts, against the program the procedure is checked in,
    every call in a CFG body that `Procedure.typeCheckIn` returns. -/
theorem Procedure.typeCheckIn_cfgCallsChecked {scope progSigs : Thunk (Std.HashSet String)}
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {p : Program}
    {proc proc' : Procedure} {md : MetaData Expression} {g : DetCFG} {o : Bool}
    (h : Procedure.typeCheckIn scope progSigs C Env p proc md = .ok (proc', Env'))
    (hg : proc'.body = .cfg g o) :
    ∀ cs ∈ proc'.callSites, callError? p cs.procName cs.args = none :=
  Procedure.typeCheckCore_cfgCallsChecked (Procedure.typeCheckIn_core_ok h) hg

/-- A procedure check keeps the variable context. -/
theorem Procedure.typeCheckIn_context_eq (scope progSigs : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckIn scope progSigs C Env p proc md = .ok (proc', Env')) :
    Env'.context = Env.context :=
  Procedure.typeCheckCore_context_eq C Env Env' p _ proc' md (Procedure.typeCheckIn_core_ok h)

/-- On success `Procedure.typeCheckIn` returns the incoming environment and
    keeps the procedure name. -/
theorem Procedure.typeCheckIn_env_eq_and_name_eq (scope progSigs : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckIn scope progSigs C Env p proc md = .ok (proc', Env')) :
    Env' = Env ∧ proc'.header.name = proc.header.name := by
  obtain ⟨henv, hname⟩ :=
    Procedure.typeCheckCore_env_eq_and_name_eq C Env Env' p _ proc' md
      (Procedure.typeCheckIn_core_ok h)
  rw [Procedure.renameReservedTypeArgs_eq] at hname
  exact ⟨henv, hname.trans (Procedure.renameTypeArgs_names proc _).1⟩

/-- If `Procedure.typeCheckIn` succeeds, every type variable of the
    procedure's declared signature is one of its type parameters. -/
theorem Procedure.typeCheckIn_noUndeclaredVars (scope progSigs : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckIn scope progSigs C Env p proc md = .ok (proc', Env')) :
    ∀ v, v ∈ LMonoTys.freeVars proc.header.inputs.values ++
            LMonoTys.freeVars proc.header.outputs.values →
        v ∈ proc.header.typeArgs :=
  (Procedure.typeCheckIn_headerNames h).2.1

/-- Every parameter type of the procedure `Procedure.typeCheckIn` returns is
    an instance of a registered type. -/
theorem Procedure.typeCheckIn_paramTypes_knownInstance
    (scope progSigs : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckIn scope progSigs C Env p proc md = .ok (proc', Env')) :
    ∀ mty ∈ proc'.header.inputs.values ++ proc'.header.outputs.values,
      LMonoTy.knownInstance mty C.knownTypes = true :=
  Procedure.typeCheckCore_paramTypes_knownInstance C Env Env' p _ proc' md
    (Procedure.typeCheckIn_core_ok h)

/-- A procedure check keeps the environment well formed. -/
theorem Procedure.typeCheckIn_preserves_TEnvWF (scope progSigs : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckIn scope progSigs C Env p proc md = .ok (proc', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) :
    LExpr.TEnvWF (T := CoreLParams) Env' :=
  Procedure.typeCheckCore_preserves_TEnvWF C Env Env' p _ proc' md
    (Procedure.typeCheckIn_core_ok h) h_env

/-- The procedure `Procedure.typeCheckIn` returns has the signature of the
    checker's renaming of the declared procedure, alias-resolved against the incoming scope. -/
theorem Procedure.typeCheckIn_sigResolved (scope progSigs : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckIn scope progSigs C Env p proc md = .ok (proc', Env')) :
    ProcSigResolved Env.context.aliases
      (Procedure.renamedForCheck C Env proc) proc' :=
  Procedure.typeCheckCore_sigResolved C Env Env' p _ proc' md (Procedure.typeCheckIn_core_ok h)

/-- If the checker accepts a caller and a callee it calls, each against its own name sets, the
    callee's returned signature is the signature of the checker's renaming of the callee,
    alias-resolved against the caller's aliases, when the caller's `progSigsCaller` holds every
    type name in the procedure signatures of the program and the callee's aliases freshly extend
    the caller's with program-declared names the caller does not register. -/
theorem Procedure.typeCheckIn_forwardCalleeSigResolved
    (scopeCaller progSigsCaller scopeCallee progSigsCallee : Thunk (Std.HashSet String))
    (program : Program)
    (Ccaller : Expression.TyContext) (Envcaller Envcaller' : Expression.TyEnv)
    (caller caller' : Procedure) (mdcaller : MetaData Expression)
    (Ccallee : Expression.TyContext) (Envcallee Envcallee' : Expression.TyEnv)
    (callee callee' : Procedure) (mdcallee : MetaData Expression)
    (calleeName : String)
    (hcaller : Procedure.typeCheckIn scopeCaller progSigsCaller Ccaller Envcaller program caller
                 mdcaller = .ok (caller', Envcaller'))
    (hP : ∀ n ∈ Program.procSigTyNames program, n ∈ progSigsCaller.get)
    (hcalled : calleeName ∈ Procedure.calledProcedureNames caller)
    (hfind : Program.Procedure.find? program calleeName = some callee)
    (hcallee : Procedure.typeCheckIn scopeCallee progSigsCallee Ccallee Envcallee program callee
                 mdcallee = .ok (callee', Envcallee'))
    (hgrow : TypeAlias.FreshExtension Envcaller.context.aliases Envcallee.context.aliases)
    (hnoCalleeOnlyAliasIsCallerKnownType : ∀ al ∈ Envcallee.context.aliases,
       al ∉ Envcaller.context.aliases →
       Ccaller.knownTypes.containsName al.name = false)
    (hcalleeOnlyAliasDeclared : ∀ al ∈ Envcallee.context.aliases,
       al ∉ Envcaller.context.aliases → DeclaredProgramName program al.name)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Envcaller)
    (h_fac : FactorySigWF Ccaller.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Envcaller) :
    ProcSigResolved Envcaller.context.aliases
      (callee.renameReservedTypeArgs
        (fun _ => Statement.substTyVars Envcallee ++ scopeTyVars Ccallee Envcallee)
        fun _ => procAnnotTys callee) callee' := by
  obtain ⟨-, ren, hren, heq⟩ := Procedure.typeCheckIn_alphaVariant hcallee
  have hcalleeCore := Procedure.typeCheckIn_core_ok hcallee
  unfold Procedure.renamedForCheck at heq
  rw [heq] at hcalleeCore ⊢
  have hcalled' : calleeName ∈ Procedure.calledProcedureNames
      (caller.renameReservedTypeArgs
        (fun _ => Statement.substTyVars Envcaller ++ scopeTyVars Ccaller Envcaller)
        fun _ => procAnnotTys caller) := by
    rw [Procedure.renameReservedTypeArgs_eq, (Procedure.renameTypeArgs_body caller _).1]
    exact hcalled
  exact Procedure.typeCheckCore_forwardCalleeSigResolved program Ccaller Envcaller Envcaller'
    _ caller' mdcaller Ccallee Envcallee Envcallee' callee callee' mdcallee calleeName ren
    (Procedure.typeCheckIn_core_ok hcaller) hP
    (Procedure.typeCheckIn_renamed_headerNames hcaller).2.1
    hcalled' hfind hren.1 hcalleeCore hgrow
    hnoCalleeOnlyAliasIsCallerKnownType hcalleeOnlyAliasDeclared h_env h_fac h_closed

end Core

end -- public section
