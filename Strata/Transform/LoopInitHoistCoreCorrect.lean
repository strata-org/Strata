/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.LoopInitHoistCorrect
public import Strata.DL.Imperative.BigStep.Sem
public import Strata.DL.Imperative.BigStep.SemProps
import Strata.DL.Imperative.Logic.TraceRelationsProps
public import Strata.DL.Imperative.Logic.TraceInterpProps
public import Strata.Transform.SpecificationProps
public import Strata.Languages.Core.StmtExtendCallBridgeProps
public import Strata.Languages.Core.ProgramFactProps
import all Strata.Transform.LoopInitHoist
import all Strata.Languages.Core.PipelinePhase

/-! # Core loop-init-hoist correctness

This module transports the generic loop-init-hoist trace simulation across the
call-free Core command bridge. `EventArg.WithWF`
carries evaluator-stability evidence. The main Core results are
`Core.LoopInitHoist.overapproximatesTraces`, `evalInterp_stableUnder`, and
`assertValid`.

`loopInitHoistPipelinePhase_ok` identifies the phase transform, and
`loopInitHoistPipelinePhase_over` connects a successful phase run to the
rewritten procedure and the body-level validity result.
-/

public section

namespace Core.LoopInitHoist

open Core Core.Logic Imperative Imperative.Logic Strata.Logic
open Imperative.Specification Imperative.Specification.Transform

variable (π : String → Option Procedure)

/-- The Core-facing loop-init-hoist wrapper overapproximates the source Core
block event language up to `Trace.WithWF` matching and final-store agreement. -/
theorem overapproximatesTraces (params : InitEnvWFParams) :
    OverapproximatesTracesUptoWhen
      (Trace.WithWF (P := Expression) (EventArg.ExtendsEnv (fun _ => True)))
      (· = ·)
      (EnvStoreAgree (P := Expression))
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      Core.hoistLoopPrefixInits
      (fun ss =>
        Statements.noCalls ss = Bool.true
        ∧ Block.uniqueInits (C := Command) ss)
      params params := by
  intro ss out ht hpre ρ₀ ρ₀' hEq hwf
  subst hEq
  obtain ⟨hnc, huniq⟩ := hpre
  obtain ⟨bs, hproj, hemb⟩ := Core.noCalls_projectStmts hnc
  have huniqBase : Block.uniqueInits (C := Cmd Expression) bs :=
    (Imperative.embedStmts_uniqueInits bs).mp (by rwa [hemb])
  rw [Core.hoistLoopPrefixInits_eq_some hproj] at ht
  obtain rfl := Option.some.inj ht
  change Core.Logic.BlockInitEnvWF params ss ρ₀ at hwf
  have hbaseWF : Imperative.Logic.BlockInitEnvWF
      (P := Expression) (CmdT := Cmd Expression) params bs ρ₀ :=
    Core.Logic.BlockInitEnvWF.toImperativeProject hwf hproj
  obtain ⟨h_prefix, h_term, h_exit, _⟩ :=
    Imperative.LoopInitHoist.overapproximatesTraces (P := Expression)
      params bs (Imperative.Block.hoistLoopPrefixInits bs) rfl
      huniqBase ρ₀ ρ₀ rfl hbaseWF
  have hsrc : (EventLang.coreBlock π).stmtCfg ss ρ₀ =
      embedConfig (.stmts bs ρ₀) := by
    simp only [EventLang.coreBlock, EventLang.imperativeBlockE, embedConfig, hemb]
  have htgt : (EventLang.coreBlock π).stmtCfg
      (embedStmts (Imperative.Block.hoistLoopPrefixInits bs)) ρ₀ =
      embedConfig (.stmts (Imperative.Block.hoistLoopPrefixInits bs) ρ₀) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cfg trace hrun
    rw [hsrc] at hrun
    obtain ⟨c', rfl, hbase⟩ :=
      Imperative.embedConfig_stepStarE_rev π (c := .stmts bs ρ₀) hrun
    obtain ⟨cfgb, trace', hrunb, htr⟩ := h_prefix c' trace hbase
    exact ⟨embedConfig cfgb, trace', by
      rw [htgt]
      exact Imperative.embedConfig_stepStarE π hrunb, htr⟩
  · intro ρ' trace hrun
    rw [hsrc] at hrun
    obtain ⟨c', hc', hbase⟩ :=
      Imperative.embedConfig_stepStarE_rev π (c := .stmts bs ρ₀) hrun
    rw [show (EventLang.coreBlock π).terminalCfg ρ' =
      embedConfig (.terminal ρ') from rfl] at hc'
    obtain rfl := Imperative.embedConfig_injective hc'
    obtain ⟨ρ'', trace', hrunb, hout, htr⟩ := h_term ρ' trace hbase
    exact ⟨ρ'', trace', by
      rw [htgt]
      exact Imperative.embedConfig_stepStarE π hrunb, hout, htr⟩
  · intro lbl ρ' trace hrun
    rw [hsrc] at hrun
    obtain ⟨c', hc', hbase⟩ :=
      Imperative.embedConfig_stepStarE_rev π (c := .stmts bs ρ₀) hrun
    rw [show (EventLang.coreBlock π).exitingCfg lbl ρ' =
      embedConfig (.exiting lbl ρ') from rfl] at hc'
    obtain rfl := Imperative.embedConfig_injective hc'
    obtain ⟨ρ'', trace', hrunb, hout, htr⟩ := h_exit lbl ρ' trace hbase
    exact ⟨ρ'', trace', by
      rw [htgt]
      exact Imperative.embedConfig_stepStarE π hrunb, hout, htr⟩
  · exact Core.LoopInitHoist.blockInitEnvWF hwf hproj
      (Core.hoistLoopPrefixInits_eq_some hproj) huniq

/-- Evaluation to `true` is stable under loop-init-hoist event matching. -/
theorem evalInterp_stableUnder :
    ConditionInterp.StableUnder (P := Expression)
      (Imperative.BigStep.evalInterp : ConditionInterp Expression)
      (EventArg.WithWF (P := Expression) (EventArg.ExtendsEnv (fun _ => True))) :=
  Imperative.BigStep.evalInterp_stableUnder

/-- Assertion validity for a successfully hoisted Core block reflects to its
source when condition truth is stable under loop-init-hoist event matching.
`evalInterp_stableUnder` supplies this for `evalInterp`. -/
theorem assertValid (params : InitEnvWFParams)
    {ss out : Statements}
    (htransform : Core.hoistLoopPrefixInits ss = some out)
    (hpre :
      Statements.noCalls ss = Bool.true
      ∧ Block.uniqueInits (C := Command) ss)
    {I : ConditionInterp Expression}
    (hstable : I.StableUnder
      (EventArg.WithWF (P := Expression) (EventArg.ExtendsEnv (fun _ => True))))
    {aid : AssertId Expression}
    (hvalid : AssertValidOnTracesWhen (EventLang.coreBlock π) I
      (Core.Logic.BlockInitEnvWF params out) out aid) :
    AssertValidOnTracesWhen (EventLang.coreBlock π) I
      (Core.Logic.BlockInitEnvWF params ss) ss aid :=
  overapproximatesTracesUptoWhen_assertValid I _ _
    (EventLang.coreBlock π) (EventLang.coreBlock π)
    Core.hoistLoopPrefixInits
    (fun block =>
      Statements.noCalls block = Bool.true
      ∧ Block.uniqueInits (C := Command) block)
    params params
    (fun _ _ htrace aid =>
      Trace.WithWF.assertionValidFrom_reflect hstable htrace aid)
    (overapproximatesTraces π params) htransform hpre hvalid

/-- Running the loop-init-hoist pipeline phase runs its program transform. -/
theorem loopInitHoistPipelinePhase_ok (program : Program)
    (s : Transform.CoreTransformState) :
    (loopInitHoistPipelinePhase.transform program).run s =
      (loopInitHoist program).run s := by
  unfold loopInitHoistPipelinePhase modelPreservingPipelinePhase
  rfl

/-- A successful declaration-list rewrite contains the hoisted declaration and
change flag for every structured procedure whose body hoists successfully. -/
private theorem loopInitHoistDecls_proc_mem
    {decls : List Decl} {results : List (Decl × Bool)}
    {q : Procedure} {md : MetaData Expression} {ss ss' : Statements}
    (h : decls.mapM loopInitHoistDecl = .ok results)
    (hq : Decl.proc q md ∈ decls) (hb : q.body = .structured ss)
    (hss : Core.hoistLoopPrefixInits ss = some ss') :
    (Decl.proc { q with body := .structured ss' } md, ss' != ss) ∈ results := by
  induction decls generalizing results with
  | nil => simp at hq
  | cons d rest ih =>
    rcases List.mem_cons.mp hq with hhead | htail
    · subst d
      simp only [List.mapM_cons, loopInitHoistDecl, hb, hss, bind, Except.bind,
        pure, Except.pure] at h
      repeat' first | split at h | simp_all
      subst results
      simp_all
    · cases d <;>
        simp only [List.mapM_cons, loopInitHoistDecl, bind, Except.bind,
          pure, Except.pure] at h
      all_goals
        repeat' first | split at h | simp_all only [Except.ok.injEq, forall_const,
          forall_eq', List.mem_cons, reduceCtorEq, or_true, Decl.proc.injEq]
        subst results
        exact List.mem_cons_of_mem _ ih

/-- A successful loop-init-hoist run places each hoisted structured procedure in
the output program. -/
private theorem loopInitHoist_proc_mem
    {program out : Program} {s s' : Transform.CoreTransformState} {changed : Bool}
    {q : Procedure} {md : MetaData Expression} {ss ss' : Statements}
    (h : (loopInitHoist program).run s = (.ok (changed, out), s'))
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss)
    (hss : Core.hoistLoopPrefixInits ss = some ss') :
    Decl.proc { q with body := .structured ss' } md ∈ out.decls := by
  cases hmap : program.decls.mapM loopInitHoistDecl with
  | error error =>
      simp only [loopInitHoist, hmap, liftExcept, pure] at h
      cases h
  | ok results =>
      simp only [loopInitHoist, hmap, liftExcept, pure] at h
      injection h with hresult _
      injection hresult with hp
      injection hp with _ hout
      rw [← hout]
      exact List.mem_map.mpr
        ⟨_, loopInitHoistDecls_proc_mem hmap hq hb hss, rfl⟩

/-- A successful loop-init-hoist phase run on a program satisfying the phase's
`noCalls` and `uniqueInits` requirements hoists every structured procedure body
into the output program, and assertion validity of the hoisted body reflects to
the source body. -/
theorem loopInitHoistPipelinePhase_over
    {program out : Program} {s s' : Transform.CoreTransformState} {changed : Bool}
    (hrun : (loopInitHoistPipelinePhase.transform program).run s =
      (.ok (changed, out), s'))
    (hnoCallsProgram : ProgramFact.noCalls.holds program)
    (huniqProgram : ProgramFact.uniqueInits.holds program)
    {q : Procedure} {md : MetaData Expression} {ss : Statements}
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss) :
    ∃ ss', Core.hoistLoopPrefixInits ss = some ss'
      ∧ Decl.proc { q with body := .structured ss' } md ∈ out.decls
      ∧ ∀ (params : InitEnvWFParams) {I : ConditionInterp Expression},
        I.StableUnder
          (EventArg.WithWF (P := Expression) (EventArg.ExtendsEnv (fun _ => True))) →
      ∀ {aid : AssertId Expression},
        AssertValidOnTracesWhen (EventLang.coreBlock π) I
          (Core.Logic.BlockInitEnvWF params ss') ss' aid →
        AssertValidOnTracesWhen (EventLang.coreBlock π) I
          (Core.Logic.BlockInitEnvWF params ss) ss aid := by
  have htransform : (loopInitHoist program).run s = (.ok (changed, out), s') := by
    rw [← loopInitHoistPipelinePhase_ok program s]
    exact hrun
  have hnc := ProgramFact.noCalls_of_program hnoCallsProgram hq hb
  obtain ⟨bs, hproj, _⟩ := Core.noCalls_projectStmts hnc
  have hss := Core.hoistLoopPrefixInits_eq_some hproj
  refine ⟨_, hss, loopInitHoist_proc_mem htransform hq hb hss, ?_⟩
  intro params I hstable aid hvalid
  exact assertValid π params hss
    ⟨hnc, ProgramFact.uniqueInits_of_program huniqProgram hq hb⟩ hstable hvalid

end Core.LoopInitHoist

end -- public section
