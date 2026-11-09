/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.StructuredToUnstructuredCorrect
public import Strata.DL.Imperative.BigStep.Sem
public import Strata.DL.Imperative.BigStep.SemProps
import Strata.DL.Imperative.Logic.TraceRelationsProps
public import Strata.DL.Imperative.Logic.TraceInterpProps
public import Strata.Transform.SpecificationProps
public import Strata.Languages.Core.StmtExtendCallBridgeProps
import all Strata.Transform.StructuredToUnstructured
import Strata.Transform.StructuredToUnstructuredProps
public import Strata.Languages.Core.ProgramFactProps
import all Strata.Languages.Core.PipelinePhase

/-! # Core structured-to-unstructured correctness

This module transports the generic structured-to-CFG trace simulation across
the call-free Core command bridge. The source gate is
`base.extend prefixesReserved` and the target gate is `base`.

Key results:
  * `Core.StructuredToUnstructured.overapproximatesTraces` — `Core.stmtsToCFG`
    overapproximates the Core block event language by the Core CFG event
    language, up to `Trace.WithWF` matching and `EnvStoreAgree`.
  * `Core.StructuredToUnstructured.assertValid` — assertion validity on the
    lowered CFG reflects to its source for interpretations stable under
    `EventArg.WithWF`; `evalInterp_stableUnder` supplies this for `evalInterp`.
  * `structuredToUnstructuredPipelinePhase_ok` identifies the phase transform,
    and `structuredToUnstructuredPipelinePhase_over` connects a successful
    phase run and its fact-tracked `requires` to the lowered procedure and the
    body-level validity result; the run's own shape checks supply the
    remaining source conditions.
-/

public section

namespace Core.StructuredToUnstructured

open Core Core.Logic Imperative Imperative.Logic Strata.Logic
open Imperative.StructuredToUnstructured
open Imperative.Specification Imperative.Specification.Transform

variable (π : String → Option Procedure)

/-- **`stmtsToCFG` trace overapproximation over Core.** `stmtsToCFG`
overapproximates the source Core block event language by the Core CFG event
language, up to `Trace.WithWF` matching on traces and `EnvStoreAgree` on final
environments. The source gate `base.extend prefixesReserved` reserves every
generated-label prefix in addition to the base prefixes, and the target gate is
`base`; both gates retain the base declared functions. -/
theorem overapproximatesTraces (base : InitEnvWFParams) :
    OverapproximatesTracesUptoWhen
      (Trace.WithWF (P := Expression) (EventArg.ExtendsEnv (fun _ => True)))
      (· = ·)
      (EnvStoreAgree (P := Expression))
      (EventLang.coreBlock π) (EventLang.coreCFG π)
      Core.stmtsToCFG
      (fun ss =>
        Statements.noCalls ss = Bool.true
        ∧ Block.noNondetGuards ss = Bool.true
        ∧ Block.uniqueInits (C := Command) ss
        ∧ Block.loopBodyNoInits (C := Command) ss = Bool.true
        ∧ Block.loopHasNoInvariants ss = Bool.true
        ∧ Block.noMeasureLoops ss = Bool.true
        ∧ Block.exitsCoveredByBlocks (CmdT := Command) [] ss
        ∧ Block.userLabelsShapeNodup (C := Command) ss
        ∧ (∀ name : String, Imperative.StructuredToUnstructured.isGeneratedName name →
            HasIdent.ident (P := Expression) name ∉
              Block.initVars (C := Command) ss))
      (base.extend prefixesReserved) base := by
  intro ss out ht hpre ρ₀ ρ₀' hEq hwf
  subst hEq
  obtain ⟨hnc, hngCore, huniqCore, hlbniCore, hlhniCore, hnmlCore,
    hcovCore, hlabelsCore, hs2uCore⟩ := hpre
  obtain ⟨bs, hproj, hemb⟩ := Core.noCalls_projectStmts hnc
  have hng : Block.noNondetGuards bs = Bool.true := by
    rw [← Imperative.embedStmts_noNondetGuards bs, hemb]
    exact hngCore
  have huniq : Block.uniqueInits (C := Cmd Expression) bs :=
    (Imperative.embedStmts_uniqueInits bs).mp (by rwa [hemb])
  have hlbni : Block.loopBodyNoInits bs = Bool.true := by
    rw [← Imperative.embedStmts_loopBodyNoInits bs, hemb]
    exact hlbniCore
  have hlhni : Block.loopHasNoInvariants bs = Bool.true := by
    rw [← Imperative.embedStmts_loopHasNoInvariants bs, hemb]
    exact hlhniCore
  have hnml : Block.noMeasureLoops bs = Bool.true := by
    rw [← Imperative.embedStmts_noMeasureLoops bs, hemb]
    exact hnmlCore
  have hcov : Block.exitsCoveredByBlocks (CmdT := Cmd Expression) [] bs :=
    (Imperative.embedStmts_exitsCoveredByBlocks [] bs).mp (by rwa [hemb])
  have hlabels : Block.userLabelsShapeNodup (C := Cmd Expression) bs :=
    (Imperative.embedStmts_userLabelsShapeNodup bs).mp (by rwa [hemb])
  have hs2u : ∀ name : String, Imperative.StructuredToUnstructured.isGeneratedName name →
      HasIdent.ident (P := Expression) name ∉ Block.initVars (C := Cmd Expression) bs := by
    intro name hkindName hmem
    exact hs2uCore name hkindName (by
      rw [← hemb, Block.initVars, Imperative.embedStmts_definedVars]
      exact hmem)
  have hout_eq : out = Imperative.embedCFG (Imperative.stmtsToCFG bs) := by
    rw [Core.stmtsToCFG_eq_some hproj] at ht; exact (Option.some.inj ht).symm
  change Core.Logic.BlockInitEnvWF (base.extend prefixesReserved) ss ρ₀ at hwf
  have hbaseWF : Imperative.Logic.BlockInitEnvWF
      (P := Expression) (CmdT := Cmd Expression)
      (base.extend prefixesReserved) bs ρ₀ :=
    Core.Logic.BlockInitEnvWF.toImperativeProject hwf hproj
  obtain ⟨h_prefix, h_term, h_exit, _⟩ :=
    Imperative.StructuredToUnstructured.overapproximatesTraces
      (P := Expression) base
      bs (Imperative.stmtsToCFG bs) rfl
      ⟨hng, huniq, hlbni, hlhni, hnml, hcov, hlabels, hs2u⟩ ρ₀ ρ₀ rfl hbaseWF
  have hsrc : (EventLang.coreBlock π).stmtCfg ss ρ₀ = embedConfig (.stmts bs ρ₀) := by
    simp only [EventLang.coreBlock, EventLang.imperativeBlockE, embedConfig, hemb]
  have htgt : (EventLang.coreCFG π).stmtCfg out ρ₀
      = Imperative.embedCFGConfig
          (.atBlock (Imperative.stmtsToCFG bs) (Imperative.stmtsToCFG bs).entry ρ₀) := by
    rw [hout_eq]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cfg trace hrun
    rw [hsrc] at hrun
    obtain ⟨c', rfl, hbase⟩ :=
      Imperative.embedConfig_stepStarE_rev π (c := .stmts bs ρ₀) hrun
    obtain ⟨cfgb, trace', hrunb, htr⟩ := h_prefix c' trace hbase
    exact ⟨Imperative.embedCFGConfig cfgb, trace',
      by rw [htgt]; exact Imperative.embedCFGConfig_stepCFGStarE π hrunb, htr⟩
  · intro ρ' trace hrun
    rw [hsrc] at hrun
    obtain ⟨c', hc', hbase⟩ :=
      Imperative.embedConfig_stepStarE_rev π (c := .stmts bs ρ₀) hrun
    rw [show (EventLang.coreBlock π).terminalCfg ρ' = embedConfig (.terminal ρ') from rfl] at hc'
    obtain rfl := Imperative.embedConfig_injective hc'
    obtain ⟨ρ'', trace', hrunb, hout, htr⟩ := h_term ρ' trace hbase
    exact ⟨ρ'', trace',
      by rw [htgt]; exact Imperative.embedCFGConfig_stepCFGStarE π hrunb, hout, htr⟩
  · intro lbl ρ' trace hrun
    rw [hsrc] at hrun
    obtain ⟨c', hc', hbase⟩ :=
      Imperative.embedConfig_stepStarE_rev π (c := .stmts bs ρ₀) hrun
    rw [show (EventLang.coreBlock π).exitingCfg lbl ρ' = embedConfig (.exiting lbl ρ') from rfl] at hc'
    obtain rfl := Imperative.embedConfig_injective hc'
    obtain ⟨ρ'', trace', hrunb, hout, htr⟩ := h_exit lbl ρ' trace hbase
    exact ⟨ρ'', trace',
      by rw [htgt]; exact Imperative.embedCFGConfig_stepCFGStarE π hrunb, hout, htr⟩
  · show Core.Logic.CFGInitEnvWF base out ρ₀
    subst hout_eq
    haveI : Nonempty Expression.Factory := ⟨ρ₀.factory⟩
    obtain ⟨hsem, hstore, hdefs, hdnr, hfresh, hdu, hfactory, htypes, -⟩ :=
      blockInitEnvWF_projectBase hwf hproj
    have hduLive :=
      Imperative.StructuredToUnstructuredWF.Block.cfgLive_defUseWellFormed
        (fun n => (ρ₀.store n).isSome) (base.extend prefixesReserved).declaredFuncs bs hdu
    refine
      { toWellFormedSemanticEval := hsem
        storeWellDefined := hstore
        readWritesDefined := ?_
        defsUndefined := ?_
        definedVarsNotReserved := ?_
        reservedFresh := ?_
        initTypesInhabited := ?_
        factoryDeclared := ?_ }
    · intro n hn hnot
      rw [Imperative.embedCFG_definedVars] at hnot
      simp only [List.mem_append] at hn
      rw [Imperative.embedCFG_modifiedVars, Imperative.embedCFG_definedVars,
        Imperative.embedCFG_readVars] at hn
      have hnotLive : n ∉ Block.initVars
          (Imperative.StructuredToUnstructuredWF.Block.cfgLive bs) := by
        intro hmem
        exact hnot ((Imperative.StructuredToUnstructuredWF.stmtsToCFG_definedVars_iff
          bs hng hlhni hnml n).2 hmem)
      have htouched : n ∈ Block.touchedVars
          (Imperative.StructuredToUnstructuredWF.Block.cfgLive bs) := by
        rcases hn with (hm | hd) | hr
        · have hmLive := (Imperative.StructuredToUnstructuredWF.stmtsToCFG_modifiedVars_iff
            bs hng hlhni hnml n).1 hm
          simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.append_assoc, List.mem_append]
          exact Or.inl hmLive
        · exact absurd hd hnot
        · have hrLive := (Imperative.StructuredToUnstructuredWF.stmtsToCFG_readVars_iff
            bs hng hlhni hnml n).1 hr
          simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.append_assoc, List.mem_append]
          exact Or.inr (Or.inr hrLive)
      exact Imperative.Block.defined_of_mem_touchedVars
        (fun _ _ h => h) hduLive htouched hnotLive
    · intro n hn
      rw [Imperative.embedCFG_definedVars] at hn
      have hLive := (Imperative.StructuredToUnstructuredWF.stmtsToCFG_definedVars_iff
        bs hng hlhni hnml n).1 hn
      exact hdefs n
        (Imperative.StructuredToUnstructuredWF.Block.mem_initVars_of_cfgLive bs n hLive)
    · intro n hn name heq p hp
      rw [Imperative.embedCFG_definedVars] at hn
      have hLive := (Imperative.StructuredToUnstructuredWF.stmtsToCFG_definedVars_iff
        bs hng hlhni hnml n).1 hn
      have hname : n.name = name :=
        congrArg (fun ident : Expression.Ident => ident.name) heq
      rw [← hname]
      exact hdnr n
        (Imperative.StructuredToUnstructuredWF.Block.mem_initVars_of_cfgLive bs n hLive)
        p (List.mem_append_right _ hp)
    · intro n hn name heq p hp
      have hname : n.name = name :=
        congrArg (fun ident : Expression.Ident => ident.name) heq
      rw [← hname]
      exact hfresh n hn p (List.mem_append_right _ hp)
    · intro ty hty
      rw [Imperative.embedCFG_initTypes] at hty
      have hLive := (Imperative.StructuredToUnstructuredWF.stmtsToCFG_initTypes_iff
        bs hng hlhni hnml ty).1 hty
      exact htypes ty
        (Imperative.StructuredToUnstructuredWF.Block.mem_initTypes_of_cfgLive bs ty hLive)
    · exact hfactory

/-- Evaluation to `true` is stable under structured-lowering event
matching. -/
theorem evalInterp_stableUnder :
    ConditionInterp.StableUnder (P := Expression)
      (Imperative.BigStep.evalInterp : ConditionInterp Expression)
      (EventArg.WithWF (EventArg.ExtendsEnv (fun _ => True))
        (P := Expression)) :=
  Imperative.BigStep.evalInterp_stableUnder

/-- Assertion validity for a successfully lowered Core CFG reflects to its
structured source when condition truth is stable under structured-lowering
event matching. `evalInterp_stableUnder` supplies this for `evalInterp`. -/
theorem assertValid (base : InitEnvWFParams)
    {ss : Statements} {out : CFG String (DetBlock String Command Expression)}
    (htransform : Core.stmtsToCFG ss = some out)
    (hpre :
      Statements.noCalls ss = Bool.true
      ∧ Block.noNondetGuards ss = Bool.true
      ∧ Block.uniqueInits (C := Command) ss
      ∧ Block.loopBodyNoInits (C := Command) ss = Bool.true
      ∧ Block.loopHasNoInvariants ss = Bool.true
      ∧ Block.noMeasureLoops ss = Bool.true
      ∧ Block.exitsCoveredByBlocks (CmdT := Command) [] ss
      ∧ Block.userLabelsShapeNodup (C := Command) ss
      ∧ (∀ name : String, Imperative.StructuredToUnstructured.isGeneratedName name →
          HasIdent.ident (P := Expression) name ∉
            Block.initVars (C := Command) ss))
    {I : ConditionInterp Expression}
    (hstable : I.StableUnder
      (EventArg.WithWF (P := Expression) (EventArg.ExtendsEnv (fun _ => True))))
    {aid : AssertId Expression}
    (hvalid : AssertValidOnTracesWhen (EventLang.coreCFG π) I
      (Core.Logic.CFGInitEnvWF base out) out aid) :
    AssertValidOnTracesWhen (EventLang.coreBlock π) I
      (Core.Logic.BlockInitEnvWF (base.extend prefixesReserved) ss) ss aid :=
  overapproximatesTracesUptoWhen_assertValid I _ _
    (EventLang.coreBlock π) (EventLang.coreCFG π)
    Core.stmtsToCFG
    (fun block =>
      Statements.noCalls block = Bool.true
      ∧ Block.noNondetGuards block = Bool.true
      ∧ Block.uniqueInits (C := Command) block
      ∧ Block.loopBodyNoInits (C := Command) block = Bool.true
      ∧ Block.loopHasNoInvariants block = Bool.true
      ∧ Block.noMeasureLoops block = Bool.true
      ∧ Block.exitsCoveredByBlocks (CmdT := Command) [] block
      ∧ Block.userLabelsShapeNodup (C := Command) block
      ∧ (∀ name : String, Imperative.StructuredToUnstructured.isGeneratedName name →
          HasIdent.ident (P := Expression) name ∉
            Block.initVars (C := Command) block))
    (base.extend prefixesReserved) (base)
    (fun _ _ htrace aid =>
      Trace.WithWF.assertionValidFrom_reflect hstable htrace aid)
    (overapproximatesTraces π base) htransform hpre hvalid

/-- Running the structured-to-unstructured pipeline phase runs its program
transform. -/
theorem structuredToUnstructuredPipelinePhase_ok (program : Program)
    (s : Transform.CoreTransformState) :
    (structuredToUnstructuredPipelinePhase.transform program).run s =
      (structuredToUnstructured program).run s := by
  unfold structuredToUnstructuredPipelinePhase modelPreservingPipelinePhase
  rfl

/-- A successful declaration-list rewrite passed the shape checks on every
nonempty structured procedure body, and contains the lowered declaration for
each such body that lowers successfully. -/
private theorem structuredToUnstructuredDecls_proc_mem
    {decls : List Decl} {results : List (Decl × Bool)}
    {q : Procedure} {md : MetaData Expression} {ss : Statements}
    {cfg : CFG String (DetBlock String Command Expression)}
    (h : decls.mapM structuredToUnstructuredDecl = .ok results)
    (hq : Decl.proc q md ∈ decls) (hb : q.body = .structured ss)
    (hne : ss ≠ []) (hcfg : Core.stmtsToCFG ss = some cfg) :
    (Imperative.Block.checkExitsCoveredByBlocks [] ss = Bool.true
      ∧ userLabelsOk ss = Bool.true ∧ initsAvoidReservedPrefixes ss = Bool.true)
    ∧ (Decl.proc { q with body := .cfg cfg } md, Bool.true) ∈ results := by
  have hempty : ss.isEmpty = Bool.false := List.isEmpty_eq_false_iff.mpr hne
  induction decls generalizing results with
  | nil => simp at hq
  | cons d rest ih =>
    rcases List.mem_cons.mp hq with hhead | htail
    · subst d
      cases h1 : Imperative.Block.checkExitsCoveredByBlocks [] ss <;>
        cases h2 : userLabelsOk ss <;> cases h3 : initsAvoidReservedPrefixes ss <;>
        simp only [List.mapM_cons, structuredToUnstructuredDecl, hb, hempty, hcfg,
          h1, h2, h3, bind, Except.bind, pure, Except.pure] at h
      all_goals
        repeat' first | split at h | simp_all
      all_goals
        subst results
        simp_all
    · cases d <;>
        simp only [List.mapM_cons, structuredToUnstructuredDecl, bind,
          Except.bind, pure, Except.pure] at h
      all_goals
        repeat' first | split at h | simp_all only [ne_eq, List.isEmpty_eq_false_iff,
          not_false_eq_true, Except.ok.injEq, forall_const, forall_eq', List.mem_cons,
          reduceCtorEq, or_true, and_self, true_and, Decl.proc.injEq, List.isEmpty_iff,
          Bool.not_eq_eq_eq_not, Bool.not_true]
        subst results
        exact List.mem_cons_of_mem _ ih.2

/-- A successful structured-to-unstructured run passed the shape checks on
every nonempty structured procedure body and places each lowered procedure in
the output program. -/
private theorem structuredToUnstructured_proc_mem
    {program out : Program} {s s' : Transform.CoreTransformState} {changed : Bool}
    {q : Procedure} {md : MetaData Expression} {ss : Statements}
    {cfg : CFG String (DetBlock String Command Expression)}
    (h : (structuredToUnstructured program).run s = (.ok (changed, out), s'))
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss)
    (hne : ss ≠ []) (hcfg : Core.stmtsToCFG ss = some cfg) :
    (Imperative.Block.checkExitsCoveredByBlocks [] ss = Bool.true
      ∧ userLabelsOk ss = Bool.true ∧ initsAvoidReservedPrefixes ss = Bool.true)
    ∧ Decl.proc { q with body := .cfg cfg } md ∈ out.decls := by
  cases hmap : program.decls.mapM structuredToUnstructuredDecl with
  | error error =>
      simp only [structuredToUnstructured, hmap, liftExcept, pure] at h
      cases h
  | ok results =>
      simp only [structuredToUnstructured, hmap, liftExcept, pure] at h
      injection h with hresult _
      injection hresult with hp
      injection hp with _ hout
      rw [← hout]
      obtain ⟨hchecks, hmem⟩ := structuredToUnstructuredDecls_proc_mem hmap hq hb hne hcfg
      exact ⟨hchecks, List.mem_map.mpr ⟨_, hmem, rfl⟩⟩

/-- A successful structured-to-unstructured phase run lowers every nonempty
structured procedure body into the output program. Under the phase's
fact-tracked `requires` (`noCalls`, `noNondetGuards`, `uniqueInits`,
`loopBodyNoInits`, `noLoopInvariants`, `noLoopMeasures`), assertion validity
of the lowered CFG reflects to the source body; the body-level shape
conditions no `ProgramFact` tracks follow from the run's success, because
`structuredToUnstructuredDecl` checks them. -/
theorem structuredToUnstructuredPipelinePhase_over
    {program out : Program} {s s' : Transform.CoreTransformState} {changed : Bool}
    (hrun : (structuredToUnstructuredPipelinePhase.transform program).run s =
      (.ok (changed, out), s'))
    (hnoCallsProgram : ProgramFact.noCalls.holds program)
    (hnoNondetGuardsProgram : ProgramFact.noNondetGuards.holds program)
    (huniqueInitsProgram : ProgramFact.uniqueInits.holds program)
    (hloopBodyNoInitsProgram : ProgramFact.loopBodyNoInits.holds program)
    (hnoLoopInvariantsProgram : ProgramFact.noLoopInvariants.holds program)
    (hnoLoopMeasuresProgram : ProgramFact.noLoopMeasures.holds program)
    {q : Procedure} {md : MetaData Expression} {ss : Statements}
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss)
    (hne : ss ≠ []) :
    ∃ cfg, Core.stmtsToCFG ss = some cfg
      ∧ Decl.proc { q with body := .cfg cfg } md ∈ out.decls
      ∧ ∀ (base : InitEnvWFParams) {I : ConditionInterp Expression},
        I.StableUnder
          (EventArg.WithWF (P := Expression) (EventArg.ExtendsEnv (fun _ => True))) →
      ∀ {aid : AssertId Expression},
        AssertValidOnTracesWhen (EventLang.coreCFG π) I
          (Core.Logic.CFGInitEnvWF base cfg) cfg aid →
        AssertValidOnTracesWhen (EventLang.coreBlock π) I
          (Core.Logic.BlockInitEnvWF (base.extend prefixesReserved) ss) ss aid := by
  have htransform :
      (structuredToUnstructured program).run s = (.ok (changed, out), s') := by
    rw [← structuredToUnstructuredPipelinePhase_ok program s]
    exact hrun
  have hnc := ProgramFact.noCalls_of_program hnoCallsProgram hq hb
  obtain ⟨bs, hproj, _⟩ := Core.noCalls_projectStmts hnc
  have hcfg := Core.stmtsToCFG_eq_some hproj
  obtain ⟨⟨hexits, hlabels, hinits⟩, hmem⟩ :=
    structuredToUnstructured_proc_mem htransform hq hb hne hcfg
  have hpre :=
    And.intro (ProgramFact.noNondetGuards_of_program hnoNondetGuardsProgram hq hb)
      (And.intro (ProgramFact.uniqueInits_of_program huniqueInitsProgram hq hb)
        (And.intro (ProgramFact.loopBodyNoInits_of_program hloopBodyNoInitsProgram hq hb)
          (And.intro (ProgramFact.noLoopInvariants_of_program hnoLoopInvariantsProgram hq hb)
            (And.intro (ProgramFact.noLoopMeasures_of_program hnoLoopMeasuresProgram hq hb)
              (loweringShape_of_checks hexits hlabels hinits)))))
  refine ⟨_, hcfg, hmem, ?_⟩
  intro base I hstable aid hvalid
  exact assertValid π base hcfg ⟨hnc, hpre⟩ hstable hvalid

end Core.StructuredToUnstructured

end -- public section
