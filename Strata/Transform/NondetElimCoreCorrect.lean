/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.NondetElimCorrect
public import Strata.DL.Imperative.BigStep.Sem
public import Strata.DL.Imperative.BigStep.SemProps
import Strata.DL.Imperative.Logic.TraceRelationsProps
public import Strata.DL.Imperative.Logic.TraceInterpProps
public import Strata.Transform.SpecificationProps
public import Strata.Languages.Core.StmtExtendCallBridgeProps
import all Strata.Transform.NondetElim
import all Strata.Languages.Core.PipelinePhase
import Strata.Languages.Core.ProgramFactProps

/-! # Core nondeterminism-elimination correctness

`Core.NondetElim.overapproximatesTraces` transports the base-command simulation
from `NondetElimCorrect` through the call-free Core bridge. The source gate
reserves the two generated guard prefixes in addition to inherited reservations;
the target gate keeps only the inherited reservations. The caller proves those
inherited prefixes disjoint from generated guard names.

`Core.NondetElim.assertValid` reflects assertion validity from the transformed
Core block to its source for interpretations stable under `EventArg.WithWF`.
`Core.NondetElim.evalInterp_stableUnder` discharges this condition for the
verifier's evaluation interpretation.

`Core.NondetElim.nondetElimPipelinePhase_ok` identifies the phase transform,
and `nondetElimPipelinePhase_over` connects a successful phase run and its
`noCalls` requirement to the rewritten procedure and body-level validity result.
`Core.NondetElim.preserves_noCalls` states that the pass keeps a call-free
block call-free, for downstream pipeline clients.
-/

public section

namespace Core.NondetElim

open Core Core.Logic Imperative Imperative.Logic Strata.Logic
open Imperative.Specification Imperative.Specification.Transform

variable (π : String → Option Procedure)

/-- Running the NondetElim pipeline phase runs its program transform. -/
theorem nondetElimPipelinePhase_ok (program : Program)
    (s : Transform.CoreTransformState) :
    (nondetElimPipelinePhase.transform program).run s =
      (nondetElim program).run s := by
  unfold nondetElimPipelinePhase modelPreservingPipelinePhase
  rfl

/-- A successful declaration-list rewrite contains the transformed declaration
and change flag for every structured procedure in the source list. -/
private theorem nondetElimDecls_proc_mem
    {decls : List Decl} {results : List (Decl × Bool)}
    {q : Procedure} {md : MetaData Expression} {ss : Statements}
    (h : decls.mapM nondetElimDecl = .ok results)
    (hq : Decl.proc q md ∈ decls) (hb : q.body = .structured ss) :
    (Decl.proc { q with body := .structured (Imperative.Block.nondetElim ss) } md,
      Imperative.Block.nondetElim ss != ss) ∈ results := by
  induction decls generalizing results with
  | nil => simp at hq
  | cons d rest ih =>
    rcases List.mem_cons.mp hq with hhead | htail
    · subst d
      simp only [List.mapM_cons, nondetElimDecl, hb, bind, Except.bind,
        pure, Except.pure] at h
      repeat' first | split at h | simp_all
      subst results
      simp_all
    · cases d <;>
        simp only [List.mapM_cons, nondetElimDecl, bind, Except.bind,
          pure, Except.pure] at h
      all_goals
        repeat' first | split at h | simp_all only [Except.ok.injEq, forall_const, forall_eq', List.mem_cons, reduceCtorEq, or_true,
    Decl.proc.injEq]
        subst results
        exact List.mem_cons_of_mem _ ih

/-- A successful NondetElim run places each rewritten structured procedure in
the output program. -/
private theorem nondetElim_proc_mem
    {program out : Program} {s s' : Transform.CoreTransformState} {changed : Bool}
    {q : Procedure} {md : MetaData Expression} {ss : Statements}
    (h : (nondetElim program).run s = (.ok (changed, out), s'))
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss) :
    Decl.proc { q with body := .structured (Imperative.Block.nondetElim ss) } md ∈
      out.decls := by
  cases hmap : program.decls.mapM nondetElimDecl with
  | error error =>
      simp only [nondetElim, hmap, liftExcept, pure] at h
      cases h
  | ok results =>
      simp only [nondetElim, hmap, liftExcept, pure] at h
      injection h with hresult _
      injection hresult with hp
      injection hp with _ hout
      rw [← hout]
      exact List.mem_map.mpr
        ⟨_, nondetElimDecls_proc_mem hmap hq hb, rfl⟩

/-- Public Core-facing call-freeness preservation for the top-level
`Block.nondetElim` wrapper. This keeps downstream phase clients independent of
the underlying state-threaded implementation theorem. -/
theorem preserves_noCalls {ss : Statements}
    (h : Statements.noCalls ss = Bool.true) :
    Statements.noCalls (Imperative.Block.nondetElim ss) = Bool.true :=
  Core.Block.nondetElimM_isNotCall ss StringGenState.emp h

/-- Nondeterminism elimination overapproximates Core event traces. Every source
trace prefix has a target prefix related by
`Trace.WithWF (EventArg.ExtendsEnv NdExtra)`; terminal and exiting runs end in environments extended only by generated guard registers. -/
theorem overapproximatesTraces (base : InitEnvWFParams)
    -- Generated NondetElim names must be orthogonal to other transforms' prefixes.
    (hprefixes : prefixesDisjoint base.prefixIdents
      Imperative.NondetElim.isGeneratedName) :
    OverapproximatesTracesUptoWhen
      -- Source and target events match with free-variable store agreement.
      (Trace.WithWF (P := Expression) (EventArg.ExtendsEnv NondetElimTrace.NdExtra))
      -- Both executions start from the same environment.
      (· = ·)
      -- Completed target environments may add only generated guard bindings.
      (Env.ExtendsWith
        (Imperative.IdentOfStringKind Imperative.NondetElim.isGeneratedName))
      -- Source and target both use Core block event semantics.
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      -- Transform nondeterministic guards in a structured block.
      (fun ss => some (Imperative.Block.nondetElim ss))
      (fun ss =>
        -- The bridge to base commands requires a call-free source block.
        Statements.noCalls ss = Bool.true
        -- The source must not define or modify generated guard names.
        ∧ (∀ name : String, Imperative.NondetElim.isGeneratedName name →
            HasIdent.ident (P := Expression) name ∉
              (Block.definedVars (C := Command) ss false ++
                Block.modifiedVars (C := Command) ss)))
      -- The source reserves generated prefixes; the target consumes them.
      (base.extend Imperative.NondetElim.prefixesReserved) base := by
  intro ss out ht hpre ρ₀ ρ₀' hEq hwf
  subst hEq
  have htransform : Imperative.Block.nondetElim ss = out := Option.some.inj ht
  subst out
  obtain ⟨hnc, hnogenCore⟩ := hpre
  obtain ⟨bs, hproj, hemb⟩ := Core.noCalls_projectStmts hnc
  have hnogen : Imperative.SrcNoGenWrites Imperative.NondetElim.isGeneratedName bs :=
    (Imperative.projectStmts_noDefinedOrModifiedKind_iff
      Imperative.NondetElim.isGeneratedName hproj).mp hnogenCore
  change Core.Logic.BlockInitEnvWF
    (base.extend Imperative.NondetElim.prefixesReserved) ss ρ₀ at hwf
  have hbaseWF : Imperative.Logic.BlockInitEnvWF
      (P := Expression) (CmdT := Cmd Expression)
      (base.extend Imperative.NondetElim.prefixesReserved) bs ρ₀ :=
    Core.Logic.BlockInitEnvWF.toImperativeProject hwf hproj
  have hread : Block.exprsShapeFree Imperative.NondetElim.isGeneratedName bs := by
    intro name hname hmem
    have hmemCore : HasIdent.ident (P := Expression) name ∈ Block.getVars ss := by
      have hmem' : HasIdent.ident (P := Expression) name ∈
          Block.getVars (C := Command) (embedStmts bs) := by
        rw [Imperative.embedStmts_getVars]
        exact hmem
      rwa [hemb] at hmem'
    rw [Imperative.NondetElim.isGeneratedName_iff] at hname
    rcases hname with ⟨state, rfl⟩ | ⟨state, rfl⟩
    · exact (hwf.getVarsNotReserved (p := Imperative.NondetElim.prefixIte)
        hmemCore (by simp [InitEnvWFParams.extend, Imperative.NondetElim.prefixesReserved]))
        (by
          change Imperative.NondetElim.prefixIte.toList.isPrefixOf
            (StringGenState.gen Imperative.NondetElim.prefixIte state).1.toList
          exact String.HasGenPrefix.bare_isPrefixOf
            (StringGenState.gen_hasGenPrefix Imperative.NondetElim.prefixIte state))
    · exact (hwf.getVarsNotReserved (p := Imperative.NondetElim.prefixLoop)
        hmemCore (by simp [InitEnvWFParams.extend, Imperative.NondetElim.prefixesReserved]))
        (by
          change Imperative.NondetElim.prefixLoop.toList.isPrefixOf
            (StringGenState.gen Imperative.NondetElim.prefixLoop state).1.toList
          exact String.HasGenPrefix.bare_isPrefixOf
            (StringGenState.gen_hasGenPrefix Imperative.NondetElim.prefixLoop state))
  obtain ⟨h_prefix, h_term, h_exit, hbaseOut⟩ :=
    Imperative.NondetElim.Internal.overapproximates_upto_base
      (P := Expression) base hprefixes bs
      (Imperative.Block.nondetElim bs) rfl ⟨hnogen, hread⟩
      ρ₀ ρ₀ rfl hbaseWF
  have hsrc : (EventLang.coreBlock π).stmtCfg ss ρ₀ =
      embedConfig (.stmts bs ρ₀) := by
    simp only [EventLang.coreBlock, EventLang.imperativeBlockE, embedConfig, hemb]
  have htgt : (EventLang.coreBlock π).stmtCfg (Imperative.Block.nondetElim ss) ρ₀ =
      embedConfig (.stmts (Imperative.Block.nondetElim bs) ρ₀) := by
    simp only [EventLang.coreBlock, EventLang.imperativeBlockE, embedConfig,
      ← hemb, embedStmts_nondetElim]
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
  · intro label ρ' trace hrun
    rw [hsrc] at hrun
    obtain ⟨c', hc', hbase⟩ :=
      Imperative.embedConfig_stepStarE_rev π (c := .stmts bs ρ₀) hrun
    rw [show (EventLang.coreBlock π).exitingCfg label ρ' =
      embedConfig (.exiting label ρ') from rfl] at hc'
    obtain rfl := Imperative.embedConfig_injective hc'
    obtain ⟨ρ'', trace', hrunb, hout, htr⟩ := h_exit label ρ' trace hbase
    exact ⟨ρ'', trace', by
      rw [htgt]
      exact Imperative.embedConfig_stepStarE π hrunb, hout, htr⟩
  · obtain ⟨hsem, hstore, hdefs, hdefinedReserved, hfresh, hdu, hfactory,
        htypes, -⟩ :=
      blockInitEnvWF_projectBase hwf hproj
    have hkindNone : ∀ name, Imperative.NondetElim.isGeneratedName name →
        (ρ₀.store (HasIdent.ident (P := Expression) name)).isNone := by
      intro name hname
      apply Option.isNone_iff_eq_none.mpr
      apply hbaseWF.generatedNamesFresh
      refine ⟨name, ?_, rfl⟩
      rw [Imperative.NondetElim.isGeneratedName_iff] at hname
      rcases hname with ⟨state, rfl⟩ | ⟨state, rfl⟩
      · exact ⟨Imperative.NondetElim.prefixIte, by
          simp [InitEnvWFParams.extend,
            Imperative.NondetElim.prefixesReserved],
          String.HasGenPrefix.bare_isPrefixOf
            (StringGenState.gen_hasGenPrefix
              Imperative.NondetElim.prefixIte state)⟩
      · exact ⟨Imperative.NondetElim.prefixLoop, by
          simp [InitEnvWFParams.extend,
            Imperative.NondetElim.prefixesReserved],
          String.HasGenPrefix.bare_isPrefixOf
            (StringGenState.gen_hasGenPrefix
              Imperative.NondetElim.prefixLoop state)⟩
    have hkindFalse : ∀ name, Imperative.NondetElim.isGeneratedName name →
        (ρ₀.store (HasIdent.ident (P := Expression) name)).isSome = Bool.false :=
      fun name hname => by simpa using hkindNone name hname
    have hout : Imperative.Block.nondetElim ss =
        embedStmts (Imperative.Block.nondetElim bs) := by
      rw [← hemb, embedStmts_nondetElim]
    rw [hout]
    have hinits := Imperative.Block.nondetElim_initsUndefinedAndInhabited bs ρ₀
      (fun ident hident => Option.isNone_iff_eq_none.mp (hdefs ident hident))
      (fun ident hident => by
        obtain ⟨name, hname, heq⟩ := hident
        subst ident
        exact Option.isNone_iff_eq_none.mp (hkindNone name hname)) htypes
    refine Core.Logic.BlockInitEnvWF.ofBaseEmbed hsem hstore ?_ ?_ ?_ ?_ ?_ hinits.2
      hbaseOut.fvarTypesOk
    · intro ident hident
      exact Option.isNone_iff_eq_none.mpr (hinits.1 ident hident)
    · intro ident hident pfx hp
      have hpbase : pfx ∈ base.prefixIdents := by
        exact hp
      rcases Imperative.Block.nondetElimM_initVars_classified
          bs StringGenState.emp ident hident with hsource | ⟨name, rfl, hname⟩
      · exact hdefinedReserved ident hsource pfx (by simp [InitEnvWFParams.extend, hpbase])
      · exact hprefixes pfx hpbase name hname
    · intro ident hdefined pfx hp
      have hpbase : pfx ∈ base.prefixIdents := by
        exact hp
      exact hfresh ident hdefined pfx (by simp [InitEnvWFParams.extend, hpbase])
    · exact Imperative.Block.nondetElim_defUseWellFormed bs
        (fun ident => (ρ₀.store ident).isSome) base.declaredFuncs base.declaredFuncs
        hkindFalse (fun _ h => h) hdu hnogen
    · intro name hname
      exact hfactory name hname

/-! ## Assertion-validity reflection -/

/-- Evaluation to `true` is stable under NondetElim event-argument matching. -/
theorem evalInterp_stableUnder :
    ConditionInterp.StableUnder (P := Expression)
      (Imperative.BigStep.evalInterp : ConditionInterp Expression)
      (EventArg.WithWF (P := Expression) (EventArg.ExtendsEnv NondetElimTrace.NdExtra)) :=
  Imperative.BigStep.evalInterp_stableUnder

/-- Nondeterminism elimination reflects validity of an assertion from the
transformed Core block to the source block when generated bindings do not change
condition truth. -/
theorem assertValid (base : InitEnvWFParams)
    {ss : Statements}
    -- Syntactic assumptions on the source block.
    (hnoCalls : Statements.noCalls ss = Bool.true)
    (hnoGeneratedWrites : ∀ name,
      Imperative.NondetElim.isGeneratedName name →
      HasIdent.ident (P := Expression) name ∉
        (Block.definedVars (C := Command) ss false ++
          Block.modifiedVars (C := Command) ss))
    -- The pass must preserve the caller's inherited name reservations.
    (hprefixes : prefixesDisjoint base.prefixIdents
      Imperative.NondetElim.isGeneratedName)
    {I : ConditionInterp Expression}
    -- Generated bindings must not change the truth of captured conditions.
    (hstable : I.StableUnder
      (EventArg.WithWF (P := Expression) (EventArg.ExtendsEnv NondetElimTrace.NdExtra)))
    {aid : AssertId Expression}
    -- Validity assumption on the transformed block.
    (hvalid : AssertValidOnTracesWhen (EventLang.coreBlock π) I
      (Core.Logic.BlockInitEnvWF base (Imperative.Block.nondetElim ss))
      (Imperative.Block.nondetElim ss) aid) :
    AssertValidOnTracesWhen (EventLang.coreBlock π) I
      (Core.Logic.BlockInitEnvWF (base.extend
    Imperative.NondetElim.prefixesReserved) ss) ss aid :=
  overapproximatesTracesUptoWhen_assertValid I _ _
    (EventLang.coreBlock π) (EventLang.coreBlock π)
    (fun block => some (Imperative.Block.nondetElim block))
    (fun block =>
      Statements.noCalls block = Bool.true
      ∧ (∀ name, Imperative.NondetElim.isGeneratedName name →
          HasIdent.ident (P := Expression) name ∉
            (Block.definedVars (C := Command) block false ++
              Block.modifiedVars (C := Command) block)))
    (base.extend
    Imperative.NondetElim.prefixesReserved) (base)
    (fun _ _ htrace aid =>
      Trace.WithWF.assertionValidFrom_reflect hstable htrace aid)
    (overapproximatesTraces π base hprefixes) rfl
      ⟨hnoCalls, hnoGeneratedWrites⟩ hvalid

/-- A successful NondetElim phase run rewrites each structured procedure body
with `Block.nondetElim`; under the phase's `noCalls` requirement, the body-level
assertion-validity result applies to that procedure. -/
theorem nondetElimPipelinePhase_over
    {program out : Program} {s s' : Transform.CoreTransformState} {changed : Bool}
    (hrun : (nondetElimPipelinePhase.transform program).run s =
      (.ok (changed, out), s'))
    (hnoCallsProgram : ProgramFact.noCalls.holds program)
    {q : Procedure} {md : MetaData Expression} {ss : Statements}
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss) :
    Decl.proc { q with body := .structured (Imperative.Block.nondetElim ss) } md ∈
        out.decls
    ∧ ∀ (base : InitEnvWFParams),
      prefixesDisjoint base.prefixIdents Imperative.NondetElim.isGeneratedName →
      (∀ name, Imperative.NondetElim.isGeneratedName name →
        HasIdent.ident (P := Expression) name ∉
          (Block.definedVars (C := Command) ss false ++
            Block.modifiedVars (C := Command) ss)) →
      ∀ {I : ConditionInterp Expression},
        I.StableUnder (EventArg.WithWF (P := Expression)
          (EventArg.ExtendsEnv NondetElimTrace.NdExtra)) →
      ∀ {aid : AssertId Expression},
        AssertValidOnTracesWhen (EventLang.coreBlock π) I
          (Core.Logic.BlockInitEnvWF base (Imperative.Block.nondetElim ss))
          (Imperative.Block.nondetElim ss) aid →
        AssertValidOnTracesWhen (EventLang.coreBlock π) I
          (Core.Logic.BlockInitEnvWF (base.extend
    Imperative.NondetElim.prefixesReserved) ss) ss aid := by
  have htransform : (nondetElim program).run s = (.ok (changed, out), s') := by
    rw [← nondetElimPipelinePhase_ok program s]
    exact hrun
  refine ⟨nondetElim_proc_mem htransform hq hb, ?_⟩
  intro base hprefixes hnoGeneratedWrites I hstable aid hvalid
  exact assertValid π base (ProgramFact.noCalls_of_program hnoCallsProgram hq hb)
    hnoGeneratedWrites hprefixes hstable hvalid

end Core.NondetElim

end -- public section
