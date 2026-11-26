/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.VerifierSlicingProofs
public import Strata.Languages.Core.ObligationExtractionProps
public import Strata.Languages.Core.ObligationExtractionTyping
public import Strata.Transform.WPRewriteLoopCorrect
import all Strata.Languages.Core.ObligationExtractionProps
import all Strata.Languages.Core.VerifierSlicingProofs
import Strata.DL.Imperative.PathConditionHolds
import all Strata.Languages.Core.ObligationExtraction
import Strata.Transform.BetaReduceTyping
import all Strata.Transform.WPLoop
import all Strata.Transform.WPRewriteLoop
import all Strata.Transform.CoreTransform
import all Strata.Transform.BetaReduce
import Strata.Transform.BetaReduceProps
import Strata.Transform.SSA.SSATyping
import Strata.Transform.SSA.SSAUnassignedCorrect
import Strata.Languages.Core.ProcedureProps
import Strata.Util.ExceptProps

/-!
# The SSA phase and the six-pass rewrite loop of `--vcgen wp`

`--vcgen wp` runs, after the declaration phase and the WP phase, the SSA phase, the rewrite loop
(`wpRewriteLoopPipelinePhase`, whose round is beta reduction, guard forwarding, the inlining of
single-use definitions, the erasure of unread definitions, guard propagation and the constructor
fold) and beta reduction (`betaReducePipelinePhase`, for the declarations other than procedure
bodies), and extracts the obligations from the program the last returns.  This module states,
for each procedure of that program, the trace over-approximation of the three phases on the WP
phase's output, and the slicing theorems on the extracted obligations.

The three phases need the procedure bodies of the WP phase's output well typed
(`WPPipelineEntryWellTyped`), which the WP phase establishes from the typing of its input
(`wpPipelinePhase_entryWellTyped`, `WPPhaseInputWellTyped`), besides the entry gates
(`WPPipelineEntryGates`).

The trace over-approximation (`wpRewritePipeline_overapproximatesTraces`) rests on the per-phase
theorems composed by `WPRewriteLoop.ssa_loopBody_betaReduce_overapproximatesTraces`, for the
three phases on one procedure body (`wpRewriteTail`) from the bodies satisfying its precondition
(`WPRewriteTailPre`).

The slicing theorem (`wpRewritePipelineProgram_sliced_counterexample_extends`) needs the facts
of the procedure bodies the loop returns (`wpRewriteLoopPipeline_bodyFacts`): the SSA phase gives
them to its output and each round keeps them (`WPRewriteLoop.loopBody_kept`), and so does beta
reduction (`betaReduce_keepsBodyFacts`), which carries them to the extracted statement lists
(`keepsBodyFacts_typed`).

Key definitions: `KeepsBodyFacts`, `wpRewriteTail`, `WPRewriteTailPre`.

Key theorems: `wpRewriteLoopPipeline_proc`, `wpRewritePipeline_proc`,
`wpRewritePipeline_overapproximatesTraces`, `betaReduce_keepsBodyFacts`, `keepsBodyFacts_typed`,
`wpRewriteLoopPipeline_bodyFacts`, `wpRewritePipelineProgram_typed`,
`wpRewritePipelineProgram_extractObligations_defsOrdered`,
`wpRewritePipelineProgram_extractObligations_defsTyped`,
`wpRewritePipelineProgram_sliced_counterexample_extends`.
-/

namespace Core
namespace ObligationExtraction

open Imperative Imperative.Specification Imperative.Specification.Transform Core.Logic

public section

/-- A relation `R` between programs, such as the runs of a phase (`PhaseRuns`), *keeps the body
    facts* when every procedure of a program `R` relates `p` to comes from a procedure of `p` with
    the same header and metadata, and its structured body has the facts of
    `WPRewriteLoop.BodyOK` (passive form, def-use well-formedness, annotations agreeing with a
    typing, typed `init`s) whenever that procedure's structured body has them. -/
@[expose] def KeepsBodyFacts (R : Program → Program → Prop) : Prop :=
  ∀ (p out : Program), R p out → ∀ (q' : Procedure) (md : Imperative.MetaData Expression),
    Decl.proc q' md ∈ out.decls → ∃ q, Decl.proc q md ∈ p.decls ∧ q'.header = q.header ∧
      ∀ ss' o, q'.body = .structured ss' o → ∃ ss, q.body = .structured ss o ∧
        ∀ D df Γ, WPRewriteLoop.BodyOK D df Γ ss → WPRewriteLoop.BodyOK D df Γ ss'

/-- **Beta reduction keeps the body facts.** -/
theorem betaReduce_keepsBodyFacts : KeepsBodyFacts (PhaseRuns betaReducePipelinePhase) := by
  rintro p out ⟨s, s', b, h⟩ q' md hq'
  rw [betaReducePipelinePhase_ok] at h
  cases h
  exact (BetaReduce.betaReduceProgram_proc_kept hq').imp fun q ⟨hq, hh, hb⟩ =>
    ⟨hq, hh, fun ss' o hs' => (hb ss' o hs').imp fun ss ⟨hs, hp, hdu, hty⟩ => ⟨hs,
      fun D df Γ ⟨hpa, hd, hw, hi⟩ => ⟨hp hpa, hdu D df hd, (hty Γ hw hi).1, (hty Γ hw hi).2⟩⟩⟩

/-- **Phases that keep the body facts carry them to the extracted statement lists.** When every
    procedure of `p₂` with a structured body has no parameters and a body with the body facts,
    and `R` keeps the body facts and relates `p₂` to `out`, the statement list extraction reads
    from every procedure of `out` is def-use well formed, agrees with a typing and has typed
    `init`s. -/
theorem keepsBodyFacts_typed {R : Program → Program → Prop} (hR : KeepsBodyFacts R)
    {p₂ out : Program} (hro : R p₂ out)
    (hfacts : ∀ q₂ md ss₂ o, Decl.proc q₂ md ∈ p₂.decls → q₂.body = .structured ss₂ o →
      q₂.header.inputs ++ q₂.header.outputs = [] ∧ ∃ D df Γ, WPRewriteLoop.BodyOK D df Γ ss₂) :
    ∀ q md ss, Decl.proc q md ∈ out.decls → procedureStatements out.funcNames q = .ok ss →
      ∃ D df Γ, Block.defUseWellFormed D df ss = true ∧ Block.fvarTypesWellAnnotated Γ ss ∧
        Block.initsTyped Expression.Typed ss := by
  intro q₃ md ss hq₃ hss
  obtain ⟨q₂, hq₂, hhd, hb⟩ := hR _ _ hro _ _ hq₃
  simp only [procedureStatements] at hss
  split at hss
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hss
  rcases hb₃ : q₃.body with ⟨ss₃, o₃⟩ | _ | _ <;> simp only [hb₃, reduceCtorEq] at hss
  · cases hss
    obtain ⟨ss₂, hb₂, hk⟩ := hb ss₃ o₃ hb₃
    obtain ⟨hio, D, df, Γ, hok⟩ := hfacts q₂ _ ss₂ _ hq₂ hb₂
    obtain ⟨-, hdu₃, hw₃, hi₃⟩ := hk D df Γ hok
    simp only [renameShadowingParams, hhd, hio, List.foldl_nil]
    exact ⟨D, df, Γ, hdu₃, hw₃, hi₃⟩
  · cases hss
    exact ⟨fun _ => False, fun _ => False, fun _ => none, by
      simp [Block.defUseWellFormed], by simp [Block.fvarTypesWellAnnotated],
      by simp [Block.initsTyped]⟩

/-- **A procedure of the output of the SSA phase and the six-pass rewrite loop.** Let the SSA
    phase and the loop (`ssaPipelinePhase`, `wpRewriteLoopPipelinePhase`) run in turn on `mid` and
    return `p₂`. Every procedure of `p₂` with a structured body `ss` comes from a procedure `q₀`
    of `mid` with a structured body `lay`: the factory of the pipeline on `mid` (`wpFactory`) is
    some `fac`, the SSA phase of `lay` under `fac` succeeds with the result `r`, `ss` is the
    loop's output on the obligation list `r.2.out`, and the procedure has no parameters. -/
theorem wpRewriteLoopPipeline_proc {moreFns : Lambda.Factory CoreLParams} {mid p₁ p₂ : Program}
    (h₁ : PhaseRuns (ssaPipelinePhase moreFns) mid p₁)
    (h₂ : PhaseRuns (wpRewriteLoopPipelinePhase moreFns) p₁ p₂)
    {q : Procedure} {md : Imperative.MetaData Expression} {ss : Statements}
    {opq : Bool} (hq : Decl.proc q md ∈ p₂.decls) (hb : q.body = .structured ss opq) :
    ∃ fac q₀ md₀ lay lo r, Decl.proc q₀ md₀ ∈ mid.decls ∧ q₀.body = .structured lay lo ∧
      wpFactory moreFns mid = .ok fac ∧
      WP.ssaLoopFree fac (Imperative.WP.IdSet.ofList
        (WP.avoidOf [] (fac.toArray.toList.map (·.name) ++ WP.declNames mid))) q₀ lay = .ok r ∧
      ss = (WPRewriteLoop.loopBody fac r.2.out).1 ∧
      q.header.inputs ++ q.header.outputs = [] := by
  obtain ⟨_, _, _, h₁⟩ := h₁
  obtain ⟨_, _, _, h₂⟩ := h₂
  obtain ⟨fac, hfac, hssa⟩ := WP.ssaPipelinePhase_ok h₁
  rw [WPRewriteLoop.wpRewriteLoopPipelinePhase_ok ((wpFactory_ssaProgram hssa).trans hfac)] at h₂
  simp only [WPLoop.wpLoopProgramWith, Transform.incrementStat, List.countP_map, List.any_map,
    List.map_map, bind_pure_comp] at h₂
  cases h₂
  obtain ⟨d₁, hd₁, he₁⟩ := List.mem_map.1 hq
  rcases d₁ with _ | _ | _ | _ | ⟨q₁, md₁⟩ | _ <;>
    simp only [Function.comp_apply, WPLoop.wpLoopDecl, reduceCtorEq] at he₁
  obtain ⟨decls, hdecls, hssa⟩ := (Except.bind_is_ok _ _ _).1 hssa
  cases hssa
  obtain ⟨od, hod, hodq⟩ := List.mem_filterMap.1 hd₁
  cases hodq
  obtain ⟨d₀, hd₀, he₀⟩ := mapM_except_mem_right _ _ _ hdecls _ hod
  rcases d₀ with _ | _ | _ | _ | ⟨q₀, md₀⟩ | _ <;>
    simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq, Option.some.injEq] at he₀
  rcases hb₀ : q₀.body with ⟨lay, lo⟩ | _ | _ <;>
    simp only [WP.ssaProc, hb₀, throw, throwThe, MonadExceptOf.throw, reduceCtorEq, pure,
      Except.pure, Except.ok.injEq] at he₀
  obtain ⟨r, hr, he₀⟩ := (Except.bind_is_ok _ _ _).1 he₀
  cases he₀
  cases he₁
  cases hb
  exact ⟨fac, q₀, md₀, lay, lo, r, hd₀, hb₀, hfac, hr, rfl, rfl⟩

/-- A procedure of the output of beta reduction with a structured body `ss` comes from a
    procedure of the input with the same header and metadata and a structured body whose beta
    reduction is `ss`. -/
private theorem betaReduceProgram_proc_body {p : Program} {q' : Procedure}
    {md : Imperative.MetaData Expression}
    (h : Decl.proc q' md ∈ (BetaReduce.betaReduceProgram p).decls)
    {ss' : Statements} {opq : Bool} (hb : q'.body = .structured ss' opq) :
    ∃ q ss, Decl.proc q md ∈ p.decls ∧ q.body = .structured ss opq ∧ q'.header = q.header ∧
      ss' = BetaReduce.betaReduceBlock ss := by
  obtain ⟨_ | _ | _ | _ | _ | _ | _, hd, ⟨⟩⟩ := List.mem_map.1 h
  split at hb <;> cases hb
  exact ⟨_, _, hd, ‹_›, rfl, rfl⟩

/-- **A procedure of the program `--vcgen wp` extracts obligations from.** Let the SSA phase, the
    six-pass rewrite loop and beta reduction run in turn on `mid` and return `out`. Every
    procedure of `out` with a structured body `ss` comes from a procedure `q₀` of `mid` with a
    structured body `lay`: the factory of the pipeline on `mid` is some `fac`, the SSA phase of
    `lay` under `fac` succeeds with the result `r`, `ss` is the beta reduction of the loop's output
    on `r.2.out`, and the procedure has no parameters. -/
theorem wpRewritePipeline_proc {moreFns : Lambda.Factory CoreLParams} {mid p₁ p₂ out : Program}
    (h₁ : PhaseRuns (ssaPipelinePhase moreFns) mid p₁)
    (h₂ : PhaseRuns (wpRewriteLoopPipelinePhase moreFns) p₁ p₂)
    (h₃ : PhaseRuns betaReducePipelinePhase p₂ out)
    {q : Procedure} {md : Imperative.MetaData Expression} {ss : Statements}
    {opq : Bool} (hq : Decl.proc q md ∈ out.decls) (hb : q.body = .structured ss opq) :
    ∃ fac q₀ md₀ lay lo r, Decl.proc q₀ md₀ ∈ mid.decls ∧ q₀.body = .structured lay lo ∧
      wpFactory moreFns mid = .ok fac ∧
      WP.ssaLoopFree fac (Imperative.WP.IdSet.ofList
        (WP.avoidOf [] (fac.toArray.toList.map (·.name) ++ WP.declNames mid))) q₀ lay = .ok r ∧
      ss = BetaReduce.betaReduceBlock (WPRewriteLoop.loopBody fac r.2.out).1 ∧
      q.header.inputs ++ q.header.outputs = [] := by
  obtain ⟨_, _, _, h₃⟩ := h₃
  rw [betaReducePipelinePhase_ok] at h₃
  cases h₃
  obtain ⟨q₂, ss₂, hq₂, hb₂, hh, rfl⟩ := betaReduceProgram_proc_body hq hb
  obtain ⟨fac, q₀, md₀, lay, lo, r, hd₀, hb₀, hfac, hr, rfl, hio⟩ :=
    wpRewriteLoopPipeline_proc h₁ h₂ hq₂ hb₂
  exact ⟨fac, q₀, md₀, lay, lo, r, hd₀, hb₀, hfac, hr, rfl, hh ▸ hio⟩

/-- **The phases `--vcgen wp` runs after the WP phase, on one procedure body** `ss` of the
    procedure `q`: the SSA phase at the factory `fac`, the global names `G` and the parameter
    types, parameters and aliases of `q`, then the six-pass rewrite loop and beta reduction;
    `none` when the SSA phase fails. -/
@[expose] def wpRewriteTail (fac : Lambda.Factory CoreLParams) (G : Imperative.WP.IdSet Expression)
    (q : Procedure) (ss : Statements) : Option Statements :=
  (WP.ssaEntry fac G q.paramTys q.entryParams q.oldAliases ss).toOption.map (·.2.out) >>=
    fun ss : Statements => some (BetaReduce.betaReduceBlock (WPRewriteLoop.loopBody fac ss).1)

/-- **The precondition of `wpRewriteTail` on the body `lay` of the procedure `q`**: the input
    `ss` is `lay`, in tree form, with an assertion or a cover in every `ite` arm, each of its free
    variables among the parameters of `q` and their aliases or neither assigned nor defined in
    `ss`, and its right-hand sides and conditions typed under a typing agreeing with the
    parameter types on the parameters and aliases (`WPRewriteLoop.SSAInputTyped`). -/
@[expose] def WPRewriteTailPre (q : Procedure) (lay ss : Statements) : Prop :=
  (ss = lay ∧ Block.treeForm ss = true ∧ Block.armsHaveChecks ss = true ∧
    ∀ x ∈ Block.freeVars ss, x ∈ q.entryParams ∨ x ∈ q.oldAliases.map (·.1) ∨
      x ∉ Block.modifiedOrDefinedVars ss false) ∧
    WPRewriteLoop.SSAInputTyped q.paramTys q.entryParams q.oldAliases ss

/-- **The SSA phase, the six-pass rewrite loop and beta reduction over-approximate the traces of
    each procedure body of the WP phase's output.** Let the WP phase (`wpPipelinePhase`) run on
    `prog` and return `mid`, and the SSA phase, the loop and beta reduction run in turn on `mid`
    and return `out`, every reserved prefix of `params` being free of `@`; let the contract-wrapped
    procedure bodies of `prog` be well typed under their parameter types
    (`WPPhaseInputWellTyped`) and `mid` satisfy the entry gates (`WPPipelineEntryGates`).  Every
    procedure of `out` with a structured body `ss` comes from a procedure `q₀` of `mid` with a
    structured body `lay`, the factory of the pipeline on `mid` being `fac`, such that the three
    phases map `lay` to `ss` (`wpRewriteTail`), `lay` satisfies their precondition
    (`WPRewriteTailPre`), and they over-approximate the traces
    (`WPRewriteLoop.ssa_loopBody_betaReduce_overapproximatesTraces`): their trace relation
    reflects the validity of every assertion (the SSA phase's relation and
    `WPRewriteLoop.loopTrace_assertValid_reflect`). -/
theorem wpRewritePipeline_overapproximatesTraces {moreFns : Lambda.Factory CoreLParams}
    {prog mid p₁ p₂ out : Program} (h₀ : PhaseRuns (wpPipelinePhase moreFns) prog mid)
    (h₁ : PhaseRuns (ssaPipelinePhase moreFns) mid p₁)
    (h₂ : PhaseRuns (wpRewriteLoopPipelinePhase moreFns) p₁ p₂)
    (h₃ : PhaseRuns betaReducePipelinePhase p₂ out)
    (π : String → Option Procedure) (params : Core.Logic.InitEnvWFParams)
    (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList) (hin : WPPhaseInputWellTyped prog)
    (hgate : WPPipelineEntryGates params moreFns mid)
    {q : Procedure} {md : Imperative.MetaData Expression} {ss : Statements}
    {opq : Bool} (hq : Decl.proc q md ∈ out.decls) (hb : q.body = .structured ss opq) :
    ∃ fac q₀ md₀ lay lo, Decl.proc q₀ md₀ ∈ mid.decls ∧ q₀.body = .structured lay lo ∧
      wpFactory moreFns mid = .ok fac ∧
      let G := Imperative.WP.IdSet.ofList
        (WP.avoidOf [] (fac.toArray.toList.map (·.name) ++ WP.declNames mid))
      wpRewriteTail fac G q₀ lay = some ss ∧ WPRewriteTailPre q₀ lay lay ∧
      OverapproximatesTracesUptoWhen (RComp (Trace.WeakensAssumes BigStep.evalInterp)
          WPRewriteLoop.LoopTrace)
        (WP.SSAEntryRel fac G q₀.paramTys q₀.entryParams q₀.oldAliases lay)
        (RComp (fun ρ ρ' => ρ'.factory = ρ.factory) WPRewriteLoop.LoopOut)
        (EventLang.coreBlock π) (EventLang.coreBlock π)
        (wpRewriteTail fac G q₀) (WPRewriteTailPre q₀ lay) params params := by
  obtain ⟨fac, q₀, md₀, lay, lo, r, hd₀, hb₀, hfac, hr, rfl, -⟩ :=
    wpRewritePipeline_proc h₁ h₂ h₃ hq hb
  obtain ⟨htree, harms, hfv, -⟩ := hgate _ hfac q₀ _ lay _ hd₀ hb₀
  obtain ⟨Γ₀, ⟨⟨hR₀, hC₀, hW₀⟩, -⟩, hty₀⟩ :=
    wpPipelinePhase_entryWellTyped h₀ hin q₀ _ lay _ hd₀ hb₀
  refine ⟨fac, q₀, md₀, lay, lo, hd₀, hb₀, hfac, ?_,
    ⟨⟨rfl, htree, harms, hfv⟩, Γ₀, hW₀, hR₀, hC₀, hty₀⟩,
    WPRewriteLoop.ssa_loopBody_betaReduce_overapproximatesTraces π params hp
      hfac _ _ _ _ (Procedure.oldAliases_mem q₀) lay⟩
  simp only [WP.ssaLoopFree] at hr
  simp [wpRewriteTail, hr, Except.toOption]

/-- **The six-pass rewrite loop's output has the body facts.** Let the SSA phase and the loop run
    in turn on `mid` and return `p₂`, every reserved prefix of `params` being free of `@`, and let
    `mid` satisfy the entry gates and its procedure bodies be well typed
    (`WPPipelineEntryWellTyped`). Then every procedure of `p₂` with a structured body has no
    parameters, and its body has the facts of `WPRewriteLoop.BodyOK`: the SSA phase gives its
    output these facts and each round of the loop keeps them. -/
theorem wpRewriteLoopPipeline_bodyFacts {moreFns : Lambda.Factory CoreLParams}
    {mid p₁ p₂ : Program} (h₁ : PhaseRuns (ssaPipelinePhase moreFns) mid p₁)
    (h₂ : PhaseRuns (wpRewriteLoopPipelinePhase moreFns) p₁ p₂)
    (params : Core.Logic.InitEnvWFParams) (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList)
    (hgate : WPPipelineEntryGates params moreFns mid) (hwt : WPPipelineEntryWellTyped mid) :
    ∀ q₂ md ss₂ o, Decl.proc q₂ md ∈ p₂.decls → q₂.body = .structured ss₂ o →
      q₂.header.inputs ++ q₂.header.outputs = [] ∧ ∃ D df Γ, WPRewriteLoop.BodyOK D df Γ ss₂ := by
  intro q₂ md ss₂ o hq₂ hb₂
  obtain ⟨fac, q₀, md₀, lay, lo, r, hd₀, hb₀, hfac, hr, rfl, hio⟩ :=
    wpRewriteLoopPipeline_proc h₁ h₂ hq₂ hb₂
  obtain ⟨htree, harms, hfv, ρ₀, ρ₀', hrel, hwf⟩ := hgate _ hfac q₀ _ lay _ hd₀ hb₀
  obtain ⟨Γ₀, ⟨⟨hR₀, -, hW₀⟩, -⟩, hty₀⟩ := hwt q₀ _ lay _ hd₀ hb₀
  have hT1 : (WP.ssaEntry fac (Imperative.WP.IdSet.ofList
      (WP.avoidOf [] (fac.toArray.toList.map (·.name) ++ WP.declNames mid))) q₀.paramTys
      q₀.entryParams q₀.oldAliases lay).toOption.map (·.2.out) = some r.2.out := by
    simp only [WP.ssaLoopFree] at hr
    simp [hr, Except.toOption]
  have hg1 := (WP.ssa_overapproximatesTraces_unassigned (fun _ => none) params hp _ _ _ _ _
    (Procedure.oldAliases_mem q₀) lay lay _ hT1 ⟨rfl, htree, harms, hfv⟩ ρ₀ ρ₀' hrel hwf).2.2.2
  have hss : WP.ssaEntry fac (Imperative.WP.IdSet.ofList
      (WP.avoidOf [] (fac.toArray.toList.map (·.name) ++ WP.declNames mid))) q₀.paramTys
      q₀.entryParams q₀.oldAliases lay = .ok r := by simpa [WP.ssaLoopFree] using hr
  have hi1 : Block.initsTyped Expression.Typed r.2.out :=
    WP.ssaEntry_initsTyped_renamed (typedOpLaws _) hss hW₀ hR₀ fun x hx T hT hk => by
      rw [(Imperative.WP.ssaEntry_ok hss).1] at hk
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hk
      exact hty₀ q.1 hx T hT ((Imperative.WP.ssaEntryRen_spec _ _ _ 0
        (Procedure.oldAliases_mem q₀)).2.1 q hq).2
  obtain ⟨Γ₁, -, hW₁⟩ := hg1.fvarTypesOk
  exact ⟨hio, _, _, _, WPRewriteLoop.loopBody_kept fac
    ⟨(WP.ssaEntry_passive hT1 htree).2.2, hg1.defUseOk, hW₁, hi1⟩⟩

/-- **The program `--vcgen wp` extracts obligations from is typed.** Let the SSA phase, the
    six-pass rewrite loop and beta reduction run in turn on `mid` and return `out`, every reserved
    prefix of `params` being free of `@`, and let `mid` satisfy the entry gates
    (`WPPipelineEntryGates`) and its procedure bodies be well typed
    (`WPPipelineEntryWellTyped`). Then the statement list extraction reads from every procedure of
    `out` is def-use well formed, agrees with a typing, and has every `init` typed at its declared
    type. -/
theorem wpRewritePipelineProgram_typed {moreFns : Lambda.Factory CoreLParams}
    {mid p₁ p₂ out : Program} (h₁ : PhaseRuns (ssaPipelinePhase moreFns) mid p₁)
    (h₂ : PhaseRuns (wpRewriteLoopPipelinePhase moreFns) p₁ p₂)
    (h₃ : PhaseRuns betaReducePipelinePhase p₂ out)
    (params : Core.Logic.InitEnvWFParams) (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList)
    (hgate : WPPipelineEntryGates params moreFns mid) (hwt : WPPipelineEntryWellTyped mid) :
    ∀ q md ss, Decl.proc q md ∈ out.decls → procedureStatements out.funcNames q = .ok ss →
      ∃ D df Γ, Block.defUseWellFormed D df ss = true ∧ Block.fvarTypesWellAnnotated Γ ss ∧
        Block.initsTyped Expression.Typed ss :=
  keepsBodyFacts_typed betaReduce_keepsBodyFacts h₃
    (wpRewriteLoopPipeline_bodyFacts h₁ h₂ params hp hgate hwt)

/-- **Definitions of the obligations `--vcgen wp` extracts are declared before use.** Under the
    hypotheses of `wpRewritePipelineProgram_typed`, every obligation `extractObligations out`
    returns has the definitions of its path condition, oldest first, declared before use with
    distinct variables (`DefsOrdered`). -/
theorem wpRewritePipelineProgram_extractObligations_defsOrdered
    {moreFns : Lambda.Factory CoreLParams} {mid p₁ p₂ out : Program}
    (h₁ : PhaseRuns (ssaPipelinePhase moreFns) mid p₁)
    (h₂ : PhaseRuns (wpRewriteLoopPipelinePhase moreFns) p₁ p₂)
    (h₃ : PhaseRuns betaReducePipelinePhase p₂ out)
    (params : Core.Logic.InitEnvWFParams) (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList)
    (hgate : WPPipelineEntryGates params moreFns mid) (hwt : WPPipelineEntryWellTyped mid)
    {obs : ProofObligations Expression} (h : extractObligations out = .ok obs) :
    ∀ ob ∈ obs, DefsOrdered (definitions ob.assumptions.reverse.flatten) :=
  extractObligations_defsOrdered h fun q md ss hq hss =>
    (wpRewritePipelineProgram_typed h₁ h₂ h₃ params hp hgate hwt q md ss hq hss).imp
      fun _ => .imp fun _ ⟨_, hd, _⟩ => hd

/-- **Definitions of the obligations `--vcgen wp` extracts are typed.** Under the hypotheses of
    `wpRewritePipelineProgram_typed`, every obligation `extractObligations out` returns has typed
    definitions (`DefsTyped`). -/
theorem wpRewritePipelineProgram_extractObligations_defsTyped
    {moreFns : Lambda.Factory CoreLParams} {mid p₁ p₂ out : Program}
    (h₁ : PhaseRuns (ssaPipelinePhase moreFns) mid p₁)
    (h₂ : PhaseRuns (wpRewriteLoopPipelinePhase moreFns) p₁ p₂)
    (h₃ : PhaseRuns betaReducePipelinePhase p₂ out)
    (params : Core.Logic.InitEnvWFParams) (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList)
    (hgate : WPPipelineEntryGates params moreFns mid) (hwt : WPPipelineEntryWellTyped mid)
    {obs : ProofObligations Expression} (h : extractObligations out = .ok obs) :
    ∀ ob ∈ obs, DefsTyped (typedDefinitions ob.assumptions.reverse.flatten) :=
  extractObligations_defsTyped h (wpRewritePipelineProgram_typed h₁ h₂ h₃ params hp hgate hwt)

end -- public section

end ObligationExtraction

open Imperative Imperative.PathConditions ObligationExtraction

/-- **A counterexample of a sliced obligation `--vcgen wp` extracts is one of the full
obligation, for a typed model.** Let the WP phase run on `prog` and return `mid`, and the SSA
phase, the six-pass rewrite loop and beta reduction run in turn on `mid` and return `out`, every
reserved prefix of `params` being free of `@`; let the contract-wrapped procedure bodies of
`prog` be well typed under their parameter types (`WPPhaseInputWellTyped`) and `mid` satisfy the
entry gates (`WPPipelineEntryGates`). For an obligation that `extractObligations out` returns, a
store satisfying the typed-model premise where the entries kept by leaving out the definitions
`unreadDefinitions` names hold (`SlicedModel`) extends to one where every entry holds and the goal
has the same value (`SlicedCounterexampleExtends`). -/
theorem wpRewritePipelineProgram_sliced_counterexample_extends {F : Expression.Factory}
    {σ : SemanticStore Expression} {moreFns : Lambda.Factory CoreLParams}
    {prog mid p₁ p₂ out : Program} (h₀ : PhaseRuns (wpPipelinePhase moreFns) prog mid)
    (h₁ : PhaseRuns (ssaPipelinePhase moreFns) mid p₁)
    (h₂ : PhaseRuns (wpRewriteLoopPipelinePhase moreFns) p₁ p₂)
    (h₃ : PhaseRuns betaReducePipelinePhase p₂ out)
    (params : Core.Logic.InitEnvWFParams) (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList)
    (hin : WPPhaseInputWellTyped prog) (hgate : WPPipelineEntryGates params moreFns mid)
    {obs : ProofObligations Expression} (h : extractObligations out = .ok obs)
    (obligation : ProofObligation Expression) (hob : obligation ∈ obs)
    (hm : SlicedModel F σ obligation) : SlicedCounterexampleExtends F σ obligation :=
  have hwt := wpPipelinePhase_entryWellTyped h₀ hin
  sliced_counterexample_extends_of_typed obligation
    (wpRewritePipelineProgram_extractObligations_defsOrdered h₁ h₂ h₃ params hp hgate hwt h
      obligation hob)
    (wpRewritePipelineProgram_extractObligations_defsTyped h₁ h₂ h₃ params hp hgate hwt h
      obligation hob) hm

end Core
