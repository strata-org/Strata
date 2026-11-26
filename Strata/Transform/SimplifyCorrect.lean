/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify.Precondition
public import Strata.Transform.Simplify.Entry
public import Strata.Transform.Simplify.Compose
public import Strata.Transform.Simplify.OutputGate
public import Strata.Languages.Core.Logic.LangDef
public import Strata.Transform.Specification
public import Strata.DL.Imperative.Logic.TraceRelations
public import Strata.DL.Imperative.BigStep.Sem
import all Strata.Transform.Simplify.Compose
import all Strata.Transform.Simplify.OutputGate
import all Strata.Transform.Simplify.SimpWF
import all Strata.Transform.Simplify.SimpRun
import all Strata.Transform.Simplify.SweepRun
import all Strata.Transform.Simplify.StmtSim
import all Strata.Transform.Simplify.Precondition
import all Strata.Transform.Simplify.Entry
import all Strata.Transform.Simplify
import Strata.Transform.DeadDefElimProps
import all Strata.Languages.Core.PipelinePhase
import Strata.DL.Imperative.BigStep.Adequacy
import Strata.DL.Imperative.StoreRelationsProps
import Strata.DL.Imperative.Logic.TraceRelationsProps
public import Strata.DL.Imperative.Analysis.Assertions
public import Strata.Languages.Core.Logic.Hoare
import Strata.Transform.SpecHoareConnection
import Strata.Languages.Core.StmtExtendCallBridgeProps
import Strata.Languages.Core.Logic.TraceInterpUsingDenoteProps
import Strata.Transform.Simplify.EvalSoundFold
public import Strata.DL.Lambda.Denote.LExprSemanticsConsistent
public import Strata.DL.Lambda.OperationalSemanticsProps
import all Strata.DL.Lambda.Denote.LExprSemanticsConsistent

/-! # The Simplify phase over-approximates the traces of a body

`sweptBody_overapproximatesTraces`: every finite trace prefix, terminating run and
exiting run of a structured body has a counterpart in the simplified body, with the same
assertions (same label, metadata and truth) and the same assumptions, and final stores that
agree on every live name. Assertion validity on the simplified body therefore carries back
to the original one (`sweptBody_assertValid`). These need the factory to bring in only its own
operators (`Lambda.Factory.OpsClosed`), under which the simplified body is well-formed
(`sweptBody_wf`). The phase installs the simplified body only when it passes its check and keeps
the body otherwise, and that checked body over-approximates the body's traces with no condition
on the factory's operators, since the check itself makes the installed body well-formed
(`gateOK_blockInitEnvWF`, `checkedBody_overapproximatesTraces`), and assertion validity carries
back through it (`checkedBody_assertValid`); `simplifyPhase_over` states this for every procedure
of a run of the phase. A Core Hoare triple proved on the checked body carries back to the
body (`checkedBody_triple`).

The proof runs a trace of the body as a big-step run, matches it with a run of the
simplification pass's output from the same store (`simp_run`, `simp_reach`), and replays
that on the output of the dead-definition sweep (`sweep_run`, `sweep_reach`).
-/

namespace Core.Simplify

open Imperative Imperative.BigStep Imperative.Specification
  Imperative.Specification.Transform
  Strata.Logic
  Core.Logic Core.DeadDefElim

public section

/-! ## The theorem -/

/-- Under `Lambda.Factory.OpsClosed`, the simplified body's entry environment is well-formed
    wherever the body's is: the simplified body is def-use well-formed from the entry store and
    annotated for the restricted entry typing, which the entry store conforms to
    (`sweptBody_wf`). -/
private theorem sweptBody_entryWF (params : Core.Logic.InitEnvWFParams) (base : Ctx)
    (proc : Procedure) (Γ : VarTyping Expression) (hfresh : base.Fresh)
    (hlaws : Lambda.Factory.EvalSoundWF base.factory)
    (hclosed : Lambda.Factory.OpsClosed base.factory) {ss : List Statement}
    (hbwf : BodyWF base.factory Γ ss) {ρ₀ : Imperative.Env Expression}
    (hwf : Core.Logic.BlockInitEnvWF params ss ρ₀) (hrel : EntryRel base.factory Γ ss ρ₀ ρ₀) :
    Core.Logic.BlockInitEnvWF params (sweptBody base proc ss) ρ₀ := by
  obtain ⟨-, hF, hst0⟩ := hrel
  obtain ⟨⟨hnc, hss⟩, -⟩ := id hbwf
  have hok := (hbwf.restrict hwf.defUseOk hwf.defsUndefined).2
  obtain ⟨hfwf, hfstep⟩ : Lambda.Factory.EvalSoundWF base.foldFactory :=
    hfresh.1 ▸ evalSoundWF_withoutInline hlaws
  have hb : ∀ x ∈ Block.entryVars ss, (ρ₀.store x).isSome := fun x hx => by
    simp only [Block.entryVars, List.mem_filter, decide_eq_true_eq] at hx
    exact hwf.readWritesDefined x hx.1 hx.2
  have hB : WFSetup base params.declaredFuncs :=
    ⟨⟨hfresh.1, hfwf.choose_spec.factoryWF⟩, hfresh.1 ▸ opsClosed_withoutInline hclosed, hfstep,
      fun o ho => hwf.runtimeFactoryDeclared o (hF ▸ (withoutInline_mem _ _ _).mp
        (hfresh.1 ▸ ho))⟩
  have hinit : ∀ ty ∈ Block.initTypes (P := Expression) (C := Command) ss,
      ∃ τ, ty = .forAll [] τ := fun ty hty => by
    obtain ⟨v, -, hm⟩ := hwf.initTypesInhabited ty hty
    exact ⟨_, Option.some.inj (eq_forAll_of_bind (t? := some ty) hm)⟩
  obtain ⟨hdu', hann'⟩ := sweptBody_wf hB hfresh.2 proc (restrictTyping_mono hst0 hb) hinit hss
    hnc hwf.defUseOk hok
  exact sweptBody_blockInitEnvWF hwf hdu'
    ⟨_, restrictTyping_storeHasTyping hst0 hb, hann'⟩ hss

/-- The traces of a body are over-approximated by those of its simplified body, given that the
    simplified body's entry environment is well-formed wherever the body's is. Both the proof
    from `Lambda.Factory.OpsClosed` (`sweptBody_overapproximatesTraces`) and the proof from the
    phase's check (`checkedBody_overapproximatesTraces`) supply that. -/
private theorem sweptBody_over_of_entryWF (π : String → Option Procedure)
    (params : Core.Logic.InitEnvWFParams) (base : Ctx) (proc : Procedure)
    (Γ : VarTyping Expression) (hfresh : base.Fresh)
    (hlaws : Lambda.Factory.EvalSoundWF base.factory)
    (ss₀ : List Statement)
    (hout : ∀ ρ₀, BodyWF base.factory Γ ss₀ → Core.Logic.BlockInitEnvWF params ss₀ ρ₀ →
      EntryRel base.factory Γ ss₀ ρ₀ ρ₀ →
      Core.Logic.BlockInitEnvWF params (sweptBody base proc ss₀) ρ₀) :
    OverapproximatesTracesUptoWhen (Trace.WeakensAssumes Imperative.BigStep.evalInterp)
      (EntryRel base.factory Γ ss₀) (EnvAgreeOnLive (procLive proc))
      (Core.Logic.EventLang.coreBlock π) (Core.Logic.EventLang.coreBlock π)
      (fun ss => some (sweptBody base proc ss))
      (fun ss => ss = ss₀ ∧ BodyWF base.factory Γ ss) params params := by
  intro ss out hT ⟨rfl, hbwf⟩ ρ₀ ρ₀' hrel hwf
  have htw := hout ρ₀ hbwf hwf ⟨rfl, hrel.2⟩
  obtain ⟨hρ, hF, hst⟩ := hrel
  rw [hρ]
  -- The run invariant types only the entry variables: restrict `Γ` to them.
  obtain ⟨⟨hnc, hss⟩, -⟩ := id hbwf
  have hok := (hbwf.restrict hwf.defUseOk hwf.defsUndefined).2
  have hst := hst.restrict
  have hT' := Option.some.inj hT
  subst hT'
  obtain ⟨hfwf, hfstep⟩ : Lambda.Factory.EvalSoundWF base.foldFactory :=
    hfresh.1 ▸ evalSoundWF_withoutInline hlaws
  obtain ⟨σ₀, M⟩ := ρ₀
  have hC : WellFormedStore σ₀ M := hwf.storeWellDefined
  have hE : EvCongr M := evCongr_of_congr hwf.exprCongr
  have hWB := hwf.bool
  have S : Setup base M := ⟨hfresh.1, hF, hfwf, hfstep⟩
  have I := inv_entry (M := M) hfresh hst hC hwf.readWritesDefined hwf.defsUndefined
    (restrictTyping_declsUntyped Γ ss)
  have hT0 : ∀ y ∈ Block.idents ss, y ∈ Block.idents ss := fun _ h => h
  have hA0 : ∀ (N : List CoreIdent), Agree N σ₀ σ₀ :=
    fun _ => ⟨fun _ _ => rfl, storeAgreement_iff.2 fun _ => .inl rfl⟩
  refine ⟨fun cfg trace h => ?_, fun ρ' trace h => ?_, fun l ρ' trace h => ?_, htw⟩
  · have h' := star_evalE h hnc
    by_cases htr : trace = []
    · subst htr
      exact ⟨_, [], .refl _, .nil⟩
    obtain ⟨evs1, hb1, hm1⟩ := simp_reach S (star_breach h' htr) I hok hT0 hss
    obtain ⟨evs2, hb2, hm2⟩ :=
      sweep_reach hE hb1 (hm1.ne_nil htr) (simpStmts_noLoops _ _ hss) hC (hA0 _)
    obtain ⟨cfg', hc⟩ := breach_star hWB hb2
    exact ⟨cfg', evs2, star_core π hc,
      Trace.WeakensAssumes.of_rel₂ (rel₂_weakensAssume_replay hE hm1 hm2)⟩
  · have h' := star_evalE h hnc
    have hEf := starE_preserves_factory h'
    obtain ⟨evs1, hb1, hm1, -⟩ := simp_run S (star_brun.1 h') I hok hT0 hss
    obtain ⟨evs2, o', hb2, hm2, hO⟩ := sweep_run hE hb1 (simpStmts_noLoops _ _ hss) hC (hA0 _)
    rcases o' with σ'' | _ <;> simp only [OAgree] at hO
    exact ⟨_, evs2, star_core π (brun_star hWB hb2),
      ⟨fun x hx => hO.1.1 x (mem_liveIds.mpr (live_iff_mem.mp hx)), hEf⟩,
      Trace.WeakensAssumes.of_rel₂ (rel₂_weakensAssume_replay hE hm1 hm2)⟩
  · have h' := star_evalE h hnc
    have hEf := starE_preserves_factory h'
    obtain ⟨evs1, hb1, hm1, -⟩ := simp_run S (star_brun.2 h') I hok hT0 hss
    obtain ⟨evs2, o', hb2, hm2, hO⟩ := sweep_run hE hb1 (simpStmts_noLoops _ _ hss) hC (hA0 _)
    rcases o' with _ | ⟨l', σ''⟩ <;> simp only [OAgree] at hO
    obtain ⟨rfl, hO⟩ := hO
    exact ⟨_, evs2, star_core π (brun_star hWB hb2),
      ⟨fun x hx => hO.1.1 x (mem_liveIds.mpr (live_iff_mem.mp hx)), hEf⟩,
      Trace.WeakensAssumes.of_rel₂ (rel₂_weakensAssume_replay hE hm1 hm2)⟩



/-- **The Simplify phase over-approximates the traces of a body.** For a body in the
    fragment whose expressions are typed under the entry typing `Γ` (`BodyWF`), simplified
    from a fresh context (`Ctx.Fresh`) whose factory meets the conditions of evaluator
    soundness (`Lambda.Factory.EvalSoundWF`, which `Core.programFactory_evalSoundWF` gives
    program factories), from any entry environment the gate admits whose store gives the
    body's entry variables their `Γ` types (`EntryRel`):
    * every finite trace of the body has a trace of the simplified body related by
      `Trace.WeakensAssumes evalInterp`, event for event;
    * every terminating or exiting run has one of the simplified body with the same outcome,
      such a trace, and a final store agreeing on every live name (`EnvAgreeOnLive`);
    * the simplified body's entry environment is well-formed for the same parameters
      (`sweptBody_blockInitEnvWF`).

    `Γ` is the **entry typing**, the typing of the names the body reads or writes without
    declaring (`Block.entryVars ss₀`); what it says of the body's locals is not used, as they
    are typed scope by scope inside `ExprOK`. `hfresh` says the context records nothing yet.

    `sweptBody base proc` is the body `simplifyProcedure` computes for `proc` before its
    check (`checkedBody`): the statements rewritten, then the definitions nothing reads
    dropped. The live names are `procLive proc`, the outputs and the free variables of the
    contract. That is enough at a call site: Core's type checker rejects a body that writes
    anything but its outputs and its own locals, so no global or input the body writes can be
    read after it.

    `hclosed` says the factory brings in only its own operators (`Lambda.Factory.OpsClosed`,
    which `Core.programFactory_opsClosed` gives program factories): a function body mentions
    only functions of the factory, and a concrete evaluator returns only operators of the
    factory or of its arguments. The gate declares every function of the factory
    (`BlockInitEnvWF.runtimeFactoryDeclared`), so the operators an inlined body brings in are
    declared, and the simplified body is def-use well-formed (`sweptBody_wf`). -/
theorem sweptBody_overapproximatesTraces (π : String → Option Procedure)
    (params : Core.Logic.InitEnvWFParams) (base : Ctx) (proc : Procedure)
    (Γ : VarTyping Expression) (hfresh : base.Fresh)
    (hlaws : Lambda.Factory.EvalSoundWF base.factory)
    (hclosed : Lambda.Factory.OpsClosed base.factory)
    (ss₀ : List Statement) :
    OverapproximatesTracesUptoWhen (Trace.WeakensAssumes Imperative.BigStep.evalInterp)
      (EntryRel base.factory Γ ss₀) (EnvAgreeOnLive (procLive proc))
      (Core.Logic.EventLang.coreBlock π) (Core.Logic.EventLang.coreBlock π)
      (fun ss => some (sweptBody base proc ss))
      (fun ss => ss = ss₀ ∧ BodyWF base.factory Γ ss) params params :=
  sweptBody_over_of_entryWF π params base proc Γ hfresh hlaws ss₀ fun _ hbwf hwf hrel =>
    sweptBody_entryWF params base proc Γ hfresh hlaws hclosed hbwf hwf hrel

/-- **Assertion validity carries back through Simplify.** If every occurrence of the
    assertion `aid` holds under its preceding assumptions on every trace of the simplified
    body from every environment its gate admits, the same holds of the body from every
    environment its gate admits whose store gives its entry variables their `Γ` types. -/
theorem sweptBody_assertValid (π : String → Option Procedure)
    (params : Core.Logic.InitEnvWFParams) (base : Ctx) (proc : Procedure)
    (Γ : VarTyping Expression) (hfresh : base.Fresh)
    (hlaws : Lambda.Factory.EvalSoundWF base.factory)
    (hclosed : Lambda.Factory.OpsClosed base.factory)
    (ss₀ : List Statement) (hwf : BodyWF base.factory Γ ss₀)
    {aid : AssertId Expression}
    (hvalid : AssertValidOnTracesWhen (Core.Logic.EventLang.coreBlock π) evalInterp
      (Core.Logic.BlockInitEnvWF params (sweptBody base proc ss₀)) (sweptBody base proc ss₀)
      aid) :
    AssertValidOnTracesWhen (Core.Logic.EventLang.coreBlock π) evalInterp
      (fun ρ => Core.Logic.BlockInitEnvWF params ss₀ ρ ∧ EntryRel base.factory Γ ss₀ ρ ρ) ss₀
      aid := by
  intro ρ₀ cfg trace ⟨hinit, hrel⟩ htrace
  have hr := sweptBody_overapproximatesTraces π params base proc Γ hfresh hlaws hclosed ss₀
    ss₀ _ rfl ⟨rfl, hwf⟩ ρ₀ ρ₀ hrel hinit
  obtain ⟨cfg', trace', htrace', hrel'⟩ := hr.1 cfg trace htrace
  exact hrel'.assertionValid aid (hvalid ρ₀ cfg' trace' hr.2.2.2 htrace')


/-! ## The checked body -/

/-- **The checked body over-approximates the traces of a body**, with no condition on which
    operators the factory brings in: when the simplified body passes the phase's check, that
    check makes its entry environment well-formed (`gateOK_blockInitEnvWF`), and otherwise the
    body is kept unchanged, which over-approximates itself. -/
theorem checkedBody_overapproximatesTraces (π : String → Option Procedure)
    (params : Core.Logic.InitEnvWFParams) (base : Ctx) (proc : Procedure)
    (Γ : VarTyping Expression) (hfresh : base.Fresh)
    (hlaws : Lambda.Factory.EvalSoundWF base.factory)
    (ss₀ : List Statement) :
    OverapproximatesTracesUptoWhen (Trace.WeakensAssumes Imperative.BigStep.evalInterp)
      (EntryRel base.factory Γ ss₀) (EnvAgreeOnLive (procLive proc))
      (Core.Logic.EventLang.coreBlock π) (Core.Logic.EventLang.coreBlock π)
      (fun ss => some (checkedBody base proc ss))
      (fun ss => ss = ss₀ ∧ BodyWF base.factory Γ ss) params params := by
  intro ss out hT hpre
  obtain ⟨rfl, -⟩ := id hpre
  replace hT := Option.some.inj hT
  simp only [checkedBody] at hT
  by_cases hok : gateOK base.factory ss (sweptBody base proc ss) = true
  · simp only [hok, ↓reduceIte] at hT
    subst hT
    exact sweptBody_over_of_entryWF π params base proc Γ hfresh hlaws ss
      (fun _ hbwf hwf hrel => gateOK_blockInitEnvWF hwf hrel.2.1 hok hbwf.1.2) ss _ rfl hpre
  · simp only [hok] at hT
    subst hT
    intro ρ₀ ρ₀' hR hwf
    obtain ⟨rfl, -⟩ := hR
    exact ⟨fun cfg tr h => ⟨cfg, tr, h, Trace.WeakensAssumes.refl _ tr⟩,
      fun ρ' tr h => ⟨ρ', tr, h, ⟨fun _ _ => rfl, rfl⟩, Trace.WeakensAssumes.refl _ tr⟩,
      fun _ ρ' tr h => ⟨ρ', tr, h, ⟨fun _ _ => rfl, rfl⟩, Trace.WeakensAssumes.refl _ tr⟩, hwf⟩

/-- **Assertion validity carries back through the checked body.** If every occurrence of
    the assertion `aid` holds under its preceding assumptions on every trace of the body the
    phase installs, from every environment its gate admits, the same holds of the original
    body from every environment its gate admits whose store gives its entry variables their
    `Γ` types. -/
theorem checkedBody_assertValid (π : String → Option Procedure)
    (params : Core.Logic.InitEnvWFParams) (base : Ctx) (proc : Procedure)
    (Γ : VarTyping Expression) (hfresh : base.Fresh)
    (hlaws : Lambda.Factory.EvalSoundWF base.factory)
    (ss₀ : List Statement) (hwf : BodyWF base.factory Γ ss₀)
    {aid : AssertId Expression}
    (hvalid : AssertValidOnTracesWhen (Core.Logic.EventLang.coreBlock π) evalInterp
      (Core.Logic.BlockInitEnvWF params (checkedBody base proc ss₀)) (checkedBody base proc ss₀)
      aid) :
    AssertValidOnTracesWhen (Core.Logic.EventLang.coreBlock π) evalInterp
      (fun ρ => Core.Logic.BlockInitEnvWF params ss₀ ρ ∧ EntryRel base.factory Γ ss₀ ρ ρ) ss₀
      aid := by
  intro ρ₀ cfg trace ⟨hinit, hrel⟩ htrace
  have hr := checkedBody_overapproximatesTraces π params base proc Γ hfresh
    hlaws ss₀ ss₀ _ rfl ⟨rfl, hwf⟩ ρ₀ ρ₀ hrel hinit
  obtain ⟨cfg', trace', htrace', hrel'⟩ := hr.1 cfg trace htrace
  exact hrel'.assertionValid aid (hvalid ρ₀ cfg' trace' hr.2.2.2 htrace')

/-- **A Core triple carries back through the checked body.** For a body meeting the
    hypotheses of `checkedBody_overapproximatesTraces`, and a precondition admitting only
    entries over the context's factory: a triple `{Pre} checkedBody base proc ss₀ {Post'}`
    read by `DenoteBasedInterp base.factory` gives the triple `{Pre} ss₀ {Post}`, when every
    entry satisfying `Pre` and the gate gives the body's entry variables their `Γ` types, and
    `Post'` of an environment gives `Post` of every environment that agrees with it on the
    live names `procLive proc` and has its factory. -/
theorem checkedBody_triple (π : String → Option Procedure)
    (params : Core.Logic.InitEnvWFParams) (base : Ctx) (proc : Procedure)
    (Γ : VarTyping Expression) (hfresh : base.Fresh)
    (hlaws : Lambda.Factory.EvalSoundWF base.factory)
    (ss₀ : List Statement) (hwf : BodyWF base.factory Γ ss₀)
    {Pre Post Post' : Imperative.Env Expression → Prop}
    (hpin : ∀ ρ₀, Pre ρ₀ → ρ₀.factory.factory = base.factory)
    (htyped : ∀ ρ₀, Pre ρ₀ → Core.Logic.BlockInitEnvWF params ss₀ ρ₀ →
      StoreTypedBy ρ₀.factory Γ ss₀ ρ₀.store)
    (hpost : ∀ ρ' ρ'', EnvAgreeOnLive (procLive proc) ρ' ρ'' → Post' ρ'' → Post ρ')
    (h : Core.Logic.Hoare.Triple π params Pre (checkedBody base proc ss₀) Post' base.factory) :
    Core.Logic.Hoare.Triple π params Pre ss₀ Post base.factory := by
  obtain ⟨⟨hnc, -⟩, -⟩ := id hwf
  have hnc' := checkedBody_noCalls base proc hnc
  refine overapproximatesTraces2UptoWhen_triple_of_sourceRuns (EventLang.coreBlock π)
    (EventLang.coreBlock π) (DenoteBasedInterp base.factory) _ _ _
    (fun ss => some (checkedBody base proc ss)) _ params params ss₀ (checkedBody base proc ss₀)
    rfl (checkedBody_overapproximatesTraces π params base proc Γ hfresh hlaws ss₀) h
    ⟨rfl, hwf⟩
    (fun tr => ∀ ev ∈ tr, ev.condition.factory.factory = base.factory)
    (fun tr => ∀ ev ∈ tr, ev.condition.factory.factory = base.factory) ?_ ?_
    (fun ρ₀ hp hg => ⟨ρ₀, ⟨rfl, hpin ρ₀ hp, htyped ρ₀ hp hg⟩, hp⟩) ?_ ?_
    (fun _ ρ' ρ'' _ _ _ _ hR hp => hpost ρ' ρ'' hR hp)
  · intro ρ₀ ρ' trace hp _ hrun ev hev
    rw [coreBlock_events_factory hnc hrun ev hev]
    exact hpin ρ₀ hp
  · intro ρ₀ ρ₀' ρ'' trace hp hrel _ hrun ev hev
    rw [coreBlock_events_factory hnc' hrun ev hev, hrel.1]
    exact hpin ρ₀ hp
  · intro _ _ hs ht hrel hv
    exact (weakensAssumes_denoteBasedInterp hrel hs ht).assertionsValid_reflect hv
  · intro _ _ hs ht hrel _ ⟨w, hw⟩
    exact ⟨w, (weakensAssumes_denoteBasedInterp hrel hs ht).assumptionsHold_transfer hw⟩

/-! ## The phase -/

/-- A procedure's structured body is replaced by `checkedBody` of it, for the procedure with
    its contract simplified. -/
private theorem simplifyProcedure_body (base : Ctx) (q : Procedure) {ss : List Statement}
    (hb : q.body = .structured ss opq) :
    (simplifyProcedure base q).body =
      .structured (checkedBody base (simplifySpec base q) ss) opq := by
  have hb' : (simplifySpec base q).body = .structured ss opq := hb
  unfold simplifyProcedure
  simp only [hb']

/-- A run of `runSimplify` simplifies every procedure of the program from one fresh
    context. -/
private theorem runSimplify_ok {p out : Program} {s s' : Transform.CoreTransformState} {b : Bool}
    (h : (runSimplify p).run s = (.ok (b, out), s')) :
    ∃ base : Ctx, base.Fresh ∧ ∀ q md, Decl.proc q md ∈ p.decls →
      Decl.proc (simplifyProcedure base q) md ∈ out.decls := by
  unfold runSimplify baseCtx at h
  simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.run, StateT.bind, pure, ExceptT.pure]
    at h
  rcases hF : programFactory p s with ⟨_ | F, s1⟩ <;> rw [hF] at h
  · cases h
  · simp only [ExceptT.bindCont, StateT.pure] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    refine ⟨Ctx.ofFactory F (lambdaCarriers p), Ctx.ofFactory_fresh _ _, fun q md hq => ?_⟩
    exact List.mem_map.mpr ⟨_, hq, rfl⟩


/-- A run of the Simplify pipeline phase is a run of `runSimplify`. -/
private theorem simplifyPhase_ok (program : Program) (s : Transform.CoreTransformState) :
    (Core.simplifyPhase.transform program).run s = (runSimplify program).run s :=
  (rfl)

/-- **The Simplify phase over-approximates each procedure body.** A run of the phase
    simplifies every procedure of the program from one fresh context `base`; each structured
    body becomes a body that over-approximates its traces
    (`checkedBody_overapproximatesTraces`) under the theorem's hypotheses on `base`,
    the body and its entry typing. -/
theorem simplifyPhase_over {program out : Program} {s s' : Transform.CoreTransformState}
    {b : Bool} (h : (Core.simplifyPhase.transform program).run s = (.ok (b, out), s')) :
    ∃ base : Ctx, base.Fresh ∧ ∀ q md ss opq, Decl.proc q md ∈ program.decls →
      q.body = .structured ss opq →
        Decl.proc (simplifyProcedure base q) md ∈ out.decls ∧
        (simplifyProcedure base q).body =
          .structured (checkedBody base (simplifySpec base q) ss) opq ∧
        ∀ (π : String → Option Procedure) (params : Core.Logic.InitEnvWFParams)
          (Γ : VarTyping Expression), Lambda.Factory.EvalSoundWF base.factory →
          OverapproximatesTracesUptoWhen (Trace.WeakensAssumes Imperative.BigStep.evalInterp)
            (EntryRel base.factory Γ ss) (EnvAgreeOnLive (procLive (simplifySpec base q)))
            (Core.Logic.EventLang.coreBlock π) (Core.Logic.EventLang.coreBlock π)
            (fun ss' => some (checkedBody base (simplifySpec base q) ss'))
            (fun ss' => ss' = ss ∧ BodyWF base.factory Γ ss') params params := by
  obtain ⟨base, hfresh, hmem⟩ := runSimplify_ok (simplifyPhase_ok program s ▸ h)
  refine ⟨base, hfresh, fun q md ss _ hq hb => ?_⟩
  exact ⟨hmem q md hq, simplifyProcedure_body base q hb, fun π params Γ hlaws =>
    checkedBody_overapproximatesTraces π params base (simplifySpec base q) Γ hfresh hlaws ss⟩

end

end Core.Simplify
