/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify.Precondition
public import Strata.Transform.Simplify.Entry
public import Strata.Transform.Simplify.Compose
public import Strata.Transform.Simplify.TargetGate
public import Strata.Languages.Core.Logic.LangDef
public import Strata.Transform.Specification
public import Strata.DL.Imperative.Logic.TraceRelations
public import Strata.DL.Imperative.BigStep.Sem
import all Strata.Transform.Simplify.Compose
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

/-! # The Simplify phase over-approximates the traces of a body

`simplifyBody_overapproximatesTraces`: every finite trace prefix, terminating run and
exiting run of a structured body has a counterpart in the simplified body, with the same
assertions (same label, metadata and truth) and the same assumptions, and final stores that
agree on every live name. Assertion validity on the simplified body therefore carries back
to the original one (`simplifyBody_assertValid`). The phase installs the simplified body only
when it passes its check and keeps the body otherwise, and that checked body
over-approximates the body's traces with no hypothesis on Simplify's output
(`simplifyBodyChecked_overapproximatesTraces`), and assertion validity carries back through
it (`simplifyBodyChecked_assertValid`); `simplifyPhase_over` states this for every procedure
of a run of the phase.

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

/-- **The Simplify phase over-approximates the traces of a body.** For a body in the
    fragment whose expressions are typed (`BodyWF`), simplified from a fresh context
    (`Ctx.Fresh`) whose fold factory satisfies the laws of the denotational semantics
    (`Laws`) with no variable named like a function's formal at another type
    (`Block.clashesWithFormals`), with an entry typing that types no variable the body
    declares, from any entry environment the gate admits whose store gives the body's
    entry variables their `Γ` types (`EntryRel`):
    * every finite trace of the body has a trace of the simplified body related by
      `Trace.WeakensAssumes evalInterp`, event for event;
    * every terminating or exiting run has one of the simplified body with the same outcome,
      such a trace, and a final store agreeing on every live name (`EnvAgreeOnLive`);
    * the simplified body's entry environment is well-formed for the same parameters
      (`targetWFB_sound`).

    `Γ` is the **entry typing**: the type checker's typing of the procedure restricted to
    `Block.entryVars ss₀`, the names the body reads or writes without declaring. Built
    that way it types no name the body declares, so `hΓ` holds by construction; the body's
    locals are typed scope by scope inside `ExprOK`, not by `Γ`. `hfresh` says the context
    records nothing yet.

    `htarget` constrains Simplify's **output**: the simplified body is def-use well-formed
    from the body's entry variables (`targetWFB`), with the operators of inlined bodies among
    `params.declaredFuncs`. It is a hypothesis because the type checker does not yet
    guarantee def-use well-formedness (the TODO on `Stmt.defUseWellFormed`). -/
theorem simplifyBody_overapproximatesTraces (π : String → Option Procedure)
    (params : Core.Logic.InitEnvWFParams) (base : Ctx)
    (inputs : @Lambda.LMonoTySignature Unit) (live : Std.HashSet String)
    (Γ : VarTyping Expression) (hfresh : base.Fresh) (hlaws : Laws base.foldFactory)
    (ss₀ : List Statement)
    (hclash : Block.clashesWithFormals base.foldFactory Γ ss₀ = false)
    (hΓ : ∀ x ∈ Block.definedVars (P := Expression) (C := Command) ss₀ false, Γ x = none)
    (htarget : ∀ out, simplifyBody base inputs live ss₀ = some out →
      targetWFB params ss₀ out = true) :
    OverapproximatesTracesUptoWhen (Trace.WeakensAssumes Imperative.BigStep.evalInterp)
      (EntryRel base.factory Γ ss₀) (EnvAgreeOnLive live)
      (Core.Logic.EventLang.coreBlock π) (Core.Logic.EventLang.coreBlock π)
      (simplifyBody base inputs live)
      (fun ss => ss = ss₀ ∧ BodyWF base.factory Γ ss) params params := by
  intro ss out hT ⟨rfl, ⟨hnc, hss⟩, hok⟩ ρ₀ ρ₀' hrel hwf
  obtain ⟨hρ, hF, hst⟩ := hrel
  rw [hρ]
  have htw := targetWFB_sound hwf hT (htarget out hT) hss
  have hT' := Option.some.inj hT
  subst hT'
  obtain ⟨σ₀, M⟩ := ρ₀
  have hC : WellFormedStore σ₀ M := hwf.storeWellDefined
  have hE : EvCongr M := evCongr_of_congr hwf.exprCongr
  have hWB := hwf.bool
  have S : Setup base M (typeList Γ ss) :=
    ⟨hfresh.1, hF, hlaws.1, fun tyMap h => hlaws.2 tyMap (agreesOnFormals_of_noClash hclash h)⟩
  have I := inv_entry (M := M) hfresh hst hC hwf.readWritesDefined hwf.defsUndefined hΓ
  have hT0 : ∀ y ∈ Block.idents ss, y ∈ Block.idents ss := fun _ h => h
  have hL0 : ∀ p ∈ Block.declaredTypes ss, p ∈ typeList Γ ss :=
    fun _ h => List.mem_append_right _ h
  have hA0 : ∀ (N : List CoreIdent), Agree N σ₀ σ₀ :=
    fun _ => ⟨fun _ _ => rfl, storeAgreement_iff.2 fun _ => .inl rfl⟩
  refine ⟨fun cfg trace h => ?_, fun ρ' trace h => ?_, fun l ρ' trace h => ?_, htw⟩
  · have h' := star_evalE h hnc
    by_cases htr : trace = []
    · subst htr
      exact ⟨_, [], .refl _, .nil⟩
    obtain ⟨evs1, hb1, hm1⟩ := simp_reach S (star_breach h' htr) I hok hT0 hL0 hss
    obtain ⟨evs2, hb2, hm2⟩ :=
      sweep_reach hE hb1 (hm1.ne_nil htr) (simpStmts_noLoops _ _ hss) hC (hA0 _)
    obtain ⟨cfg', hc⟩ := breach_star hWB hb2
    exact ⟨cfg', evs2, star_core π hc,
      Trace.WeakensAssumes.of_rel₂ (rel₂_weakensAssume_replay hE hm1 hm2)⟩
  · have h' := star_evalE h hnc
    have hEf := starE_preserves_factory h'
    obtain ⟨evs1, hb1, hm1, -⟩ := simp_run S (star_brun.1 h') I hok hT0 hL0 hss
    obtain ⟨evs2, o', hb2, hm2, hO⟩ := sweep_run hE hb1 (simpStmts_noLoops _ _ hss) hC (hA0 _)
    rcases o' with σ'' | _ <;> simp only [OAgree] at hO
    exact ⟨_, evs2, star_core π (brun_star hWB hb2),
      ⟨fun x hx => hO.1.1 x (mem_liveIds.mpr (live_iff_mem.mp hx)), hEf⟩,
      Trace.WeakensAssumes.of_rel₂ (rel₂_weakensAssume_replay hE hm1 hm2)⟩
  · have h' := star_evalE h hnc
    have hEf := starE_preserves_factory h'
    obtain ⟨evs1, hb1, hm1, -⟩ := simp_run S (star_brun.2 h') I hok hT0 hL0 hss
    obtain ⟨evs2, o', hb2, hm2, hO⟩ := sweep_run hE hb1 (simpStmts_noLoops _ _ hss) hC (hA0 _)
    rcases o' with _ | ⟨l', σ''⟩ <;> simp only [OAgree] at hO
    obtain ⟨rfl, hO⟩ := hO
    exact ⟨_, evs2, star_core π (brun_star hWB hb2),
      ⟨fun x hx => hO.1.1 x (mem_liveIds.mpr (live_iff_mem.mp hx)), hEf⟩,
      Trace.WeakensAssumes.of_rel₂ (rel₂_weakensAssume_replay hE hm1 hm2)⟩


/-- **Assertion validity carries back through Simplify.** If every occurrence of the
    assertion `aid` holds under its preceding assumptions on every trace of the simplified
    body from every environment its gate admits, the same holds of the body from every
    environment its gate admits whose store gives its entry variables their `Γ` types. -/
theorem simplifyBody_assertValid (π : String → Option Procedure)
    (params : Core.Logic.InitEnvWFParams) (base : Ctx)
    (inputs : @Lambda.LMonoTySignature Unit) (live : Std.HashSet String)
    (Γ : VarTyping Expression) (hfresh : base.Fresh) (hlaws : Laws base.foldFactory)
    (ss₀ : List Statement) (hwf : BodyWF base.factory Γ ss₀)
    (hclash : Block.clashesWithFormals base.foldFactory Γ ss₀ = false)
    (hΓ : ∀ x ∈ Block.definedVars (P := Expression) (C := Command) ss₀ false, Γ x = none)
    (htarget : ∀ out, simplifyBody base inputs live ss₀ = some out →
      targetWFB params ss₀ out = true)
    {out : List Statement} (hout : simplifyBody base inputs live ss₀ = some out)
    {aid : AssertId Expression}
    (hvalid : AssertValidOnTracesWhen (Core.Logic.EventLang.coreBlock π) evalInterp
      (Core.Logic.BlockInitEnvWF params out) out aid) :
    AssertValidOnTracesWhen (Core.Logic.EventLang.coreBlock π) evalInterp
      (fun ρ => Core.Logic.BlockInitEnvWF params ss₀ ρ ∧ EntryRel base.factory Γ ss₀ ρ ρ) ss₀
      aid := by
  intro ρ₀ cfg trace ⟨hinit, hrel⟩ htrace
  have hr := simplifyBody_overapproximatesTraces π params base inputs live Γ hfresh hlaws ss₀
    hclash hΓ htarget ss₀ out hout ⟨rfl, hwf⟩ ρ₀ ρ₀ hrel hinit
  obtain ⟨cfg', trace', htrace', hrel'⟩ := hr.1 cfg trace htrace
  exact hrel'.assertionValid aid (hvalid ρ₀ cfg' trace' hr.2.2.2 htrace')


/-! ## The checked body -/

/-- **The checked body over-approximates the traces of a body**, with no hypothesis on
    Simplify's output: when the simplified body passes the phase's def-use check it is
    `simplifyBody_overapproximatesTraces`'s, and otherwise the body is kept unchanged, which
    over-approximates itself. The
    declared functions of `params` include the factory's, which is how a caller sets them. -/
theorem simplifyBodyChecked_overapproximatesTraces (π : String → Option Procedure)
    (params : Core.Logic.InitEnvWFParams) (base : Ctx)
    (inputs : @Lambda.LMonoTySignature Unit) (live : Std.HashSet String)
    (Γ : VarTyping Expression) (hfresh : base.Fresh) (hlaws : Laws base.foldFactory)
    (ss₀ : List Statement)
    (hclash : Block.clashesWithFormals base.foldFactory Γ ss₀ = false)
    (hΓ : ∀ x ∈ Block.definedVars (P := Expression) (C := Command) ss₀ false, Γ x = none)
    (hdecl : ∀ f, (factoryParams base.factory).declaredFuncs f = true →
      params.declaredFuncs f = true) :
    OverapproximatesTracesUptoWhen (Trace.WeakensAssumes Imperative.BigStep.evalInterp)
      (EntryRel base.factory Γ ss₀) (EnvAgreeOnLive live)
      (Core.Logic.EventLang.coreBlock π) (Core.Logic.EventLang.coreBlock π)
      (simplifyBodyChecked base inputs live)
      (fun ss => ss = ss₀ ∧ BodyWF base.factory Γ ss) params params := by
  intro ss out hT hpre
  obtain ⟨rfl, -⟩ := id hpre
  have hsb : simplifyBody base inputs live ss = some (dropDeadDefs base.factory
      (Defined.ofParams inputs (simpStmts base ss).1) live (simpStmts base ss).1) := rfl
  simp only [simplifyBodyChecked] at hT
  replace hT := Option.some.inj hT
  by_cases hok : gateOK base.factory ss (dropDeadDefs base.factory
      (Defined.ofParams inputs (simpStmts base ss).1) live (simpStmts base ss).1) = true
  · simp only [hok, ↓reduceIte] at hT
    subst hT
    exact simplifyBody_overapproximatesTraces π params base inputs live Γ hfresh hlaws ss
      hclash hΓ (fun o ho => by
        rw [hsb] at ho
        cases Option.some.inj ho
        exact targetWFB_mono hdecl ((gateOK_eq_targetWFB _ _ _) ▸ hok)) ss _ hsb hpre
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
    `Γ` types. There is no hypothesis on Simplify's output. -/
theorem simplifyBodyChecked_assertValid (π : String → Option Procedure)
    (params : Core.Logic.InitEnvWFParams) (base : Ctx)
    (inputs : @Lambda.LMonoTySignature Unit) (live : Std.HashSet String)
    (Γ : VarTyping Expression) (hfresh : base.Fresh) (hlaws : Laws base.foldFactory)
    (ss₀ : List Statement) (hwf : BodyWF base.factory Γ ss₀)
    (hclash : Block.clashesWithFormals base.foldFactory Γ ss₀ = false)
    (hΓ : ∀ x ∈ Block.definedVars (P := Expression) (C := Command) ss₀ false, Γ x = none)
    (hdecl : ∀ f, (factoryParams base.factory).declaredFuncs f = true →
      params.declaredFuncs f = true)
    {out : List Statement} (hout : simplifyBodyChecked base inputs live ss₀ = some out)
    {aid : AssertId Expression}
    (hvalid : AssertValidOnTracesWhen (Core.Logic.EventLang.coreBlock π) evalInterp
      (Core.Logic.BlockInitEnvWF params out) out aid) :
    AssertValidOnTracesWhen (Core.Logic.EventLang.coreBlock π) evalInterp
      (fun ρ => Core.Logic.BlockInitEnvWF params ss₀ ρ ∧ EntryRel base.factory Γ ss₀ ρ ρ) ss₀
      aid := by
  intro ρ₀ cfg trace ⟨hinit, hrel⟩ htrace
  have hr := simplifyBodyChecked_overapproximatesTraces π params base inputs live Γ hfresh
    hlaws ss₀ hclash hΓ hdecl ss₀ out hout ⟨rfl, hwf⟩ ρ₀ ρ₀ hrel hinit
  obtain ⟨cfg', trace', htrace', hrel'⟩ := hr.1 cfg trace htrace
  exact hrel'.assertionValid aid (hvalid ρ₀ cfg' trace' hr.2.2.2 htrace')

/-! ## The phase -/

/-- A procedure's structured body is replaced by `simplifyBodyChecked`'s output, with the
    live set `simplifyProcedure` computes. -/
private theorem simplifyProcedure_body (base : Ctx) (q : Procedure) {ss : List Statement}
    (hb : q.body = .structured ss) :
    ∃ live out, simplifyBodyChecked base q.header.inputs live ss = some out ∧
      (simplifyProcedure base q).body = .structured out := by
  have hb' : (simplifySpec base q).body = .structured ss := hb
  unfold simplifyProcedure
  simp only [hb']
  exact ⟨_, _, rfl, rfl⟩

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
    (`simplifyBodyChecked_overapproximatesTraces`) under the theorem's hypotheses on `base`,
    the body and its entry typing. -/
theorem simplifyPhase_over {program out : Program} {s s' : Transform.CoreTransformState}
    {b : Bool} (h : (Core.simplifyPhase.transform program).run s = (.ok (b, out), s')) :
    ∃ base : Ctx, base.Fresh ∧ ∀ q md ss, Decl.proc q md ∈ program.decls →
      q.body = .structured ss → ∃ live out',
        Decl.proc (simplifyProcedure base q) md ∈ out.decls ∧
        (simplifyProcedure base q).body = .structured out' ∧
        simplifyBodyChecked base q.header.inputs live ss = some out' ∧
        ∀ (π : String → Option Procedure) (params : Core.Logic.InitEnvWFParams)
          (Γ : VarTyping Expression), Laws base.foldFactory →
          Block.clashesWithFormals base.foldFactory Γ ss = false →
          (∀ x ∈ Block.definedVars (P := Expression) (C := Command) ss false, Γ x = none) →
          (∀ f, (factoryParams base.factory).declaredFuncs f = true →
            params.declaredFuncs f = true) →
          OverapproximatesTracesUptoWhen (Trace.WeakensAssumes Imperative.BigStep.evalInterp)
            (EntryRel base.factory Γ ss) (EnvAgreeOnLive live)
            (Core.Logic.EventLang.coreBlock π) (Core.Logic.EventLang.coreBlock π)
            (simplifyBodyChecked base q.header.inputs live)
            (fun ss' => ss' = ss ∧ BodyWF base.factory Γ ss') params params := by
  obtain ⟨base, hfresh, hmem⟩ := runSimplify_ok (simplifyPhase_ok program s ▸ h)
  refine ⟨base, hfresh, fun q md ss hq hb => ?_⟩
  obtain ⟨live, out', hs, hbody⟩ := simplifyProcedure_body base q hb
  exact ⟨live, out', hmem q md hq, hbody, hs, fun π params Γ hlaws hclash hΓ hdecl =>
    simplifyBodyChecked_overapproximatesTraces π params base q.header.inputs live Γ hfresh hlaws
      ss hclash hΓ hdecl⟩

end

end Core.Simplify
