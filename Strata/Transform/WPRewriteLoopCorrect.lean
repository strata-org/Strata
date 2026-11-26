/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WPRewriteLoop
public import Strata.Transform.BetaReduceCorrect
public import Strata.Transform.GuardPropCoreCorrect
public import Strata.Transform.CtorFoldCoreCorrect
public import Strata.Transform.WPLoopCorrect
import all Strata.Transform.WPRewriteLoop
import all Strata.Transform.WPLoopCorrect
import all Strata.Transform.WPLoop
import all Strata.Transform.BetaReduce
import all Strata.Transform.BetaReduceProps
import all Strata.Transform.BetaReduceTyping
import all Strata.Transform.GuardPropCoreCorrect
import all Strata.Transform.CtorFold
import all Strata.Transform.DeadDefElim
import all Strata.Languages.Core.PipelinePhase
import all Strata.Transform.CoreTransform
import Strata.Transform.DeadDefElimProps
import Strata.Transform.GuardFwdTyping
import Strata.Transform.DefInlineTyping
import Strata.Util.RelationsProps
import Strata.Transform.SSA.SSATyping
import Strata.Transform.SSA.SSAUnassignedCorrect
import Strata.Transform.Passive.WPFactoryProps

/-! # The six-pass rewrite loop of `--vcgen wp` over-approximates

A round of the loop (`Core.WPRewriteLoop.round`) runs six passes, each of which is a trace
over-approximation of a Core statement list in passive form (the per-phase theorems
`Core.BetaReduce.betaReduce_overapproximatesTraces`,
`Core.WPLoop.wpRound_overapproximatesTraces` for guard forwarding, the inlining and the erasure,
`Core.GuardProp.guardProp_overapproximatesTraces` and
`Core.CtorFold.ctorFold_overapproximatesTraces`).  They compose (`round_overapproximatesTraces`,
by `OverapproximatesTracesUptoWhen.comp_eqOn_right`), with traces related by the reflexive and
transitive closure `LoopTrace` of the trace relations of the passes (`LoopStep`), which reflects the
validity of every assertion (`loopTrace_assertValid_reflect`), and final environments by the
reflexive and transitive closure `LoopOut` of theirs.

Each pass keeps the precondition of the loop (`LoopPre`): no loops, no calls, the passive form, the
`assume`, `assert` and `cover` conditions typed Boolean expressions (`Block.condsTyped`), and the
`init`s typed with annotations agreeing with a typing and def-use well formed.  Beta reduction
needs the typed conditions: an assertion whose condition has no value can get one by the
contraction of an ill-typed redex.  So every number of rounds over-approximates
(`loopIter_overapproximatesTraces`, by `OverapproximatesTracesUptoWhen.iterate`), and so does the
loop that runs, whatever its fuel (`loopBody_overapproximatesTraces`), alone, followed by beta
reduction, and after the SSA phase, whose output satisfies the precondition when its input's
right-hand sides and conditions are typed (`SSAInputTyped`).

Key theorems: `loopTrace_assertValid_reflect`, `round_kept`, `round_pre`,
`round_overapproximatesTraces`, `loopBody_eq_iterateT`, `loopIter_overapproximatesTraces`,
`loopBody_overapproximatesTraces`, `loopBody_betaReduce_overapproximatesTraces`, `loopBody_pre`,
`loopBody_kept`, `roundF_eq`, `loopBodyF_eq`, `wpRewriteLoopPipelinePhase_ok`,
`wpRewriteLoopPipelinePhase_error`, `loopProgram_over`, `ssa_loopBody_overapproximatesTraces`,
`ssa_loopBody_betaReduce_overapproximatesTraces`.

Key definitions: `Core.WPRewriteLoop.LoopStep`, `Core.WPRewriteLoop.LoopTrace`,
`Core.WPRewriteLoop.LoopOut`, `Core.WPRewriteLoop.TypedFacts`, `Core.WPRewriteLoop.LoopPre`,
`Core.WPRewriteLoop.BodyOK`, `Core.WPRewriteLoop.SSAInputTyped`. -/

namespace Core
namespace WPRewriteLoop

open Imperative Imperative.BigStep Imperative.Specification Imperative.Specification.Transform
  Imperative.DeadDefElim Imperative.GuardProp Core.Logic Core.DeadDefElim

public section

/-! ## The relations of the loop -/

/-- The generators of the trace relation of the loop: the source trace's assumptions weakened
    under evaluation to `true` (beta reduction, guard forwarding, the inlinings), the source trace
    event by event with the target stores projected (the erasures of unread definitions), or the
    source trace kept while its assumptions hold (guard propagation). -/
@[expose] def LoopStep (t t' : Trace Expression) : Prop :=
  Trace.WeakensAssumes evalInterp t t' ∨ List.Rel₂ DDEventRel t t' ∨ Trace.KeepsWhileAssumed t t'

/-- **The trace relation of the loop**: the reflexive and transitive closure of `LoopStep`. -/
abbrev LoopTrace : Relation (Trace Expression) := ReflTrans LoopStep

/-- **The final-environment relation of the loop**: the reflexive and transitive closure of the
    final-environment relations of the passes, `DDOut` (the erasures) and
    `Core.GuardProp.EnvSameTypes` (guard propagation). -/
abbrev LoopOut : Relation (Imperative.Env Expression) :=
  ReflTrans fun ρ ρ' => DDOut ρ ρ' ∨ GuardProp.EnvSameTypes ρ ρ'

/-- **The trace relation of the loop reflects assertion validity** under evaluation to `true`:
    if every occurrence of `aid` in `t'` holds whenever the assumptions before it do, so does
    every occurrence in `t`. -/
theorem loopTrace_assertValid_reflect {t t' : Trace Expression} (h : LoopTrace t t')
    (aid : AssertId Expression) :
    Trace.AssertionValid Expression evalInterp aid t' →
      Trace.AssertionValid Expression evalInterp aid t := by
  induction h with
  | refl => exact id
  | step _ _ _ hs _ ih =>
    exact fun hv => hs.elim (·.assertionValid aid (ih hv)) fun hs => hs.elim
      (dd_assertValid_reflect evalInterp_stableUnder _ _ · aid (ih hv))
      (·.assertValid_reflect (ih hv))

/-- The trace relation of the three-pass round is contained in `LoopTrace`. -/
private theorem loopTrace_of_wpLoop {t t' : Trace Expression} (h : WPLoop.LoopTrace t t') :
    LoopTrace t t' := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hs _ ih => exact .step _ _ _ (hs.imp id .inl) ih

/-! ## The precondition of the loop -/

/-- The typing facts the loop keeps: the `assume`, `assert` and `cover` conditions are typed
    Boolean expressions, and the list is def-use well formed, its annotations agree with a typing,
    and its `init`s are typed at their declared types. -/
@[expose] def TypedFacts (ss : Statements) : Prop :=
  Block.condsTyped Expression.Typed ss ∧ ∃ D df Γ, Block.defUseWellFormed D df ss = true ∧
    Block.fvarTypesWellAnnotated Γ ss ∧ Block.initsTyped Expression.Typed ss

/-- **The precondition of the loop**: no loops, no calls, the passive form (`WPLoop.LoopPre`),
    and the typing facts (`TypedFacts`). -/
abbrev LoopPre (ss : Statements) : Prop := WPLoop.LoopPre ss ∧ TypedFacts ss

/-- A list in passive form has no loops and no calls. -/
private theorem loopPre_of_passive {ss : Statements} (hp : Block.passiveForm ss = true) :
    WPLoop.LoopPre ss :=
  ⟨Imperative.GuardFwd.Block.passiveForm_allSubstmts (fun _ => rfl) (fun _ _ _ => rfl) hp,
    Imperative.GuardFwd.Block.passiveForm_allSubstmts (fun _ => rfl) (fun _ _ _ => rfl) hp, hp⟩

/-- The facts of a procedure body the loop keeps besides its typed conditions: the passive form,
    def-use well-formedness from `D` and `df`, annotations agreeing with `Γ`, and typed `init`s. -/
@[expose] def BodyOK (D df : Expression.Ident → Bool) (Γ : VarTyping Expression)
    (ss : Statements) : Prop :=
  Block.passiveForm ss = true ∧ Block.defUseWellFormed D df ss = true ∧
    Block.fvarTypesWellAnnotated Γ ss ∧ Block.initsTyped Expression.Typed ss

/-- A pass that keeps `BodyOK` and, on lists satisfying it, the typed conditions, keeps the
    precondition of the loop. -/
private theorem pre_of {ss ss' : Statements}
    (hk : ∀ D df Γ, BodyOK D df Γ ss → BodyOK D df Γ ss')
    (hc : ∀ D df Γ, BodyOK D df Γ ss → Block.condsTyped Expression.Typed ss →
      Block.condsTyped Expression.Typed ss')
    (h : LoopPre ss) : LoopPre ss' := by
  obtain ⟨⟨-, -, hp⟩, hcs, D, df, Γ, hd, hw, hi⟩ := h
  obtain ⟨hp', hd', hw', hi'⟩ := hk D df Γ ⟨hp, hd, hw, hi⟩
  exact ⟨loopPre_of_passive hp', hc D df Γ ⟨hp, hd, hw, hi⟩ hcs, D, df, Γ, hd', hw', hi'⟩

/-- Beta reduction keeps `BodyOK`. -/
private theorem kept_betaReduce {D df : Expression.Ident → Bool} {Γ : VarTyping Expression}
    {ss : Statements} (h : BodyOK D df Γ ss) : BodyOK D df Γ (BetaReduce.betaReduceBlock ss) := by
  obtain ⟨hp, hd, hw, hi⟩ := h
  obtain ⟨hw', hi'⟩ := BetaReduce.reduceBlock_typed ss Γ hw hi
  exact ⟨BetaReduce.betaReduceBlock_passive hp, BetaReduce.reduceBlock_defUse D df ss hd, hw', hi'⟩

/-- Guard forwarding keeps `BodyOK`. -/
private theorem kept_guardFwd {D df : Expression.Ident → Bool} {Γ : VarTyping Expression}
    {ss : Statements} (h : BodyOK D df Γ ss) : BodyOK D df Γ (GuardFwd.guardFwd ss) := by
  obtain ⟨hp, hd, hw, hi⟩ := h
  have hg := Imperative.GuardFwd.walk_gate GuardFwd.coreGuardFwdSynLaws
    ⟨GuardFwd.countB {} ss, Std.HashSet.ofList (Block.assignedVarsH ss),
      GuardFwd.innerB {} ss⟩ df ss hp {} D Γ hd hw fun _ _ h => by simp at h
  exact ⟨GuardFwd.guardFwd_passive hp, hg.1, hg.2, Imperative.GuardFwd.guardFwd_initsTyped
    GuardFwd.coreGuardFwdSynLaws (typedOpLaws .default) hp hd hw hi⟩

/-- The inlining at `WPLoop.loopNorm fac` keeps `BodyOK`. -/
private theorem kept_defInline (fac : Lambda.Factory CoreLParams) {D df : Expression.Ident → Bool}
    {Γ : VarTyping Expression} {ss : Statements} (h : BodyOK D df Γ ss) :
    BodyOK D df Γ (DefInline.defInline (WPLoop.loopNorm fac) ss) := by
  obtain ⟨hp, hd, hw, hi⟩ := h
  have hg := Imperative.DefInline.walk_gate (WPLoop.loopNorm_synLaws fac)
    ⟨GuardFwd.countB {} ss, Std.HashSet.ofList (Block.assignedVarsH ss)⟩ df _ hp {} D Γ hd hw
    fun _ _ h => by simp at h
  exact ⟨(Imperative.DefInline.walk_shape (P := Expression) (WPLoop.loopNorm fac)
    ⟨GuardFwd.countB {} ss, Std.HashSet.ofList (Block.assignedVarsH ss)⟩ _ hp {}).1, hg.1, hg.2,
    Imperative.DefInline.defInline_initsTyped (typedOpLaws fac) (WPLoop.loopNorm_typed fac) hp hw
      hi⟩

/-- The erasure of unread definitions keeps `BodyOK`. -/
private theorem kept_deadDefElim {D df : Expression.Ident → Bool} {Γ : VarTyping Expression}
    {ss : Statements} (h : BodyOK D df Γ ss) :
    BodyOK D df Γ (Imperative.DeadDefElim.deadDefElim [] ss) := by
  obtain ⟨hp, hd, hw, hi⟩ := h
  have h2 := loopPre_of_passive hp
  have hk := deadDefElim_defUse_fvarTypes h2.1 h2.2.1 hd hw
  exact ⟨Imperative.DeadDefElim.deadDefElim_passive [] _ hp, hk.1, hk.2,
    deadDefElim_initsTyped _ _ hi⟩

/-- The three-pass round at `WPLoop.loopNorm fac` is the erasure of the inlining of the output of
    guard forwarding. -/
private theorem wpRound_eq (fac : Lambda.Factory CoreLParams) (ss : Statements) :
    WPLoop.wpRound (WPLoop.loopNorm fac) ss = Imperative.DeadDefElim.deadDefElim []
      (DefInline.defInline (WPLoop.loopNorm fac) (GuardFwd.guardFwd ss)) :=
  Imperative.DeadDefElim.deadDefElimH_eq (P := Expression) [] _

/-- The constructor fold is the erasure of the inlining at its selection. -/
private theorem ctorFold_eq (fac : Lambda.Factory CoreLParams) (ss : Statements) :
    CtorFold.ctorFold fac ss = Imperative.DeadDefElim.deadDefElim [] (DefInline.defInlineWith
      (CtorFold.ctorNorm fac) (CtorFold.ctorFoldSel fac ss) ss) :=
  (CtorFold.ctorFold_eq fac ss).trans
    (Imperative.DeadDefElim.deadDefElimH_eq (P := Expression) [] _)

/-- Guard propagation keeps `BodyOK`. -/
private theorem kept_guardProp {D df : Expression.Ident → Bool} {Γ : VarTyping Expression}
    {ss : Statements} (h : BodyOK D df Γ ss) :
    BodyOK D df Γ (Imperative.GuardProp.guardProp ss) := by
  obtain ⟨hp, hd, hw, hi⟩ := h
  have hg := Imperative.GuardProp.walk_gate GuardFwd.coreGuardFwdSynLaws
    GuardProp.coreGuardPropSynLaws (Std.HashSet.ofList (Block.assignedVarsH ss)) df ss hp {} D Γ
    hd hw fun _ _ h => by simp at h
  exact ⟨GuardProp.guardProp_passive hp, hg.1, hg.2, GuardProp.guardProp_initsTyped hp hi⟩

/-- The constructor fold keeps `BodyOK`. -/
private theorem kept_ctorFold (fac : Lambda.Factory CoreLParams) {D df : Expression.Ident → Bool}
    {Γ : VarTyping Expression} {ss : Statements} (h : BodyOK D df Γ ss) :
    BodyOK D df Γ (CtorFold.ctorFold fac ss) := by
  obtain ⟨hp, hd, hw, hi⟩ := h
  have hw3 := DefInline.defInlineWith_passive (norm := CtorFold.ctorNorm fac)
    (sel := CtorFold.ctorFoldSel fac ss) hp
  have hg := Imperative.DefInline.walk_gate (CtorFold.ctorNorm_synLaws fac)
    ⟨CtorFold.ctorFoldSel fac ss, Std.HashSet.ofList (Block.assignedVarsH ss)⟩ df ss hp {} D Γ hd hw
    fun _ _ h => by simp at h
  have hk := (ctorFold_eq fac ss) ▸ deadDefElim_defUse_fvarTypes hw3.1 hw3.2.1 hg.1 hg.2
  exact ⟨CtorFold.ctorFold_passive hp, hk.1, hk.2, CtorFold.ctorFold_initsTyped hp hw hi⟩

/-- **A round keeps `BodyOK`.** -/
theorem round_kept (fac : Lambda.Factory CoreLParams) {D df : Expression.Ident → Bool}
    {Γ : VarTyping Expression} {ss : Statements} (h : BodyOK D df Γ ss) :
    BodyOK D df Γ (round fac ss) := by
  have h1 := kept_guardFwd (kept_betaReduce h)
  have h2 := kept_deadDefElim (kept_defInline fac h1)
  rw [← wpRound_eq] at h2
  exact kept_ctorFold fac (kept_guardProp h2)

/-- Beta reduction keeps the precondition of the loop. -/
private theorem pre_betaReduce {ss : Statements} (h : LoopPre ss) :
    LoopPre (BetaReduce.betaReduceBlock ss) :=
  pre_of (fun _ _ _ => kept_betaReduce) (fun _ _ _ h hc => BetaReduce.betaReduceBlock_condsTyped
    h.1 hc) h

/-- Guard forwarding, the inlining at `WPLoop.loopNorm fac` and the erasure keep the
    precondition of the loop. -/
private theorem pre_wpRound (fac : Lambda.Factory CoreLParams) {ss : Statements}
    (h : LoopPre ss) : LoopPre (WPLoop.wpRound (WPLoop.loopNorm fac) ss) := by
  refine pre_of (fun _ _ _ h => ?_) (fun _ _ _ h hc => ?_) h
  · have h2 := kept_deadDefElim (kept_defInline fac (kept_guardFwd h))
    rwa [← wpRound_eq] at h2
  · obtain ⟨hp, hd, hw, hi⟩ := h
    have h1 := kept_guardFwd ⟨hp, hd, hw, hi⟩
    rw [wpRound_eq]
    exact Imperative.DeadDefElim.deadDefElim_condsTyped _ _
      (Imperative.DefInline.defInline_condsTyped (typedOpLaws fac) (WPLoop.loopNorm_typed fac)
        h1.1 h1.2.2.1 h1.2.2.2 (GuardFwd.coreGuardFwd_condsTyped hp hd hw hi hc))

/-- Guard propagation keeps the precondition of the loop. -/
private theorem pre_guardProp {ss : Statements} (h : LoopPre ss) :
    LoopPre (Imperative.GuardProp.guardProp ss) :=
  pre_of (fun _ _ _ => kept_guardProp)
    (fun _ _ _ h hc => GuardProp.guardProp_condsTyped h.1 h.2.1 h.2.2.1 h.2.2.2 hc) h

/-- The constructor fold keeps the precondition of the loop. -/
private theorem pre_ctorFold (fac : Lambda.Factory CoreLParams) {ss : Statements}
    (h : LoopPre ss) : LoopPre (CtorFold.ctorFold fac ss) :=
  pre_of (fun _ _ _ => kept_ctorFold fac)
    (fun _ _ _ h hc => CtorFold.ctorFold_condsTyped h.1 h.2.2.1 h.2.2.2 hc) h

/-- **A round keeps the precondition of the loop.** -/
theorem round_pre (fac : Lambda.Factory CoreLParams) {ss : Statements} (h : LoopPre ss) :
    LoopPre (round fac ss) :=
  pre_ctorFold fac (pre_guardProp (pre_wpRound fac (pre_betaReduce h)))

/-! ## The trace over-approximation -/

/-- A trace over-approximation under a precondition holds under every stronger precondition. -/
private theorem mono_pre {Rt : Relation (Trace Expression)}
    {Rin Rout : Relation (Imperative.Env Expression)} {π : String → Option Procedure}
    {T : Statements → Option Statements} {pre pre' : Statements → Prop} {params : InitEnvWFParams}
    (hp : ∀ ss, pre' ss → pre ss)
    (h : OverapproximatesTracesUptoWhen Rt Rin Rout (EventLang.coreBlock π)
      (EventLang.coreBlock π) T pre params params) :
    OverapproximatesTracesUptoWhen Rt Rin Rout (EventLang.coreBlock π) (EventLang.coreBlock π)
      T pre' params params :=
  fun ss st' hT hpre => h ss st' hT (hp ss hpre)

/-- **A round over-approximates the traces of a Core statement list satisfying the precondition
    of the loop**, with traces related by `LoopTrace` and final environments by `LoopOut`, from
    equal initial environments whose factory has the functions of `fac`, the factory of the
    pipeline on a program `p` (`wpFactory`). -/
theorem round_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) {moreFns fac : Lambda.Factory CoreLParams} {p : Program}
    (hfac : wpFactory moreFns p = .ok fac) :
    OverapproximatesTracesUptoWhen LoopTrace
      (fun ρ ρ' : Imperative.Env Expression => ρ = ρ' ∧ ρ.factory.factory = fac) LoopOut
      (EventLang.coreBlock π) (EventLang.coreBlock π) (fun ss => some (round fac ss))
      LoopPre params params := by
  have hQ : ∀ ρ ρ' : Imperative.Env Expression, ρ = ρ' ∧ ρ.factory.factory = fac →
      ρ'.factory.factory = fac := fun _ _ ⟨h, q⟩ => h ▸ q
  have hB := mono_pre (pre := fun ss => Block.noLoops ss = true ∧ Statements.noCalls ss = true ∧
      Block.passiveForm ss = true ∧ Block.condsTyped Expression.Typed ss ∧
      Block.initsTyped Expression.Typed ss) (pre' := LoopPre)
    (fun _ ⟨⟨h1, h2, h3⟩, hc, _, _, _, _, _, hi⟩ => ⟨h1, h2, h3, hc, hi⟩)
    ((BetaReduce.betaReduce_overapproximatesTraces π params).mono_in
      (Rin' := fun ρ ρ' : Imperative.Env Expression => ρ = ρ' ∧ ρ.factory.factory = fac)
      fun _ _ h => h.1)
  have hR := mono_pre (fun _ (h : LoopPre _) => h.1) (WPLoop.wpRound_overapproximatesTraces π
    params (Q := fun ρ => ρ.factory.factory = fac)
    (fun _ hF => WPLoop.loopNorm_normLawT hF (WPLoop.wpFactory_intAdd hfac)
      (WPLoop.wpFactory_boolNot hfac)) (WPLoop.loopNorm_synLaws fac))
  have hG := mono_pre (fun _ (h : LoopPre _) => h.1)
    ((GuardProp.guardProp_overapproximatesTraces π params).mono_in
      (Rin' := fun ρ ρ' : Imperative.Env Expression => ρ = ρ' ∧ ρ.factory.factory = fac)
      fun _ _ h => h.1)
  have hC := mono_pre (fun _ (h : LoopPre _) => h.1)
    (CtorFold.ctorFold_overapproximatesTraces π params hfac)
  refine ((((hB.comp_eqOn_right hQ (fun _ _ h hp => ?_) hR).comp_eqOn_right hQ
    (fun _ _ h hp => ?_) hG).comp_eqOn_right hQ (fun _ _ h hp => ?_) hC).mono_trace
      ?_).mono_out ?_
  · cases h
    exact pre_betaReduce hp
  · obtain ⟨_, h1, h2⟩ := (Option.bind_eq_some_iff).1 h
    cases h1
    cases h2
    exact pre_wpRound fac (pre_betaReduce hp)
  · obtain ⟨_, h1, h2⟩ := (Option.bind_eq_some_iff).1 h
    obtain ⟨_, h3, h4⟩ := (Option.bind_eq_some_iff).1 h1
    cases h3
    cases h4
    cases h2
    exact pre_guardProp (pre_wpRound fac (pre_betaReduce hp))
  · rintro _ _ ⟨_, ⟨_, ⟨_, h1, h2⟩, h3⟩, _, h4, h5⟩
    exact (ReflTrans_Transitive _ _ _ _ (.step _ _ _ (.inl h1) (loopTrace_of_wpLoop h2))
      (.step _ _ _ (.inr (.inr h3)) (.step _ _ _ (.inl h4)
        (.step _ _ _ (.inr (.inl h5)) (.refl _)))))
  · rintro _ _ ⟨_, ⟨_, ⟨_, rfl, h2⟩, h3⟩, _, rfl, h5⟩
    exact .step _ _ _ (.inl h2) (.step _ _ _ (.inr h3) (.step _ _ _ (.inl h5) (.refl _)))


/-! ## The loop -/

/-- **The loop that runs returns the output of some number of rounds**, whatever its fuel. -/
theorem loopBody_eq_iterateT (fac : Lambda.Factory CoreLParams) (ss : Statements) :
    ∃ m, iterateT (fun ss => some (round fac ss)) m ss = some (loopBody fac ss).1 :=
  WPLoop.loopFix_eq_iterateT (round fac) _ ss 0

/-- **Every number of rounds over-approximates the traces of a Core statement list satisfying
    the precondition of the loop**, with the relations of one round
    (`round_overapproximatesTraces`). -/
theorem loopIter_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) {moreFns fac : Lambda.Factory CoreLParams} {p : Program}
    (hfac : wpFactory moreFns p = .ok fac) (n : Nat) :
    OverapproximatesTracesUptoWhen LoopTrace
      (fun ρ ρ' : Imperative.Env Expression => ρ = ρ' ∧ ρ.factory.factory = fac) LoopOut
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (iterateT (fun ss => some (round fac ss)) n) LoopPre params params :=
  OverapproximatesTracesUptoWhen.iterate (ReflTrans_Reflexive _) (ReflTrans_Transitive _)
    (ReflTrans_Reflexive _) (ReflTrans_Transitive _)
    (fun _ _ h hp => Option.some.inj h ▸ round_pre fac hp)
    (round_overapproximatesTraces π params hfac) n

/-- **The loop that runs over-approximates the traces of a Core statement list satisfying the
    precondition of the loop**, whatever its fuel.  For `fac` the factory of the pipeline on a
    program `p` (`wpFactory`), from equal initial environments whose factory has the functions of
    `fac` and that satisfy `BlockInitEnvWF params`:
    * every finite trace of `ss` has a trace of the loop's output related by `LoopTrace`, which
      reflects the validity of every assertion (`loopTrace_assertValid_reflect`);
    * every terminating or exiting run of `ss` has a run of the output ending in the same way,
      its final environment related by `LoopOut`, with such a trace;
    * the output satisfies `BlockInitEnvWF params`. -/
theorem loopBody_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) {moreFns fac : Lambda.Factory CoreLParams} {p : Program}
    (hfac : wpFactory moreFns p = .ok fac) :
    OverapproximatesTracesUptoWhen LoopTrace
      (fun ρ ρ' : Imperative.Env Expression => ρ = ρ' ∧ ρ.factory.factory = fac) LoopOut
      (EventLang.coreBlock π) (EventLang.coreBlock π) (fun ss => some (loopBody fac ss).1)
      LoopPre params params := by
  rintro ss _ ⟨⟩
  obtain ⟨m, hm⟩ := loopBody_eq_iterateT fac ss
  exact loopIter_overapproximatesTraces π params hfac m ss _ hm

/-- **The loop keeps its precondition**: its output is that of some number of rounds, each of
    which keeps it. -/
theorem loopBody_pre (fac : Lambda.Factory CoreLParams) {ss : Statements} (h : LoopPre ss) :
    LoopPre (loopBody fac ss).1 := by
  obtain ⟨m, hm⟩ := loopBody_eq_iterateT fac ss
  generalize (loopBody fac ss).1 = ss' at hm ⊢
  induction m generalizing ss with
  | zero => exact Option.some.inj hm ▸ h
  | succ m ih => exact ih (round_pre fac h) hm

/-- **The loop keeps `BodyOK`**: its output is that of some number of rounds, each of which
    keeps it. -/
theorem loopBody_kept (fac : Lambda.Factory CoreLParams) {D df : Expression.Ident → Bool}
    {Γ : VarTyping Expression} {ss : Statements} (h : BodyOK D df Γ ss) :
    BodyOK D df Γ (loopBody fac ss).1 := by
  obtain ⟨m, hm⟩ := loopBody_eq_iterateT fac ss
  generalize (loopBody fac ss).1 = ss' at hm ⊢
  induction m generalizing ss with
  | zero => exact Option.some.inj hm ▸ h
  | succ m ih => exact ih (round_kept fac h) hm

/-- **The loop followed by beta reduction over-approximates the traces of a Core statement list
    satisfying the precondition of the loop**, with the relations of the loop: `--vcgen wp` runs
    the beta-reduction phase after the loop, for the declarations other than procedure bodies;
    on a body it is one more pass of the loop's first kind. -/
theorem loopBody_betaReduce_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) {moreFns fac : Lambda.Factory CoreLParams} {p : Program}
    (hfac : wpFactory moreFns p = .ok fac) :
    OverapproximatesTracesUptoWhen LoopTrace
      (fun ρ ρ' : Imperative.Env Expression => ρ = ρ' ∧ ρ.factory.factory = fac) LoopOut
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss => some (BetaReduce.betaReduceBlock (loopBody fac ss).1)) LoopPre params params := by
  have hB := mono_pre (pre := fun ss => Block.noLoops ss = true ∧ Statements.noCalls ss = true ∧
      Block.passiveForm ss = true ∧ Block.condsTyped Expression.Typed ss ∧
      Block.initsTyped Expression.Typed ss) (pre' := LoopPre)
    (fun _ ⟨⟨h1, h2, h3⟩, hc, _, _, _, _, _, hi⟩ => ⟨h1, h2, h3, hc, hi⟩)
    ((BetaReduce.betaReduce_overapproximatesTraces π params).mono_in
      (Rin' := fun ρ ρ' : Imperative.Env Expression => ρ = ρ' ∧ ρ.factory.factory = fac)
      fun _ _ h => h.1)
  refine (((loopBody_overapproximatesTraces π params hfac).comp_eqOn_right
    (fun _ _ ⟨h, q⟩ => h ▸ q) (fun _ _ h hp => ?_) hB).mono_trace ?_).mono_out ?_
  · cases h
    exact loopBody_pre fac hp
  · rintro _ _ ⟨_, h1, h2⟩
    exact ReflTrans_Transitive _ _ _ _ h1 (.step _ _ _ (.inl h2) (.refl _))
  · rintro _ _ ⟨_, h1, rfl⟩
    exact h1

/-- **The round with cached checks is the round**: its middle three passes,
    `WPLoop.wpRoundF fac`, are `WPLoop.wpRound (WPLoop.loopNorm fac)`. -/
theorem roundF_eq (fac : Lambda.Factory CoreLParams) : roundF fac = round fac := by
  have hr : WPLoop.wpRoundF fac = WPLoop.wpRound (WPLoop.loopNorm fac) := funext fun ss => by
    simp only [WPLoop.wpRoundF, WPLoop.wpRound, WPLoop.defInlineF_eq]
  funext ss
  simp only [roundF, round, hr]

/-- **The loop with cached checks is the loop.** -/
theorem loopBodyF_eq (fac : Lambda.Factory CoreLParams) : loopBodyF fac = loopBody fac := by
  funext ss
  simp only [loopBodyF, loopBody, roundF_eq]

/-! ## The pipeline phase -/

/-- When the factory of the WP pipeline on `program` is `fac`, a run of
    `wpRewriteLoopPipelinePhase moreFns` on `program` runs the loop on each procedure body
    (`WPLoop.wpLoopProgramWith (loopBody fac)`). -/
theorem wpRewriteLoopPipelinePhase_ok {moreFns fac : Lambda.Factory CoreLParams}
    {program : Program} (h : wpFactory moreFns program = .ok fac)
    (s : Transform.CoreTransformState) :
    ((wpRewriteLoopPipelinePhase moreFns).transform program).run s =
      (WPLoop.wpLoopProgramWith (loopBody fac) program).run s := by
  simp only [wpRewriteLoopPipelinePhase, loopBodyF_eq, modelPreservingPipelinePhase, h,
    Transform.liftDiag, pure_bind]

/-- When the factory of the WP pipeline on `program` fails with the error `e`, a run of
    `wpRewriteLoopPipelinePhase moreFns` on `program` fails with `e` and leaves the state
    unchanged. -/
theorem wpRewriteLoopPipelinePhase_error {moreFns : Lambda.Factory CoreLParams}
    {e : Strata.Message} {program : Program} (h : wpFactory moreFns program = .error e)
    (s : Transform.CoreTransformState) :
    ((wpRewriteLoopPipelinePhase moreFns).transform program).run s = (.error e, s) := by
  simp only [wpRewriteLoopPipelinePhase, modelPreservingPipelinePhase, h, Transform.liftDiag]
  rfl

/-- **The loop transform runs the loop on each procedure body.**  Let a run of
    `WPLoop.wpLoopProgramWith (loopBody fac)` on `prog` succeed with `out`.  Every procedure of
    `prog` with a structured body `ss` is, in `out`, the same procedure with the body
    `(loopBody fac ss).1`. -/
theorem loopProgram_over {fac : Lambda.Factory CoreLParams} {prog out : Program}
    {s s' : Transform.CoreTransformState} {b : Bool}
    (h : (WPLoop.wpLoopProgramWith (loopBody fac) prog).run s = (.ok (b, out), s'))
    {q : Procedure} {md : Imperative.MetaData Expression} {ss : Statements}
    {opq : Bool} (hq : Decl.proc q md ∈ prog.decls) (hb : q.body = .structured ss opq) :
    Decl.proc { q with body := .structured (loopBody fac ss).1 opq } md ∈ out.decls := by
  simp only [WPLoop.wpLoopProgramWith, Transform.incrementStat, List.countP_map, List.any_map,
    List.map_map, bind_pure_comp] at h
  cases h
  exact List.mem_map.2 ⟨_, hq, by simp [WPLoop.wpLoopDecl, hb]⟩

/-! ## Composition with the SSA phase -/

/-- A trace over-approximation under a precondition holds under the precondition that the
    gate of every initial environment the statement is well formed from gives the original
    precondition. -/
private theorem gate_pre {Rt : Relation (Trace Expression)}
    {Rin Rout : Relation (Imperative.Env Expression)} {π : String → Option Procedure}
    {T : Statements → Option Statements} {pre : Statements → Prop} {params : InitEnvWFParams}
    (h : OverapproximatesTracesUptoWhen Rt Rin Rout (EventLang.coreBlock π)
      (EventLang.coreBlock π) T pre params params) :
    OverapproximatesTracesUptoWhen Rt Rin Rout (EventLang.coreBlock π) (EventLang.coreBlock π)
      T (fun ss => ∀ ρ, BlockInitEnvWF params ss ρ → pre ss) params params :=
  fun ss st' hT hpre ρ₀ ρ₀' hin hwf => h ss st' hT (hpre ρ₀ hwf) ρ₀ ρ₀' hin hwf

/-- The typing premise of the SSA phase's input that the loop needs, for the parameters `xs`
    and the aliases `al`: a typing `Γ` its annotations agree with, under which its right-hand
    sides and the guards of its deterministic `ite`s have the types of their variables or the
    Boolean type (`Block.rhsTyped`), its `assume`, `assert` and `cover` conditions are typed
    Boolean expressions, and whose types of the free variables that are parameters or aliases are
    those `tys` records; the other free variables have the types of their annotations. -/
@[expose] def SSAInputTyped (tys : WP.Tys Expression) (xs : List Expression.Ident)
    (al : List (Expression.Ident × Expression.Ident)) (ss : Statements) : Prop :=
  ∃ Γ, Block.fvarTypesWellAnnotated Γ ss ∧ Block.rhsTyped Expression.Typed Γ ss ∧
    Block.condsTyped Expression.Typed ss ∧
    ∀ x ∈ Block.freeVars ss, ∀ T, Γ x = some T → x ∈ xs ∨ x ∈ al.map (·.1) →
      WP.Tys.get? (P := Expression) tys x = some T

/-- **The SSA phase followed by the loop over-approximates the traces of a guarded statement
    list**, under the precondition of `WP.ssa_overapproximatesTraces_unassigned` and the typing
    premise `SSAInputTyped`, for `fac` the factory of the pipeline on a program `p`.  Initial
    environments are related by the entry renaming (`SSAEntryRel`); traces by the composition of
    the SSA phase's relation and `LoopTrace`; final environments by the composition of the
    factory equality of the SSA phase and `LoopOut`. -/
theorem ssa_loopBody_overapproximatesTraces
    (π : String → Option Procedure) (params : InitEnvWFParams)
    (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList) {moreFns fac : Lambda.Factory CoreLParams}
    {p : Program} (hfac : wpFactory moreFns p = .ok fac)
    (G : WP.IdSet Expression) (tys : WP.Tys Expression) (xs : List Expression.Ident)
    (al : List (Expression.Ident × Expression.Ident)) (hal : ∀ q ∈ al, q.2 ∈ xs)
    (ss₀ : Statements) :
    OverapproximatesTracesUptoWhen (RComp (Trace.WeakensAssumes evalInterp) LoopTrace)
      (WP.SSAEntryRel fac G tys xs al ss₀) (RComp (fun ρ ρ' => ρ'.factory = ρ.factory) LoopOut)
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss : Statements => (WP.ssaEntry fac G tys xs al ss).toOption.map (·.2.out) >>=
        fun ss : Statements => some (loopBody fac ss).1)
      (fun ss : Statements => (ss = ss₀ ∧ Block.treeForm ss = true ∧
        Block.armsHaveChecks ss = true ∧ ∀ x ∈ Block.freeVars ss,
          x ∈ xs ∨ x ∈ al.map (·.1) ∨ x ∉ Block.modifiedOrDefinedVars ss false) ∧
        SSAInputTyped tys xs al ss) params params := by
  refine OverapproximatesTracesUptoWhen.comp_eqOn_right
    (fun _ _ h => by rw [h.factory]; exact h.factoryIs) (fun ss out h hpre => ?_)
    (mono_pre (fun _ h => h.1)
      (WP.ssa_overapproximatesTraces_unassigned π params hp fac G tys xs al hal ss₀))
    (gate_pre (loopBody_overapproximatesTraces π params hfac))
  intro ρ hwf
  obtain ⟨⟨-, htf, -, -⟩, Γ, hW, hR, hC, hty⟩ := hpre
  obtain ⟨⟨ρ0, so⟩, hss, rfl⟩ : ∃ r, WP.ssaEntry fac G tys xs al ss = .ok r ∧ r.2.out = out := by
    cases h' : WP.ssaEntry fac G tys xs al ss <;>
      simp only [h', Except.toOption, Option.map, reduceCtorEq] at h
    exact ⟨_, rfl, Option.some.inj h⟩
  obtain ⟨Γ', -, hw'⟩ := hwf.fvarTypesOk
  have hty' : ∀ x ∈ Block.freeVars ss, ∀ T, Γ x = some T → x ∈ ρ0.map (·.1) →
      WP.Tys.get? (P := Expression) tys x = some T := fun x hx T hT hk => by
    obtain ⟨rfl, -⟩ := Imperative.WP.ssaEntry_ok hss
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hk
    exact hty q.1 hx T hT ((Imperative.WP.ssaEntryRen_spec _ xs al 0 hal).2.1 q hq).2
  exact ⟨WP.ssaEntry_passive h htf,
    Imperative.WP.ssaEntry_condsTyped_renamed (typedOpLaws fac) hss hW hR hC hty',
    _, _, Γ', hwf.defUseOk, hw',
    Imperative.WP.ssaEntry_initsTyped_renamed (typedOpLaws fac) hss hW hR hty'⟩

/-- **The SSA phase followed by the loop and beta reduction over-approximates the traces of a
    guarded statement list**, with the relations, the precondition and the typing premise of
    `ssa_loopBody_overapproximatesTraces`. -/
theorem ssa_loopBody_betaReduce_overapproximatesTraces
    (π : String → Option Procedure) (params : InitEnvWFParams)
    (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList) {moreFns fac : Lambda.Factory CoreLParams}
    {p : Program} (hfac : wpFactory moreFns p = .ok fac)
    (G : WP.IdSet Expression) (tys : WP.Tys Expression) (xs : List Expression.Ident)
    (al : List (Expression.Ident × Expression.Ident)) (hal : ∀ q ∈ al, q.2 ∈ xs)
    (ss₀ : Statements) :
    OverapproximatesTracesUptoWhen (RComp (Trace.WeakensAssumes evalInterp) LoopTrace)
      (WP.SSAEntryRel fac G tys xs al ss₀) (RComp (fun ρ ρ' => ρ'.factory = ρ.factory) LoopOut)
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss : Statements => (WP.ssaEntry fac G tys xs al ss).toOption.map (·.2.out) >>=
        fun ss : Statements => some (BetaReduce.betaReduceBlock (loopBody fac ss).1))
      (fun ss : Statements => (ss = ss₀ ∧ Block.treeForm ss = true ∧
        Block.armsHaveChecks ss = true ∧ ∀ x ∈ Block.freeVars ss,
          x ∈ xs ∨ x ∈ al.map (·.1) ∨ x ∉ Block.modifiedOrDefinedVars ss false) ∧
        SSAInputTyped tys xs al ss) params params := by
  refine OverapproximatesTracesUptoWhen.comp_eqOn_right
    (fun _ _ h => by rw [h.factory]; exact h.factoryIs) (fun ss out h hpre => ?_)
    (mono_pre (fun _ h => h.1)
      (WP.ssa_overapproximatesTraces_unassigned π params hp fac G tys xs al hal ss₀))
    (gate_pre (loopBody_betaReduce_overapproximatesTraces π params hfac))
  intro ρ hwf
  obtain ⟨⟨-, htf, -, -⟩, Γ, hW, hR, hC, hty⟩ := hpre
  obtain ⟨⟨ρ0, so⟩, hss, rfl⟩ : ∃ r, WP.ssaEntry fac G tys xs al ss = .ok r ∧ r.2.out = out := by
    cases h' : WP.ssaEntry fac G tys xs al ss <;>
      simp only [h', Except.toOption, Option.map, reduceCtorEq] at h
    exact ⟨_, rfl, Option.some.inj h⟩
  obtain ⟨Γ', -, hw'⟩ := hwf.fvarTypesOk
  have hty' : ∀ x ∈ Block.freeVars ss, ∀ T, Γ x = some T → x ∈ ρ0.map (·.1) →
      WP.Tys.get? (P := Expression) tys x = some T := fun x hx T hT hk => by
    obtain ⟨rfl, -⟩ := Imperative.WP.ssaEntry_ok hss
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hk
    exact hty q.1 hx T hT ((Imperative.WP.ssaEntryRen_spec _ xs al 0 hal).2.1 q hq).2
  exact ⟨WP.ssaEntry_passive h htf,
    Imperative.WP.ssaEntry_condsTyped_renamed (typedOpLaws fac) hss hW hR hC hty',
    _, _, Γ', hwf.defUseOk, hw',
    Imperative.WP.ssaEntry_initsTyped_renamed (typedOpLaws fac) hss hW hR hty'⟩

end -- public section

end WPRewriteLoop
end Core
