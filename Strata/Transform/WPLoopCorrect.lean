/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WPLoop
public import Strata.Transform.DefInlineCoreCorrect
import all Strata.Transform.WPLoop
import all Strata.Transform.DeadDefElim
import all Strata.Util.Relations
import Strata.Util.RelationsProps
import Strata.DL.Imperative.StoreRelationsProps
public import Strata.Transform.DefInlineRewriteCorrect
public import Strata.Transform.GuardFwdTyping
import Strata.Transform.DeadDefElimProps
import Strata.DL.Imperative.Logic.TraceRelationsProps
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.Util.ExceptProps
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.Factory
import Strata.Transform.Passive.WPFactoryProps

/-! # The three-pass round and its loop over-approximate

The three-pass round (`Core.WPLoop.wpRound`: guard forwarding, the inlining of single-use
definitions, the erasure of unread definitions), which the rewrite loop of `--vcgen wp` runs as
the middle of its six-pass round (`Strata.Transform.WPRewriteLoopCorrect`), over-approximates
the traces of a Core statement list in passive form (`wpRound_overapproximatesTraces`, from
`guardFwd_defInline_deadDefElimH_overapproximatesTraces`), with the trace relation weakened to
the reflexive and transitive closure `LoopTrace` of its generators (`Trace.WeakensAssumes
evalInterp` and the event-by-event correspondence of the erasure, `List.Rel₂ DDEventRel`) and
the output relation weakened to `DDOut`, which is reflexive and transitive.  Each round keeps the
passive form (`wpRound_passive`), so every number of rounds over-approximates with the same
relations (`wpLoop_overapproximatesTraces`, by `OverapproximatesTracesUptoWhen.iterate`).  The
loop that runs, whatever its fuel, returns the output of some number of rounds
(`wpLoopBody_eq_iterateT`), so it over-approximates too (`wpLoopBody_overapproximatesTraces`),
and so does its composition with the SSA phase
(`ssa_wpLoopBody_overapproximatesTraces`, by `comp_eqOn_right`).

At the normalization of the pipeline (`loopNorm fac`: the substitution and
`rwAll fac`, then `addFold`), the laws the
inlining needs hold (`loopNorm_normLawT`, `loopNorm_synLaws`, `loopNorm_typed`) for a factory
with the functions of `fac` when `fac` resolves `Int.Add` and `Bool.Not` to Core's built-ins, as
every extension of `Core.Factory` does (`DefInline.addFactory_intAdd`, `addFactory_boolNot`), the
factory of the pipeline on a program among them (`wpFactory_intAdd`, `wpFactory_boolNot`, in
`Strata.Transform.Passive.WPFactoryProps`);
hence the loop at that normalization, alone and after the SSA phase, over-approximates
(`wpLoopBody_loopNorm_overapproximatesTraces`, `ssa_wpLoopBody_loopNorm_overapproximatesTraces`,
whose entry relation gives the factory condition).  The inlining with cached ground checks
(`defInlineF`), which keeps the ground checks of the recorded right-hand sides, walks as the
inlining at `loopNorm fac` from states holding the same entries with those checks, so it is the
inlining at `loopNorm fac` (`defInlineF_eq`).

`LoopTrace` reflects the validity of every assertion under evaluation to `true`
(`loopTrace_assertValid_reflect`): each of its generators does
(`Trace.WeakensAssumes.assertionValid`, `dd_assertValid_reflect`).

Key theorems: `wpRound_passive`, `wpRound_overapproximatesTraces`,
`wpLoop_overapproximatesTraces`, `wpLoopBody_eq_iterateT`, `wpLoopBody_overapproximatesTraces`,
`ssa_wpLoopBody_overapproximatesTraces`,
`loopTrace_assertValid_reflect`, `loopNorm_normLawT`, `loopNorm_synLaws`, `loopNorm_typed`,
`wpLoopBody_loopNorm_overapproximatesTraces`,
`ssa_wpLoopBody_loopNorm_overapproximatesTraces`, `defInlineF_eq`.

Key definitions: `Core.WPLoop.LoopStep`, `Core.WPLoop.LoopTrace`. -/

namespace Core
namespace WPLoop

open Imperative Imperative.BigStep Imperative.Specification Imperative.Specification.Transform
  Imperative.DefInline Imperative.GuardFwd Imperative.DeadDefElim Core.Logic Core.DeadDefElim
  Core.DefInline Core.GuardFwd

public section

/-! ## The relations of the loop -/

/-- The generators of the trace relation of the loop: the source trace's assumptions weakened
    under evaluation to `true` (guard forwarding, the inlining), or the source trace event by
    event with the target stores projected (the erasure of unread definitions). -/
@[expose] def LoopStep (t t' : Trace Expression) : Prop :=
  Trace.WeakensAssumes evalInterp t t' ∨ List.Rel₂ DDEventRel t t'

/-- **The trace relation of the loop**: the reflexive and transitive closure of `LoopStep`. -/
abbrev LoopTrace : Relation (Trace Expression) := ReflTrans LoopStep

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
    exact fun hv => hs.elim (·.assertionValid aid (ih hv))
      (dd_assertValid_reflect evalInterp_stableUnder _ _ · aid (ih hv))

/-- `DDOut` is reflexive. -/
private theorem ddOut_refl (ρ : Imperative.Env Expression) : DDOut ρ ρ :=
  ⟨rfl, StoreAgreement.refl _⟩

/-! ## The loop returns the output of some number of rounds -/

/-- The loop with fuel returns the output of some number of rounds. -/
private theorem loopFix_eq_iterateT (round : Statements → Statements) :
    ∀ (fuel : Nat) (ss : Statements) (k : Nat),
      ∃ m, iterateT (fun ss => some (round ss)) m ss = some (loopFix round fuel ss k).1
  | 0, _, _ => ⟨0, rfl⟩
  | fuel + 1, ss, k => by
    simp only [loopFix]
    split
    · exact ⟨0, rfl⟩
    · exact (loopFix_eq_iterateT round fuel (round ss) (k + 1)).elim fun m hm => ⟨m + 1, hm⟩

/-- **The loop that runs returns the output of some number of rounds**, whatever its fuel. -/
theorem wpLoopBody_eq_iterateT (norm : SubstNorm Expression) (ss : Statements) :
    ∃ m, iterateT (fun ss => some (wpRound norm ss)) m ss = some (wpLoopBody norm ss).1 :=
  loopFix_eq_iterateT (wpRound norm) _ ss 0

/-! ## The passive form -/

/-- The precondition of the loop: no loops, no calls, passive form. -/
abbrev LoopPre (ss : Statements) : Prop :=
  Block.noLoops ss = true ∧ Statements.noCalls ss = true ∧ Block.passiveForm ss = true

/-- **A round keeps the passive form.** -/
theorem wpRound_passive (norm : SubstNorm Expression) {ss : Statements}
    (hp : Block.passiveForm ss = true) : Block.passiveForm (wpRound norm ss) = true := by
  have hg := guardFwd_passive hp
  have hd := (Imperative.DefInline.walk_shape (P := Expression) norm
    ⟨countB {} (guardFwd ss), Std.HashSet.ofList (Block.assignedVarsH (guardFwd ss))⟩
    (guardFwd ss) hg {}).1
  show Block.passiveForm (DeadDefElim.deadDefElimH (P := Expression) [] _) = true
  exact (deadDefElimH_eq (P := Expression) [] _).symm ▸
    Imperative.DeadDefElim.deadDefElim_passive [] _ hd

/-- A round keeps the precondition of the loop. -/
private theorem wpRound_pre (norm : SubstNorm Expression) :
    ∀ st st', some (wpRound norm st) = some st' → LoopPre st → LoopPre st' := by
  rintro st _ ⟨⟩ ⟨-, -, hp⟩
  have hp' := wpRound_passive norm hp
  exact ⟨Block.passiveForm_allSubstmts (fun _ => rfl) (fun _ _ _ => rfl) hp',
    Block.passiveForm_allSubstmts (fun _ => rfl) (fun _ _ _ => rfl) hp', hp'⟩

/-! ## The trace over-approximation -/

/-- **A round over-approximates the traces of a Core statement list in passive form**, with
    traces related by `LoopTrace` and final environments by `DDOut`, for a substituting
    normalization `norm` that
    keeps the values of substituted expressions in typed stores under the factory of every
    environment satisfying `Q` (`hN`) and adds no free variable, annotated occurrence or operator
    to them (`hS`). -/
theorem wpRound_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) {norm : SubstNorm Expression}
    {Q : Imperative.Env Expression → Prop}
    (hN : ∀ ρ, Q ρ → SubstNormLawT (P := Expression) ρ.factory norm)
    (hS : DefInlineSynLaws Expression norm) :
    OverapproximatesTracesUptoWhen LoopTrace (fun ρ ρ' => ρ = ρ' ∧ Q ρ) DDOut
      (EventLang.coreBlock π) (EventLang.coreBlock π) (fun ss => some (wpRound norm ss))
      LoopPre params params :=
  ((guardFwd_defInline_deadDefElimH_overapproximatesTraces π params hN hS).mono_trace
    fun _ _ ⟨_, h₁, _, h₂, h₃⟩ =>
      .step _ _ _ (.inl h₁) (.step _ _ _ (.inl h₂) (.step _ _ _ (.inr h₃) (.refl _)))).mono_out
    fun _ _ ⟨_, h₁, _, h₂, h₃⟩ => h₁ ▸ h₂ ▸ h₃

/-- **Every number of rounds over-approximates the traces of a Core statement list in passive
    form**, under the hypotheses of `wpRound_overapproximatesTraces` and with the relations of one
    round. -/
theorem wpLoop_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) {norm : SubstNorm Expression}
    {Q : Imperative.Env Expression → Prop}
    (hN : ∀ ρ, Q ρ → SubstNormLawT (P := Expression) ρ.factory norm)
    (hS : DefInlineSynLaws Expression norm) (n : Nat) :
    OverapproximatesTracesUptoWhen LoopTrace (fun ρ ρ' => ρ = ρ' ∧ Q ρ) DDOut
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (iterateT (fun ss => some (wpRound norm ss)) n) LoopPre params params :=
  OverapproximatesTracesUptoWhen.iterate (ReflTrans_Reflexive _) (ReflTrans_Transitive _)
    ddOut_refl ddOut_trans (wpRound_pre norm) (wpRound_overapproximatesTraces π params hN hS) n

/-- **The loop that runs over-approximates the traces of a Core statement list in passive
    form**, whatever its fuel.  Under the hypotheses of `wpRound_overapproximatesTraces`, from
    equal initial environments satisfying `Q` and `BlockInitEnvWF params`:
    * every finite trace of `ss` has a trace of the loop's output related by `LoopTrace`;
    * every terminating or exiting run of `ss` has a run of the output ending in the same way,
      its final environment related by `DDOut`, with such a trace;
    * the output satisfies `BlockInitEnvWF params`. -/
theorem wpLoopBody_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) {norm : SubstNorm Expression}
    {Q : Imperative.Env Expression → Prop}
    (hN : ∀ ρ, Q ρ → SubstNormLawT (P := Expression) ρ.factory norm)
    (hS : DefInlineSynLaws Expression norm) :
    OverapproximatesTracesUptoWhen LoopTrace (fun ρ ρ' => ρ = ρ' ∧ Q ρ) DDOut
      (EventLang.coreBlock π) (EventLang.coreBlock π) (fun ss => some (wpLoopBody norm ss).1)
      LoopPre params params := by
  rintro ss _ ⟨⟩
  obtain ⟨m, hm⟩ := wpLoopBody_eq_iterateT norm ss
  exact wpLoop_overapproximatesTraces π params hN hS m ss _ hm

/-- **The SSA phase followed by the loop over-approximates the traces of a guarded statement
    list**, under the hypotheses and the precondition of `ssa_overapproximatesTraces`, for a
    substituting normalization `norm` that keeps the values of substituted expressions in typed
    stores under the factory of every environment satisfying `Q`, and a `Q` that every target
    environment of the entry relation satisfies (`hQ`).  Initial environments are related by the
    entry renaming (`SSAEntryRel`); traces by the composition of the SSA phase's relation and
    `LoopTrace`; final environments by the composition of the factory equality of the SSA phase
    and `DDOut`. -/
theorem ssa_wpLoopBody_overapproximatesTraces
    (π : String → Option Procedure) (params : InitEnvWFParams)
    (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList) (fac : Lambda.Factory CoreLParams)
    (G : WP.IdSet Expression) (tys : WP.Tys Expression) (xs : List Expression.Ident)
    (al : List (Expression.Ident × Expression.Ident)) (hal : ∀ q ∈ al, q.2 ∈ xs)
    (ss₀ : Statements) {norm : SubstNorm Expression}
    {Q : Imperative.Env Expression → Prop}
    (hN : ∀ ρ, Q ρ → SubstNormLawT (P := Expression) ρ.factory norm)
    (hS : DefInlineSynLaws Expression norm)
    (hQ : ∀ ρ ρ', WP.SSAEntryRel fac G tys xs al ss₀ ρ ρ' → Q ρ') :
    OverapproximatesTracesUptoWhen (RComp (Trace.WeakensAssumes evalInterp) LoopTrace)
      (WP.SSAEntryRel fac G tys xs al ss₀) (RComp (fun ρ ρ' => ρ'.factory = ρ.factory) DDOut)
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss : Statements => (WP.ssaEntry fac G tys xs al ss).toOption.map (·.2.out) >>=
        fun ss : Statements => some (wpLoopBody norm ss).1)
      (fun ss : Statements => ss = ss₀ ∧ Block.treeForm ss = true ∧ Block.armsHaveChecks ss = true ∧
        ∀ x ∈ Block.freeVars ss, x ∈ xs ∨ x ∈ al.map (·.1)) params params :=
  OverapproximatesTracesUptoWhen.comp_eqOn_right hQ
    (fun _ _ h hpre => WP.ssaEntry_passive h hpre.2.1)
    (WP.ssa_overapproximatesTraces π params hp fac G tys xs al hal ss₀)
    (wpLoopBody_overapproximatesTraces π params hN hS)


/-! ## The loop at the normalization of the pipeline -/

/-- **The normalization of the loop keeps the values of substituted expressions in typed
    stores**, under a factory whose
    functions are those of `fac` (`hF`), when `fac` resolves `Int.Add` and `Bool.Not` to Core's
    built-in addition and negation. -/
theorem loopNorm_normLawT {fac : Lambda.Factory CoreLParams} {F : Expression.Factory}
    (hF : F.factory = fac)
    (hAdd : fac["Int.Add"]? = some (Lambda.intAddFunc (T := CoreLParams)).func)
    (hNot : fac["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func) :
    SubstNormLawT F (loopNorm fac) := fun g e hC hσ =>
  (addFold_normLaw (hF ▸ hAdd) _ hC).trans
    (rwAllWith_normLawT (rwRoot_laws fac) hF
      (coreEvaluator_WellFormedSemanticEvalBool F (hF ▸ hNot)) g e hC hσ)

/-- **The normalization of the loop satisfies the syntax laws of the inlining**: neither
    `rwAll fac` nor `addFold` adds a free variable, annotated occurrence or operator. -/
theorem loopNorm_synLaws (fac : Lambda.Factory CoreLParams) :
    DefInlineSynLaws Expression (loopNorm fac) :=
  coreDefInlineSynLaws
    (fun _ _ _ hp => rwAllWith_freeVars (rwRoot_laws fac) (addFold_freeVars _ _ hp))
    fun _ _ _ ho => rwAllWith_ops (rwRoot_laws fac) (addFold_ops _ _ ho)

/-- **The normalization of the loop keeps types** (`Core.Expression.Typed`). -/
theorem loopNorm_typed (fac : Lambda.Factory CoreLParams) :
    SubstNormTyped Expression.Typed (loopNorm fac) :=
  fun h => addFold_typed (rwAllWith_typed (rwRoot_laws fac) h)

/-- **The loop of the pipeline over-approximates the traces of a Core statement list in passive
    form**: `wpLoopBody_overapproximatesTraces` at the normalization `loopNorm fac` of the
    factory `fac` of the pipeline on a program `p` (`wpFactory`), from equal initial environments
    whose factory has the functions of `fac`. -/
theorem wpLoopBody_loopNorm_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) {moreFns fac : Lambda.Factory CoreLParams} {p : Program}
    (hfac : wpFactory moreFns p = .ok fac) :
    OverapproximatesTracesUptoWhen LoopTrace
      (fun ρ ρ' : Imperative.Env Expression => ρ = ρ' ∧ ρ.factory.factory = fac)
      DDOut
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss => some (wpLoopBody (loopNorm fac) ss).1)
      LoopPre params params :=
  wpLoopBody_overapproximatesTraces π params
    (fun _ hF => loopNorm_normLawT hF (wpFactory_intAdd hfac) (wpFactory_boolNot hfac))
    (loopNorm_synLaws _)

/-- **The SSA phase followed by the loop of the pipeline over-approximates the traces of a
    guarded statement list**: `ssa_wpLoopBody_overapproximatesTraces` at the normalization
    `loopNorm fac`, with `fac` the factory of the pipeline on a program `p` (`wpFactory`).  The
    entry relation
    of the SSA phase gives its target environment the factory of its source, whose functions are
    those of `fac`, so the condition on the factory holds there. -/
theorem ssa_wpLoopBody_loopNorm_overapproximatesTraces
    (π : String → Option Procedure) (params : InitEnvWFParams)
    (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList) {moreFns fac : Lambda.Factory CoreLParams}
    {p : Program} (hfac : wpFactory moreFns p = .ok fac)
    (G : WP.IdSet Expression) (tys : WP.Tys Expression) (xs : List Expression.Ident)
    (al : List (Expression.Ident × Expression.Ident)) (hal : ∀ q ∈ al, q.2 ∈ xs)
    (ss₀ : Statements) :
    OverapproximatesTracesUptoWhen (RComp (Trace.WeakensAssumes evalInterp) LoopTrace)
      (WP.SSAEntryRel fac G tys xs al ss₀)
      (RComp (fun ρ ρ' => ρ'.factory = ρ.factory) DDOut)
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss : Statements =>
        (WP.ssaEntry fac G tys xs al ss).toOption.map (·.2.out) >>=
          fun ss : Statements => some (wpLoopBody (loopNorm fac) ss).1)
      (fun ss : Statements => ss = ss₀ ∧ Block.treeForm ss = true ∧ Block.armsHaveChecks ss = true ∧
        ∀ x ∈ Block.freeVars ss, x ∈ xs ∨ x ∈ al.map (·.1)) params params :=
  ssa_wpLoopBody_overapproximatesTraces π params hp _ G tys xs al hal ss₀
    (Q := fun ρ => ρ.factory.factory = fac)
    (fun _ hF => loopNorm_normLawT hF (wpFactory_intAdd hfac) (wpFactory_boolNot hfac))
    (loopNorm_synLaws _) fun _ _ h => by rw [h.factory]; exact h.factoryIs

/-! ## The loop keeps the `init`s typed -/

/-- A round keeps the precondition of the loop, the initial-environment gate and the typing of
    the `init`s of a list, from an environment whose factory has the functions of `fac`. -/
private theorem wpRound_typed (params : InitEnvWFParams)
    {fac : Lambda.Factory CoreLParams}
    (hAdd : fac["Int.Add"]? = some (Lambda.intAddFunc (T := CoreLParams)).func)
    (hNot : fac["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func)
    {ρ : Imperative.Env Expression} (hq : ρ.factory.factory = fac) {ss : Statements}
    (hpre : LoopPre ss) (hwf : BlockInitEnvWF params ss ρ)
    (hi : Block.initsTyped Expression.Typed ss) :
    LoopPre (wpRound (loopNorm fac) ss) ∧ BlockInitEnvWF params (wpRound (loopNorm fac) ss) ρ ∧
      Block.initsTyped Expression.Typed (wpRound (loopNorm fac) ss) := by
  have hwf' := (wpRound_overapproximatesTraces (fun _ => none) params
    (Q := fun ρ => ρ.factory.factory = fac) (fun _ hF => loopNorm_normLawT hF hAdd hNot)
    (loopNorm_synLaws fac) ss _ rfl hpre ρ ρ ⟨rfl, hq⟩ hwf).2.2.2
  obtain ⟨Γ₁, -, hW₁⟩ := hwf.fvarTypesOk
  have hi2 := guardFwd_initsTyped (P := Expression) coreGuardFwdSynLaws (typedOpLaws fac)
    hpre.2.2 hwf.defUseOk hW₁ hi
  obtain ⟨Γ₂, -, hW₂⟩ := (blockInitEnvWF_guardFwd hpre.2.2 hwf).fvarTypesOk
  have hi3 := Imperative.DefInline.defInline_initsTyped (typedOpLaws fac) (loopNorm_typed fac)
    (guardFwd_passive hpre.2.2) hW₂ hi2
  refine ⟨wpRound_pre (loopNorm fac) ss _ rfl hpre, hwf', ?_⟩
  show Block.initsTyped Expression.Typed (DeadDefElim.deadDefElimH (P := Expression) [] _)
  rw [deadDefElimH_eq (P := Expression)]
  exact deadDefElim_initsTyped _ _ hi3

/-- **The loop keeps the passive form**: its output is that of some number of rounds
    (`wpLoopBody_eq_iterateT`), each of which keeps it (`wpRound_passive`). -/
theorem wpLoopBody_passive (norm : SubstNorm Expression) {ss : Statements}
    (hp : Block.passiveForm ss = true) : Block.passiveForm (wpLoopBody norm ss).1 = true := by
  obtain ⟨m, hm⟩ := wpLoopBody_eq_iterateT norm ss
  generalize (wpLoopBody norm ss).1 = ss' at hm ⊢
  induction m generalizing ss with
  | zero => exact Option.some.inj hm ▸ hp
  | succ m ih => exact ih (wpRound_passive norm hp) hm

/-- **The loop keeps the `init`s typed** (`Core.Expression.Typed` at their declared types): on a
    list without loops and calls in passive form satisfying the initial-environment gate at an
    environment whose factory has the functions of `fac`, when `fac` resolves `Int.Add` and
    `Bool.Not` to Core's built-ins.  Each round keeps the gate (its trace over-approximation) and
    the typing (guard forwarding, the inlining at `loopNorm fac` and the erasure keep it). -/
theorem wpLoopBody_initsTyped (params : InitEnvWFParams)
    {fac : Lambda.Factory CoreLParams}
    (hAdd : fac["Int.Add"]? = some (Lambda.intAddFunc (T := CoreLParams)).func)
    (hNot : fac["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func)
    {ρ : Imperative.Env Expression} (hq : ρ.factory.factory = fac) {ss : Statements}
    (hpre : LoopPre ss) (hwf : BlockInitEnvWF params ss ρ)
    (hi : Block.initsTyped Expression.Typed ss) :
    Block.initsTyped Expression.Typed (wpLoopBody (loopNorm fac) ss).1 := by
  obtain ⟨m, hm⟩ := wpLoopBody_eq_iterateT (loopNorm fac) ss
  generalize (wpLoopBody (loopNorm fac) ss).1 = ss' at hm ⊢
  induction m generalizing ss with
  | zero => exact Option.some.inj hm ▸ hi
  | succ m ih =>
    obtain ⟨hpre', hwf', hi'⟩ := wpRound_typed params hAdd hNot hq hpre hwf hi
    exact ih hpre' hwf' hi' hm

/-! ## The inlining with cached checks -/

/-- The `RInfo` of an application is computed from those of its parts. -/
private theorem rinfo_app (m : ExpressionMetadata) (f a : Expression.Expr) :
    rinfo (.app m f a) = rinfoApp f a (rinfo f) (rinfo a) := by
  simp only [rinfo, rinfoApp, WP.constFold, WP.constFoldApp, findIte]
  split
  · cases WP.constFold a with
    | none => cases findIte f <;> cases findIte a <;> simp
    | some c => cases c <;> cases findIte f <;> cases findIte a <;> simp
  · cases findIte f <;> cases a <;> simp

/-- The `RInfo` of an equality is computed from those of its sides. -/
private theorem rinfo_eq (m : ExpressionMetadata) (a b : Expression.Expr) :
    rinfo (.eq m a b) = rinfoEq (rinfo a) (rinfo b) := by
  simp only [rinfo, rinfoEq, WP.constFold, WP.constFoldEq, findIte]
  cases WP.constFold a <;> cases WP.constFold b <;> cases findIte a <;> cases findIte b <;> simp

/-- `withI f keep e (rinfo e)` is `f e` with its `RInfo`, when `keep` implies `f e = e`. -/
private theorem withI_eq {f : Expression.Expr → Expression.Expr} {keep : Bool}
    {e : Expression.Expr} (hk : keep = true → f e = e) :
    withI f keep e (rinfo e) = (f e, rinfo (f e)) := by
  unfold withI
  split
  · rw [hk ‹_›]
  · rfl

/-- **The rewrites at the root with `RInfo`s are `rwRoot`**, with the `RInfo` of the result. -/
private theorem rwRootI_eq (fac : Lambda.Factory CoreLParams) (e : Expression.Expr) :
    rwRootI fac e (rinfo e) = (rwRoot fac e, rinfo (rwRoot fac e)) := by
  have hb : ∀ e, keepBeta e = true → betaNG e = e := fun e h => by
    unfold keepBeta betaNG at *
    split <;> simp_all
  have hd : ∀ e, keepDec e = true → DefInline.decEq e = e := fun e h => by
    unfold keepDec DefInline.decEq at *
    split <;> simp_all
  have hf : ∀ e, keepFold fac e (rinfo e) = true → foldOp fac e = e := fun e h => by
    unfold keepFold foldOp at *
    split
    · rfl
    · simp_all [rinfo, Imperative.WP.WPOps.evalOp?, WP.opFold]
  have hl : ∀ e, (rinfo e).2 = true → liftIte fac e = e := fun e h => by
    simp only [rinfo, Option.isNone_iff_eq_none] at h
    simp [liftIte, h]
  have hs : ∀ e, keepSame e = true → iteSame e = e := fun e h => by
    unfold keepSame iteSame at *
    split <;> simp_all
  have ht : ∀ e, keepTest e = true → testCtor fac e = e := fun e h => by
    have hn : bodyFold fac e = none := by
      unfold bodyFold
      split
      · simp [keepTest] at h
      · rfl
    simp only [testCtor, hn]
  simp only [rwRootI, DefInline.rwRoot, withI_eq (hb e), withI_eq (hd _), withI_eq (hf _),
    withI_eq (hl _), withI_eq (hs _), withI_eq (ht _)]

/-- **The bottom-up rewrite with `RInfo`s is `rwBelowWith (rwRoot fac)`**, with the `RInfo` of
    the result, when `g'` gives the expressions of `g` with their `RInfo`s. -/
private theorem rwBelowI_eq (fac : Lambda.Factory CoreLParams)
    {g : Expression.Ident → Option Expression.Expr}
    {g' : Expression.Ident → Option (Expression.Expr × RInfo)}
    (hg : ∀ y, g' y = (g y).map fun d => (d, rinfo d)) :
    ∀ e, rwBelowI fac g' e =
      (rwBelowWith (rwRoot fac) g e, rinfo (rwBelowWith (rwRoot fac) g e)) := by
  have hg1 : (fun y => (g' y).map (·.1)) = g := funext fun y => by rw [hg y]; cases g y <;> rfl
  intro e
  induction e with
  | app m f a ihf iha =>
    simp only [rwBelowI, rwBelowWith, ihf, iha]
    exact rinfo_app .. ▸ rwRootI_eq fac _
  | ite m c t f _ _ _ => simp_all only [rwBelowI, rwBelowWith]; exact rwRootI_eq fac _
  | eq m a b iha ihb =>
    simp only [rwBelowI, rwBelowWith, iha, ihb]
    exact rinfo_eq .. ▸ rwRootI_eq fac _
  | fvar m x ty =>
    simp only [rwBelowI, rwBelowWith, leafRwI, leafRwWith, hg x]
    cases g x <;> rfl
  | _ => simp only [rwBelowI, rwBelowWith, leafRwI, leafRwWith, hg1]

/-- A scope value with the flags of its right-hand side: whether its annotations are ground, and
    its `RInfo`. -/
private def tagV : Option Expression.Expr → Option (Expression.Expr × Flags) :=
  Option.map fun d => (d, annGround d, rinfo d)

/-- An entry of the undo log with the flags of its right-hand side. -/
private def tagE (p : Expression.Ident × Option (Option Expression.Expr)) :
    Expression.Ident × Option (Option (Expression.Expr × Flags)) :=
  (p.1, p.2.map tagV)

/-- The state `stF` of the fast walk holds the state `st` of `defInline` with each recorded
    right-hand side flagged: same lookups up to the flags, same undo log, same log length. -/
private def FRel (st : GSt Expression) (stF : GSt FlagExpr) : Prop :=
  (∀ y : Expression.Ident, stF.scope[y]? = (st.scope[y]?).map tagV) ∧
    stF.trail = st.trail.map tagE ∧ stF.trailLen = st.trailLen

/-- Entering a name with the flagged entry keeps `FRel`. -/
private theorem FRel.push {st : GSt Expression} {stF : GSt FlagExpr} (h : FRel st stF)
    (x : Expression.Ident) (v : Option Expression.Expr) :
    FRel (st.push x v) (stF.push x (tagV v)) := by
  obtain ⟨hs, ht, hk⟩ := h
  rcases st with ⟨sc, tr, n⟩
  rcases stF with ⟨scF, trF, nF⟩
  refine ⟨fun y => ?_, by simp_all [GSt.push, tagE], by simp_all [GSt.push]⟩
  simp only [GSt.push, Std.HashMap.getElem?_insert]
  split <;> simp_all

/-- Undoing a log and its flagged copy in scopes related by flagging gives the flagged log and
    scopes related by flagging. -/
private theorem undoGo_tag :
    ∀ (k : Nat) (tr : List (Expression.Ident × Option (Option Expression.Expr)))
    {sc : Scope Expression} {scF : Scope FlagExpr},
    (∀ y : Expression.Ident, scF[y]? = (sc[y]?).map tagV) →
    (undoGo k (tr.map tagE) scF).1 = (undoGo k tr sc).1.map tagE ∧
      ∀ y : Expression.Ident, (undoGo k (tr.map tagE) scF).2[y]? = ((undoGo k tr sc).2[y]?).map tagV
  | 0, _, _, _, h | _ + 1, [], _, _, h => ⟨rfl, h⟩
  | k + 1, (x, old) :: tr, _, _, h => undoGo_tag k tr fun y => by
    cases old <;> simp only [Option.map_some, Option.map_none, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem?_erase] <;> split <;> simp_all

/-- Undoing to a mark keeps `FRel`. -/
private theorem FRel.undoTo {st : GSt Expression} {stF : GSt FlagExpr} (h : FRel st stF)
    (m : Nat) : FRel (st.undoTo m) (stF.undoTo m) := by
  obtain ⟨hs, ht, hk⟩ := h
  have hu := undoGo_tag (st.trailLen - m) st.trail hs
  rcases st with ⟨sc, tr, n⟩
  rcases stF with ⟨scF, trF, nF⟩
  simp only at ht hk hu
  subst ht hk
  exact ⟨hu.2, hu.1, rfl⟩

/-- The flagged lookup of the fast walk reads the recorded right-hand side with its flag. -/
private theorem lookF_eq {sc : Scope Expression} {scF : Scope FlagExpr}
    (h : ∀ y : Expression.Ident, scF[y]? = (sc[y]?).map tagV) (y : Expression.Ident) :
    lookF scF y = (look sc y).map fun d => (d, annGround d, rinfo d) := by
  simp only [lookF, look, h y]
  rcases sc[y]? with _ | _ | d <;> rfl

/-- The folding of the constants of a sum keeps the ground annotations, in both directions. -/
private theorem annGround_addFold (e : Expression.Expr) : annGround (addFold e) = annGround e := by
  unfold addFold
  split
  · split
    · rename_i h
      obtain ⟨-, -, rfl, rfl⟩ := h
      simp [annGround, intAddTy]
    · rfl
  · rfl

/-- `keepAdd e` implies that `addFold` leaves `e` unchanged. -/
private theorem addFold_of_keepAdd {e : Expression.Expr} (h : keepAdd e = true) :
    addFold e = e := by
  unfold keepAdd addFold at *
  split <;> simp_all

/-- **The fast normalization is `loopNorm` with the ground check and the `RInfo` of its
    result**, in a scope related by flagging. -/
private theorem loopNormF_eq (fac : Lambda.Factory CoreLParams) {sc : Scope Expression}
    {scF : Scope FlagExpr} (h : ∀ y : Expression.Ident, scF[y]? = (sc[y]?).map tagV)
    (e : Expression.Expr) :
    loopNormF fac scF e = (loopNorm fac (look sc) e, annGround (loopNorm fac (look sc) e),
      rinfo (loopNorm fac (look sc) e)) := by
  have hg : (fun y => (lookF scF y).map (·.1)) = look sc := funext fun y => by
    rw [lookF_eq h]; cases look sc y <;> rfl
  have hw := annGroundWith_eq (fl := fun y => ((lookF scF y).map (·.2.1)).getD true)
    (g := look sc) (fun x => by rw [lookF_eq h]; cases look sc x <;> rfl) e
  have hr := rwBelowI_eq fac (g := look sc) (g' := fun y => (lookF scF y).map fun d => (d.1, d.2.2))
    (fun y => by rw [lookF_eq h]; cases look sc y <;> rfl) e
  simp only [loopNormF, loopNorm, rwAll, rwAllWith, hg, hw, annGround_addFold, hr,
    withI_eq addFold_of_keepAdd]
  split
  next hc => simp [annGround_rwBelowWith (rwRoot_laws fac) hc]
  next hc => simp [hc]

/-- The flagged entry of the fast walk is the entry of `defInline`, flagged. -/
private theorem entryF_eq (cx : ICtx Expression) {sc : Scope Expression} {scF : Scope FlagExpr}
    (h : ∀ y : Expression.Ident, scF[y]? = (sc[y]?).map tagV) (x : Expression.Ident)
    (e e' : Expression.Expr) :
    entryF cx scF x e (e', annGround e', rinfo e') = tagV (entry cx sc x e e') := by
  have hc : ∀ z : Expression.Ident, scF.contains z = sc.contains z := fun z => by
    rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.contains_eq_isSome_getElem?, h z]
    cases sc[z]? <;> rfl
  simp only [entryF, entry, hc]
  split <;> rfl

mutual
/-- **The fast walk computes the walk of `defInline (loopNorm fac)`**, from states related by
    flagging, and ends in states related by flagging. -/
private theorem walkF_eq (fac : Lambda.Factory CoreLParams) (cx : ICtx Expression) :
    ∀ (st : GSt Expression) (stF : GSt FlagExpr) (ss : Statements), FRel st stF →
      (walkF fac cx stF ss).1 = (walk (loopNorm fac) cx st ss).1 ∧
        FRel (walk (loopNorm fac) cx st ss).2 (walkF fac cx stF ss).2
  | _, _, [], h => ⟨rfl, h⟩
  | st, stF, s :: rest, h => by
    obtain ⟨h1, h2⟩ := walkSF_eq fac cx st stF s h
    obtain ⟨h3, h4⟩ := walkF_eq fac cx _ _ rest h2
    simp only [walkF, DefInline.walk]
    exact ⟨by rw [h1, h3], h4⟩
/-- The fast walk over a statement computes the walk of `defInline (loopNorm fac)`. -/
private theorem walkSF_eq (fac : Lambda.Factory CoreLParams) (cx : ICtx Expression) :
    ∀ (st : GSt Expression) (stF : GSt FlagExpr) (s : Statement), FRel st stF →
      (walkSF fac cx stF s).1 = (walkS (loopNorm fac) cx st s).1 ∧
        FRel (walkS (loopNorm fac) cx st s).2 (walkSF fac cx stF s).2
  | st, stF, .cmd (.cmd (.init x ty (.det e) md)), h => by
    simp only [walkSF, DefInline.walkS, rwE, loopNormF_eq fac h.1, entryF_eq cx h.1, true_and]
    exact h.push _ _
  | st, stF, .cmd (.cmd (.init x ty .nondet md)), h => ⟨rfl, h.push x none⟩
  | st, stF, .cmd (.cmd (.assume l e md)), h | st, stF, .cmd (.cmd (.assert l e md)), h
  | st, stF, .cmd (.cmd (.cover l e md)), h => by
    simp only [walkSF, DefInline.walkS, rwE, loopNormF_eq fac h.1, true_and]
    exact h
  | st, stF, .cmd (.cmd (.set _ _ _)), h | st, stF, .cmd (.call _ _ _ _), h
  | st, stF, .loop _ _ _ _ _, h | st, stF, .exit _ _, h | st, stF, .typeDecl _ _, h => ⟨rfl, h⟩
  | st, stF, .ite c tss ess md, h => by
    obtain ⟨t1, r1⟩ := walkF_eq fac cx st stF tss h
    obtain ⟨t2, r2⟩ := walkF_eq fac cx _ _ ess (r1.undoTo st.trailLen)
    simp only [walkSF, DefInline.walkS, h.2.2] at t2 r2 ⊢
    exact ⟨by rw [t1, t2], r2.undoTo _⟩
  | st, stF, .block l ss md, h => by
    obtain ⟨t1, r1⟩ := walkF_eq fac cx st stF ss h
    simp only [walkSF, DefInline.walkS, h.2.2]
    exact ⟨by rw [t1], r1.undoTo _⟩
end

/-- **The inlining with cached ground checks is the inlining at `loopNorm fac`.** -/
theorem defInlineF_eq (fac : Lambda.Factory CoreLParams) (ss : Statements) :
    defInlineF fac ss = defInline (loopNorm fac) ss := by
  exact (walkF_eq fac _ {} {} ss ⟨fun _ => by simp, rfl, rfl⟩).1


end -- public section

end WPLoop
end Core
