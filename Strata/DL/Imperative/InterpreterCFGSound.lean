/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterCFG
public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.InterpreterSemanticsSpec
import Strata.DL.Imperative.CFGSemanticsProps
import all Strata.DL.Imperative.InterpreterCFG
import Strata.DL.Imperative.InterpreterSoundGeneric

/-! # Soundness of the monadic CFG interpreter against `StepCFGE`

The executable, monad-generic `runInterpCFG`, run through any `InterpObs P m`
observation, is sound against the *event-trace* relational semantics `StepCFGE`
(`CFGSemantics.lean`): a successful run from a configuration `start` whose stores denote at
the factory `F` (`ICFGConfig.Denoting`) to `final` corresponds to a `StepCFGStarE` derivation
from the semantic image `start.abs F` to `final.abs F` whose emitted events are the semantic
images of the runtime events the run recorded in the observation's trace, and `final` denotes
at `F` again.

The whole-run bookkeeping is phrased against the observation's `trace`, which is
most-recent-first: a run that chronologically emits `evs` lands in a state whose
trace is `evs.reverse ++ (trace of the start state)`.  Both the command
correspondence hypothesis `hCmd` and the conclusion use this `evs.reverse ++ …`
shape.

Two hypotheses parameterize the theorem:
* `hCmd` — the command-level correspondence between the executable store-stepper
  `stepCmd` and the command relation `EvalCmd`, under a configuration invariant `Inv`
  (the reusable content proved for the structured engine, instantiated per
  language);
* `hPres` — `Inv` is closed under `StepCFGE` steps.

Each command runs at the factory and store of the configuration's environment.

This module's own content is the CFG control-flow induction, event-trace–aware.

Key theorem: `runInterpCFG_soundE` (whole-run soundness). -/

namespace Imperative

public section

variable {P : PureExpr} {l CmdT : Type} [BEq l]
variable [HasBool P] [HasBoolOps P] [HasFvars P]
    [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P]
variable {m : Type → Type} [Monad m] [InterpEffects P m] [MonadExcept StopReason m]

/-- **Per-step soundness of `stepInterpCFG`.**  One successful executable CFG step from a
    non-terminal config that satisfies a configuration invariant `Inv` is one transition of the
    event-trace CFG reference relation `StepCFGE`, emitting exactly the events the step recorded
    (chronologically, so the observed trace grows by their reverse), and the next config
    satisfies `Inv`.  It assumes that each successful command step is a reference command step,
    that `Inv` is closed under reference steps, and that at the factory `F` every value the
    bounded evaluator commits to denotes the reference evaluator's value. -/
theorem stepInterpCFG_soundE [InterpLangBool P]
    (obs : InterpObs P m)
    (EvalCmd : EvalCmdParamE P CmdT (Event P))
    (stepCmd : StepCmdStoreM P CmdT m)
    (Inv : CFGConfig l CmdT P → Prop)
    (F : P.Factory)
    (hCmd : ∀ fuel g t c cs tr (ρ : IEnv P) σ' cfgr st st',
        RStore.Denoting F ρ.store.get → ρ.factory = InterpLang.rfactory F →
        Inv (.inBlock g t (c :: cs) tr (ρ.abs F)) →
        obs.run (stepCmd fuel ρ.factory ρ.store c) cfgr st = (.ok σ', st') →
        ∃ revs : List (IEvent P), obs.trace st' = revs.reverse ++ obs.trace st
          ∧ EvalCmd F (InterpLang.absStore F ρ.store.get) c (InterpLang.absStore F σ'.get)
            (revs.map (REvent.abs F))
          ∧ RStore.Denoting F σ'.get)
    (hPres : ∀ a emitted b,
        StepCFGE P EvalCmd a emitted b → Inv a → Inv b)
    (hEvalBridge : BoundedEvalSoundAt P F)
    (fuel : Nat)
    {start next : ICFGConfig l CmdT P} {cfgr : obs.Cfg} {st st' : obs.St}
    (hnt : ∀ ρ, start ≠ .terminal ρ)
    (hden : start.Denoting F)
    (hInv : Inv (start.abs F))
    (hrun : obs.run (stepInterpCFG stepCmd fuel start) cfgr st = (.ok next, st')) :
    (∃ revs : List (IEvent P), obs.trace st' = revs.reverse ++ obs.trace st
      ∧ StepCFGE P EvalCmd (start.abs F) (revs.map (REvent.abs F)) (next.abs F))
    ∧ next.Denoting F ∧ Inv (next.abs F) := by
  have hstep : ∀ {a : ICFGConfig l CmdT P} {revs : List (IEvent P)} {b : ICFGConfig l CmdT P},
      StepCFGE P EvalCmd (ICFGConfig.abs F a) (revs.map (REvent.abs F))
      (ICFGConfig.abs F b) → Inv (a.abs F) → Inv (b.abs F) := fun h hi => hPres _ _ _ h hi
  obtain ⟨hds, hfac⟩ := hden
  rcases start with ⟨g, t, ρ⟩ | ⟨g, t, _ | ⟨c, cs⟩, tr, ρ⟩ | ρ
  · simp only [stepInterpCFG] at hrun
    split at hrun <;> simp only [obs.run_pure, obs.run_throw, Prod.mk.injEq, reduceCtorEq,
      false_and, Except.ok.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    have hs : StepCFGE P EvalCmd (ICFGConfig.abs F (.atBlock g t ρ)) (([] : List (IEvent P)).map
        (REvent.abs F)) (ICFGConfig.abs F (.inBlock g t _ _ ρ)) := (.fetch ‹_›)
    exact ⟨⟨[], by simp, hs⟩, ⟨hds, hfac⟩, hstep hs hInv⟩
  · simp only [stepInterpCFG] at hrun
    have hg := fun {c r : P.Expr}
        (hb : InterpLang.boundedEval (P := P) fuel ρ.factory ρ.store.get c = some r) =>
      BoundedEvalSoundAt.guard hEvalBridge hds (hfac ▸ hb)
    cases tr with
    | condGoto c tl el md =>
      simp only at hrun
      (repeat' (first
        | split at hrun
        | simp only [obs.run_pure, obs.run_throw, obs.run_bind, obs.branch_stuck, Prod.mk.injEq,
            reduceCtorEq, false_and, Except.ok.injEq] at hrun))
      all_goals obtain ⟨rfl, rfl⟩ := hrun
      all_goals subst_vars
      · have hs : StepCFGE P EvalCmd (ICFGConfig.abs F (.inBlock g t [] (.condGoto c tl el md) ρ))
            (([] : List (IEvent P)).map (REvent.abs F)) (ICFGConfig.abs F (.atBlock g tl ρ)) :=
          (.goto_true ((hg ‹_›).1 ‹_›))
        exact ⟨⟨[], by simp, hs⟩, ⟨hds, hfac⟩, hstep hs hInv⟩
      · have hs : StepCFGE P EvalCmd (ICFGConfig.abs F (.inBlock g t [] (.condGoto c tl el md) ρ))
            (([] : List (IEvent P)).map (REvent.abs F)) (ICFGConfig.abs F (.atBlock g el ρ)) :=
          (.goto_false ((hg ‹_›).2 ‹_›))
        exact ⟨⟨[], by simp, hs⟩, ⟨hds, hfac⟩, hstep hs hInv⟩
    | finish md =>
      simp only [obs.run_pure, Prod.mk.injEq, Except.ok.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      have hs : StepCFGE P EvalCmd (ICFGConfig.abs F (.inBlock g t [] (.finish md) ρ))
          (([] : List (IEvent P)).map (REvent.abs F)) (ICFGConfig.abs F (.terminal ρ)) :=
        .finish
      exact ⟨⟨[], by simp, hs⟩, ⟨hds, hfac⟩, hstep hs hInv⟩
  · simp only [stepInterpCFG, obs.run_bind, obs.run_pure] at hrun
    split at hrun <;> simp only [Prod.mk.injEq, Except.ok.injEq, reduceCtorEq, false_and] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    rename_i σ' _ hc
    obtain ⟨revs, htr, he, hd'⟩ := hCmd _ _ _ _ _ _ _ _ _ _ _ hds hfac hInv hc
    have hs : StepCFGE P EvalCmd (ICFGConfig.abs F (.inBlock g t (c :: cs) tr ρ))
        (revs.map (REvent.abs F)) (ICFGConfig.abs F (.inBlock g t cs tr { ρ with store := σ' })) :=
      .step_cmd he
    exact ⟨⟨revs, htr, hs⟩, ⟨hd', hfac⟩, hstep hs hInv⟩
  · exact absurd rfl (hnt _)

/-- **Soundness of the monadic CFG interpreter against `StepCFGE`.**  A successful
    observation of `runInterpCFG` from a config `start` whose `CFGConfig` (`ICFGConfig.abs`)
    satisfies a configuration invariant `Inv` to `final` is a derivation from the `CFGConfig` of
    `start` to that of `final` of `StepCFGStarE`, the multi-step
    event-trace CFG reference semantics, emitting exactly the run's recorded events
    (chronologically, so the observed trace grows by their reverse).  It assumes that each
    successful command step is a reference command step, that `Inv` is closed under reference
    steps, and that at the factory `F` every value the bounded evaluator commits to denotes the
    reference evaluator's value. -/
theorem runInterpCFG_soundE [InterpLangBool P]
    (obs : InterpObs P m)
    (EvalCmd : EvalCmdParamE P CmdT (Event P))
    (stepCmd : StepCmdStoreM P CmdT m)
    (Inv : CFGConfig l CmdT P → Prop)
    (F : P.Factory)
    (hCmd : ∀ fuel g t c cs tr (ρ : IEnv P) σ' cfgr st st',
        RStore.Denoting F ρ.store.get → ρ.factory = InterpLang.rfactory F →
        Inv (.inBlock g t (c :: cs) tr (ρ.abs F)) →
        obs.run (stepCmd fuel ρ.factory ρ.store c) cfgr st = (.ok σ', st') →
        ∃ revs : List (IEvent P), obs.trace st' = revs.reverse ++ obs.trace st
          ∧ EvalCmd F (InterpLang.absStore F ρ.store.get) c (InterpLang.absStore F σ'.get)
            (revs.map (REvent.abs F))
          ∧ RStore.Denoting F σ'.get)
    (hPres : ∀ a emitted b,
        StepCFGE P EvalCmd a emitted b → Inv a → Inv b)
    (hEvalBridge : BoundedEvalSoundAt P F) :
    ∀ (fuel : Nat) (start final : ICFGConfig l CmdT P) (cfgr : obs.Cfg) (st st' : obs.St),
      start.Denoting F → Inv (start.abs F) →
      obs.run (runInterpCFG stepCmd fuel start) cfgr st = (.ok final, st') →
      ∃ revs : List (IEvent P), obs.trace st' = revs.reverse ++ obs.trace st
        ∧ StepCFGStarE P EvalCmd (start.abs F) (revs.map (REvent.abs F)) (final.abs F)
        ∧ final.Denoting F := by
  intro fuel c _ _ s _ hd hi h
  fun_induction runInterpCFG stepCmd fuel c generalizing s <;>
    simp only [InterpObs.run_pure, InterpObs.run_throw, InterpObs.run_bind, Prod.mk.injEq,
      Except.ok.injEq, reduceCtorEq, false_and] at h
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, .refl _, hd⟩
  rename_i hnt ih
  split at h <;> rename_i hs
  · obtain ⟨⟨revs, htr, hstepE⟩, hd', hi'⟩ :=
      stepInterpCFG_soundE obs EvalCmd stepCmd Inv F hCmd hPres hEvalBridge _
        (fun ρ heq => hnt ρ heq) hd hi hs
    obtain ⟨revs2, htr2, hrest, hdf⟩ := ih _ _ hd' hi' h
    refine ⟨revs ++ revs2, by simp [htr, htr2], ?_, hdf⟩
    rw [List.map_append]
    exact .step _ _ _ _ _ hstepE hrest
  · simp at h

end -- public section

end Imperative
