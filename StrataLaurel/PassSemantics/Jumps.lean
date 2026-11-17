/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.Labels

/-!
# Jump boundaries

A `jump_` never crosses a call or an expression: `invokeProc` and `evalExprMd` run under
`jumpBoundary`, which turns an escaping `jump_` into the error of a jump with nowhere to land.

* `NoJ x`: `x` never returns a `jump_` signal. `NoJ.bind`, `NoJ.tryCatch` and so on prove it
  compositionally, `noJ_jumpBoundary` gives it for every boundary, and `jumpBoundary_noJ` says a
  boundary around an action that has it changes nothing.
* `fs_jumpBoundary`: two simulated actions stay simulated under boundaries on both sides, and
  `fs_jumpBoundaryL`/`fs_jumpBoundaryR` drop a boundary on one side when the other side has
  `NoJ`.
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

theorem run_ext {x y : EvalM PM α} (h : ∀ σ τ, run x σ τ = run y σ τ) : x = y := by
  funext σ τ
  exact h σ τ

/-- `x` never returns a `jump_` signal. -/
def NoJ (x : EvalM PM α) : Prop :=
  ∀ σ τ l d σ1 τ1, run x σ τ ≠ .ok ((.error (.jump_ l d), σ1), τ1)

/-- A control signal that is not a `jump_`. -/
def NotJump (c : Control) : Prop := ∀ l d, c ≠ .jump_ l d

theorem NoJ.pure (a : α) : NoJ (pure a : EvalM PM α) := by
  intro σ τ l d σ1 τ1 h
  rw [run_pure] at h
  cases h

theorem NoJ.throw {c : Control} (hc : NotJump c) : NoJ (throw c : EvalM PM α) := by
  intro σ τ l d σ1 τ1 h
  rw [run_throw] at h
  simp only [Except.ok.injEq, Prod.mk.injEq, Except.error.injEq] at h
  exact hc l d h.1.1

theorem NoJ.get : NoJ (MonadState.get : EvalM PM EvalState) := by
  intro σ τ l d σ1 τ1 h
  rw [run_get] at h
  cases h

theorem NoJ.set (σ' : EvalState) : NoJ (MonadStateOf.set σ' : EvalM PM PUnit) := by
  intro σ τ l d σ1 τ1 h
  have e : run (MonadStateOf.set σ' : EvalM PM PUnit) σ τ = .ok ((.ok (), σ'), τ) := rfl
  rw [e] at h
  cases h

theorem NoJ.modify (f : EvalState → EvalState) : NoJ (_root_.modify f : EvalM PM PUnit) := by
  intro σ τ l d σ1 τ1 h
  rw [run_modify] at h
  cases h

theorem NoJ.liftM (x : PM α) : NoJ (liftM x : EvalM PM α) := by
  intro σ τ l d σ1 τ1 h
  rw [run_lift] at h
  rcases hx : x τ with e | ⟨a, τ'⟩ <;> rw [hx] at h <;> cases h

theorem NoJ.bind {x : EvalM PM α} {f : α → EvalM PM β} (hx : NoJ x) (hf : ∀ a, NoJ (f a)) : NoJ (x >>= f) := by
  intro σ τ l d σ1 τ1 h
  rw [run_bind] at h
  rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq, Except.error.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact hx _ _ _ _ _ _ hr
  · exact hf a _ _ _ _ _ _ h

theorem NoJ.getBind {f : EvalState → EvalM PM β} (hf : ∀ s, NoJ (f s)) : NoJ (MonadState.get >>= f) :=
  NoJ.bind NoJ.get hf

/-- `tryCatch` never returns a `jump_` if its body does not and its handler does not on any signal other
than a `jump_`. -/
theorem NoJ.tryCatch {x : EvalM PM α} {h : Control → EvalM PM α} (hx : NoJ x)
    (hh : ∀ c, NotJump c → NoJ (h c)) : NoJ (MonadExcept.tryCatch x h) := by
  intro σ τ l d σ1 τ1 he
  rw [run_tryCatch] at he
  rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at he
  · cases he
  · exact hh c (fun l' d' hc => hx _ _ _ _ _ _ (hc ▸ hr)) _ _ _ _ _ _ he
  · cases he

theorem NoJ.ite {c : Prop} [Decidable c] {x y : EvalM PM α} (hx : NoJ x) (hy : NoJ y) :
    NoJ (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem NoJ.map {x : EvalM PM α} (f : α → β) (hx : NoJ x) : NoJ (f <$> x) := by
  simp only [map_eq_pure_bind]
  exact hx.bind (fun _ => NoJ.pure _)

theorem NoJ.forM {l : List β} {f : β → EvalM PM PUnit} (h : ∀ b, NoJ (f b)) : NoJ (l.forM f) := by
  induction l with
  | nil => exact NoJ.pure _
  | cons b bs ih => exact (h b).bind (fun _ => ih)

theorem NoJ.mapM {l : List β} {f : β → EvalM PM γ} (h : ∀ b, NoJ (f b)) : NoJ (l.mapM f) := by
  induction l with
  | nil => exact NoJ.pure _
  | cons b bs ih =>
    simp only [List.mapM_cons]
    exact (h b).bind (fun _ => ih.bind (fun _ => NoJ.pure _))

theorem NoJ.forIn {l : List β} {b : γ} {f : β → γ → EvalM PM (ForInStep γ)} (h : ∀ x c, NoJ (f x c)) :
    NoJ (forIn l b f) := by
  induction l generalizing b with
  | nil => exact NoJ.pure _
  | cons x xs ih =>
    simp only [List.forIn_cons]
    refine (h x b).bind (fun r => ?_)
    cases r with
    | done c => exact NoJ.pure _
    | yield c => exact ih

theorem run_evalError (msg : String) (σ : EvalState) (τ : Trace) :
    ∃ m, run (evalError msg : EvalM PM α) σ τ = .error (.fail m) := by
  simp only [evalError, hostFail, run_bind, run_get, run_lift]
  exact ⟨_, rfl⟩

theorem NoJ.evalError (msg : String) : NoJ (evalError msg : EvalM PM α) := by
  intro σ τ l d σ1 τ1 h
  obtain ⟨m, hm⟩ := run_evalError (α := α) msg σ τ
  rw [hm] at h
  cases h

/-- Running `jumpBoundary x` runs `x`, and turns a `jump_` it returns into the error of a jump with nowhere
to land. -/
theorem run_jumpBoundary (x : EvalM PM α) (σ : EvalState) (τ : Trace) :
    run (jumpBoundary x) σ τ = match run x σ τ with
      | .ok ((.error (.jump_ l _), σ1), τ1) => run (evalError s!"no block labelled '{l}' to jump to") σ1 τ1
      | r => r := by
  unfold jumpBoundary
  rw [run_tryCatch]
  rcases run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩
  · rfl
  · cases c <;> rfl
  · rfl

/-- A boundary never lets a `jump_` out. -/
theorem noJ_jumpBoundary (x : EvalM PM α) : NoJ (jumpBoundary x) := by
  intro σ τ l d σ1 τ1 h
  rw [run_jumpBoundary] at h
  rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · cases c
    case jump_ l' d' =>
      obtain ⟨m, hm⟩ := run_evalError (α := α) s!"no block labelled '{l'}' to jump to" σ2 τ2
      dsimp only at h
      rw [hm] at h
      cases h
    all_goals cases h
  · cases h

/-- A boundary around an action that never returns a `jump_` changes nothing. -/
theorem jumpBoundary_noJ {x : EvalM PM α} (hx : NoJ x) : jumpBoundary x = x := by
  refine run_ext (fun σ τ => ?_)
  rw [run_jumpBoundary]
  rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩
  · rfl
  · cases c
    case jump_ l d => exact absurd hr (hx _ _ _ _ _ _)
    all_goals rfl
  · rfl

theorem NoJ.withLabels {x : EvalM PM α} (f : List String → List String) (hx : NoJ x) :
    NoJ (Interpreter.withLabels f x) := by
  intro σ τ l d σ1 τ1 h
  rw [run_withLabels] at h
  rcases hr : run x { σ with openLabels := f σ.openLabels } τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq, Except.error.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact hx _ _ _ _ _ _ hr
  · cases h

theorem CtlR.notJump {ret : Option String} {c c' : Control} (h : CtlR ret c c') (hc : NotJump c) : NotJump c' := by
  intro l d hc'
  subst hc'
  rcases h with rfl | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩
  · exact hc l d rfl
  · cases h
  · cases h

theorem CtlR.notJump' {ret : Option String} {c c' : Control} (h : CtlR ret c c') (hc : NotJump c') : NotJump c := by
  intro l d hc0
  subst hc0
  rcases h with rfl | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩
  · exact hc l d rfl
  · cases h
  · cases h

/-- A run that returns a `jump_` and the run it is related to by `RR`: the other one returns the same `jump_`. -/
theorem RR.jump_tgt {T U : SimRel} {A : α → β → Prop} {l : String} {d : GotoDestination} {σ1 : EvalState}
    {τ1 : Trace} {r' : R β} (h : RR T U A (.ok ((.error (.jump_ l d), σ1), τ1)) r') :
    ∃ σ1' τ1', r' = .ok ((.error (.jump_ l d), σ1'), τ1') := by
  rcases r' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;> simp only [RR, ExRel, false_and] at h
  obtain ⟨hsg, -⟩ := h
  rcases hsg with ⟨hcr, -, -⟩ | ⟨v, hv, -, -⟩
  · rcases hcr with rfl | ⟨_, _, h1, _⟩ | ⟨_, _, h1, _⟩
    · exact ⟨_, _, rfl⟩
    · cases h1
    · cases h1
  · cases hv

/-- A run related by `RR` to one that returns a `jump_`, and does not return one itself, is stuck. -/
theorem RR.jump_src {T U : SimRel} {A : α → β → Prop} {l : String} {d : GotoDestination} {σ1' : EvalState}
    {τ1' : Trace} {r : R α} (h : RR T U A r (.ok ((.error (.jump_ l d), σ1'), τ1')))
    (hr : ∀ l d σ1 τ1, r ≠ .ok ((.error (.jump_ l d), σ1), τ1)) : ∃ e, r = .error e ∧ Stuck e := by
  rcases r with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;> simp only [RR, ExRel, false_and] at h
  · exact ⟨e, rfl, h⟩
  · obtain ⟨hsg, -⟩ := h
    rcases hsg with ⟨hcr, -, -⟩ | ⟨v, -, hv, -⟩
    · rcases hcr with rfl | ⟨_, _, _, h1⟩ | ⟨_, _, _, h1⟩
      · exact absurd rfl (hr _ _ _ _)
      · cases h1
      · cases h1
    · cases hv

theorem run_jumpBoundary_of {x : EvalM PM α} {σ : EvalState} {τ : Trace}
    (hx : ∀ l d σ1 τ1, run x σ τ ≠ .ok ((.error (.jump_ l d), σ1), τ1)) : run (jumpBoundary x) σ τ = run x σ τ := by
  rw [run_jumpBoundary]
  revert hx
  rcases run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> intro hx
  · rfl
  · cases c
    case jump_ l d => exact absurd rfl (hx _ _ _ _)
    all_goals rfl
  · rfl

theorem not_oof_of_jumpBoundary {x : EvalM PM α} {σ : EvalState} {τ : Trace} (hn : ¬ OOF (run (jumpBoundary x) σ τ)) :
    ¬ OOF (run x σ τ) := by
  intro ho
  apply hn
  rw [run_jumpBoundary]
  revert ho
  rcases run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> intro ho <;> (try cases c) <;> simp_all [OOF]

/-- Two simulated actions stay simulated under a boundary on each side: a `jump_` on one side is a `jump_`
on the other, and both become an error that is not a stuck run. -/
theorem fs_jumpBoundary {S T U : SimRel} {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β}
    (h : FSH S T U A x y) : FSH S T U A (jumpBoundary x) (jumpBoundary y) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have h0 := h.sim σ σ' τ τ' hs ht (not_oof_of_jumpBoundary hn)
  by_cases hj : ∃ l d σ1 τ1, run x σ τ = .ok ((.error (.jump_ l d), σ1), τ1)
  · obtain ⟨l, d, σ1, τ1, hr⟩ := hj
    rw [hr] at h0
    obtain ⟨σ1', τ1', hr'⟩ := RR.jump_tgt h0
    rw [run_jumpBoundary, run_jumpBoundary, hr, hr']
    dsimp only
    obtain ⟨m, hm⟩ := run_evalError (α := α) s!"no block labelled '{l}' to jump to" σ1 τ1
    obtain ⟨m', hm'⟩ := run_evalError (α := β) s!"no block labelled '{l}' to jump to" σ1' τ1'
    rw [hm, hm']
    exact fun h => absurd h stuck_fail
  · have hx : ∀ l d σ1 τ1, run x σ τ ≠ .ok ((.error (.jump_ l d), σ1), τ1) :=
      fun l d σ1 τ1 he => hj ⟨l, d, σ1, τ1, he⟩
    rw [run_jumpBoundary_of hx]
    by_cases hj' : ∃ l d σ1' τ1', run y σ' τ' = .ok ((.error (.jump_ l d), σ1'), τ1')
    · obtain ⟨l, d, σ1', τ1', hr'⟩ := hj'
      rw [hr'] at h0
      obtain ⟨e, he, hst⟩ := RR.jump_src h0 hx
      rw [he, run_jumpBoundary, hr']
      dsimp only
      obtain ⟨m', hm'⟩ := run_evalError (α := β) s!"no block labelled '{l}' to jump to" σ1' τ1'
      rw [hm']
      exact fun _ => hst
    · rw [run_jumpBoundary_of (fun l d σ1' τ1' he => hj' ⟨l, d, σ1', τ1', he⟩)]
      exact h0

/-- A boundary on the source side can be dropped when the target never returns a `jump_`. -/
theorem fs_jumpBoundaryL {S T U : SimRel} {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β}
    (hy : NoJ y) (h : FSH S T U A x y) : FSH S T U A (jumpBoundary x) y := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have h0 := h.sim σ σ' τ τ' hs ht (not_oof_of_jumpBoundary hn)
  have hx : ∀ l d σ1 τ1, run x σ τ ≠ .ok ((.error (.jump_ l d), σ1), τ1) := by
    intro l d σ1 τ1 hr
    rw [hr] at h0
    obtain ⟨σ1', τ1', hr'⟩ := RR.jump_tgt h0
    exact hy _ _ _ _ _ _ hr'
  rw [run_jumpBoundary_of hx]
  exact h0

/-- A boundary on the target side can be dropped when the source never returns a `jump_`. -/
theorem fs_jumpBoundaryR {S T U : SimRel} {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β}
    (hx : NoJ x) (h : FSH S T U A x y) : FSH S T U A x (jumpBoundary y) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have h0 := h.sim σ σ' τ τ' hs ht hn
  by_cases hj' : ∃ l d σ1' τ1', run y σ' τ' = .ok ((.error (.jump_ l d), σ1'), τ1')
  · obtain ⟨l, d, σ1', τ1', hr'⟩ := hj'
    rw [hr'] at h0
    obtain ⟨e, he, hst⟩ := RR.jump_src h0 (hx σ τ)
    rw [he, run_jumpBoundary, hr']
    dsimp only
    obtain ⟨m', hm'⟩ := run_evalError (α := β) s!"no block labelled '{l}' to jump to" σ1' τ1'
    rw [hm']
    exact fun _ => hst
  · rw [run_jumpBoundary_of (fun l d σ1' τ1' he => hj' ⟨l, d, σ1', τ1', he⟩)]
    exact h0

end Strata.Laurel.PassSemantics
