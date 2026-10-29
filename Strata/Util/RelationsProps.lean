/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.Relations
import all Strata.Util.Relations

/-!
# Properties of relations (`RComp`, `ReflTrans`, `ReflTransT`)

## Key theorems

* `RComp.collapse`, `RComp.mono` — composition collapses under transitivity and is monotone
* `IsReflexive.dense` — every reflexive relation is dense
* `ReflTrans_Reflexive`, `ReflTrans_Transitive` — `ReflTrans` is reflexive and transitive
* `reflTransT_to_prop` — the `Type`-valued closure implies the `Prop`-valued one
* `reflTransTraceT_to_prop`, `reflTransTrace_nonempty_T`, and
  `reflTransTrace_to_T` — convert between the `Type`- and `Prop`-valued traced
  closures
* `ReflTransTrace.trans` — traced executions compose by chronological trace
  concatenation
* `ReflTransTrace.toReflTrans` — erasing each step's emitted events recovers an
  ordinary reflexive-transitive execution
* `ReflTransTrace.imp` — a traced closure is monotone in its step relation
* `ReflTransTraceN.mono`, `reflTransTrace_iff_reflTransTraceN` — a larger bound
  allows more, and a finite traced execution is one within some bound
-/

public section
section Relation
namespace Relations
end Relations

/-- `RComp R₁ R₂` reduces to `R` when `R` is transitive and `R₁, R₂ ⊆ R`. -/
theorem RComp.collapse {A : Type} {R₁ R₂ R : Relation A} {a c : A}
    (htrans : IsTransitive R)
    (h₁ : ∀ x y, R₁ x y → R x y) (h₂ : ∀ x y, R₂ x y → R x y)
    (h : RComp R₁ R₂ a c) : R a c := by
  obtain ⟨b, hr₁, hr₂⟩ := h
  exact htrans _ _ _ (h₁ _ _ hr₁) (h₂ _ _ hr₂)


/-- `RComp` is monotone in both arguments. -/
theorem RComp.mono {A : Type} {R₁ R₁' R₂ R₂' : Relation A}
    (h₁ : ∀ x y, R₁ x y → R₁' x y) (h₂ : ∀ x y, R₂ x y → R₂' x y)
    {a c : A} (h : RComp R₁ R₂ a c) : RComp R₁' R₂' a c := by
  obtain ⟨b, hr₁, hr₂⟩ := h
  exact ⟨b, h₁ _ _ hr₁, h₂ _ _ hr₂⟩

@[expose] def IsDense (r : Relation A) : Prop := ∀ a c, r a c → ∃ b, r a b ∧ r b c

/-- Any reflexive relation is dense: split `r a c` at the endpoint `a` using
    `r a a`.  In particular equality is dense, which is why the shared-start
    (`· = ·`) composition combinators need no separate density hypothesis. -/
theorem IsReflexive.dense {A : Type} {r : Relation A} (h : IsReflexive r) : IsDense r :=
  fun a _c hac => ⟨a, h a, hac⟩


theorem ReflTrans_Reflexive {A: Type} (r: Relation A):
  IsReflexive (ReflTrans r) := by apply ReflTrans.refl


theorem ReflTrans_Transitive {A: Type} (r: Relation A):
  IsTransitive (ReflTrans r) := by
  unfold IsTransitive; intros x y z rxy
  induction rxy generalizing z
  case refl => simp
  case step x1 y1 z1 rxy1 ryz1 IH =>
    intros rzz1;
    apply (ReflTrans.step _ y1 _ rxy1 (IH _ rzz1))


theorem reflTransT_to_prop {A : Type} {r : A → A → Prop} {a b : A} :
    ReflTransT r a b → ReflTrans r a b := by
  intro h; induction h with
  | refl => exact .refl _
  | step _ _ _ hstep _ ih => exact .step _ _ _ hstep ih


/-- Traced executions compose by concatenating their chronological traces. -/
theorem ReflTransTrace.trans {A E : Type} (r : A → List E → A → Prop)
    {a b c : A} {trace₁ trace₂ : List E}
    (h₁ : ReflTransTrace r a trace₁ b)
    (h₂ : ReflTransTrace r b trace₂ c) :
    ReflTransTrace r a (trace₁ ++ trace₂) c := by
  induction h₁ with
  | refl => simpa using h₂
  | step x emitted y rest z hstep _ ih =>
    simpa [List.append_assoc] using
      (ReflTransTrace.step x emitted y (rest ++ trace₂) c hstep (ih h₂))

/-- Forgetting labels from every step of a traced execution yields an ordinary
reflexive-transitive execution. -/
theorem ReflTransTrace.toReflTrans {A E : Type}
    {r : A → List E → A → Prop} {u : A → A → Prop}
    (hforget : ∀ a emitted b, r a emitted b → u a b)
    {a b : A} {trace : List E}
    (h : ReflTransTrace r a trace b) : ReflTrans u a b := by
  induction h with
  | refl => exact .refl _
  | step x emitted y _ z hstep _ ih =>
    exact .step x y z (hforget x emitted y hstep) ih

/-- The `Type`-valued traced closure implies the `Prop`-valued one: forget the
step-count structure. -/
theorem reflTransTraceT_to_prop {A E : Type} {r : A → List E → A → Prop}
    {a b : A} {trace : List E} :
    ReflTransTraceT r a trace b → ReflTransTrace r a trace b := by
  intro h; induction h with
  | refl => exact .refl _
  | step _ _ _ _ _ hstep _ ih => exact .step _ _ _ _ _ hstep ih

/-- Every `Prop`-valued traced derivation has a `Type`-valued witness with the
same endpoints and trace (its step count is not observable through `Prop`). -/
theorem reflTransTrace_nonempty_T {A E : Type} {r : A → List E → A → Prop}
    {a b : A} {trace : List E} :
    ReflTransTrace r a trace b → Nonempty (ReflTransTraceT r a trace b) := by
  intro h; induction h with
  | refl => exact ⟨.refl _⟩
  | step _ _ _ _ _ hstep _ ih => exact ih.elim fun rest => ⟨.step _ _ _ _ _ hstep rest⟩

/-- Recover a `Type`-valued traced derivation from a `Prop`-valued one via choice.
`noncomputable`; harmless when the enclosing result is again a `Prop`. -/
noncomputable def reflTransTrace_to_T {A E : Type} {r : A → List E → A → Prop}
    {a b : A} {trace : List E} :
    ReflTransTrace r a trace b → ReflTransTraceT r a trace b :=
  fun h => Classical.choice (reflTransTrace_nonempty_T h)

/-- A traced closure is monotone in its step relation. -/
theorem ReflTransTrace.imp {A E : Type} {r r' : A → List E → A → Prop}
    (h : ∀ x evs y, r x evs y → r' x evs y) :
    ∀ {x evs y}, ReflTransTrace r x evs y → ReflTransTrace r' x evs y :=
  (by induction · <;> solve_by_elim)

/-- A larger bound allows every execution a smaller one does. -/
theorem ReflTransTraceN.mono {A E : Type} {r : A → List E → A → Prop} {n m : Nat}
    (hnm : n ≤ m) :
    ∀ {x t z}, ReflTransTraceN r n x t z → ReflTransTraceN r m x t z := by
  induction n generalizing m with
  | zero =>
    intro x t z h
    cases m with
    | zero => exact h
    | succ m => exact .inl h
  | succ n ih =>
    intro x t z h
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rcases h with h | ⟨emitted, y, rest, hstep, hrest, ht⟩
    · exact .inl h
    · exact .inr ⟨emitted, y, rest, hstep, ih (by omega) hrest, ht⟩

/-- A finite traced execution is one within some bound. -/
theorem reflTransTrace_iff_reflTransTraceN {A E : Type} {r : A → List E → A → Prop}
    {x z : A} {t : List E} :
    ReflTransTrace r x t z ↔ ∃ n, ReflTransTraceN r n x t z := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl, rfl⟩
    | step _ emitted y rest _ hstep _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, .inr ⟨emitted, y, rest, hstep, hn, rfl⟩⟩
  · rintro ⟨n, h⟩
    induction n generalizing x t with
    | zero => obtain ⟨rfl, rfl⟩ := h; exact .refl _
    | succ n ih =>
      rcases h with ⟨rfl, rfl⟩ | ⟨emitted, y, rest, hstep, hrest, rfl⟩
      · exact .refl _
      · exact .step _ emitted y rest _ hstep (ih hrest)

end Relation
end
