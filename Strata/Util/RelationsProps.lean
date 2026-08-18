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
* `Reflexive.dense` — every reflexive relation is dense
* `ReflTrans_Reflexive`, `ReflTrans_Transitive` — `ReflTrans` is reflexive and transitive
* `reflTransT_to_prop` — the `Type`-valued closure implies the `Prop`-valued one
-/

public section
section Relation
namespace Relations
end Relations

/-- `RComp R₁ R₂` reduces to `R` when `R` is transitive and `R₁, R₂ ⊆ R`. -/
theorem RComp.collapse {A : Type} {R₁ R₂ R : Relation A} {a c : A}
    (htrans : Transitive R)
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

@[expose] def Dense (r : Relation A) : Prop := ∀ a c, r a c → ∃ b, r a b ∧ r b c

/-- Any reflexive relation is dense: split `r a c` at the endpoint `a` using
    `r a a`.  In particular equality is dense, which is why the shared-start
    (`· = ·`) composition combinators need no separate density hypothesis. -/
theorem Reflexive.dense {A : Type} {r : Relation A} (h : Reflexive r) : Dense r :=
  fun a _c hac => ⟨a, h a, hac⟩


theorem ReflTrans_Reflexive {A: Type} (r: Relation A):
  Reflexive (ReflTrans r) := by apply ReflTrans.refl


theorem ReflTrans_Transitive {A: Type} (r: Relation A):
  Transitive (ReflTrans r) := by
  unfold Transitive; intros x y z rxy
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

end Relation
end
