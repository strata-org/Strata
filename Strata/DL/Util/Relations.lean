/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public section
section Relation

@[expose] def Relation (A: Type) := A → A → Prop
def Reflexive (r: Relation A) : Prop := ∀ x, r x x
abbrev Transitive (r: Relation A) : Prop := ∀ x y z, r x y → r y z → r x z

inductive ReflTrans {A: Type} (r: Relation A) : Relation A where
  | refl : ∀ x, ReflTrans r x x
  | step: ∀ x y z, r x y → ReflTrans r y z → ReflTrans r x z

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

/-! ## Type-valued reflexive transitive closure

`ReflTrans` lives in `Prop`, so Lean's large-elimination restriction forbids
pattern-matching on it to produce data (e.g. a `Nat` step count).
`ReflTransT` is the identical definition but in `Type`, which allows:

* **Structural recursion on derivations** — useful when a proof needs
  well-founded recursion keyed on the *length* of a multi-step execution
  (e.g. loop-simulation arguments where each iteration strictly shrinks the
  remaining trace).
* **Step counting** via `ReflTransT.len` — enables `termination_by` /
  `decreasing_by` on the derivation length.

Convert between the two with `reflTrans_nonempty_T` (Prop → Nonempty Type)
and `reflTransT_to_prop` (Type → Prop).  The Prop-to-Type direction requires
`Classical.choice` (`reflTrans_to_T`), so definitions that use it are
`noncomputable`; this is harmless when the final result is again a `Prop`. -/

inductive ReflTransT {A : Type} (r : A → A → Prop) : A → A → Type where
  | refl : ∀ x, ReflTransT r x x
  | step : ∀ x y z, r x y → ReflTransT r y z → ReflTransT r x z

theorem reflTrans_nonempty_T {A : Type} {r : A → A → Prop} {a b : A} :
    ReflTrans r a b → Nonempty (ReflTransT r a b) := by
  intro h; induction h with
  | refl => exact ⟨.refl _⟩
  | step _ _ _ hstep _ ih => exact ih.elim fun rest => ⟨.step _ _ _ hstep rest⟩

noncomputable def reflTrans_to_T {A : Type} {r : A → A → Prop} {a b : A} :
    ReflTrans r a b → ReflTransT r a b :=
  fun h => Classical.choice (reflTrans_nonempty_T h)

theorem reflTransT_to_prop {A : Type} {r : A → A → Prop} {a b : A} :
    ReflTransT r a b → ReflTrans r a b := by
  intro h; induction h with
  | refl => exact .refl _
  | step _ _ _ hstep _ ih => exact .step _ _ _ hstep ih

@[simp] def ReflTransT.len : @ReflTransT A r a b → Nat
  | .refl _ => 0
  | .step _ _ _ _ rest => 1 + rest.len

end Relation
end
