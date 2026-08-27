/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public section
section Relation


@[expose] def Relation (A: Type) := A → A → Prop

@[expose] def Reflexive (r: Relation A) : Prop := ∀ x, r x x
abbrev Transitive (r: Relation A) : Prop := ∀ x y z, r x y → r y z → r x z


/-- Composition of two relations: `RComp R₁ R₂ a c` holds when some intermediate
    `b` has `R₁ a b` and `R₂ b c`.  Read left-to-right: "first `R₁`, then `R₂`".

    The scoped notation `R₁ ∘ R₂` is available via `open scoped Relations`. -/
@[expose] def RComp {A : Type} (R₁ R₂ : Relation A) : Relation A :=
  fun a c => ∃ b, R₁ a b ∧ R₂ b c


namespace Relations
/- Scoped infix `∘` for relation composition (`RComp`).  Enable with
   `open scoped Relations`.  Distinct from `Function.comp`'s `∘` by being
   scoped, so it does not globally shadow function composition. -/
scoped infixr:90 " ∘ " => RComp

end Relations

/-- `r` is *dense* when every related pair has an interpolating midpoint:
    `r a c` splits into `r a b` and `r b c`.  This is exactly `r ⊆ RComp r r`,
    the dual of `RComp.collapse`'s `RComp r r ⊆ r` (transitivity): density lets a
    single relatedness fact be re-expressed as the two-step form that a composed
    relation consumes. -/


inductive ReflTrans {A: Type} (r: Relation A) : Relation A where
  | refl : ∀ x, ReflTrans r x x
  | step: ∀ x y z, r x y → ReflTrans r y z → ReflTrans r x z


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


@[simp] def ReflTransT.len : @ReflTransT A r a b → Nat
  | .refl _ => 0
  | .step _ _ _ _ rest => 1 + rest.len


end Relation
end
