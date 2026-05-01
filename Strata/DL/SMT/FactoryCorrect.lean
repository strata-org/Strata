/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.SMT.DenotePred
import Strata.DL.SMT.Factory

/-!
# Correctness of Factory optimizations via `DenotePred`

This module proves that the simplifications performed by `Factory` functions
preserve the denotational semantics captured by `DenotePred`.

The core theorems state that if the inputs satisfy `DenotePred`, then the
Factory output also satisfies `DenotePred` with the correct result value.
Derived corollaries relate these to `denoteBoolTermAux` / `denoteIntTermAux`.
-/

open Strata.SMT

/-! ## Helper: extract value from prim derivation -/

private theorem DenotePred.prim_bool_val {b b' : Bool}
    (h : DenotePred (.prim (.bool b)) (.bool b')) : b' = b := by
  cases h; rfl

private theorem DenotePred.prim_bool_eq {b : Bool} {t : Term}
    (heq : t = .prim (.bool b)) (h : DenotePred t (.bool b')) : b' = b := by
  subst heq; exact prim_bool_val h

/-! ## Factory.not correctness -/

/-- `Factory.not` preserves `DenotePred` semantics. -/
theorem Factory.not_correct {t : Term} {b : Bool}
    (h : DenotePred t (.bool b)) :
    DenotePred (Factory.not t) (.bool (!b)) := by
  unfold Factory.not
  -- Case-split on the term structure (matching Factory.not's pattern match)
  split
  · -- Case: .prim (.bool b')
    rename_i b'
    have := DenotePred.prim_bool_val h; subst this
    cases b <;> exact .prim_bool _
  · -- Case: .app .not [t'] _
    rename_i t' ty
    cases h with
    | not h' => simp [Bool.not_not] at *; exact h'
  · -- Default case: t
    exact .not h

/-! ## Factory.and correctness -/

private theorem of_decide {p : Prop} [Decidable p] (h : decide p = true) : p :=
  of_decide_eq_true h

private theorem or_decide_true {p q : Prop} [Decidable p] [Decidable q]
    (h : (decide p || decide q) = true) : p ∨ q := by
  simp [Bool.or_eq_true, decide_eq_true_eq] at h; exact h

/-- If `Factory.opposites t₁ t₂ = true`, then one is the negation of the other. -/
private theorem Factory.opposites_spec {t₁ t₂ : Term}
    (h : Factory.opposites t₁ t₂ = true) :
    (∃ t ty, t₁ = t ∧ t₂ = .app .not [t] ty) ∨
    (∃ t ty, t₁ = .app .not [t] ty ∧ t₂ = t) := by
  unfold Factory.opposites at h
  split at h
  · -- Case: t₂ = .app .not [t₂'] ty and h : decide (t₁ = t₂') = true
    next t₂' ty =>
      left
      refine ⟨t₂', ty, of_decide h, rfl⟩
  · -- Case: t₁ = .app .not [t₁inner] ty and h : decide (t₁inner = t₂) = true
    rename_i t₁inner ty _
    right
    have : t₁inner = t₂ := of_decide h
    refine ⟨t₁inner, ty, rfl, this.symm⟩
  · simp at h

/-- If `t₁` and `t₂` are opposites and both denote booleans, their values are complementary. -/
private theorem Factory.opposites_complement {t₁ t₂ : Term} {b₁ b₂ : Bool}
    (hopp : Factory.opposites t₁ t₂ = true)
    (h₁ : DenotePred t₁ (.bool b₁)) (h₂ : DenotePred t₂ (.bool b₂)) :
    b₁ = !b₂ := by
  rcases Factory.opposites_spec hopp with ⟨t, ty, rfl, rfl⟩ | ⟨t, ty, rfl, rfl⟩
  · -- t₂ = .app .not [t₁] ty
    cases h₂ with | not h₂' =>
    have := DenotePred.deterministic h₁ h₂'
    simp_all
  · -- t₁ = .app .not [t₂] ty
    cases h₁ with | not h₁' =>
    have := DenotePred.deterministic h₁' h₂
    simp_all

private theorem or3_decide_true {p q : Prop} {r : Bool} [Decidable p] [Decidable q]
    (h : (decide p || decide q || r) = true) : p ∨ q ∨ (r = true) := by
  cases hp : decide p
  · cases hq : decide q
    · simp [hp, hq] at h; right; right; exact h
    · simp [decide_eq_true_eq] at hq; right; left; exact hq
  · simp [decide_eq_true_eq] at hp; left; exact hp

/-- `Factory.and` preserves `DenotePred` semantics. -/
theorem Factory.and_correct {t₁ t₂ : Term} {b₁ b₂ : Bool}
    (h₁ : DenotePred t₁ (.bool b₁)) (h₂ : DenotePred t₂ (.bool b₂)) :
    DenotePred (Factory.and t₁ t₂) (.bool (b₁ && b₂)) := by
  unfold Factory.and
  split
  · rename_i hcond
    rcases or_decide_true hcond with heq | heq
    · subst heq
      have := DenotePred.deterministic h₁ h₂
      simp_all
    · subst heq
      cases h₂ with | prim_bool => simp_all
  · split
    · rename_i hcond
      subst hcond
      cases h₁ with | prim_bool => simp_all
    · split
      · rename_i hcond
        have : (decide (t₁ = Term.prim (TermPrim.bool false)) || decide (t₂ = Term.prim (TermPrim.bool false)) || Factory.opposites t₁ t₂) = true := hcond
        rcases or3_decide_true this with h | h | h
        · subst h
          cases h₁ with | prim_bool => simp; exact .prim_bool false
        · subst h
          cases h₂ with | prim_bool => simp; exact .prim_bool false
        · -- opposites case: one is `not` of the other
          have := Factory.opposites_complement h h₁ h₂
          subst this; simp; exact .prim_bool false
      · exact .and h₁ h₂

/-! ## Factory.or correctness -/

/-- `Factory.or` preserves `DenotePred` semantics. -/
theorem Factory.or_correct {t₁ t₂ : Term} {b₁ b₂ : Bool}
    (h₁ : DenotePred t₁ (.bool b₁)) (h₂ : DenotePred t₂ (.bool b₂)) :
    DenotePred (Factory.or t₁ t₂) (.bool (b₁ || b₂)) := by
  unfold Factory.or
  split
  · rename_i hcond
    rcases or_decide_true hcond with heq | heq
    · subst heq
      have := DenotePred.deterministic h₁ h₂
      simp_all
    · subst heq
      cases h₂ with | prim_bool => simp_all
  · split
    · rename_i hcond
      subst hcond
      cases h₁ with | prim_bool => simp_all
    · split
      · rename_i hcond
        have : (decide (t₁ = Term.prim (TermPrim.bool true)) || decide (t₂ = Term.prim (TermPrim.bool true)) || Factory.opposites t₁ t₂) = true := hcond
        rcases or3_decide_true this with h | h | h
        · subst h
          cases h₁ with | prim_bool => simp; exact .prim_bool true
        · subst h
          cases h₂ with | prim_bool => simp; exact .prim_bool true
        · -- opposites case: one is `not` of the other
          have := Factory.opposites_complement h h₁ h₂
          subst this; simp; exact .prim_bool true
      · exact .or h₁ h₂

/-! ## Factory.implies correctness -/

/-- `Factory.implies` preserves `DenotePred` semantics. -/
theorem Factory.implies_correct {t₁ t₂ : Term} {b₁ b₂ : Bool}
    (h₁ : DenotePred t₁ (.bool b₁)) (h₂ : DenotePred t₂ (.bool b₂)) :
    DenotePred (Factory.implies t₁ t₂) (.bool ((!b₁) || b₂)) := by
  unfold Factory.implies
  exact Factory.or_correct (Factory.not_correct h₁) h₂

/-! ## Integer Factory correctness -/

/-- `Factory.intNeg` preserves `DenotePred` semantics. -/
theorem Factory.intNeg_correct {t : Term} {n : Int}
    (h : DenotePred t (.int n)) :
    DenotePred (Factory.intNeg t) (.int (-n)) := by
  unfold Factory.intNeg
  match t, h with
  | .prim (.int i), h =>
    cases h; simp [Int.neg]; exact .prim_int _
  | .var _, h => exact .neg_int h
  | .app _ _ _, h => exact .neg_int h

/-- `Factory.intAdd` preserves `DenotePred` semantics. -/
theorem Factory.intAdd_correct {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : DenotePred t₁ (.int n₁)) (h₂ : DenotePred t₂ (.int n₂)) :
    DenotePred (Factory.intAdd t₁ t₂) (.int (n₁ + n₂)) := by
  unfold Factory.intAdd Factory.intapp
  match t₁, t₂, h₁, h₂ with
  | .prim (.int i₁), .prim (.int i₂), h₁, h₂ =>
    cases h₁; cases h₂; exact .prim_int _
  | .prim (.int _), .var _, h₁, h₂ => exact .add_int h₁ h₂
  | .prim (.int _), .app _ _ _, h₁, h₂ => exact .add_int h₁ h₂
  | .var _, _, h₁, h₂ => exact .add_int h₁ h₂
  | .app _ _ _, _, h₁, h₂ => exact .add_int h₁ h₂

/-- `Factory.intSub` preserves `DenotePred` semantics. -/
theorem Factory.intSub_correct {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : DenotePred t₁ (.int n₁)) (h₂ : DenotePred t₂ (.int n₂)) :
    DenotePred (Factory.intSub t₁ t₂) (.int (n₁ - n₂)) := by
  unfold Factory.intSub Factory.intapp
  match t₁, t₂, h₁, h₂ with
  | .prim (.int i₁), .prim (.int i₂), h₁, h₂ =>
    cases h₁; cases h₂; exact .prim_int _
  | .prim (.int _), .var _, h₁, h₂ => exact .sub_int h₁ h₂
  | .prim (.int _), .app _ _ _, h₁, h₂ => exact .sub_int h₁ h₂
  | .var _, _, h₁, h₂ => exact .sub_int h₁ h₂
  | .app _ _ _, _, h₁, h₂ => exact .sub_int h₁ h₂

/-- `Factory.intMul` preserves `DenotePred` semantics. -/
theorem Factory.intMul_correct {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : DenotePred t₁ (.int n₁)) (h₂ : DenotePred t₂ (.int n₂)) :
    DenotePred (Factory.intMul t₁ t₂) (.int (n₁ * n₂)) := by
  unfold Factory.intMul Factory.intapp
  match t₁, t₂, h₁, h₂ with
  | .prim (.int i₁), .prim (.int i₂), h₁, h₂ =>
    cases h₁; cases h₂; exact .prim_int _
  | .prim (.int _), .var _, h₁, h₂ => exact .mul_int h₁ h₂
  | .prim (.int _), .app _ _ _, h₁, h₂ => exact .mul_int h₁ h₂
  | .var _, _, h₁, h₂ => exact .mul_int h₁ h₂
  | .app _ _ _, _, h₁, h₂ => exact .mul_int h₁ h₂

/-! ## Derived denoteBoolTermAux corollaries -/

/-- `Factory.not` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.not_denote {t : Term} {b : Bool} (h : DenotePred t (.bool b)) :
    ∃ p, denoteBoolTermAux (Factory.not t) = some p ∧ (p ↔ (!b) = true) :=
  DenotePred.sound_bool (Factory.not_correct h)

/-- `Factory.and` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.and_denote {t₁ t₂ : Term} {b₁ b₂ : Bool}
    (h₁ : DenotePred t₁ (.bool b₁)) (h₂ : DenotePred t₂ (.bool b₂)) :
    ∃ p, denoteBoolTermAux (Factory.and t₁ t₂) = some p ∧ (p ↔ (b₁ && b₂) = true) :=
  DenotePred.sound_bool (Factory.and_correct h₁ h₂)

/-- `Factory.or` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.or_denote {t₁ t₂ : Term} {b₁ b₂ : Bool}
    (h₁ : DenotePred t₁ (.bool b₁)) (h₂ : DenotePred t₂ (.bool b₂)) :
    ∃ p, denoteBoolTermAux (Factory.or t₁ t₂) = some p ∧ (p ↔ (b₁ || b₂) = true) :=
  DenotePred.sound_bool (Factory.or_correct h₁ h₂)

/-- `Factory.implies` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.implies_denote {t₁ t₂ : Term} {b₁ b₂ : Bool}
    (h₁ : DenotePred t₁ (.bool b₁)) (h₂ : DenotePred t₂ (.bool b₂)) :
    ∃ p, denoteBoolTermAux (Factory.implies t₁ t₂) = some p ∧ (p ↔ ((!b₁) || b₂) = true) :=
  DenotePred.sound_bool (Factory.implies_correct h₁ h₂)

/-- `Factory.intNeg` preserves `denoteIntTermAux` semantics. -/
theorem Factory.intNeg_denote {t : Term} {n : Int} (h : DenotePred t (.int n)) :
    denoteIntTermAux (Factory.intNeg t) = some (-n) :=
  DenotePred.sound_int (Factory.intNeg_correct h)

/-- `Factory.intAdd` preserves `denoteIntTermAux` semantics. -/
theorem Factory.intAdd_denote {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : DenotePred t₁ (.int n₁)) (h₂ : DenotePred t₂ (.int n₂)) :
    denoteIntTermAux (Factory.intAdd t₁ t₂) = some (n₁ + n₂) :=
  DenotePred.sound_int (Factory.intAdd_correct h₁ h₂)

/-- `Factory.intSub` preserves `denoteIntTermAux` semantics. -/
theorem Factory.intSub_denote {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : DenotePred t₁ (.int n₁)) (h₂ : DenotePred t₂ (.int n₂)) :
    denoteIntTermAux (Factory.intSub t₁ t₂) = some (n₁ - n₂) :=
  DenotePred.sound_int (Factory.intSub_correct h₁ h₂)

/-- `Factory.intMul` preserves `denoteIntTermAux` semantics. -/
theorem Factory.intMul_denote {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : DenotePred t₁ (.int n₁)) (h₂ : DenotePred t₂ (.int n₂)) :
    denoteIntTermAux (Factory.intMul t₁ t₂) = some (n₁ * n₂) :=
  DenotePred.sound_int (Factory.intMul_correct h₁ h₂)
