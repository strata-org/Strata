/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.Denote
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

/-! ## DenotePred determinism -/

/-- `DenotePred` is deterministic: a term has at most one denotation. -/
theorem DenotePred.deterministic {t : Term} {v₁ v₂ : TermPrim}
    (h₁ : DenotePred t v₁) (h₂ : DenotePred t v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | prim_bool b => cases h₂; rfl
  | prim_int n => cases h₂; rfl
  | prim_bitvec x => cases h₂; rfl
  | prim_string s => cases h₂; rfl
  | ite_true _ _ _ _ ihc iha _ =>
    cases h₂ with
    | ite_true _ ha' _ _ => exact iha ha'
    | ite_false hc' _ _ _ => exact absurd (ihc hc') (by simp)
  | ite_false _ _ _ _ ihc _ ihb =>
    cases h₂ with
    | ite_true hc' _ _ _ => exact absurd (ihc hc') (by simp)
    | ite_false _ _ hb' _ => exact ihb hb'
  -- All remaining constructors: unique matching, close with injection + subst
  | not _ ih => cases h₂ with | not h' => have := ih h'; simp_all
  | and _ _ iha ihb => cases h₂ with | and ha' hb' => have := iha ha'; have := ihb hb'; simp_all
  | or _ _ iha ihb => cases h₂ with | or ha' hb' => have := iha ha'; have := ihb hb'; simp_all
  | implies _ _ iha ihb => cases h₂ with | implies ha' hb' => have := iha ha'; have := ihb hb'; simp_all
  | eq _ _ _ iha ihb => cases h₂ with | eq ha' hb' _ => have := iha ha'; have := ihb hb'; simp_all
  | neg_int _ ih => cases h₂ with | neg_int h' => have := ih h'; simp_all
  | add_int _ _ iha ihb => cases h₂ with | add_int ha' hb' => have := iha ha'; have := ihb hb'; simp_all
  | sub_int _ _ iha ihb => cases h₂ with | sub_int ha' hb' => have := iha ha'; have := ihb hb'; simp_all
  | mul_int _ _ iha ihb => cases h₂ with | mul_int ha' hb' => have := iha ha'; have := ihb hb'; simp_all
  | div_int _ _ iha ihb => cases h₂ with | div_int ha' hb' => have := iha ha'; have := ihb hb'; simp_all
  | mod_int _ _ iha ihb => cases h₂ with | mod_int ha' hb' => have := iha ha'; have := ihb hb'; simp_all
  | abs_int _ ih => cases h₂ with | abs_int h' => have := ih h'; simp_all
  | le_int _ _ iha ihb => cases h₂ with | le_int ha' hb' => have := iha ha'; have := ihb hb'; simp_all
  | lt_int _ _ iha ihb => cases h₂ with | lt_int ha' hb' => have := iha ha'; have := ihb hb'; simp_all
  | ge_int _ _ iha ihb => cases h₂ with | ge_int ha' hb' => have := iha ha'; have := ihb hb'; simp_all
  | gt_int _ _ iha ihb => cases h₂ with | gt_int ha' hb' => have := iha ha'; have := ihb hb'; simp_all
  | bvneg _ ih => cases h₂ with | bvneg h' => have h := ih h'; cases h; rfl
  | bvadd _ _ iha ihb => cases h₂ with | bvadd ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvsub _ _ iha ihb => cases h₂ with | bvsub ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvmul _ _ iha ihb => cases h₂ with | bvmul ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvnot _ ih => cases h₂ with | bvnot h' => have h := ih h'; cases h; rfl
  | bvand _ _ iha ihb => cases h₂ with | bvand ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvor _ _ iha ihb => cases h₂ with | bvor ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvxor _ _ iha ihb => cases h₂ with | bvxor ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvshl _ _ iha ihb => cases h₂ with | bvshl ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvlshr _ _ iha ihb => cases h₂ with | bvlshr ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvashr _ _ iha ihb => cases h₂ with | bvashr ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvslt _ _ iha ihb => cases h₂ with | bvslt ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvsle _ _ iha ihb => cases h₂ with | bvsle ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvult _ _ iha ihb => cases h₂ with | bvult ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvule _ _ iha ihb => cases h₂ with | bvule ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvsgt _ _ iha ihb => cases h₂ with | bvsgt ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvsge _ _ iha ihb => cases h₂ with | bvsge ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvugt _ _ iha ihb => cases h₂ with | bvugt ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvuge _ _ iha ihb => cases h₂ with | bvuge ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvudiv _ _ iha ihb => cases h₂ with | bvudiv ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvurem _ _ iha ihb => cases h₂ with | bvurem ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvsdiv _ _ iha ihb => cases h₂ with | bvsdiv ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvsrem _ _ iha ihb => cases h₂ with | bvsrem ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvnego _ ih => cases h₂ with | bvnego h' => have h := ih h'; cases h; rfl
  | bvsaddo _ _ iha ihb => cases h₂ with | bvsaddo ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvssubo _ _ iha ihb => cases h₂ with | bvssubo ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvsmulo _ _ iha ihb => cases h₂ with | bvsmulo ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | bvconcat _ _ iha ihb => cases h₂ with | bvconcat ha' hb' => have h1 := iha ha'; have h2 := ihb hb'; cases h1; cases h2; rfl
  | zero_extend i ha iha => cases h₂ with | zero_extend i' ha' => have := iha ha'; cases this; rfl
  | str_length _ ih => cases h₂ with | str_length h' => have := ih h'; simp_all
  | str_concat _ _ iha ihb => cases h₂ with | str_concat ha' hb' => have := iha ha'; have := ihb hb'; simp_all

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
