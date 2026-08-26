/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.Denote
import all Strata.DL.SMT.Denote
import all Strata.DL.SMT.Factory
import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Correctness of Factory optimizations

This module proves that the simplifications performed by `Factory` functions
preserve the denotational semantics directly in terms of the functional
denotation (`denoteBoolTermAux`, `denoteIntTermAux`).

These proofs rely on propositional extensionality (`propext`) and classical
excluded middle (`Classical.em`, `Classical.not_not`), since `denoteTerm` maps
booleans to `Prop` and the Factory rewrites produce logically equivalent but
not definitionally equal propositions.
-/

open Strata.SMT

/-! ## Infrastructure -/

/-- The unique `TermDenoteInput` for the empty context. -/
private abbrev tdi₀ : TermDenoteInput ({} : Context) :=
  ⟨[], ⟨rfl, fun _ hi => nomatch hi⟩, ⟨[], []⟩,
   ⟨⟨rfl, fun _ hi => nomatch hi⟩, ⟨rfl, fun _ hi => nomatch hi⟩⟩⟩

/-- Extract denoteTerm witness from denoteBoolTermAux. -/
private theorem denoteBoolTermAux_extract {t : Term} {p : Prop}
    (h : denoteBoolTermAux t = some p) :
    ∃ f : TermDenoteInput ({} : Context) → Prop,
      denoteTerm ({} : Context) t = some ⟨.prim .bool, rfl, f⟩ ∧ (f tdi₀ ↔ p) := by
  simp only [denoteBoolTermAux] at h
  split at h
  · rename_i _ _ fi _
    exact ⟨fi, by grind, by grind⟩
  · grind

/-- Extract denoteTerm witness from denoteIntTermAux. -/
private theorem denoteIntTermAux_extract {t : Term} {n : Int}
    (h : denoteIntTermAux t = some n) :
    ∃ f : TermDenoteInput ({} : Context) → Int,
      denoteTerm ({} : Context) t = some ⟨.prim .int, rfl, f⟩ ∧ f tdi₀ = n := by
  simp only [denoteIntTermAux] at h
  split at h
  · rename_i _ _ fi _
    exact ⟨fi, by grind, by grind⟩
  · grind

/-- Extract denoteTerm witness from denoteBVTermAux. -/
private theorem denoteBVTermAux_extract {n : Nat} {t : Term} {b : BitVec n}
    (h : denoteBVTermAux n t = some b) :
    ∃ f : TermDenoteInput ({} : Context) → BitVec n,
      denoteTerm ({} : Context) t = some ⟨.prim (.bitvec n), rfl, f⟩ ∧ f tdi₀ = b := by
  simp only [denoteBVTermAux] at h
  split at h
  · rename_i m _ _ fi _
    split at h
    · rename_i hmn
      subst hmn
      exact ⟨fi, by grind, by grind⟩
    · grind
  · grind

/-- Extract denoteTerm witness from denoteStringTermAux. -/
private theorem denoteStringTermAux_extract {t : Term} {s : String}
    (h : denoteStringTermAux t = some s) :
    ∃ f : TermDenoteInput ({} : Context) → String,
      denoteTerm ({} : Context) t = some ⟨.prim .string, rfl, f⟩ ∧ f tdi₀ = s := by
  simp only [denoteStringTermAux] at h
  split at h
  · rename_i _ _ fi _
    exact ⟨fi, by grind, by grind⟩
  · grind

/-! ## Lemma: denoteBoolTermAux for .app .not -/

/-- Invert `denoteBoolTermAux` of a negation: the inner term denotes `¬p`. -/
private theorem denoteBoolTermAux_not_inv {t' : Term} {ty : TermType} {p : Prop}
    (h : denoteBoolTermAux (.app .not [t'] ty) = some p) :
    denoteBoolTermAux t' = some (¬ p) := by
  unfold denoteBoolTermAux at h ⊢
  conv at h => simp only [denoteTerm]
  revert h
  generalize denoteTerm {} t' = res'
  intro h
  match res' with
  | some ⟨.prim .bool, rfl, g⟩ => simp_all; grind
  | some ⟨.prim .int, _, _⟩ | some ⟨.prim .string, _, _⟩
  | some ⟨.prim (.bitvec _), _, _⟩ | some ⟨.prim .real, _, _⟩
  | some ⟨.prim .regex, _, _⟩
  | some ⟨.option _, _, _⟩ | some ⟨.constr _ _, _, _⟩
  | none => grind

/-! ## Helper lemmas -/

private theorem of_decide {p : Prop} [Decidable p] (h : decide p = true) : p :=
  of_decide_eq_true h

private theorem or_decide_true {p q : Prop} [Decidable p] [Decidable q]
    (h : (decide p || decide q) = true) : p ∨ q := by grind

private theorem or3_decide_true {p q : Prop} {r : Bool} [Decidable p] [Decidable q]
    (h : (decide p || decide q || r) = true) : p ∨ q ∨ (r = true) := by grind

/-- If two `denoteBoolTermAux` calls agree, their propositions are equal. -/
private theorem denoteBoolTermAux_eq {t : Term} {p₁ p₂ : Prop}
    (h₁ : denoteBoolTermAux t = some p₁) (h₂ : denoteBoolTermAux t = some p₂) :
    p₁ = p₂ := by grind

/-- `denoteBoolTermAux` of a boolean literal denotes `b = true`. -/
private theorem denoteBool_prim_bool (b : Bool) :
    denoteBoolTermAux (.prim (.bool b)) = some (b = true) := by
  cases b <;> simp [denoteBoolTermAux, denoteTerm]

/-- If `denoteBoolTermAux t = some p` and `t.isLiteral`, there exists `b` such
    that `t = .prim (.bool b)` and `p ↔ b = true`. -/
private theorem denoteBoolTermAux_literal_form {t : Term} {p : Prop}
    (h : denoteBoolTermAux t = some p) (hlit : t.isLiteral = true) :
    ∃ b : Bool, t = .prim (.bool b) ∧ (p ↔ b = true) := by
  match t with
  | .prim (.bool b) =>
    refine ⟨b, rfl, ?_⟩
    cases b <;> simp [denoteBoolTermAux, denoteTerm] at h <;> simp [h]
  | .prim (.int _) | .prim (.real _) | .prim (.bitvec _) | .prim (.string _) =>
    simp [denoteBoolTermAux, denoteTerm] at h
  | .none _ => simp [denoteBoolTermAux, denoteTerm] at h
  | .some t' =>
    exfalso
    simp [denoteBoolTermAux, denoteTerm] at h
    rcases hd : denoteTerm {} t' with _ | ⟨ty', _, _⟩ <;> rw [hd] at h <;> simp at h
  | .var _ | .app _ _ _ | .quant _ _ _ _ => simp [Term.isLiteral] at hlit

/-- If `denoteIntTermAux t = some n` and `t.isLiteral`, then `t = .prim (.int n)`. -/
private theorem denoteIntTermAux_literal_form {t : Term} {n : Int}
    (h : denoteIntTermAux t = some n) (hlit : t.isLiteral = true) :
    t = .prim (.int n) := by
  match t with
  | .prim (.int i) =>
    simp [denoteIntTermAux, denoteTerm] at h
    rw [h]
  | .prim (.bool b) =>
    exfalso
    cases b <;> simp [denoteIntTermAux, denoteTerm] at h
  | .prim (.real _) | .prim (.bitvec _) | .prim (.string _) =>
    simp [denoteIntTermAux, denoteTerm] at h
  | .none _ => simp [denoteIntTermAux, denoteTerm] at h
  | .some t' =>
    exfalso
    simp [denoteIntTermAux, denoteTerm] at h
    rcases hd : denoteTerm {} t' with _ | ⟨ty', _, _⟩ <;> rw [hd] at h <;> simp at h
  | .var _ | .app _ _ _ | .quant _ _ _ _ => simp [Term.isLiteral] at hlit

/-- If `denoteBVTermAux n t = some b` and `t.isLiteral`, then `t = .prim (.bitvec b)`. -/
private theorem denoteBVTermAux_literal_form {n : Nat} {t : Term} {b : BitVec n}
    (h : denoteBVTermAux n t = some b) (hlit : t.isLiteral = true) :
    t = .prim (.bitvec b) := by
  match t with
  | .prim (@TermPrim.bitvec m b') =>
    simp [denoteBVTermAux, denoteTerm] at h
    obtain ⟨hmn, hb⟩ := h; subst hmn; subst hb; rfl
  | .prim (.bool bb) =>
    exfalso
    cases bb <;> simp [denoteBVTermAux, denoteTerm] at h
  | .prim (.int _) | .prim (.real _) | .prim (.string _) =>
    simp [denoteBVTermAux, denoteTerm] at h
  | .none _ => simp [denoteBVTermAux, denoteTerm] at h
  | .some t' =>
    exfalso
    simp [denoteBVTermAux, denoteTerm] at h
    rcases hd : denoteTerm {} t' with _ | ⟨ty', _, _⟩ <;> rw [hd] at h <;> simp at h
  | .var _ | .app _ _ _ | .quant _ _ _ _ => simp [Term.isLiteral] at hlit

/-- If `denoteStringTermAux t = some s` and `t.isLiteral`, then `t = .prim (.string s)`. -/
private theorem denoteStringTermAux_literal_form {t : Term} {s : String}
    (h : denoteStringTermAux t = some s) (hlit : t.isLiteral = true) :
    t = .prim (.string s) := by
  match t with
  | .prim (.string s') =>
    simp [denoteStringTermAux, denoteTerm] at h
    rw [h]
  | .prim (.bool b) =>
    exfalso
    cases b <;> simp [denoteStringTermAux, denoteTerm] at h
  | .prim (.int _) | .prim (.real _) | .prim (.bitvec _) =>
    simp [denoteStringTermAux, denoteTerm] at h
  | .none _ => simp [denoteStringTermAux, denoteTerm] at h
  | .some t' =>
    exfalso
    simp [denoteStringTermAux, denoteTerm] at h
    rcases hd : denoteTerm {} t' with _ | ⟨ty', _, _⟩ <;> rw [hd] at h <;> simp at h
  | .var _ | .app _ _ _ | .quant _ _ _ _ => simp [Term.isLiteral] at hlit

/-! ## Factory.not correctness -/

/-- `Factory.not` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.not_correct {t : Term} {p : Prop}
    (h : denoteBoolTermAux t = some p) :
    denoteBoolTermAux (Factory.not t) = some (¬p) := by
  unfold Factory.not
  split
  · rename_i b
    have hp := denoteBoolTermAux_eq h (denoteBool_prim_bool b)
    cases b <;> simp [denoteBoolTermAux, denoteTerm, hp]
  · exact denoteBoolTermAux_not_inv h
  · obtain ⟨f, hdt, hiff⟩ := denoteBoolTermAux_extract h
    simp [denoteBoolTermAux, denoteTerm, hdt]
    rw [propext hiff]

/-! ## Factory.opposites spec -/

private theorem Factory.opposites_spec {t₁ t₂ : Term}
    (h : Factory.opposites t₁ t₂ = true) :
    (∃ t ty, t₁ = t ∧ t₂ = .app .not [t] ty) ∨
    (∃ t ty, t₁ = .app .not [t] ty ∧ t₂ = t) := by
  unfold Factory.opposites at h
  split at h
  · next t₂' ty => exact Or.inl ⟨t₂', ty, of_decide h, rfl⟩
  · next t₁inner ty _ => exact Or.inr ⟨t₁inner, ty, rfl, (of_decide h).symm⟩
  · grind

/-! ## Factory.and correctness -/

/-- `Factory.and` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.and_correct {t₁ t₂ : Term} {p₁ p₂ : Prop}
    (h₁ : denoteBoolTermAux t₁ = some p₁) (h₂ : denoteBoolTermAux t₂ = some p₂) :
    denoteBoolTermAux (Factory.and t₁ t₂) = some (p₁ ∧ p₂) := by
  unfold Factory.and
  split
  · rename_i hcond
    rcases or_decide_true hcond with heq | heq
    · subst heq; cases denoteBoolTermAux_eq h₁ h₂
      rw [h₁]; simp
    · subst heq
      have hp₂ := denoteBoolTermAux_eq h₂ (denoteBool_prim_bool true)
      rw [h₁, hp₂]; simp
  · split
    · rename_i hcond; subst hcond
      have hp₁ := denoteBoolTermAux_eq h₁ (denoteBool_prim_bool true)
      rw [h₂, hp₁]; simp
    · split
      · rename_i hcond
        rcases or3_decide_true hcond with hf | hf | hf
        · subst hf
          have hp₁ := denoteBoolTermAux_eq h₁ (denoteBool_prim_bool false)
          rw [hp₁]; simp [denoteBoolTermAux, denoteTerm]
        · subst hf
          have hp₂ := denoteBoolTermAux_eq h₂ (denoteBool_prim_bool false)
          rw [hp₂]; simp [denoteBoolTermAux, denoteTerm]
        · rcases Factory.opposites_spec hf with ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
          · have hq := denoteBoolTermAux_not_inv h₂
            have hpq := denoteBoolTermAux_eq hq h₁
            rw [← hpq]; simp [denoteBoolTermAux, denoteTerm]
          · have hq := denoteBoolTermAux_not_inv h₁
            have hpq := denoteBoolTermAux_eq hq h₂
            rw [← hpq]; simp [denoteBoolTermAux, denoteTerm]
      · obtain ⟨f₁, hdt₁, hiff₁⟩ := denoteBoolTermAux_extract h₁
        obtain ⟨f₂, hdt₂, hiff₂⟩ := denoteBoolTermAux_extract h₂
        simp [denoteBoolTermAux, denoteTerm, denoteTerms, leftAssoc, leftAssoc.go, hdt₁, hdt₂]
        rw [propext hiff₁, propext hiff₂]

/-! ## Factory.or correctness -/

/-- `Factory.or` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.or_correct {t₁ t₂ : Term} {p₁ p₂ : Prop}
    (h₁ : denoteBoolTermAux t₁ = some p₁) (h₂ : denoteBoolTermAux t₂ = some p₂) :
    denoteBoolTermAux (Factory.or t₁ t₂) = some (p₁ ∨ p₂) := by
  unfold Factory.or
  split
  · rename_i hcond
    rcases or_decide_true hcond with heq | heq
    · subst heq; cases denoteBoolTermAux_eq h₁ h₂
      rw [h₁]; simp
    · subst heq
      have hp₂ := denoteBoolTermAux_eq h₂ (denoteBool_prim_bool false)
      rw [h₁, hp₂]; simp
  · split
    · rename_i hcond; subst hcond
      have hp₁ := denoteBoolTermAux_eq h₁ (denoteBool_prim_bool false)
      rw [h₂, hp₁]; simp
    · split
      · rename_i hcond
        rcases or3_decide_true hcond with ht | ht | ht
        · subst ht
          have hp₁ := denoteBoolTermAux_eq h₁ (denoteBool_prim_bool true)
          rw [hp₁]; simp [denoteBoolTermAux, denoteTerm]
        · subst ht
          have hp₂ := denoteBoolTermAux_eq h₂ (denoteBool_prim_bool true)
          rw [hp₂]; simp [denoteBoolTermAux, denoteTerm]
        · rcases Factory.opposites_spec ht with ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
          · have hq := denoteBoolTermAux_not_inv h₂
            have hpq := denoteBoolTermAux_eq hq h₁
            rw [← hpq]
            simp [denoteBoolTermAux, denoteTerm]
            cases Classical.em p₂ with
            | inl h => exact Or.inr h
            | inr h => exact Or.inl h
          · have hq := denoteBoolTermAux_not_inv h₁
            have hpq := denoteBoolTermAux_eq hq h₂
            rw [← hpq]
            simp [denoteBoolTermAux, denoteTerm]
            cases Classical.em p₁ with
            | inl h => exact Or.inl h
            | inr h => exact Or.inr h
      · obtain ⟨f₁, hdt₁, hiff₁⟩ := denoteBoolTermAux_extract h₁
        obtain ⟨f₂, hdt₂, hiff₂⟩ := denoteBoolTermAux_extract h₂
        simp [denoteBoolTermAux, denoteTerm, denoteTerms, leftAssoc, leftAssoc.go, hdt₁, hdt₂]
        rw [propext hiff₁, propext hiff₂]

/-! ## Factory.implies correctness -/

/-- `Factory.implies` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.implies_correct {t₁ t₂ : Term} {p₁ p₂ : Prop}
    (h₁ : denoteBoolTermAux t₁ = some p₁) (h₂ : denoteBoolTermAux t₂ = some p₂) :
    denoteBoolTermAux (Factory.implies t₁ t₂) = some (p₁ → p₂) := by
  unfold Factory.implies
  have hnot := Factory.not_correct h₁
  have hor := Factory.or_correct hnot h₂
  rw [hor]
  congr 1
  apply propext
  constructor
  · intro h hp₁; cases h with
    | inl hnp₁ => contradiction
    | inr hp₂ => exact hp₂
  · intro h; by_cases hp₁ : p₁
    · exact Or.inr (h hp₁)
    · exact Or.inl hp₁

/-! ## Integer Factory correctness -/

/-- `Factory.intNeg` preserves `denoteIntTermAux` semantics. -/
theorem Factory.intNeg_correct {t : Term} {n : Int}
    (h : denoteIntTermAux t = some n) :
    denoteIntTermAux (Factory.intNeg t) = some (-n) := by
  obtain ⟨f, hdt, rfl⟩ := denoteIntTermAux_extract h
  unfold Factory.intNeg
  split
  · simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               heq_eq_eq, true_and] at hdt; subst hdt
    simp only [denoteIntTermAux, denoteTerm, Int.neg, Nat.succ_eq_add_one, Int.natCast_add,
               Int.cast_ofNat_Int, Option.pure_def, Option.some.injEq]; rfl
  · simp [denoteIntTermAux, denoteTerm, hdt]

/-- `Factory.intAdd` preserves `denoteIntTermAux` semantics. -/
theorem Factory.intAdd_correct {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : denoteIntTermAux t₁ = some n₁) (h₂ : denoteIntTermAux t₂ = some n₂) :
    denoteIntTermAux (Factory.intAdd t₁ t₂) = some (n₁ + n₂) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteIntTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteIntTermAux_extract h₂
  unfold Factory.intAdd Factory.intapp
  split
  · simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               heq_eq_eq, true_and] at hdt₁ hdt₂; subst hdt₁; subst hdt₂
    simp [denoteIntTermAux, denoteTerm]
  · simp [denoteIntTermAux, denoteTerm, denoteTerms, leftAssoc, leftAssoc.go, hdt₁, hdt₂]

/-- `Factory.intSub` preserves `denoteIntTermAux` semantics. -/
theorem Factory.intSub_correct {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : denoteIntTermAux t₁ = some n₁) (h₂ : denoteIntTermAux t₂ = some n₂) :
    denoteIntTermAux (Factory.intSub t₁ t₂) = some (n₁ - n₂) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteIntTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteIntTermAux_extract h₂
  unfold Factory.intSub Factory.intapp
  split
  · simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               heq_eq_eq, true_and] at hdt₁ hdt₂; subst hdt₁; subst hdt₂
    simp only [denoteIntTermAux, denoteTerm, Option.pure_def, Option.some.injEq]; rfl
  · simp [denoteIntTermAux, denoteTerm, denoteTerms, leftAssoc, leftAssoc.go, hdt₁, hdt₂]

/-- `Factory.intMul` preserves `denoteIntTermAux` semantics. -/
theorem Factory.intMul_correct {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : denoteIntTermAux t₁ = some n₁) (h₂ : denoteIntTermAux t₂ = some n₂) :
    denoteIntTermAux (Factory.intMul t₁ t₂) = some (n₁ * n₂) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteIntTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteIntTermAux_extract h₂
  unfold Factory.intMul Factory.intapp
  split
  · simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               heq_eq_eq, true_and] at hdt₁ hdt₂; subst hdt₁; subst hdt₂
    simp [denoteIntTermAux, denoteTerm]
  · simp [denoteIntTermAux, denoteTerm, denoteTerms, leftAssoc, leftAssoc.go, hdt₁, hdt₂]

/-- `Factory.intAbs` preserves `denoteIntTermAux` semantics. -/
theorem Factory.intAbs_correct {t : Term} {n : Int}
    (h : denoteIntTermAux t = some n) :
    denoteIntTermAux (Factory.intAbs t) = some (if n < 0 then -n else n) := by
  obtain ⟨f, hdt, rfl⟩ := denoteIntTermAux_extract h
  unfold Factory.intAbs
  split
  · next i =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               heq_eq_eq, true_and] at hdt
    subst hdt
    by_cases hlt : i < 0 <;>
      grind [denoteIntTermAux, denoteTerm, Option.pure_def, Int.natAbs_of_nonneg, Int.natAbs_neg]
  · simp only [denoteIntTermAux, denoteTerm, hdt, Option.pure_def, Option.bind_eq_bind,
               Option.bind_some, Option.some.injEq]
    split <;> rfl

/-- `Factory.intDiv` preserves `denoteIntTermAux` semantics. -/
theorem Factory.intDiv_correct {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : denoteIntTermAux t₁ = some n₁) (h₂ : denoteIntTermAux t₂ = some n₂) :
    denoteIntTermAux (Factory.intDiv t₁ t₂) = some (n₁ / n₂) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteIntTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteIntTermAux_extract h₂
  unfold Factory.intDiv Factory.intapp
  split
  · simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               heq_eq_eq, true_and] at hdt₁ hdt₂; subst hdt₁; subst hdt₂
    simp only [denoteIntTermAux, denoteTerm, Option.pure_def, Option.some.injEq]; rfl
  · simp [denoteIntTermAux, denoteTerm, denoteTerms, leftAssoc, leftAssoc.go, hdt₁, hdt₂]

/-- `Factory.intMod` preserves `denoteIntTermAux` semantics. -/
theorem Factory.intMod_correct {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : denoteIntTermAux t₁ = some n₁) (h₂ : denoteIntTermAux t₂ = some n₂) :
    denoteIntTermAux (Factory.intMod t₁ t₂) = some (n₁ % n₂) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteIntTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteIntTermAux_extract h₂
  unfold Factory.intMod Factory.intapp
  split
  · simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               heq_eq_eq, true_and] at hdt₁ hdt₂; subst hdt₁; subst hdt₂
    simp only [denoteIntTermAux, denoteTerm, Option.pure_def, Option.some.injEq]; rfl
  · simp [denoteIntTermAux, denoteTerm, hdt₁, hdt₂]

/-! ## Integer comparison correctness -/

/-- `Factory.intLe` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.intLe_correct {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : denoteIntTermAux t₁ = some n₁) (h₂ : denoteIntTermAux t₂ = some n₂) :
    denoteBoolTermAux (Factory.intLe t₁ t₂) = some (n₁ ≤ n₂) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteIntTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteIntTermAux_extract h₂
  unfold Factory.intLe Factory.intcmp
  split
  · next i₁ i₂ =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               heq_eq_eq, true_and] at hdt₁ hdt₂; subst hdt₁; subst hdt₂
    rw [denoteBool_prim_bool]; simp
  · simp [denoteBoolTermAux, denoteTerm, denoteTerms, chainable, chainable.go, hdt₁, hdt₂]

/-- `Factory.intLt` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.intLt_correct {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : denoteIntTermAux t₁ = some n₁) (h₂ : denoteIntTermAux t₂ = some n₂) :
    denoteBoolTermAux (Factory.intLt t₁ t₂) = some (n₁ < n₂) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteIntTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteIntTermAux_extract h₂
  unfold Factory.intLt Factory.intcmp
  split
  · next i₁ i₂ =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               heq_eq_eq, true_and] at hdt₁ hdt₂; subst hdt₁; subst hdt₂
    rw [denoteBool_prim_bool]; simp
  · simp [denoteBoolTermAux, denoteTerm, denoteTerms, chainable, chainable.go, hdt₁, hdt₂]

/-- `Factory.intGe` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.intGe_correct {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : denoteIntTermAux t₁ = some n₁) (h₂ : denoteIntTermAux t₂ = some n₂) :
    denoteBoolTermAux (Factory.intGe t₁ t₂) = some (n₁ ≥ n₂) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteIntTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteIntTermAux_extract h₂
  unfold Factory.intGe Factory.intcmp
  split
  · next i₁ i₂ =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               heq_eq_eq, true_and] at hdt₁ hdt₂; subst hdt₁; subst hdt₂
    rw [denoteBool_prim_bool]; simp
  · simp [denoteBoolTermAux, denoteTerm, denoteTerms, chainable, chainable.go, hdt₁, hdt₂]

/-- `Factory.intGt` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.intGt_correct {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : denoteIntTermAux t₁ = some n₁) (h₂ : denoteIntTermAux t₂ = some n₂) :
    denoteBoolTermAux (Factory.intGt t₁ t₂) = some (n₁ > n₂) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteIntTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteIntTermAux_extract h₂
  unfold Factory.intGt Factory.intcmp
  split
  · next i₁ i₂ =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               heq_eq_eq, true_and] at hdt₁ hdt₂; subst hdt₁; subst hdt₂
    rw [denoteBool_prim_bool]; simp
  · simp [denoteBoolTermAux, denoteTerm, denoteTerms, chainable, chainable.go, hdt₁, hdt₂]

/-! ## Bitvector Factory correctness -/

/-- `Factory.bvneg` preserves `denoteBVTermAux` semantics. -/
theorem Factory.bvneg_correct {n : Nat} {t : Term} {x : BitVec n}
    (h : denoteBVTermAux n t = some x) :
    denoteBVTermAux n (Factory.bvneg t) = some (-x) := by
  obtain ⟨f, hdt, rfl⟩ := denoteBVTermAux_extract h
  unfold Factory.bvneg
  split
  · next m b =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               TermType.prim.injEq, TermPrimType.bitvec.injEq] at hdt
    obtain ⟨hmn, hf⟩ := hdt
    subst hmn; subst hf
    simp [denoteBVTermAux, denoteTerm]
  · simp [denoteBVTermAux, denoteTerm, hdt]

/-- `Factory.bvadd` preserves `denoteBVTermAux` semantics. -/
theorem Factory.bvadd_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    denoteBVTermAux n (Factory.bvadd t₁ t₂) = some (x + y) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteBVTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteBVTermAux_extract h₂
  unfold Factory.bvadd Factory.bvapp
  split
  · next m b₁ b₂ =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               TermType.prim.injEq, TermPrimType.bitvec.injEq] at hdt₁ hdt₂
    obtain ⟨hmn₁, hf₁⟩ := hdt₁
    obtain ⟨hmn₂, hf₂⟩ := hdt₂
    subst hmn₁; subst hmn₂; subst hf₁; subst hf₂
    simp [denoteBVTermAux, denoteTerm]
  · simp [denoteBVTermAux, denoteTerm, denoteTerms, leftAssoc, leftAssoc.go, hdt₁, hdt₂]

/-- `Factory.bvsub` preserves `denoteBVTermAux` semantics. -/
theorem Factory.bvsub_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    denoteBVTermAux n (Factory.bvsub t₁ t₂) = some (x - y) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteBVTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteBVTermAux_extract h₂
  unfold Factory.bvsub Factory.bvapp
  split
  · next m b₁ b₂ =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               TermType.prim.injEq, TermPrimType.bitvec.injEq] at hdt₁ hdt₂
    obtain ⟨hmn₁, hf₁⟩ := hdt₁
    obtain ⟨hmn₂, hf₂⟩ := hdt₂
    subst hmn₁; subst hmn₂; subst hf₁; subst hf₂
    simp [denoteBVTermAux, denoteTerm]
  · simp [denoteBVTermAux, denoteTerm, denoteTerms, leftAssoc, leftAssoc.go, hdt₁, hdt₂]

/-- `Factory.bvmul` preserves `denoteBVTermAux` semantics. -/
theorem Factory.bvmul_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    denoteBVTermAux n (Factory.bvmul t₁ t₂) = some (x * y) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteBVTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteBVTermAux_extract h₂
  unfold Factory.bvmul Factory.bvapp
  split
  · next m b₁ b₂ =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               TermType.prim.injEq, TermPrimType.bitvec.injEq] at hdt₁ hdt₂
    obtain ⟨hmn₁, hf₁⟩ := hdt₁
    obtain ⟨hmn₂, hf₂⟩ := hdt₂
    subst hmn₁; subst hmn₂; subst hf₁; subst hf₂
    simp [denoteBVTermAux, denoteTerm]
  · simp [denoteBVTermAux, denoteTerm, denoteTerms, leftAssoc, leftAssoc.go, hdt₁, hdt₂]

/-- `Factory.bvshl` preserves `denoteBVTermAux` semantics. -/
theorem Factory.bvshl_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    denoteBVTermAux n (Factory.bvshl t₁ t₂) = some (x <<< y) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteBVTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteBVTermAux_extract h₂
  unfold Factory.bvshl Factory.bvapp
  split
  · next m b₁ b₂ =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               TermType.prim.injEq, TermPrimType.bitvec.injEq] at hdt₁ hdt₂
    obtain ⟨hmn₁, hf₁⟩ := hdt₁
    obtain ⟨hmn₂, hf₂⟩ := hdt₂
    subst hmn₁; subst hmn₂; subst hf₁; subst hf₂
    simp [denoteBVTermAux, denoteTerm]
  · simp [denoteBVTermAux, denoteTerm, hdt₁, hdt₂]

/-- `Factory.bvlshr` preserves `denoteBVTermAux` semantics. -/
theorem Factory.bvlshr_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    denoteBVTermAux n (Factory.bvlshr t₁ t₂) = some (x >>> y) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteBVTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteBVTermAux_extract h₂
  unfold Factory.bvlshr Factory.bvapp
  split
  · next m b₁ b₂ =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq,
        TermDenoteResult.mk.injEq, TermType.prim.injEq,
        TermPrimType.bitvec.injEq] at hdt₁ hdt₂
    obtain ⟨hmn₁, hf₁⟩ := hdt₁
    obtain ⟨hmn₂, hf₂⟩ := hdt₂
    subst hmn₁; subst hmn₂; subst hf₁; subst hf₂
    simp [denoteBVTermAux, denoteTerm]
  · simp [denoteBVTermAux, denoteTerm, hdt₁, hdt₂]

/-! ## Bitvector comparison correctness -/

private theorem BitVec.ofNat_toNat_self {n : Nat} (x : BitVec n) :
    BitVec.ofNat n x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

private theorem overflows_eq_saddOverflow {n : Nat} (x y : BitVec n) :
    BitVec.overflows n (x.toInt + y.toInt) = BitVec.saddOverflow x y := by
  unfold BitVec.overflows BitVec.signedMin BitVec.signedMax BitVec.saddOverflow
  by_cases h1 : x.toInt + y.toInt < -(2^(n-1) : Int)
  · simp [h1]
  · by_cases h2 : x.toInt + y.toInt ≥ (2^(n-1) : Int) <;>
      simp only [h1, h2, decide_false, decide_true, gt_iff_lt, Bool.false_or, Bool.or_false,
                 Bool.or_self, decide_eq_true_eq, decide_eq_false_iff_not,
                 Int.not_lt] <;> omega

private theorem overflows_eq_ssubOverflow {n : Nat} (x y : BitVec n) :
    BitVec.overflows n (x.toInt - y.toInt) = BitVec.ssubOverflow x y := by
  unfold BitVec.overflows BitVec.signedMin BitVec.signedMax BitVec.ssubOverflow
  by_cases h1 : x.toInt - y.toInt < -(2^(n-1) : Int)
  · simp [h1]
  · by_cases h2 : x.toInt - y.toInt ≥ (2^(n-1) : Int) <;>
      simp only [h1, h2, decide_false, decide_true, gt_iff_lt, Bool.false_or, Bool.or_false,
                 Bool.or_self, decide_eq_true_eq, decide_eq_false_iff_not,
                 Int.not_lt] <;> omega

private theorem overflows_eq_smulOverflow {n : Nat} (x y : BitVec n) :
    BitVec.overflows n (x.toInt * y.toInt) = BitVec.smulOverflow x y := by
  unfold BitVec.overflows BitVec.signedMin BitVec.signedMax BitVec.smulOverflow
  by_cases h1 : x.toInt * y.toInt < -(2^(n-1) : Int)
  · simp [h1]
  · by_cases h2 : x.toInt * y.toInt ≥ (2^(n-1) : Int) <;>
      simp only [h1, h2, decide_false, decide_true, gt_iff_lt, Bool.false_or, Bool.or_false,
                 Bool.or_self, decide_eq_true_eq, decide_eq_false_iff_not,
                 Int.not_lt] <;> omega

private theorem BitVec.overflows_neg_eq_negOverflow {n : Nat} (x : BitVec n) :
    BitVec.overflows n (-x.toInt) = BitVec.negOverflow x := by
  unfold BitVec.overflows BitVec.signedMin BitVec.signedMax BitVec.negOverflow
  have hlt : x.toInt < 2^(n-1) := BitVec.toInt_lt
  have hge : -(2^(n-1) : Int) ≤ x.toInt := BitVec.le_toInt x
  have hpow : (0 : Int) < 2^(n-1) := by
    rw [show ((2:Int)^(n-1) = ((2^(n-1) : Nat) : Int)) from by norm_cast]
    exact_mod_cast Nat.two_pow_pos (n-1)
  by_cases hneg : x.toInt = -(2^(n-1) : Int)
  · have h1 : (x.toInt == -2 ^ (n - 1)) = true := by simp [hneg]
    rw [h1]
    have h2 : decide (2 ^ (n - 1) - 1 < -x.toInt) = true := by
      rw [hneg]; simp; omega
    rw [h2]; simp
  · have hne : (x.toInt == -2 ^ (n - 1)) = false := by simp [hneg]
    rw [hne]
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨?_, ?_⟩ <;> omega

/-- `Factory.bvslt` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.bvslt_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    denoteBoolTermAux (Factory.bvslt t₁ t₂) = some (BitVec.slt x y = true) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteBVTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteBVTermAux_extract h₂
  unfold Factory.bvslt Factory.bvcmp
  split
  · simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               TermType.prim.injEq, TermPrimType.bitvec.injEq] at hdt₁ hdt₂
    obtain ⟨hmn₁, hf₁⟩ := hdt₁
    obtain ⟨hmn₂, hf₂⟩ := hdt₂
    subst hmn₁; subst hmn₂; subst hf₁; subst hf₂
    simp only [BitVec.ofNat_toNat_self]
    exact denoteBool_prim_bool _
  · simp [denoteBoolTermAux, denoteTerm, hdt₁, hdt₂]

/-- `Factory.bvsle` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.bvsle_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    denoteBoolTermAux (Factory.bvsle t₁ t₂) = some (BitVec.sle x y = true) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteBVTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteBVTermAux_extract h₂
  unfold Factory.bvsle Factory.bvcmp
  split
  · simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               TermType.prim.injEq, TermPrimType.bitvec.injEq] at hdt₁ hdt₂
    obtain ⟨hmn₁, hf₁⟩ := hdt₁
    obtain ⟨hmn₂, hf₂⟩ := hdt₂
    subst hmn₁; subst hmn₂; subst hf₁; subst hf₂
    simp only [BitVec.ofNat_toNat_self]
    exact denoteBool_prim_bool _
  · simp [denoteBoolTermAux, denoteTerm, hdt₁, hdt₂]

/-- `Factory.bvult` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.bvult_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    denoteBoolTermAux (Factory.bvult t₁ t₂) = some (x < y) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteBVTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteBVTermAux_extract h₂
  unfold Factory.bvult Factory.bvcmp
  split
  · simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               TermType.prim.injEq, TermPrimType.bitvec.injEq] at hdt₁ hdt₂
    obtain ⟨hmn₁, hf₁⟩ := hdt₁
    obtain ⟨hmn₂, hf₂⟩ := hdt₂
    subst hmn₁; subst hmn₂; subst hf₁; subst hf₂
    simp only [BitVec.ofNat_toNat_self]
    rw [denoteBool_prim_bool]; simp [BitVec.ult_iff_lt]
  · simp [denoteBoolTermAux, denoteTerm, hdt₁, hdt₂]

/-- `Factory.bvule` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.bvule_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    denoteBoolTermAux (Factory.bvule t₁ t₂) = some (x ≤ y) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteBVTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteBVTermAux_extract h₂
  unfold Factory.bvule Factory.bvcmp
  split
  · simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               TermType.prim.injEq, TermPrimType.bitvec.injEq] at hdt₁ hdt₂
    obtain ⟨hmn₁, hf₁⟩ := hdt₁
    obtain ⟨hmn₂, hf₂⟩ := hdt₂
    subst hmn₁; subst hmn₂; subst hf₁; subst hf₂
    rename_i b₂ b₁
    simp only [BitVec.ofNat_toNat_self]
    have hule_iff : BitVec.ule b₁ b₂ = true ↔ b₁ ≤ b₂ := by
      rw [BitVec.ule_eq_decide]; exact ⟨of_decide_eq_true, decide_eq_true⟩
    rw [denoteBool_prim_bool]; simp [hule_iff]
  · simp [denoteBoolTermAux, denoteTerm, hdt₁, hdt₂]

/-! ## Bitvector overflow correctness -/

/-- `Factory.bvnego` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.bvnego_correct {n : Nat} {t : Term} {x : BitVec n}
    (h : denoteBVTermAux n t = some x) :
    denoteBoolTermAux (Factory.bvnego t) = some (BitVec.negOverflow x = true) := by
  obtain ⟨f, hdt, rfl⟩ := denoteBVTermAux_extract h
  unfold Factory.bvnego
  split
  · next m b =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               TermType.prim.injEq, TermPrimType.bitvec.injEq] at hdt
    obtain ⟨hmn, hf⟩ := hdt
    subst hmn; subst hf
    rw [BitVec.overflows_neg_eq_negOverflow]
    exact denoteBool_prim_bool _
  · simp [denoteBoolTermAux, denoteTerm, hdt]

/-- `Factory.bvsaddo` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.bvsaddo_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    denoteBoolTermAux (Factory.bvsaddo t₁ t₂) = some (BitVec.saddOverflow x y = true) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteBVTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteBVTermAux_extract h₂
  unfold Factory.bvsaddo Factory.bvso
  split
  · simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               TermType.prim.injEq, TermPrimType.bitvec.injEq] at hdt₁ hdt₂
    obtain ⟨hmn₁, hf₁⟩ := hdt₁
    obtain ⟨hmn₂, hf₂⟩ := hdt₂
    subst hmn₁; subst hmn₂; subst hf₁; subst hf₂
    rename_i b₂ b₁
    rw [overflows_eq_saddOverflow]
    exact denoteBool_prim_bool _
  · simp [denoteBoolTermAux, denoteTerm, hdt₁, hdt₂]

/-- `Factory.bvssubo` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.bvssubo_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    denoteBoolTermAux (Factory.bvssubo t₁ t₂) = some (BitVec.ssubOverflow x y = true) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteBVTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteBVTermAux_extract h₂
  unfold Factory.bvssubo Factory.bvso
  split
  · simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               TermType.prim.injEq, TermPrimType.bitvec.injEq] at hdt₁ hdt₂
    obtain ⟨hmn₁, hf₁⟩ := hdt₁
    obtain ⟨hmn₂, hf₂⟩ := hdt₂
    subst hmn₁; subst hmn₂; subst hf₁; subst hf₂
    rename_i b₂ b₁
    rw [overflows_eq_ssubOverflow]
    exact denoteBool_prim_bool _
  · simp [denoteBoolTermAux, denoteTerm, hdt₁, hdt₂]

/-- `Factory.bvsmulo` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.bvsmulo_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    denoteBoolTermAux (Factory.bvsmulo t₁ t₂) = some (BitVec.smulOverflow x y = true) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteBVTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteBVTermAux_extract h₂
  unfold Factory.bvsmulo Factory.bvso
  split
  · simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               TermType.prim.injEq, TermPrimType.bitvec.injEq] at hdt₁ hdt₂
    obtain ⟨hmn₁, hf₁⟩ := hdt₁
    obtain ⟨hmn₂, hf₂⟩ := hdt₂
    subst hmn₁; subst hmn₂; subst hf₁; subst hf₂
    rename_i b₂ b₁
    rw [overflows_eq_smulOverflow]
    exact denoteBool_prim_bool _
  · simp [denoteBoolTermAux, denoteTerm, hdt₁, hdt₂]

/-! ## eq correctness -/

/-- `Factory.eq` preserves `denoteBoolTermAux` semantics on boolean arguments. -/
theorem Factory.eq_correct_bool {t₁ t₂ : Term} {p₁ p₂ : Prop}
    (h₁ : denoteBoolTermAux t₁ = some p₁) (h₂ : denoteBoolTermAux t₂ = some p₂) :
    denoteBoolTermAux (Factory.eq t₁ t₂) = some (p₁ ↔ p₂) := by
  unfold Factory.eq
  split
  · rename_i heq
    subst heq
    cases denoteBoolTermAux_eq h₁ h₂
    simp [denoteBoolTermAux, denoteTerm]
  · rename_i hne
    split
    · rename_i hlit
      simp [Bool.and_eq_true] at hlit
      obtain ⟨hl₁, hl₂⟩ := hlit
      obtain ⟨b₁, ht₁, hbp₁⟩ := denoteBoolTermAux_literal_form h₁ hl₁
      obtain ⟨b₂, ht₂, hbp₂⟩ := denoteBoolTermAux_literal_form h₂ hl₂
      have hbne : b₁ ≠ b₂ := by
        intro heq; apply hne; rw [ht₁, ht₂, heq]
      simp [denoteBoolTermAux, denoteTerm]
      intro hiff
      apply hbne
      have : (b₁ = true) ↔ (b₂ = true) := hbp₁.symm.trans (hiff.trans hbp₂)
      cases b₁ <;> cases b₂ <;> grind
    · split
      iterate 3
        · exfalso
          first
          | (simp only [denoteBoolTermAux, denoteTerm] at h₁
             split at h₁
             · rename_i heq
               rcases hd : denoteTerm {} _ with _ | ⟨ty', _, _⟩ <;> rw [hd] at heq <;> simp at heq
             · simp_all)
          | (simp only [denoteBoolTermAux, denoteTerm] at h₂
             split at h₂
             · rename_i heq
               rcases hd : denoteTerm {} _ with _ | ⟨ty', _, _⟩ <;> rw [hd] at heq <;> simp at heq
             · simp_all)
      · obtain ⟨f₁, hdt₁, hiff₁⟩ := denoteBoolTermAux_extract h₁
        obtain ⟨f₂, hdt₂, hiff₂⟩ := denoteBoolTermAux_extract h₂
        have h1 := propext hiff₁
        have h2 := propext hiff₂
        subst h1; subst h2
        simp only [denoteBoolTermAux, denoteTerm, Option.pure_def, Option.bind_eq_bind,
                   Option.bind_some, hdt₁, hdt₂, denoteTerms, chainable, chainable.go,
                   dif_pos trivial]
        exact congrArg some (propext ⟨fun h => h ▸ Iff.rfl, propext⟩)

/-- `Factory.eq` preserves `denoteBoolTermAux` semantics on integer arguments. -/
theorem Factory.eq_correct_int {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : denoteIntTermAux t₁ = some n₁) (h₂ : denoteIntTermAux t₂ = some n₂) :
    denoteBoolTermAux (Factory.eq t₁ t₂) = some (n₁ = n₂) := by
  unfold Factory.eq
  split
  · rename_i heq
    subst heq
    cases Option.some.inj (h₁.symm.trans h₂)
    simp [denoteBoolTermAux, denoteTerm]
  · rename_i hne
    split
    · rename_i hlit
      simp [Bool.and_eq_true] at hlit
      obtain ⟨hl₁, hl₂⟩ := hlit
      have ht₁ := denoteIntTermAux_literal_form h₁ hl₁
      have ht₂ := denoteIntTermAux_literal_form h₂ hl₂
      simp [denoteBoolTermAux, denoteTerm]
      intro heq; subst heq; apply hne; rw [ht₁, ht₂]
    · split
      iterate 3
        · exfalso
          first
          | (simp only [denoteIntTermAux, denoteTerm] at h₁
             split at h₁
             · rename_i heq
               rcases hd : denoteTerm {} _ with _ | ⟨ty', _, _⟩ <;> rw [hd] at heq <;> simp at heq
             · simp_all)
          | (simp only [denoteIntTermAux, denoteTerm] at h₂
             split at h₂
             · rename_i heq
               rcases hd : denoteTerm {} _ with _ | ⟨ty', _, _⟩ <;> rw [hd] at heq <;> simp at heq
             · simp_all)
      · obtain ⟨f₁, hdt₁, rfl⟩ := denoteIntTermAux_extract h₁
        obtain ⟨f₂, hdt₂, rfl⟩ := denoteIntTermAux_extract h₂
        simp only [denoteBoolTermAux, denoteTerm, Option.pure_def, Option.bind_eq_bind,
                   Option.bind_some, hdt₁, hdt₂, denoteTerms, chainable, chainable.go]
        rfl

/-- `Factory.eq` preserves `denoteBoolTermAux` semantics on bitvector arguments. -/
theorem Factory.eq_correct_bv {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    denoteBoolTermAux (Factory.eq t₁ t₂) = some (x = y) := by
  unfold Factory.eq
  split
  · rename_i heq
    subst heq
    cases Option.some.inj (h₁.symm.trans h₂)
    simp [denoteBoolTermAux, denoteTerm]
  · rename_i hne
    split
    · rename_i hlit
      simp [Bool.and_eq_true] at hlit
      obtain ⟨hl₁, hl₂⟩ := hlit
      have ht₁ := denoteBVTermAux_literal_form h₁ hl₁
      have ht₂ := denoteBVTermAux_literal_form h₂ hl₂
      simp [denoteBoolTermAux, denoteTerm]
      intro heq; subst heq; apply hne; rw [ht₁, ht₂]
    · split
      iterate 3
        · exfalso
          first
          | (simp only [denoteBVTermAux, denoteTerm] at h₁
             split at h₁
             · rename_i heq
               rcases hd : denoteTerm {} _ with _ | ⟨ty', _, _⟩ <;> rw [hd] at heq <;> simp at heq
             · simp_all)
          | (simp only [denoteBVTermAux, denoteTerm] at h₂
             split at h₂
             · rename_i heq
               rcases hd : denoteTerm {} _ with _ | ⟨ty', _, _⟩ <;> rw [hd] at heq <;> simp at heq
             · simp_all)
      · obtain ⟨f₁, hdt₁, rfl⟩ := denoteBVTermAux_extract h₁
        obtain ⟨f₂, hdt₂, rfl⟩ := denoteBVTermAux_extract h₂
        simp only [denoteBoolTermAux, denoteTerm, Option.pure_def, Option.bind_eq_bind,
                   Option.bind_some, hdt₁, hdt₂, denoteTerms, chainable, chainable.go]
        rfl

/-- `Factory.eq` preserves `denoteBoolTermAux` semantics on string arguments. -/
theorem Factory.eq_correct_string {t₁ t₂ : Term} {s₁ s₂ : String}
    (h₁ : denoteStringTermAux t₁ = some s₁) (h₂ : denoteStringTermAux t₂ = some s₂) :
    denoteBoolTermAux (Factory.eq t₁ t₂) = some (s₁ = s₂) := by
  unfold Factory.eq
  split
  · rename_i heq
    subst heq
    cases Option.some.inj (h₁.symm.trans h₂)
    simp [denoteBoolTermAux, denoteTerm]
  · rename_i hne
    split
    · rename_i hlit
      simp [Bool.and_eq_true] at hlit
      obtain ⟨hl₁, hl₂⟩ := hlit
      have ht₁ := denoteStringTermAux_literal_form h₁ hl₁
      have ht₂ := denoteStringTermAux_literal_form h₂ hl₂
      simp [denoteBoolTermAux, denoteTerm]
      intro heq; subst heq; apply hne; rw [ht₁, ht₂]
    · split
      iterate 3
        · exfalso
          first
          | (simp only [denoteStringTermAux, denoteTerm] at h₁
             split at h₁
             · rename_i heq
               rcases hd : denoteTerm {} _ with _ | ⟨ty', _, _⟩ <;> rw [hd] at heq <;> simp at heq
             · simp_all)
          | (simp only [denoteStringTermAux, denoteTerm] at h₂
             split at h₂
             · rename_i heq
               rcases hd : denoteTerm {} _ with _ | ⟨ty', _, _⟩ <;> rw [hd] at heq <;> simp at heq
             · simp_all)
      · obtain ⟨f₁, hdt₁, rfl⟩ := denoteStringTermAux_extract h₁
        obtain ⟨f₂, hdt₂, rfl⟩ := denoteStringTermAux_extract h₂
        simp only [denoteBoolTermAux, denoteTerm, Option.pure_def, Option.bind_eq_bind,
                   Option.bind_some, hdt₁, hdt₂, denoteTerms, chainable, chainable.go]
        rfl

/-! ## ite correctness -/

open Classical in
/-- `Factory.ite` preserves `denoteBoolTermAux` semantics for boolean branches. -/
theorem Factory.ite_correct_bool {t₁ t₂ t₃ : Term} {p₁ p₂ p₃ : Prop}
    (h₁ : denoteBoolTermAux t₁ = some p₁)
    (h₂ : denoteBoolTermAux t₂ = some p₂)
    (h₃ : denoteBoolTermAux t₃ = some p₃) :
    denoteBoolTermAux (Factory.ite t₁ t₂ t₃) = some (if p₁ then p₂ else p₃) := by
  unfold Factory.ite
  split
  · rename_i hcond
    rcases or_decide_true hcond with ht | heq
    · subst ht
      have hp₁ := denoteBoolTermAux_eq h₁ (denoteBool_prim_bool true)
      rw [h₂, hp₁, if_pos rfl]
    · subst heq
      cases denoteBoolTermAux_eq h₂ h₃
      rw [h₂]
      by_cases hp₁ : p₁ <;> simp [hp₁]
  · split
    · rename_i _ hf; subst hf
      have hp₁ := denoteBoolTermAux_eq h₁ (denoteBool_prim_bool false)
      rw [h₃, hp₁, if_neg (by decide)]
    · split
      · exfalso
        simp only [denoteBoolTermAux, denoteTerm] at h₂
        split at h₂
        · rename_i heq
          rcases hd : denoteTerm {} _ with _ | ⟨ty', _, _⟩ <;> rw [hd] at heq <;> simp at heq
        · simp_all
      · obtain ⟨f₁, hdt₁, hiff₁⟩ := denoteBoolTermAux_extract h₁
        obtain ⟨f₂, hdt₂, hiff₂⟩ := denoteBoolTermAux_extract h₂
        obtain ⟨f₃, hdt₃, hiff₃⟩ := denoteBoolTermAux_extract h₃
        simp only [denoteBoolTermAux, denoteTerm, Option.pure_def, Option.bind_eq_bind,
                   Option.bind_some, hdt₁, hdt₂, hdt₃, dif_pos trivial]
        by_cases hp₁ : p₁
        · rw [if_pos hp₁, if_pos (hiff₁.mpr hp₁)]
          exact congrArg some (propext hiff₂)
        · rw [if_neg hp₁, if_neg (fun h => hp₁ (hiff₁.mp h))]
          exact congrArg some (propext hiff₃)

open Classical in
/-- `Factory.ite` preserves `denoteIntTermAux` semantics for integer branches. -/
theorem Factory.ite_correct_int {t₁ t₂ t₃ : Term} {p₁ : Prop} {n₂ n₃ : Int}
    (h₁ : denoteBoolTermAux t₁ = some p₁)
    (h₂ : denoteIntTermAux t₂ = some n₂)
    (h₃ : denoteIntTermAux t₃ = some n₃) :
    denoteIntTermAux (Factory.ite t₁ t₂ t₃) = some (if p₁ then n₂ else n₃) := by
  unfold Factory.ite
  split
  · rename_i hcond
    rcases or_decide_true hcond with ht | heq
    · grind [denoteBoolTermAux, denoteTerm]
    · subst heq
      rw [h₂]
      have hnn : n₂ = n₃ := Option.some.inj (h₃ ▸ h₂).symm
      by_cases hp₁ : p₁ <;> simp [hp₁, hnn]
  · split
    · rename_i _ hf; subst hf
      grind [denoteBoolTermAux, denoteTerm]
    · split
      · exfalso
        simp only [denoteIntTermAux, denoteTerm] at h₂
        split at h₂
        · rename_i heq
          rcases hd : denoteTerm {} _ with _ | ⟨ty', _, _⟩ <;> rw [hd] at heq <;> simp at heq
        · simp_all
      · obtain ⟨f₁, hdt₁, hiff₁⟩ := denoteBoolTermAux_extract h₁
        obtain ⟨f₂, hdt₂, rfl⟩ := denoteIntTermAux_extract h₂
        obtain ⟨f₃, hdt₃, rfl⟩ := denoteIntTermAux_extract h₃
        simp only [denoteIntTermAux, denoteTerm, Option.pure_def, Option.bind_eq_bind,
                   Option.bind_some, hdt₁, hdt₂, hdt₃]
        by_cases hp₁ : p₁
        · rw [if_pos hp₁]; simp [if_pos (hiff₁.mpr hp₁)]
        · rw [if_neg hp₁]; simp [if_neg (fun h => hp₁ (hiff₁.mp h))]

open Classical in
/-- `Factory.ite` preserves `denoteBVTermAux` semantics for bitvector branches. -/
theorem Factory.ite_correct_bv {n : Nat} {t₁ t₂ t₃ : Term} {p₁ : Prop} {b₂ b₃ : BitVec n}
    (h₁ : denoteBoolTermAux t₁ = some p₁)
    (h₂ : denoteBVTermAux n t₂ = some b₂)
    (h₃ : denoteBVTermAux n t₃ = some b₃) :
    denoteBVTermAux n (Factory.ite t₁ t₂ t₃) = some (if p₁ then b₂ else b₃) := by
  unfold Factory.ite
  split
  · rename_i hcond
    rcases or_decide_true hcond with ht | heq
    · grind [denoteBoolTermAux, denoteTerm]
    · subst heq
      rw [h₂]
      have hnn : b₂ = b₃ := Option.some.inj (h₃ ▸ h₂).symm
      by_cases hp₁ : p₁ <;> simp [hp₁, hnn]
  · split
    · rename_i _ hf; subst hf
      grind [denoteBoolTermAux, denoteTerm]
    · split
      · exfalso
        simp only [denoteBVTermAux, denoteTerm] at h₂
        split at h₂
        · rename_i heq
          rcases hd : denoteTerm {} _ with _ | ⟨ty', _, _⟩ <;> rw [hd] at heq <;> simp at heq
        · simp_all
      · obtain ⟨f₁, hdt₁, hiff₁⟩ := denoteBoolTermAux_extract h₁
        obtain ⟨f₂, hdt₂, rfl⟩ := denoteBVTermAux_extract h₂
        obtain ⟨f₃, hdt₃, rfl⟩ := denoteBVTermAux_extract h₃
        simp only [denoteBVTermAux, denoteTerm, Option.pure_def, Option.bind_eq_bind,
                   Option.bind_some, hdt₁, hdt₂, hdt₃]
        by_cases hp₁ : p₁
        · rw [if_pos hp₁]; simp [if_pos (hiff₁.mpr hp₁)]
        · rw [if_neg hp₁]; simp [if_neg (fun h => hp₁ (hiff₁.mp h))]

open Classical in
/-- `Factory.ite` preserves `denoteStringTermAux` semantics for string branches. -/
theorem Factory.ite_correct_string {t₁ t₂ t₃ : Term} {p₁ : Prop} {s₂ s₃ : String}
    (h₁ : denoteBoolTermAux t₁ = some p₁)
    (h₂ : denoteStringTermAux t₂ = some s₂)
    (h₃ : denoteStringTermAux t₃ = some s₃) :
    denoteStringTermAux (Factory.ite t₁ t₂ t₃) = some (if p₁ then s₂ else s₃) := by
  unfold Factory.ite
  split
  · rename_i hcond
    rcases or_decide_true hcond with ht | heq
    · grind [denoteBoolTermAux, denoteTerm]
    · subst heq
      rw [h₂]
      have hnn : s₂ = s₃ := Option.some.inj (h₃ ▸ h₂).symm
      by_cases hp₁ : p₁ <;> simp [hp₁, hnn]
  · split
    · rename_i _ hf; subst hf
      grind [denoteBoolTermAux, denoteTerm]
    · split
      · exfalso
        simp only [denoteStringTermAux, denoteTerm] at h₂
        split at h₂
        · rename_i heq
          rcases hd : denoteTerm {} _ with _ | ⟨ty', _, _⟩ <;> rw [hd] at heq <;> simp at heq
        · simp_all
      · obtain ⟨f₁, hdt₁, hiff₁⟩ := denoteBoolTermAux_extract h₁
        obtain ⟨f₂, hdt₂, rfl⟩ := denoteStringTermAux_extract h₂
        obtain ⟨f₃, hdt₃, rfl⟩ := denoteStringTermAux_extract h₃
        simp only [denoteStringTermAux, denoteTerm, Option.pure_def, Option.bind_eq_bind,
                   Option.bind_some, hdt₁, hdt₂, hdt₃]
        by_cases hp₁ : p₁
        · rw [if_pos hp₁]; simp [if_pos (hiff₁.mpr hp₁)]
        · rw [if_neg hp₁]; simp [if_neg (fun h => hp₁ (hiff₁.mp h))]

/-! ## Bitvector extension correctness -/

/-- `Factory.zero_extend` preserves `denoteBVTermAux` semantics
    when the input term's declared type matches the denoted type. -/
theorem Factory.zero_extend_correct {m n : Nat} {t : Term} {x : BitVec m}
    (h : denoteBVTermAux m t = some x) (hty : t.typeOf = .prim (.bitvec m)) :
    denoteBVTermAux (m + n) (Factory.zero_extend n t) = some (BitVec.zeroExtend (m + n) x) := by
  obtain ⟨f, hdt, rfl⟩ := denoteBVTermAux_extract h
  unfold Factory.zero_extend
  split
  · next k b =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               TermType.prim.injEq, TermPrimType.bitvec.injEq] at hdt
    obtain ⟨hkm, hf⟩ := hdt
    subst hkm; subst hf
    grind [denoteBVTermAux, denoteTerm, Option.pure_def, Nat.add_comm]
  · grind [denoteBVTermAux, denoteTerm, Option.pure_def, Option.bind_eq_bind]

/-! ## Factory.app correctness (UF) -/

/-- `Factory.app` for a UF is a no-op wrapper: it produces exactly the term
    `.app (.uf f) ts f.out`, so its denotation agrees with the direct term
    in any context. -/
theorem Factory.app_uf_correct (ctx : Context) (f : UF) (ts : List Term) :
    denoteTerm ctx (Factory.app (.uf f) ts) = denoteTerm ctx (.app (.uf f) ts f.out) :=
  rfl


/-! ## Option Factory correctness -/

/-- `Factory.noneOf` is a no-op wrapper: it produces exactly `.none ty`, so
    its denotation agrees with the direct term in any context. -/
theorem Factory.noneOf_correct (ctx : Context) (ty : TermType) :
    denoteTerm ctx (Factory.noneOf ty) = denoteTerm ctx (.none ty) :=
  rfl

/-- `Factory.someOf` is a no-op wrapper: it produces exactly `.some t`, so
    its denotation agrees with the direct term in any context. -/
theorem Factory.someOf_correct (ctx : Context) (t : Term) :
    denoteTerm ctx (Factory.someOf t) = denoteTerm ctx (.some t) :=
  rfl

/-- `Factory.option.get` applied to `.some t` strips the wrapper, returning
    `t` itself. Its denotation therefore agrees with that of `t`. -/
theorem Factory.option_get_some_correct (ctx : Context) (t : Term) :
    denoteTerm ctx (Factory.option.get (.some t)) = denoteTerm ctx t :=
  rfl

/-! ## Quantifier coalescing correctness -/

/-- `isSome` of a cons `denoteFunSort` iff the head sort and the tail fun-sort are both `isSome`. -/
private theorem denoteFunSort_cons_isSome_iff {sctx : SortContext} {a : TermType} {as : List TermType}
    {out : TermType} :
    (denoteFunSort sctx (a :: as) out).isSome
      ↔ (denoteSort sctx a).isSome ∧ (denoteFunSort sctx as out).isSome := by
  constructor
  · exact denoteFunSortCons_isSome
  · rintro ⟨ha, has⟩
    simp only [denoteFunSort, Option.pure_def, Option.bind_eq_bind, Option.isSome_bind,
      Option.isSome_some, Option.any_true]
    rw [Option.any_eq_true_iff_get]
    exact ⟨ha, has⟩

/-- The empty-argument `denoteFunSort` is just the output-sort denotation. -/
private theorem denoteFunSort_nil {sctx : SortContext} {out : TermType} :
    denoteFunSort sctx [] out = denoteSort sctx out := rfl

/-- `bool` is always denotable. -/
private theorem denoteSort_bool_isSome {sctx : SortContext} :
    (denoteSort sctx (.prim .bool)).isSome = true := rfl

/-- A single-argument `denoteFunSort` is `isSome` iff its (sole) argument sort is — the output is
    `bool`, always denotable. -/
private theorem denoteFunSort_singleton_bool_isSome_iff {sctx : SortContext} {a : TermType} :
    (denoteFunSort sctx [a] (.prim .bool)).isSome ↔ (denoteSort sctx a).isSome := by
  rw [denoteFunSort_cons_isSome_iff, denoteFunSort_nil]
  simp [denoteSort_bool_isSome]

/-- A dependently-typed function applied at equal arguments gives equal (up to transport) results:
    `f a₁ = h ▸ f a₂` when `h : a₁ = a₂`. Used to relate the merged- vs. nested-context body
    denotations across the `.tctx.vs` reassociation quantifier coalescing introduces. -/
private theorem congr_dep_fun {α : Sort _} {β : α → Sort _} (f : (a : α) → β a)
    {a₁ a₂ : α} (h : a₁ = a₂) :
    f a₁ = h ▸ f a₂ := by
  cases h; rfl

/-- Transport of `none` across an index equality is `none` (any type family). -/
private theorem eqrec_option_none {α : Sort _} {F : α → Type _} {a₁ a₂ : α} (h : a₁ = a₂) :
    (h ▸ (none : Option (F a₂))) = (none : Option (F a₁)) := by
  cases h; rfl

/-- Transport of `some r` across an index equality is `some` of the transported value. -/
private theorem eqrec_option_some {α : Sort _} {F : α → Type _} {a₁ a₂ : α} (h : a₁ = a₂) (r : F a₂) :
    (h ▸ (some r : Option (F a₂))) = some (h ▸ r) := by
  cases h; rfl

/-- Transport of a `TermDenoteResult` record across a context equality is the record with
    transported fields. -/
private theorem eqrec_result {c₁ c₂ : Context} (h : c₁ = c₂)
    (t : TermType) (rh : (denoteSort c₂.sctx t).isSome = true)
    (rres : (tdi : TermDenoteInput c₂) → (denoteSort c₂.sctx t).get rh { sΓ := tdi.sΓ, hsΓ := tdi.hsΓ }) :
    (h ▸ ({ ty := t, h := rh, res := rres } : TermDenoteResult c₂) : TermDenoteResult c₁)
      = { ty := t, h := h ▸ rh, res := h ▸ rres } := by
  cases h; rfl

/-- Transport of a bool-typed `TermDenoteResult` record: the `.res` field lands in the simple
    `TermDenoteInput → Prop` motive (since `(denoteSort _ (.prim .bool)).get _ _` is `Prop`). -/
private theorem eqrec_result_bool {c₁ c₂ : Context} (h : c₁ = c₂)
    (rh : (denoteSort c₂.sctx (.prim .bool)).isSome = true)
    (rres : (tdi : TermDenoteInput c₂) → (denoteSort c₂.sctx (.prim .bool)).get rh { sΓ := tdi.sΓ, hsΓ := tdi.hsΓ }) :
    (h ▸ ({ ty := .prim .bool, h := rh, res := rres } : TermDenoteResult c₂) : TermDenoteResult c₁)
      = { ty := .prim .bool, h := h ▸ rh,
          res := (h ▸ (rres : TermDenoteInput c₂ → Prop) : TermDenoteInput c₁ → Prop) } := by
  cases h; rfl

/-- The pure `buildQuant` cons-step reassociation: a merged binder over `v :: vs` equals the
    nested `[v]`-then-`vs` binders, modulo the body-context transport `hctx`. This isolates the
    dependently-typed reassociation (via `buildQuant`'s own cons/nil equations + HEq transport)
    away from the monadic `denoteTerm` layer. -/
private theorem buildQuant_cons_reassoc (bindVar : QuantVarBinder) (ctx : Context) (v : TermVar) (vs : List TermVar)
    (h : (denoteFunSort ctx.sctx (List.map (fun x => x.ty) (v :: vs)) (.prim .bool)).isSome = true)
    (h₁ : (denoteFunSort ctx.sctx (List.map (fun x => x.ty) [v]) (.prim .bool)).isSome = true)
    (h₂ : (denoteFunSort ({ sctx := ctx.sctx, tctx := { vs := v :: ctx.tctx.vs, ufs := ctx.tctx.ufs } } : Context).sctx (List.map (fun x => x.ty) vs) (.prim .bool)).isSome = true)
    (body : TermDenoteInput { sctx := ctx.sctx, tctx := { vs := (v :: vs).reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } } → Prop)
    (hctx : ({ sctx := ctx.sctx, tctx := { vs := (v :: vs).reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } } : Context)
        = { sctx := ctx.sctx, tctx := { vs := vs.reverse ++ ([v].reverse ++ ctx.tctx.vs), ufs := ctx.tctx.ufs } })
    (tdi : TermDenoteInput ctx) :
    buildQuant bindVar ctx (v :: vs) h body tdi
      = buildQuant bindVar ctx [v] h₁
          (buildQuant bindVar { sctx := ctx.sctx, tctx := { vs := [v].reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } } vs h₂ (hctx ▸ body)) tdi := by
  simp only [buildQuant]
  congr 1
  funext tdi'
  congr 1
  apply eq_of_heq
  refine HEq.trans
    (eqRec_heq (φ := fun x => TermDenoteInput { sctx := ctx.sctx, tctx := { vs := x, ufs := ctx.tctx.ufs } } → Prop) _ body)
    (HEq.symm (eqRec_heq (φ := fun x => TermDenoteInput x → Prop) hctx body))

/-- Funext form of `buildQuant_cons_reassoc` (as an equality of `buildQuant`s, not applied). -/
private theorem buildQuant_cons_reassoc' (bindVar : QuantVarBinder) (ctx : Context) (v : TermVar) (vs : List TermVar)
    (h : (denoteFunSort ctx.sctx (List.map (fun x => x.ty) (v :: vs)) (.prim .bool)).isSome = true)
    (h₁ : (denoteFunSort ctx.sctx (List.map (fun x => x.ty) [v]) (.prim .bool)).isSome = true)
    (h₂ : (denoteFunSort ({ sctx := ctx.sctx, tctx := { vs := v :: ctx.tctx.vs, ufs := ctx.tctx.ufs } } : Context).sctx (List.map (fun x => x.ty) vs) (.prim .bool)).isSome = true)
    (body : TermDenoteInput { sctx := ctx.sctx, tctx := { vs := (v :: vs).reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } } → Prop)
    (hctx : ({ sctx := ctx.sctx, tctx := { vs := (v :: vs).reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } } : Context)
        = { sctx := ctx.sctx, tctx := { vs := vs.reverse ++ ([v].reverse ++ ctx.tctx.vs), ufs := ctx.tctx.ufs } }) :
    buildQuant bindVar ctx (v :: vs) h body
      = buildQuant bindVar ctx [v] h₁
          (buildQuant bindVar { sctx := ctx.sctx, tctx := { vs := [v].reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } } vs h₂ (hctx ▸ body)) := by
  funext tdi
  apply buildQuant_cons_reassoc

/-- The bool-case `some`-branch equality: the merged `buildQuant bindVar (v :: args2)` over the
    transported body `hctx ▸ rres` equals the nested `buildQuant bindVar [v]`-then-`args2`, discharging the
    residual double-transport via `buildQuant_cons_reassoc'` + HEq peeling. -/
private theorem buildQuant_some_branch_eq (bindVar : QuantVarBinder) (ctx : Context) (v : TermVar) (args2 : List TermVar)
    (hm : (denoteFunSort ctx.sctx (List.map (fun x => x.ty) (v :: args2)) (.prim .bool)).isSome = true)
    (h₁ : (denoteFunSort ctx.sctx (List.map (fun x => x.ty) [v]) (.prim .bool)).isSome = true)
    (h₂ : (denoteFunSort ({ sctx := ctx.sctx, tctx := { vs := v :: ctx.tctx.vs, ufs := ctx.tctx.ufs } } : Context).sctx (List.map (fun x => x.ty) args2) (.prim .bool)).isSome = true)
    (hctx : ({ sctx := ctx.sctx, tctx := { vs := (v :: args2).reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } } : Context)
        = { sctx := ctx.sctx, tctx := { vs := args2.reverse ++ ([v].reverse ++ ctx.tctx.vs), ufs := ctx.tctx.ufs } })
    (rres : TermDenoteInput ({ sctx := ctx.sctx, tctx := { vs := args2.reverse ++ ([v].reverse ++ ctx.tctx.vs), ufs := ctx.tctx.ufs } } : Context) → Prop) :
    buildQuant bindVar ctx (v :: args2) hm (hctx ▸ rres)
      = buildQuant bindVar ctx [v] h₁ (buildQuant bindVar { sctx := ctx.sctx, tctx := { vs := [v].reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } } args2 h₂ rres) := by
  rw [buildQuant_cons_reassoc' bindVar ctx v args2 hm h₁ h₂ _ hctx]
  apply congrArg
  apply congrArg
  apply eq_of_heq
  refine HEq.trans (eqRec_heq (φ := fun x => TermDenoteInput x → Prop) hctx _) ?_
  exact eqRec_heq (φ := fun x => TermDenoteInput x → Prop) _ rres

/-- One-step quantifier coalescing at the denotation level: a merged binder over
    `⟨x,ty⟩ :: args2` denotes exactly like the nested `⟨x,ty⟩`-then-`args2` binders.

    Stated generically over `qk`: `cases qk` reduces `denoteTerm` to its `buildForall` / `buildExists`
    arm. -/
private theorem denoteTerm_quant_coalesce (qk : QuantifierKind) (ctx : Context) (x : String) (ty : TermType)
    (tr trM tr2 : List (List Term)) (args2 : List TermVar) (e2 : Term) :
    denoteTerm ctx (.quant qk ([⟨x, ty⟩] ++ args2) trM e2)
      = denoteTerm ctx (.quant qk [⟨x, ty⟩] tr (.quant qk args2 tr2 e2)) := by
  cases qk <;>
  · simp only [denoteTerm, List.map_cons, List.map_nil, List.singleton_append]
    -- Align the three `dite` guards. The merged head guard `(ty :: map args2)` holds iff BOTH the
    -- head-sort `(denoteSort ty)` and the tail guard `(map args2)` hold; the nested-outer guard
    -- `[ty]` reduces to `(denoteSort ty)` since the output `bool` is always denotable.
    by_cases hhd : (denoteSort ctx.sctx ty).isSome = true
    · have hhd' : (denoteFunSort ctx.sctx [ty] (.prim .bool)).isSome = true :=
        denoteFunSort_singleton_bool_isSome_iff.mpr hhd
      by_cases htl : (denoteFunSort ctx.sctx (args2.map (·.ty)) (.prim .bool)).isSome = true
      · -- both hold ⇒ merged guard holds too; every `dite` takes its `then` branch
        have hmerged : (denoteFunSort ctx.sctx (ty :: args2.map (·.ty)) (.prim .bool)).isSome = true :=
          denoteFunSort_cons_isSome_iff.mpr ⟨hhd, htl⟩
        rw [dif_pos hmerged, dif_pos hhd', dif_pos htl]
        have hctx : ({ sctx := ctx.sctx, tctx := { vs := ({ id := x, ty := ty } :: args2).reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } } : Context)
            = { sctx := ctx.sctx, tctx := { vs := args2.reverse ++ ([{ id := x, ty := ty }].reverse ++ ctx.tctx.vs), ufs := ctx.tctx.ufs } } := by
          simp [List.reverse_cons]
        -- The merged-context and nested-inner-context body denotations are equal up to `hctx`.
        -- Generalize both and relate via the context-congruence helper, then case-split the option.
        generalize hmd : denoteTerm { sctx := ctx.sctx, tctx := { vs := ({ id := x, ty := ty } :: args2).reverse ++ ctx.tctx.vs, ufs := ctx.tctx.ufs } } e2 = md
        generalize hid : denoteTerm { sctx := ctx.sctx, tctx := { vs := args2.reverse ++ ([{ id := x, ty := ty }].reverse ++ ctx.tctx.vs), ufs := ctx.tctx.ufs } } e2 = idn
        have hrel : md = hctx ▸ idn := by
          rw [← hmd, ← hid]
          exact congr_dep_fun (fun c => denoteTerm c e2) hctx
        subst hrel
        cases idn with
        | none =>
          -- both sides fail on `none`
          rw [eqrec_option_none hctx]
          rfl
        | some r =>
          rw [eqrec_option_some hctx r]
          obtain ⟨rty, rh, rres⟩ := r
          -- Only the `bool`-typed result survives the `denoteTerm` quantifier pattern; all other
          -- result types make both binds short-circuit to `none` (closed after `eqrec_result`).
          cases rty with
          | prim p =>
            cases p with
            | bool =>
              -- Transport the bool record (simple `→ Prop` motive), fire the match, then reassociate.
              -- The `_` binder is inferred: `bindForallVar` in the `.all` arm, `bindExistsVar` in `.exist`.
              rw [eqrec_result_bool hctx rh rres]
              show some _ = some _
              apply congrArg
              congr 1
              -- The goal's `buildForall`/`buildExists` is definitionally `buildQuant bindForallVar` /
              -- `buildQuant bindExistsVar`; supply the concrete binder for the current arm (a bare `_`
              -- can't unify through the wrapper). `first` picks the right one per `cases qk` branch.
              first
              | exact buildQuant_some_branch_eq bindForallVar ctx ⟨x, ty⟩ args2 hmerged hhd' htl hctx rres
              | exact buildQuant_some_branch_eq bindExistsVar ctx ⟨x, ty⟩ args2 hmerged hhd' htl hctx rres
            | _ => rw [eqrec_result hctx]; rfl
          | _ => rw [eqrec_result hctx]; rfl
      · -- tail guard fails ⇒ merged guard fails, and the nested inner produces `none`; both sides `none`
        rw [dif_neg (fun h => htl (denoteFunSort_cons_isSome_iff.mp h).2),
            dif_pos hhd', dif_neg htl]
        rfl
    · -- head guard fails ⇒ both the merged guard and the nested-outer `[ty]` guard fail; both `none`
      rw [dif_neg (fun h => hhd (denoteFunSort_cons_isSome_iff.mp h).1),
          dif_neg (fun h => hhd (denoteFunSort_singleton_bool_isSome_iff.mp h))]

/-- **Coalescing preserves denotation.** `Factory.quant qk x ty tr e` wraps `e` in a
    single-variable quantifier, but when `e` is itself a same-kind quantifier and the outer
    trigger is simple, it COALESCES the two into one multi-variable binder
    (`.quant qk (⟨x,ty⟩ :: args2) …`). This theorem states that the coalesced term denotes
    exactly like the naive, un-coalesced single-binder wrapping `.quant qk [⟨x,ty⟩] tr e`. -/
theorem Factory.quant_correct (ctx : Context) (qk : QuantifierKind)
    (x : String) (ty : TermType) (tr : List (List Term)) (e : Term) :
    denoteTerm ctx (Factory.quant qk x ty tr e)
      = denoteTerm ctx (.quant qk [⟨x, ty⟩] tr e) := by
  -- Only `e = .quant qk2 args2 tr2 e2` can differ from the naive wrapper; every other shape of
  -- `e` returns `.quant qk [⟨x,ty⟩] tr e` verbatim, so those cases are definitional.
  cases e with
  | quant qk2 args2 tr2 e2 =>
    -- The coalescing guard: same kind + simple outer trigger.
    simp only [Factory.quant]
    by_cases hg : (decide (qk = qk2) && Factory.isSimpleTrigger tr) = true
    · rw [if_pos hg]
      -- coalescing fires: merged multi-var binder vs nested single-var binders.
      -- From the guard, the two quantifier kinds coincide.
      obtain ⟨hqk, _⟩ := Bool.and_eq_true .. ▸ hg
      have hqk : qk = qk2 := of_decide_eq_true hqk
      subst hqk
      -- Triggers are ignored by `denoteTerm`, so the goal is a pure `buildQuant` reassociation.
      -- After unfolding `denoteTerm`, both sides denote the SAME body `e2`, but the merged binder
      -- denotes it at body context `(⟨x,ty⟩ :: args2).reverse ++ vs` while the nested binder denotes
      -- it at `args2.reverse ++ (⟨x,ty⟩ :: vs)`. These `.tctx.vs` lists are PROPOSITIONALLY equal
      -- (`List.reverse_cons` + `append_assoc`) but not definitionally, and `denoteTerm`'s result
      -- TYPE `Option (TermDenoteResult ctx)` depends on `ctx`.
      -- Given that, the outer `buildForall`/`buildExists` collapses by its
      -- own `buildQuant` cons-step (nil tail on the naive side), modulo the `▸` transport.
      exact denoteTerm_quant_coalesce qk ctx x ty tr _ tr2 args2 e2
    · rw [if_neg hg]
  | _ => rfl
