/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.Denote
import all Strata.DL.SMT.Denote
public import Strata.DL.SMT.Factory
import all Strata.DL.SMT.Factory

/-!
# Correctness of Factory optimizations

This module proves that the simplifications performed by `Factory` functions
preserve the denotational semantics directly in terms of the functional
denotation (`denoteBoolTermAux`, `denoteIntTermAux`).

For boolean operations, results use `∃ p', ... ∧ (p' ↔ expected)` because
`denoteTerm` maps booleans to `Prop` and propositional double-negation
elimination is not definitional.

For integer operations, results use direct equality.
-/

open Strata.SMT

/-! ## Infrastructure -/

/-- The unique `TermDenoteInput` for the empty context. -/
private noncomputable abbrev tdi₀ : TermDenoteInput ({} : Context) :=
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

/-- If `denoteBoolTermAux (.app .not [t'] ty) = some p`, then there exists `q`
    such that `denoteBoolTermAux t' = some q` and `p ↔ ¬q`. -/
private theorem denoteBoolTermAux_not_inv {t' : Term} {ty : TermType} {p : Prop}
    (h : denoteBoolTermAux (.app .not [t'] ty) = some p) :
    ∃ q, denoteBoolTermAux t' = some q ∧ (p ↔ ¬q) := by
  unfold denoteBoolTermAux at h ⊢
  conv at h => simp only [denoteTerm]
  revert h
  generalize denoteTerm {} t' = res'
  intro h
  match res' with
  | some ⟨.prim .bool, rfl, g⟩ => exact ⟨g tdi₀, by simp, by simp at h; rw [h]⟩
  | some ⟨.prim .int, _, _⟩ | some ⟨.prim .string, _, _⟩
  | some ⟨.prim (.bitvec _), _, _⟩ | some ⟨.prim .real, _, _⟩
  | some ⟨.prim .regex, _, _⟩ | some ⟨.prim .trigger, _, _⟩
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

/-- `denoteBoolTermAux` of a primitive `Bool` term is `True`/`False` accordingly. -/
private theorem denoteBool_prim_bool (b : Bool) :
    ∃ p, denoteBoolTermAux (.prim (.bool b)) = some p ∧ (p ↔ b = true) := by
  by_cases hd : b = true
  · exact ⟨True, by rw [hd]; rfl, iff_of_true trivial hd⟩
  · exact ⟨False, by rw [eq_false_of_ne_true hd]; rfl, iff_of_false not_false hd⟩

/-- For bool literal terms `.prim (.bool b₁) ≠ .prim (.bool b₂)` implies `b₁ ≠ b₂`. -/
private theorem prim_bool_ne_of_term_ne {b₁ b₂ : Bool}
    (h : (.prim (.bool b₁) : Term) ≠ .prim (.bool b₂)) : b₁ ≠ b₂ := by
  intro heq; apply h; rw [heq]

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
    ∃ p', denoteBoolTermAux (Factory.not t) = some p' ∧ (p' ↔ ¬p) := by
  unfold Factory.not
  split
  · -- Case: t = .prim (.bool b)
    rename_i b
    cases b
    · exact ⟨True, rfl, by
        simp only [denoteBoolTermAux, denoteTerm, Bool.false_eq_true, ↓reduceIte,
                   Option.pure_def, Option.some.injEq, eq_iff_iff, false_iff] at h
        grind⟩
    · exact ⟨False, rfl, by
        simp only [denoteBoolTermAux, denoteTerm, ↓reduceIte, Option.pure_def,
                   Option.some.injEq, eq_iff_iff, true_iff] at h
        grind⟩
  · -- Case: t = .app .not [t'] _
    obtain ⟨q, hq, hpq⟩ := denoteBoolTermAux_not_inv h
    exact ⟨q, hq, by rw [hpq]; exact Classical.not_not.symm⟩
  · -- Default: .app .not [t] .bool
    obtain ⟨f, hdt, hiff⟩ := denoteBoolTermAux_extract h
    exact ⟨¬ f tdi₀, by simp [denoteBoolTermAux, denoteTerm, hdt], not_congr hiff⟩

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
    ∃ p', denoteBoolTermAux (Factory.and t₁ t₂) = some p' ∧ (p' ↔ p₁ ∧ p₂) := by
  unfold Factory.and
  split
  · rename_i hcond
    rcases or_decide_true hcond with heq | heq
    · subst heq; cases denoteBoolTermAux_eq h₁ h₂
      exact ⟨p₁, h₁, by grind⟩
    · subst heq; simp only [denoteBoolTermAux, denoteTerm, ↓reduceIte, Option.pure_def,
                             Option.some.injEq, eq_iff_iff, true_iff] at h₂
      exact ⟨p₁, h₁, by grind⟩
  · split
    · rename_i hcond; subst hcond
      simp only [denoteBoolTermAux, denoteTerm, ↓reduceIte, Option.pure_def,
                 Option.some.injEq, eq_iff_iff, true_iff] at h₁
      exact ⟨p₂, h₂, by grind⟩
    · split
      · rename_i hcond
        refine ⟨False, rfl, ?_⟩
        rcases or3_decide_true hcond with hf | hf | hf
        · subst hf
          simp only [denoteBoolTermAux, denoteTerm, Bool.false_eq_true, ↓reduceIte,
                     Option.pure_def, Option.some.injEq, eq_iff_iff, false_iff] at h₁
          grind
        · subst hf
          simp only [denoteBoolTermAux, denoteTerm, Bool.false_eq_true, ↓reduceIte,
                     Option.pure_def, Option.some.injEq, eq_iff_iff, false_iff] at h₂
          grind
        · refine ⟨False.elim, ?_⟩
          rcases Factory.opposites_spec hf with ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
          · obtain ⟨_, hq, hiff⟩ := denoteBoolTermAux_not_inv h₂
            cases denoteBoolTermAux_eq hq h₁; grind
          · obtain ⟨_, hq, hiff⟩ := denoteBoolTermAux_not_inv h₁
            cases denoteBoolTermAux_eq hq h₂; grind
      · obtain ⟨f₁, hdt₁, hiff₁⟩ := denoteBoolTermAux_extract h₁
        obtain ⟨f₂, hdt₂, hiff₂⟩ := denoteBoolTermAux_extract h₂
        exact ⟨f₁ tdi₀ ∧ f₂ tdi₀,
               by simp [denoteBoolTermAux, denoteTerm, denoteTerms, leftAssoc, leftAssoc.go, hdt₁, hdt₂],
               and_congr hiff₁ hiff₂⟩

/-! ## Factory.or correctness -/

/-- `Factory.or` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.or_correct {t₁ t₂ : Term} {p₁ p₂ : Prop}
    (h₁ : denoteBoolTermAux t₁ = some p₁) (h₂ : denoteBoolTermAux t₂ = some p₂) :
    ∃ p', denoteBoolTermAux (Factory.or t₁ t₂) = some p' ∧ (p' ↔ p₁ ∨ p₂) := by
  unfold Factory.or
  split
  · rename_i hcond
    rcases or_decide_true hcond with heq | heq
    · subst heq; cases denoteBoolTermAux_eq h₁ h₂
      exact ⟨p₁, h₁, by grind⟩
    · subst heq
      simp only [denoteBoolTermAux, denoteTerm, Bool.false_eq_true, ↓reduceIte,
                 Option.pure_def, Option.some.injEq, eq_iff_iff, false_iff] at h₂
      exact ⟨p₁, h₁, by grind⟩
  · split
    · rename_i hcond; subst hcond
      simp only [denoteBoolTermAux, denoteTerm, Bool.false_eq_true, ↓reduceIte,
                 Option.pure_def, Option.some.injEq, eq_iff_iff, false_iff] at h₁
      exact ⟨p₂, h₂, by grind⟩
    · split
      · rename_i hcond
        refine ⟨True, rfl, ?_⟩
        rcases or3_decide_true hcond with ht | ht | ht
        · subst ht
          simp only [denoteBoolTermAux, denoteTerm, ↓reduceIte, Option.pure_def,
                     Option.some.injEq, eq_iff_iff, true_iff] at h₁
          grind
        · subst ht
          simp only [denoteBoolTermAux, denoteTerm, ↓reduceIte, Option.pure_def,
                     Option.some.injEq, eq_iff_iff, true_iff] at h₂
          grind
        · refine ⟨fun _ => ?_, fun _ => trivial⟩
          rcases Factory.opposites_spec ht with ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
          · obtain ⟨_, hq, hiff⟩ := denoteBoolTermAux_not_inv h₂
            cases denoteBoolTermAux_eq hq h₁
            exact (Classical.em p₁).elim Or.inl (Or.inr ∘ hiff.mpr)
          · obtain ⟨_, hq, hiff⟩ := denoteBoolTermAux_not_inv h₁
            cases denoteBoolTermAux_eq hq h₂
            exact (Classical.em p₂).elim Or.inr (Or.inl ∘ hiff.mpr)
      · obtain ⟨f₁, hdt₁, hiff₁⟩ := denoteBoolTermAux_extract h₁
        obtain ⟨f₂, hdt₂, hiff₂⟩ := denoteBoolTermAux_extract h₂
        exact ⟨f₁ tdi₀ ∨ f₂ tdi₀,
               by simp [denoteBoolTermAux, denoteTerm, denoteTerms, leftAssoc, leftAssoc.go, hdt₁, hdt₂],
               or_congr hiff₁ hiff₂⟩

/-! ## Factory.implies correctness -/

/-- `Factory.implies` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.implies_correct {t₁ t₂ : Term} {p₁ p₂ : Prop}
    (h₁ : denoteBoolTermAux t₁ = some p₁) (h₂ : denoteBoolTermAux t₂ = some p₂) :
    ∃ p', denoteBoolTermAux (Factory.implies t₁ t₂) = some p' ∧ (p' ↔ (p₁ → p₂)) := by
  unfold Factory.implies
  obtain ⟨np₁, hnot, hiff_not⟩ := Factory.not_correct h₁
  obtain ⟨p', hor, hiff_or⟩ := Factory.or_correct hnot h₂
  refine ⟨p', hor, hiff_or.trans ?_⟩
  rw [hiff_not]
  exact ⟨fun h hp => h.elim (absurd hp) id,
         fun h => (Classical.em p₁).elim (fun hp => Or.inr (h hp)) Or.inl⟩

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
    ∃ p, denoteBoolTermAux (Factory.intLe t₁ t₂) = some p ∧ (p ↔ n₁ ≤ n₂) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteIntTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteIntTermAux_extract h₂
  unfold Factory.intLe Factory.intcmp
  split
  · next i₁ i₂ =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               heq_eq_eq, true_and] at hdt₁ hdt₂; subst hdt₁; subst hdt₂
    exact (denoteBool_prim_bool _).imp fun _ ⟨h1, h2⟩ => ⟨h1, h2.trans (by simp)⟩
  · refine ⟨_, ?_, Iff.rfl⟩
    simp [denoteBoolTermAux, denoteTerm, denoteTerms, chainable, chainable.go, hdt₁, hdt₂]

/-- `Factory.intLt` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.intLt_correct {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : denoteIntTermAux t₁ = some n₁) (h₂ : denoteIntTermAux t₂ = some n₂) :
    ∃ p, denoteBoolTermAux (Factory.intLt t₁ t₂) = some p ∧ (p ↔ n₁ < n₂) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteIntTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteIntTermAux_extract h₂
  unfold Factory.intLt Factory.intcmp
  split
  · next i₁ i₂ =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               heq_eq_eq, true_and] at hdt₁ hdt₂; subst hdt₁; subst hdt₂
    exact (denoteBool_prim_bool _).imp fun _ ⟨h1, h2⟩ => ⟨h1, h2.trans (by simp)⟩
  · refine ⟨_, ?_, Iff.rfl⟩
    simp [denoteBoolTermAux, denoteTerm, denoteTerms, chainable, chainable.go, hdt₁, hdt₂]

/-- `Factory.intGe` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.intGe_correct {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : denoteIntTermAux t₁ = some n₁) (h₂ : denoteIntTermAux t₂ = some n₂) :
    ∃ p, denoteBoolTermAux (Factory.intGe t₁ t₂) = some p ∧ (p ↔ n₁ ≥ n₂) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteIntTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteIntTermAux_extract h₂
  unfold Factory.intGe Factory.intcmp
  split
  · next i₁ i₂ =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               heq_eq_eq, true_and] at hdt₁ hdt₂; subst hdt₁; subst hdt₂
    exact (denoteBool_prim_bool _).imp fun _ ⟨h1, h2⟩ => ⟨h1, h2.trans (by simp)⟩
  · refine ⟨_, ?_, Iff.rfl⟩
    simp [denoteBoolTermAux, denoteTerm, denoteTerms, chainable, chainable.go, hdt₁, hdt₂]

/-- `Factory.intGt` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.intGt_correct {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : denoteIntTermAux t₁ = some n₁) (h₂ : denoteIntTermAux t₂ = some n₂) :
    ∃ p, denoteBoolTermAux (Factory.intGt t₁ t₂) = some p ∧ (p ↔ n₁ > n₂) := by
  obtain ⟨f₁, hdt₁, rfl⟩ := denoteIntTermAux_extract h₁
  obtain ⟨f₂, hdt₂, rfl⟩ := denoteIntTermAux_extract h₂
  unfold Factory.intGt Factory.intcmp
  split
  · next i₁ i₂ =>
    simp only [denoteTerm, Option.pure_def, Option.some.injEq, TermDenoteResult.mk.injEq,
               heq_eq_eq, true_and] at hdt₁ hdt₂; subst hdt₁; subst hdt₂
    exact (denoteBool_prim_bool _).imp fun _ ⟨h1, h2⟩ => ⟨h1, h2.trans (by simp)⟩
  · refine ⟨_, ?_, Iff.rfl⟩
    simp [denoteBoolTermAux, denoteTerm, denoteTerms, chainable, chainable.go, hdt₁, hdt₂]

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
    ∃ p, denoteBoolTermAux (Factory.bvslt t₁ t₂) = some p ∧ (p ↔ BitVec.slt x y = true) := by
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
  · refine ⟨_, ?_, Iff.rfl⟩
    simp [denoteBoolTermAux, denoteTerm, hdt₁, hdt₂]

/-- `Factory.bvsle` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.bvsle_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    ∃ p, denoteBoolTermAux (Factory.bvsle t₁ t₂) = some p ∧ (p ↔ BitVec.sle x y = true) := by
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
  · refine ⟨_, ?_, Iff.rfl⟩
    simp [denoteBoolTermAux, denoteTerm, hdt₁, hdt₂]

/-- `Factory.bvult` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.bvult_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    ∃ p, denoteBoolTermAux (Factory.bvult t₁ t₂) = some p ∧ (p ↔ x < y) := by
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
    exact (denoteBool_prim_bool _).imp fun _ ⟨h1, h2⟩ => ⟨h1, h2.trans BitVec.ult_iff_lt⟩
  · refine ⟨_, ?_, Iff.rfl⟩
    simp [denoteBoolTermAux, denoteTerm, hdt₁, hdt₂]

/-- `Factory.bvule` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.bvule_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    ∃ p, denoteBoolTermAux (Factory.bvule t₁ t₂) = some p ∧ (p ↔ x ≤ y) := by
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
    exact (denoteBool_prim_bool _).imp fun _ ⟨h1, h2⟩ => ⟨h1, h2.trans hule_iff⟩
  · refine ⟨_, ?_, Iff.rfl⟩
    simp [denoteBoolTermAux, denoteTerm, hdt₁, hdt₂]

/-! ## Bitvector overflow correctness -/

/-- `Factory.bvnego` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.bvnego_correct {n : Nat} {t : Term} {x : BitVec n}
    (h : denoteBVTermAux n t = some x) :
    ∃ p, denoteBoolTermAux (Factory.bvnego t) = some p ∧ (p ↔ BitVec.negOverflow x = true) := by
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
  · refine ⟨_, ?_, Iff.rfl⟩
    simp [denoteBoolTermAux, denoteTerm, hdt]

/-- `Factory.bvsaddo` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.bvsaddo_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    ∃ p, denoteBoolTermAux (Factory.bvsaddo t₁ t₂) = some p ∧
         (p ↔ BitVec.saddOverflow x y = true) := by
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
  · refine ⟨_, ?_, Iff.rfl⟩
    simp [denoteBoolTermAux, denoteTerm, hdt₁, hdt₂]

/-- `Factory.bvssubo` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.bvssubo_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    ∃ p, denoteBoolTermAux (Factory.bvssubo t₁ t₂) = some p ∧
         (p ↔ BitVec.ssubOverflow x y = true) := by
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
  · refine ⟨_, ?_, Iff.rfl⟩
    simp [denoteBoolTermAux, denoteTerm, hdt₁, hdt₂]

/-- `Factory.bvsmulo` preserves `denoteBoolTermAux` semantics. -/
theorem Factory.bvsmulo_correct {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    ∃ p, denoteBoolTermAux (Factory.bvsmulo t₁ t₂) = some p ∧
         (p ↔ BitVec.smulOverflow x y = true) := by
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
  · refine ⟨_, ?_, Iff.rfl⟩
    simp [denoteBoolTermAux, denoteTerm, hdt₁, hdt₂]

/-! ## eq correctness

We prove correctness for `Factory.eq` in three regimes:
* syntactically equal arguments (Factory returns `true`);
* both arguments are literals with `t₁ ≠ t₂` (Factory returns `false` —
  correct because literals of the same type denote distinct values);
* otherwise (Factory returns `.app .eq [t₁, t₂] .bool`). -/

/-- `Factory.eq` preserves `denoteBoolTermAux` semantics on boolean arguments. -/
theorem Factory.eq_correct_bool {t₁ t₂ : Term} {p₁ p₂ : Prop}
    (h₁ : denoteBoolTermAux t₁ = some p₁) (h₂ : denoteBoolTermAux t₂ = some p₂) :
    ∃ p, denoteBoolTermAux (Factory.eq t₁ t₂) = some p ∧ (p ↔ (p₁ ↔ p₂)) := by
  unfold Factory.eq
  split
  · rename_i heq
    subst heq
    cases denoteBoolTermAux_eq h₁ h₂
    exact ⟨True, rfl, iff_of_true trivial Iff.rfl⟩
  · rename_i hne
    split
    · -- Both literals, t₁ ≠ t₂: Factory returns `false`, must show `¬ (p₁ ↔ p₂)`.
      rename_i hlit
      simp [Bool.and_eq_true] at hlit
      obtain ⟨hl₁, hl₂⟩ := hlit
      obtain ⟨b₁, ht₁, hbp₁⟩ := denoteBoolTermAux_literal_form h₁ hl₁
      obtain ⟨b₂, ht₂, hbp₂⟩ := denoteBoolTermAux_literal_form h₂ hl₂
      refine ⟨False, rfl, iff_of_false not_false ?_⟩
      -- t₁ = .prim (.bool b₁), t₂ = .prim (.bool b₂), t₁ ≠ t₂, so b₁ ≠ b₂
      have hbne : b₁ ≠ b₂ := by
        intro heq; apply hne; rw [ht₁, ht₂, heq]
      intro hiff
      -- hbp₁ : p₁ ↔ b₁ = true, hbp₂ : p₂ ↔ b₂ = true
      -- hiff : p₁ ↔ p₂ contradicts b₁ ≠ b₂.
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
        refine ⟨f₁ tdi₀ = f₂ tdi₀, ?_, ?_⟩
        · simp only [denoteBoolTermAux, denoteTerm, Option.pure_def, Option.bind_eq_bind,
                     Option.bind_some, hdt₁, hdt₂, denoteTerms, chainable, chainable.go]
          rfl
        · constructor
          · intro heq; rw [show p₁ = f₁ tdi₀ from (propext hiff₁).symm,
                            show p₂ = f₂ tdi₀ from (propext hiff₂).symm, heq]
          · intro hiff
            rw [propext hiff₁, propext hiff₂] at *
            exact propext hiff

/-- `Factory.eq` preserves `denoteBoolTermAux` semantics on integer arguments. -/
theorem Factory.eq_correct_int {t₁ t₂ : Term} {n₁ n₂ : Int}
    (h₁ : denoteIntTermAux t₁ = some n₁) (h₂ : denoteIntTermAux t₂ = some n₂) :
    ∃ p, denoteBoolTermAux (Factory.eq t₁ t₂) = some p ∧ (p ↔ n₁ = n₂) := by
  unfold Factory.eq
  split
  · rename_i heq
    subst heq
    cases Option.some.inj (h₁.symm.trans h₂)
    exact ⟨True, rfl, iff_of_true trivial rfl⟩
  · rename_i hne
    split
    · -- Both literals, t₁ ≠ t₂: Factory returns `false`, must show `n₁ ≠ n₂`.
      rename_i hlit
      simp [Bool.and_eq_true] at hlit
      obtain ⟨hl₁, hl₂⟩ := hlit
      have ht₁ := denoteIntTermAux_literal_form h₁ hl₁
      have ht₂ := denoteIntTermAux_literal_form h₂ hl₂
      refine ⟨False, rfl, iff_of_false not_false ?_⟩
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
        refine ⟨f₁ tdi₀ = f₂ tdi₀, ?_, Iff.rfl⟩
        simp only [denoteBoolTermAux, denoteTerm, Option.pure_def, Option.bind_eq_bind,
                   Option.bind_some, hdt₁, hdt₂, denoteTerms, chainable, chainable.go]
        rfl

/-- `Factory.eq` preserves `denoteBoolTermAux` semantics on bitvector arguments. -/
theorem Factory.eq_correct_bv {n : Nat} {t₁ t₂ : Term} {x y : BitVec n}
    (h₁ : denoteBVTermAux n t₁ = some x) (h₂ : denoteBVTermAux n t₂ = some y) :
    ∃ p, denoteBoolTermAux (Factory.eq t₁ t₂) = some p ∧ (p ↔ x = y) := by
  unfold Factory.eq
  split
  · rename_i heq
    subst heq
    cases Option.some.inj (h₁.symm.trans h₂)
    exact ⟨True, rfl, iff_of_true trivial rfl⟩
  · rename_i hne
    split
    · -- Both literals, t₁ ≠ t₂: Factory returns `false`, must show `x ≠ y`.
      rename_i hlit
      simp [Bool.and_eq_true] at hlit
      obtain ⟨hl₁, hl₂⟩ := hlit
      have ht₁ := denoteBVTermAux_literal_form h₁ hl₁
      have ht₂ := denoteBVTermAux_literal_form h₂ hl₂
      refine ⟨False, rfl, iff_of_false not_false ?_⟩
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
        refine ⟨f₁ tdi₀ = f₂ tdi₀, ?_, Iff.rfl⟩
        simp only [denoteBoolTermAux, denoteTerm, Option.pure_def, Option.bind_eq_bind,
                   Option.bind_some, hdt₁, hdt₂, denoteTerms, chainable, chainable.go]
        rfl

/-- `Factory.eq` preserves `denoteBoolTermAux` semantics on string arguments. -/
theorem Factory.eq_correct_string {t₁ t₂ : Term} {s₁ s₂ : String}
    (h₁ : denoteStringTermAux t₁ = some s₁) (h₂ : denoteStringTermAux t₂ = some s₂) :
    ∃ p, denoteBoolTermAux (Factory.eq t₁ t₂) = some p ∧ (p ↔ s₁ = s₂) := by
  unfold Factory.eq
  split
  · rename_i heq
    subst heq
    cases Option.some.inj (h₁.symm.trans h₂)
    exact ⟨True, rfl, iff_of_true trivial rfl⟩
  · rename_i hne
    split
    · -- Both literals, t₁ ≠ t₂: Factory returns `false`, must show `s₁ ≠ s₂`.
      rename_i hlit
      simp [Bool.and_eq_true] at hlit
      obtain ⟨hl₁, hl₂⟩ := hlit
      have ht₁ := denoteStringTermAux_literal_form h₁ hl₁
      have ht₂ := denoteStringTermAux_literal_form h₂ hl₂
      refine ⟨False, rfl, iff_of_false not_false ?_⟩
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
        refine ⟨f₁ tdi₀ = f₂ tdi₀, ?_, Iff.rfl⟩
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
    ∃ p, denoteBoolTermAux (Factory.ite t₁ t₂ t₃) = some p ∧
         (p ↔ (if p₁ then p₂ else p₃)) := by
  unfold Factory.ite
  split
  · rename_i hcond
    rcases or_decide_true hcond with ht | heq
    · subst ht
      simp only [denoteBoolTermAux, denoteTerm, ↓reduceIte, Option.pure_def,
                 Option.some.injEq, eq_iff_iff, true_iff] at h₁
      exact ⟨p₂, h₂, by simp [if_pos h₁]⟩
    · subst heq
      cases denoteBoolTermAux_eq h₂ h₃
      refine ⟨p₂, h₂, ?_⟩
      by_cases hp₁ : p₁ <;> simp [hp₁]
  · split
    · rename_i _ hf; subst hf
      simp only [denoteBoolTermAux, denoteTerm, Bool.false_eq_true, ↓reduceIte,
                 Option.pure_def, Option.some.injEq, eq_iff_iff, false_iff] at h₁
      exact ⟨p₃, h₃, by rw [if_neg h₁]⟩
    · split
      · exfalso
        -- t₂ = .some t₂' case; but denote of `.some` has option type, not bool
        simp only [denoteBoolTermAux, denoteTerm] at h₂
        split at h₂
        · rename_i heq
          rcases hd : denoteTerm {} _ with _ | ⟨ty', _, _⟩ <;> rw [hd] at heq <;> simp at heq
        · simp_all
      · obtain ⟨f₁, hdt₁, hiff₁⟩ := denoteBoolTermAux_extract h₁
        obtain ⟨f₂, hdt₂, hiff₂⟩ := denoteBoolTermAux_extract h₂
        obtain ⟨f₃, hdt₃, hiff₃⟩ := denoteBoolTermAux_extract h₃
        refine ⟨(if f₁ tdi₀ then f₂ tdi₀ else f₃ tdi₀), ?_, ?_⟩
        · simp only [denoteBoolTermAux, denoteTerm, Option.pure_def, Option.bind_eq_bind,
                     Option.bind_some, hdt₁, hdt₂, hdt₃]
          rfl
        · by_cases hp₁ : p₁
          · rw [if_pos hp₁]
            simp only [if_pos (hiff₁.mpr hp₁)]; exact hiff₂
          · rw [if_neg hp₁]
            simp only [if_neg (fun h => hp₁ (hiff₁.mp h))]; exact hiff₃

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
        · rw [if_pos hp₁]; congr 1; simp [if_pos (hiff₁.mpr hp₁)]
        · rw [if_neg hp₁]; congr 1; simp [if_neg (fun h => hp₁ (hiff₁.mp h))]

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
  · -- t is not a literal .prim (.bitvec ...); Factory dispatches on t.typeOf
    -- Factory returns `.app (.zero_extend n) [t] (.bitvec (n + m))`
    grind [denoteBVTermAux, denoteTerm, Option.pure_def, Option.bind_eq_bind]

/-! ## Factory.app correctness (UF) -/

/-- `Factory.app` for a UF is a no-op wrapper: it produces exactly the term
    `.app (.uf f) ts f.out`, so its denotation agrees with the direct term
    in any context. -/
theorem Factory.app_uf_correct (ctx : Context) (f : UF) (ts : List Term) :
    denoteTerm ctx (Factory.app (.uf f) ts) = denoteTerm ctx (.app (.uf f) ts f.out) :=
  rfl

/-! ## Factory.quant correctness

`Factory.quant qk x ty tr e` is semantically equivalent to `.quant qk [⟨x, ty⟩] tr e`.
The Factory rewrites nested same-kind quantifiers into a single flat binder list,
which is sound because `denoteTerm` ignores triggers and treats a nested quantifier
of the same kind as a flat one via `buildQuant`'s recursive structure. -/

/-- For same-kind quantifiers, flattening one nested binder into the outer binder
    list is semantically a no-op: `.quant qk ([v] ++ args2) tr' e2` denotes the same
    as `.quant qk [v] tr (.quant qk args2 tr2 e2)`.

Proof approach: unfold `denoteTerm` on both sides to expose the two `.quant`
branches. The LHS has a single `denoteFunSort (v :: args2)` check plus a
`denoteTerm` call on `e2` in the context `args2.reverse ++ v :: ctx.tctx.vs`.
The RHS has an outer `denoteFunSort [v]` check (which reduces to
`denoteSort v.ty`) plus an inner recursive `.quant` denotation that checks
`denoteFunSort args2` and denotes `e2` in the same context. The isSome
conditions agree (by `denoteFunSort`'s cons-unfolding), and when both succeed
the produced `TermDenoteResult`s are equal by `buildQuant`'s recursion:
`buildQuant (v :: vs) ... = bindVar v ctx (buildQuant vs ...)`. -/
private theorem denoteFunSort_singleton_of_cons' (sctx : SortContext) (v : TermVar)
    (args2 : List TermVar)
    (h : (denoteFunSort sctx (v :: args2) (.prim .bool)).isSome) :
    (denoteFunSort sctx [v] (.prim .bool)).isSome :=
  isSome_denoteFunSortCons (denoteFunSortCons_isSome h).left
    (isSome_denoteFunSortNil (denoteSortOut_isSome_of_denoteFunSort_isSome h))

set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
private theorem quant_bind_forall_eq (ctx : Context) (v : TermVar) (args2 : List TermVar) (e2 : Term)
    (hCons : (denoteFunSort ctx.sctx (v :: args2) (.prim .bool)).isSome)
    (hSingle : (denoteFunSort ctx.sctx [v] (.prim .bool)).isSome)
    (hArgs : (denoteFunSort ctx.sctx args2 (.prim .bool)).isSome)
    (h1 : (v :: args2).reverse ++ ctx.tctx.vs = (args2.reverse ++ [v]) ++ ctx.tctx.vs)
    (h2 : args2.reverse ++ (v :: ctx.tctx.vs) = (args2.reverse ++ [v]) ++ ctx.tctx.vs) :
    ((denoteTerm ⟨ctx.sctx, ⟨(args2.reverse ++ [v]) ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ e2).bind
      (fun r : TermDenoteResult _ => match r with
      | ⟨.prim .bool, _, tFt⟩ => some (⟨.prim .bool, rfl, buildForall ctx (v :: args2) hCons (h1 ▸ tFt)⟩ : TermDenoteResult ctx)
      | _ => none)) =
    ((denoteTerm ⟨ctx.sctx, ⟨(args2.reverse ++ [v]) ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ e2).bind
      (fun y : TermDenoteResult _ => (match y with
          | ⟨.prim .bool, _, tFt⟩ => some (⟨.prim .bool, rfl, buildForall ⟨ctx.sctx, ⟨v :: ctx.tctx.vs, ctx.tctx.ufs⟩⟩ args2 hArgs (h2 ▸ tFt)⟩ : TermDenoteResult _)
          | _ => none).bind
        (fun r : TermDenoteResult _ => match r with
          | ⟨.prim .bool, _, inner⟩ => some (⟨.prim .bool, rfl, buildForall ctx [v] hSingle inner⟩ : TermDenoteResult ctx)
          | _ => none))) := by
  congr 1; funext r; obtain ⟨ty, hp, res⟩ := r
  cases ty with
  | prim p =>
    cases p <;> simp [Option.bind]
    rw [buildForall_cons]; grind
  | option => simp [Option.bind]
  | constr => simp [Option.bind]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
private theorem quant_bind_exists_eq (ctx : Context) (v : TermVar) (args2 : List TermVar) (e2 : Term)
    (hCons : (denoteFunSort ctx.sctx (v :: args2) (.prim .bool)).isSome)
    (hSingle : (denoteFunSort ctx.sctx [v] (.prim .bool)).isSome)
    (hArgs : (denoteFunSort ctx.sctx args2 (.prim .bool)).isSome)
    (h1 : (v :: args2).reverse ++ ctx.tctx.vs = (args2.reverse ++ [v]) ++ ctx.tctx.vs)
    (h2 : args2.reverse ++ (v :: ctx.tctx.vs) = (args2.reverse ++ [v]) ++ ctx.tctx.vs) :
    ((denoteTerm ⟨ctx.sctx, ⟨(args2.reverse ++ [v]) ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ e2).bind
      (fun r : TermDenoteResult _ => match r with
      | ⟨.prim .bool, _, tFt⟩ => some (⟨.prim .bool, rfl, buildExists ctx (v :: args2) hCons (h1 ▸ tFt)⟩ : TermDenoteResult ctx)
      | _ => none)) =
    ((denoteTerm ⟨ctx.sctx, ⟨(args2.reverse ++ [v]) ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ e2).bind
      (fun y : TermDenoteResult _ => (match y with
          | ⟨.prim .bool, _, tFt⟩ => some (⟨.prim .bool, rfl, buildExists ⟨ctx.sctx, ⟨v :: ctx.tctx.vs, ctx.tctx.ufs⟩⟩ args2 hArgs (h2 ▸ tFt)⟩ : TermDenoteResult _)
          | _ => none).bind
        (fun r : TermDenoteResult _ => match r with
          | ⟨.prim .bool, _, inner⟩ => some (⟨.prim .bool, rfl, buildExists ctx [v] hSingle inner⟩ : TermDenoteResult ctx)
          | _ => none))) := by
  congr 1; funext r; obtain ⟨ty, hp, res⟩ := r
  cases ty with
  | prim p =>
    cases p <;> simp [Option.bind]
    rw [buildExists_cons]; grind
  | option => simp [Option.bind]
  | constr => simp [Option.bind]


/-- `Factory.quant` preserves the denotation of the corresponding direct `.quant` term. -/
theorem Factory.quant_correct (ctx : Context) (qk : QuantifierKind)
    (x : String) (ty : TermType) (tr e : Term) :
    denoteTerm ctx (Factory.quant qk x ty tr e) =
      denoteTerm ctx (.quant qk [⟨x, ty⟩] tr e) := by
  unfold Factory.quant
  split
  · -- e = .quant qk2 args2 tr2 e2
    rename_i qk2 args2 tr2 e2
    split
    · -- Coalescing case: qk = qk2 ∧ isSimpleTrigger tr
      rename_i hcond
      simp [Bool.and_eq_true] at hcond
      obtain ⟨hqk, _⟩ := hcond
      subst hqk
      -- The result is `.quant qk ([⟨x,ty⟩] ++ args2) coalescedTrigger e2`.
      -- Reduce to the coalescing lemma (triggers are irrelevant).
      exact denoteTerm_quant_coalesce ctx qk ⟨x, ty⟩ args2 tr _ tr2 e2
    · rfl
  · rfl

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
