/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.DL.SMT.DenoteTyped
public import Strata.DL.SMT.DenoteTypedProps
import all Strata.DL.SMT.DenoteTyped
import all Strata.DL.SMT.DenoteTypedProps
public import Strata.DL.SMT.Factory
import all Strata.DL.SMT.Factory

/-!
# SMT Factory-function correctness (against `Term.denoteTyped`)

Smart constructors in `Strata.SMT.Factory` (`Factory.quant`, the arithmetic normalizers, …) perform
value-level rewrites — e.g. `Factory.quant` COALESCES nested same-kind quantifiers into a single
multi-binder `.quant`, since SMT-LIB binds many variables at once. Each such rewrite must be shown
denotationally transparent.

`DL/SMT/FactoryCorrect.lean` already proves these against PRODUCTION's `denoteTerm`. This file is the
analog against the restricted typed semantics `Term.denoteTyped` — the semantics the encoder-refactor
soundness (`TranslateSound`) targets. Same spirit, different denotation.

With the `Term.quant` trigger representation `List (List Term)`, `Factory.quant`'s coalescing is
trigger-preserving: it only fires when the OUTER trigger is empty (`isSimpleTrigger tr = tr.isEmpty`),
and keeps the inner trigger `tr2` as the merged binder's trigger. So the merged and naive-nested forms
carry the SAME `wfTriggers` obligations, and `Factory.quant_typeCheck` holds in full.

Currently: `Factory.quant` (the only smart constructor `translate` uses at a binder). More can be added
as the verified subset grows.

Key results: `Factory_eq_typeCheck`, `Factory_ite_typeCheck`, `Factory.quant_correct`,
`Factory.quant_typeCheck`.
-/

open Strata.SMT Std
open Strata.SMT.DenoteTyped
variable {σ : SortInterp} {𝒜 : ArrayTheory}

namespace Strata.SMT.DenoteTyped

/-! ## `Factory.eq` / `Factory.ite` type-check characterization -/

/-- When the operands are syntactically equal, `Factory.eq` reduces to the `true` literal. -/
theorem Factory_eq_true_form {t1 t2 : Term} (hc : t1 = t2) :
    Factory.eq t1 t2 = Term.prim (.bool true) := by
  unfold Factory.eq; rw [if_pos hc]

/-- For distinct literal operands, `Factory.eq` reduces to the `false` literal. -/
theorem Factory_eq_false_form {t1 t2 : Term} (hc : t1 ≠ t2)
    (hlit : (t1.isLiteral && t2.isLiteral) = true) :
    Factory.eq t1 t2 = Term.prim (.bool false) := by
  unfold Factory.eq; rw [if_neg hc, if_pos hlit]

/-- For distinct, non-literal, non-option operands, `Factory.eq` builds the `.core .eq` application. -/
theorem Factory_eq_app_form {t1 t2 : Term} (hc : t1 ≠ t2)
    (hlit : ¬ (t1.isLiteral && t2.isLiteral) = true)
    (hs1 : (∀ a, t1 ≠ .some a) ∧ (∀ ty, t1 ≠ .none ty))
    (hs2 : (∀ a, t2 ≠ .some a) ∧ (∀ ty, t2 ≠ .none ty)) :
    Factory.eq t1 t2 = Term.app (.core .eq) [t1, t2] .bool := by
  unfold Factory.eq; rw [if_neg hc, if_neg hlit]
  cases t1 <;> cases t2 <;>
    first
    | rfl
    | (exact absurd rfl (hs1.1 _))
    | (exact absurd rfl (hs1.2 _))
    | (exact absurd rfl (hs2.1 _))
    | (exact absurd rfl (hs2.2 _))

/-- When the condition is `true` (or both branches coincide), `Factory.ite` reduces to the then-branch. -/
theorem Factory_ite_t2_form {t1 t2 t3 : Term}
    (hcond : (decide (t1 = (true : Term)) || decide (t2 = t3)) = true) :
    Factory.ite t1 t2 t3 = t2 := by
  unfold Factory.ite; rw [if_pos hcond]

/-- When the condition is `false` (and the branches differ), `Factory.ite` reduces to the else-branch. -/
theorem Factory_ite_t3_form {t1 t2 t3 : Term}
    (hcond : ¬ (decide (t1 = (true : Term)) || decide (t2 = t3)) = true)
    (hf : t1 = (false : Term)) :
    Factory.ite t1 t2 t3 = t3 := by
  unfold Factory.ite; rw [if_neg hcond, if_pos hf]

/-- For a non-constant condition with distinct branches, `Factory.ite` builds the `.core .ite`
    application. -/
theorem Factory_ite_app_form {t1 t2 t3 : Term}
    (hcond : ¬ (decide (t1 = (true : Term)) || decide (t2 = t3)) = true)
    (hf : t1 ≠ (false : Term))
    (hs2 : (∀ a, t2 ≠ .some a) ∧ (∀ ty, t2 ≠ .none ty)) :
    Factory.ite t1 t2 t3 = Term.app (.core .ite) [t1, t2, t3] t2.typeOf := by
  unfold Factory.ite; rw [if_neg hcond, if_neg hf]
  cases t2 <;> cases t3 <;>
    first
    | rfl
    | (exact absurd rfl (hs2.1 _))

/-- `Factory.eq` at base operands type-checks to `.bool`. -/
theorem Factory_eq_typeCheck {ufs : UFCtx} {bvs : TermVarCtx} {t1 t2 : Term} {smtτ' : TermType}
    (hb : TermType.isBase smtτ' = true)
    (h1 : Term.typeCheck ⟨[], ufs, bvs⟩ t1 = .ok smtτ')
    (h2 : Term.typeCheck ⟨[], ufs, bvs⟩ t2 = .ok smtτ') :
    Term.typeCheck ⟨[], ufs, bvs⟩ (Factory.eq t1 t2) = .ok .bool := by
  have hns1 := not_someNone_of_base hb h1
  have hns2 := not_someNone_of_base hb h2
  by_cases hc : t1 = t2
  · rw [Factory_eq_true_form hc]; simp [Term.typeCheck, TermPrim.typeOf, TermType.isBase]
  · by_cases hlit : (t1.isLiteral && t2.isLiteral) = true
    · rw [Factory_eq_false_form hc hlit]; simp [Term.typeCheck, TermPrim.typeOf, TermType.isBase]
    · rw [Factory_eq_app_form hc hlit hns1 hns2]
      simp [Term.typeCheck, h1, h2, bind, Except.bind]

/-- `Factory.ite` at base branches type-checks to the branch sort. -/
theorem Factory_ite_typeCheck {ufs : UFCtx} {bvs : TermVarCtx} {t1 t2 t3 : Term} {smtτ' : TermType}
    (hb : TermType.isBase smtτ' = true)
    (h1 : Term.typeCheck ⟨[], ufs, bvs⟩ t1 = .ok .bool)
    (h2 : Term.typeCheck ⟨[], ufs, bvs⟩ t2 = .ok smtτ')
    (h3 : Term.typeCheck ⟨[], ufs, bvs⟩ t3 = .ok smtτ') :
    Term.typeCheck ⟨[], ufs, bvs⟩ (Factory.ite t1 t2 t3) = .ok smtτ' := by
  have hns2 := not_someNone_of_base hb h2
  by_cases hcond : (decide (t1 = (true : Term)) || decide (t2 = t3)) = true
  · rw [Factory_ite_t2_form hcond]; exact h2
  · by_cases hf : t1 = (false : Term)
    · rw [Factory_ite_t3_form hcond hf]; exact h3
    · rw [Factory_ite_app_form hcond hf hns2]
      simp [Term.typeCheck, h1, h2, h3, Term.typeOf_of_typeCheck h2, bind, Except.bind]

/-! ## `Factory.quant` correctness: coalescing is denotationally transparent -/

/-- **`Factory.quant` correctness** (against `Term.denoteTyped`): the coalescing smart constructor denotes
    exactly as the naive single-binder wrapper `.quant qk [⟨x,ty⟩] tr e`. Every non-coalescing shape of
    `e` is definitional; when `e` is itself a same-kind quantifier the merged multi-binder is
    denotationally transparent (nested same-kind quantifiers compose). -/
theorem Factory.quant_correct
    {ctx : TypedContext} (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜)
    (divByZero modByZero : Int → Int)
    (qk : Strata.SMT.QuantifierKind) (x : String) (ty : TermType) (tr : List (List Term)) (e : Term)
    {τ : TermType}
    (hF : Term.typeCheck ctx (Factory.quant qk x ty tr e) = .ok τ)
    (hN : Term.typeCheck ctx (.quant qk [⟨x, ty⟩] tr e) = .ok τ) :
    Term.denoteTyped ufInterp env divByZero modByZero (Factory.quant qk x ty tr e) τ hF
      = Term.denoteTyped ufInterp env divByZero modByZero (.quant qk [⟨x, ty⟩] tr e) τ hN := by
  -- Only `e = .quant qk2 args2 tr2 e2` can differ from the naive wrapper; every other shape returns
  -- `.quant qk [⟨x,ty⟩] tr e` verbatim (definitionally).
  match e, hF, hN with
  | .quant qk2 args2 tr2 e2, hF, hN =>
    by_cases hg : (decide (qk = qk2) && Factory.isSimpleTrigger tr) = true
    · -- coalescing fires: merged multi-var binder vs nested single-var binders.
      obtain ⟨hqk, _⟩ := Bool.and_eq_true .. ▸ hg
      have hqk : qk = qk2 := of_decide_eq_true hqk
      subst hqk
      -- `Factory.quant … = .quant qk (⟨x,ty⟩::args2) tr2 e2` (the merged binder keeps the inner trigger).
      have heqt : Factory.quant qk x ty tr (.quant qk args2 tr2 e2)
          = .quant qk ([⟨x, ty⟩] ++ args2) tr2 e2 := by
        show (if (decide (qk = qk) && Factory.isSimpleTrigger tr) = true then _ else _) = _
        rw [if_pos hg]
      -- Move to the merged binder (via `heqt`), then coalesce to the nested naive form.
      rw [Term.denoteTyped_congr heqt hF (heqt ▸ hF)]
      exact Term.denoteTyped_quant_coalesce ufInterp env divByZero modByZero qk x ty tr _ tr2 args2 e2 _ hN
    · -- no coalescing: `Factory.quant … = .quant qk [⟨x,ty⟩] tr e` verbatim.
      have heqt : Factory.quant qk x ty tr (.quant qk2 args2 tr2 e2)
          = .quant qk [⟨x, ty⟩] tr (.quant qk2 args2 tr2 e2) := by
        show (if (decide (qk = qk2) && Factory.isSimpleTrigger tr) = true then _ else _) = _
        rw [if_neg hg]
      exact Term.denoteTyped_congr heqt hF hN
  | .prim _, _, _ => rfl
  | .var _, _, _ => rfl
  | .app _ _ _, _, _ => rfl
  | .none _, _, _ => rfl
  | .some _, _, _ => rfl

/-- **`Factory.quant` type-checking transfer.** `Factory.quant qk x ty tr e` type-checks at `τ` iff the
    naive single-binder wrapper `.quant qk [⟨x,ty⟩] tr e` does. Under the trigger-preserving coalescing
    (fires only when the outer trigger `tr` is empty, and keeps the inner `tr2`), the merged and nested
    forms impose the SAME body/sort/trigger obligations modulo binder-context reassociation. -/
theorem Factory.quant_typeCheck
    {ctx : TypedContext}
    (qk : Strata.SMT.QuantifierKind) (x : String) (ty : TermType) (tr : List (List Term)) (e : Term)
    {τ : TermType} :
    Term.typeCheck ctx (Factory.quant qk x ty tr e) = .ok τ
      ↔ Term.typeCheck ctx (.quant qk [⟨x, ty⟩] tr e) = .ok τ := by
  match e with
  | .quant qk2 args2 tr2 e2 =>
    by_cases hg : (decide (qk = qk2) && Factory.isSimpleTrigger tr) = true
    · -- Coalescing fires. From the guard: `qk = qk2` and the outer trigger is empty (`tr = []`).
      obtain ⟨hqk, htr⟩ := Bool.and_eq_true .. ▸ hg
      have hqk : qk = qk2 := of_decide_eq_true hqk
      subst hqk
      have htr0 : tr = [] := by
        cases tr with
        | nil => rfl
        | cons a l => simp [Factory.isSimpleTrigger] at htr
      subst htr0
      -- `Factory.quant` coalesces to the merged binder, keeping the inner trigger `tr2`.
      have heqF : Factory.quant qk x ty [] (.quant qk args2 tr2 e2)
          = .quant qk ([⟨x, ty⟩] ++ args2) tr2 e2 := by
        show (if (decide (qk = qk) && Factory.isSimpleTrigger ([] : List (List Term))) = true then _ else _) = _
        rw [if_pos hg]
      rw [heqF]
      -- Body context equality: the merged binder's body context equals the nested-inner one (list identity).
      have hctxEq : ({ctx with Γ := ([(⟨x, ty⟩ : TermVar)] ++ args2).reverse ++ ctx.Γ} : TypedContext)
          = {ctx with Γ := args2.reverse ++ ([(⟨x, ty⟩ : TermVar)].reverse ++ ctx.Γ)} := by
        simp [List.append_assoc]
      constructor
      · -- merged ⟹ nested
        intro hM
        obtain ⟨hbody, hall, hwf, hτ⟩ := Term.typeCheck_quant_ok_iff.mp hM
        simp only [List.cons_append, List.nil_append, List.all_cons, Bool.and_eq_true] at hall
        rw [Term.typeCheck_quant_ok_iff]
        refine ⟨?_, ?_, rfl, hτ⟩
        · -- inner quant over `args2` type-checks at the (⟨x,ty⟩-extended) context
          rw [Term.typeCheck_quant_ok_iff]
          exact ⟨hctxEq ▸ hbody, hall.2, hctxEq ▸ hwf, rfl⟩
        · -- `[⟨x,ty⟩]`'s sole sort obligation is `ty`'s, i.e. the head of the merged obligation.
          simpa using hall.1
      · -- nested ⟹ merged
        intro hN
        obtain ⟨hinner, hhead, -, hτ⟩ := Term.typeCheck_quant_ok_iff.mp hN
        obtain ⟨hbody, hargs, hwf, -⟩ := Term.typeCheck_quant_ok_iff.mp hinner
        rw [Term.typeCheck_quant_ok_iff]
        refine ⟨?_, ?_, ?_, hτ⟩
        · rw [hctxEq]; exact hbody
        · simp only [List.cons_append, List.nil_append, List.all_cons, Bool.and_eq_true]
          exact ⟨by simpa using hhead, hargs⟩
        · rw [hctxEq]; exact hwf
    · -- No coalescing: `Factory.quant … = .quant qk [⟨x,ty⟩] tr e` verbatim.
      have heqt : Factory.quant qk x ty tr (.quant qk2 args2 tr2 e2)
          = .quant qk [⟨x, ty⟩] tr (.quant qk2 args2 tr2 e2) := by
        show (if (decide (qk = qk2) && Factory.isSimpleTrigger tr) = true then _ else _) = _
        rw [if_neg hg]
      rw [heqt]
  | .prim _ => exact Iff.rfl
  | .var _ => exact Iff.rfl
  | .app _ _ _ => exact Iff.rfl
  | .none _ => exact Iff.rfl
  | .some _ => exact Iff.rfl

end Strata.SMT.DenoteTyped
