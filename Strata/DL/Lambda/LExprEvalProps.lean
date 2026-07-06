/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.LState
import all Strata.DL.Lambda.LStateProps
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprProps
import Strata.DL.Lambda.Semantics

/-!
## Properties of the Lambda expression evaluator

Key results (organized roughly in the order they appear below):

- `eval_value_isCanonicalValue` — if `eval` returns a `.value _`, the result's
  `.fst` satisfies `isCanonicalValue`.
- `eval_canonical_identity` — if `e` is a canonical value, `eval n F env e = (e, .value true)`
  at any fuel.
- `eval_getVars_subset` — `eval` does not introduce fresh free variables:
  every free variable in the result was already free in the input.
- `eval_env_congr` — `eval` respects environment agreement: two well-formed
  stores that agree on `e`'s free variables produce the same `eval` result.
- `eval_value_true_mono` — one-step fuel monotonicity on fully-reduced results:
  if `eval m F env e = (v, .value true)`, then `eval (m+1) F env e = (v, .value true)`.
  (This is the key property that separates `.value true` from unqualified
  `.value`, which is *not* fuel-monotone.)
- `eval_value_true_add_fuel` / `eval_value_true_deterministic` — iterated
  monotonicity and value-determinism corollaries.
- `evalFully_of_value_true` — if any fuel `m` produces `(v, .value true)`,
  then `evalFully = some v`.  This is the closure that discharges the
  reverse direction of `coreEvaluator_WellFormedSemanticEvalBool` without
  needing an external axiom.
-/

namespace Lambda
open Strata
open Std (ToFormat Format format)

variable {Tbase : LExprParams}
  [DecidableEq Tbase.IDMeta]
  [Inhabited Tbase.IDMeta]
  [Traceable LExpr.EvalProvenance Tbase.Metadata]


/-! ## Part I: Properties of `eval` -/

/-! ### `eval_value_isCanonicalValue`

If `eval n F env e = (_, .value _)`, the `.fst` component satisfies
`isCanonicalValue F _ = true`.  The main theorem `eval_value_isCanonicalValue`
is preceded by per-sub-evaluator helpers (`evalApp_value_isCanonicalValue`,
`evalEq_value_isCanonicalValue`, `evalIte_value_isCanonicalValue`,
`evalCore_value_isCanonicalValue`) that carry the same statement at the
recursive level and are chained together by the top-level induction. -/

section eval_value_isCanonicalValue

/-- Helper: if `evalApp` returns `.value _`, the result is canonical. -/
private theorem evalApp_value_isCanonicalValue
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (e e1 e2 : LExpr Tbase.mono)
    (ih_eval : ∀ e' b, (LExpr.eval n' F env e').snd = .value b →
        LExpr.isCanonicalValue F (LExpr.eval n' F env e').fst = true)
    {b : Bool} (h : (LExpr.evalApp n' F env e e1 e2).snd = .value b) :
    LExpr.isCanonicalValue F (LExpr.evalApp n' F env e e1 e2).fst = true := by
  have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
      p = LExpr.evalApp n' F env e e1 e2 →
      p.snd = .value b → LExpr.isCanonicalValue F p.fst = true := by
    intro p hp hv
    simp only [LExpr.evalApp] at hp
    split at hp
    · -- abs
      rename_i mAbs _prettyName _ty0 body1' _body1'_eq
      split at hp
      · -- eqModuloMeta: (e, .nonvalue)
        subst hp; simp at hv
      · -- not eqModuloMeta
        subst hp
        simp only at hv
        have h_and : ∃ b0, (LExpr.eval n' F env
            (LExpr.subst (fun metaReplacementVar =>
              LExpr.replaceMetadata1
                (LExpr.mergeMetadataForSubst mAbs (LExpr.eval n' F env e2).fst.metadata metaReplacementVar)
                (LExpr.eval n' F env e2).fst) body1')).snd = .value b0 := by
          rcases h_split : (LExpr.eval n' F env _).snd with _ | b0 | _
          · rw [h_split] at hv; simp [LExpr.EvalResult.combineValueFlag] at hv
          · exact ⟨b0, rfl⟩
          · rw [h_split] at hv; simp [LExpr.EvalResult.combineValueFlag] at hv
        obtain ⟨b0, hb0⟩ := h_and
        exact ih_eval _ b0 hb0
    · -- not abs
      split at hp
      · -- eqModuloMeta: (e, .nonvalue)
        subst hp; simp at hv
      · -- not eqModuloMeta
        subst hp
        simp only at hv
        have h_and : ∃ b0, (LExpr.eval n' F env
            (LExpr.app e.metadata (LExpr.eval n' F env e1).fst (LExpr.eval n' F env e2).fst)).snd
              = .value b0 := by
          rcases h_split : (LExpr.eval n' F env _).snd with _ | b0 | _
          · rw [h_split] at hv; simp [LExpr.EvalResult.combineValueFlag] at hv
          · exact ⟨b0, rfl⟩
          · rw [h_split] at hv; simp [LExpr.EvalResult.combineValueFlag] at hv
        obtain ⟨b0, hb0⟩ := h_and
        exact ih_eval _ b0 hb0
  exact key _ rfl h


/-- Helper: if `evalEq` returns `.value _`, the result is canonical. -/
private theorem evalEq_value_isCanonicalValue
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m : Tbase.Metadata) (e1 e2 : LExpr Tbase.mono)
    (_ih_eval : ∀ e' b, (LExpr.eval n' F env e').snd = .value b →
        LExpr.isCanonicalValue F (LExpr.eval n' F env e').fst = true)
    {b : Bool} (h : (LExpr.evalEq n' F env m e1 e2).snd = .value b) :
    LExpr.isCanonicalValue F (LExpr.evalEq n' F env m e1 e2).fst = true := by
  have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
      p = LExpr.evalEq n' F env m e1 e2 →
      p.snd = .value b → LExpr.isCanonicalValue F p.fst = true := by
    intro p hp hv
    simp only [LExpr.evalEq] at hp
    generalize LExpr.eval n' F env e1 = r1 at hp
    generalize LExpr.eval n' F env e2 = r2 at hp
    generalize LExpr.eql F r1.fst r2.fst = eql_res at hp
    cases eql_res with
    | some b0 => subst hp; unfold LExpr.isCanonicalValue; rfl
    | none => subst hp; simp at hv
  exact key _ rfl h


/-- Helper: if `evalIte` returns `.value _`, the result is canonical. -/
private theorem evalIte_value_isCanonicalValue
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m : Tbase.Metadata) (c t f : LExpr Tbase.mono)
    (ih_eval : ∀ e' b, (LExpr.eval n' F env e').snd = .value b →
        LExpr.isCanonicalValue F (LExpr.eval n' F env e').fst = true)
    {b : Bool} (h : (LExpr.evalIte n' F env m c t f).snd = .value b) :
    LExpr.isCanonicalValue F (LExpr.evalIte n' F env m c t f).fst = true := by
  have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
      p = LExpr.evalIte n' F env m c t f →
      p.snd = .value b → LExpr.isCanonicalValue F p.fst = true := by
    intro p hp hv
    simp only [LExpr.evalIte] at hp
    split at hp
    · -- c' = .true
      subst hp
      simp only at hv
      have h_and : ∃ b0, (LExpr.eval n' F env t).snd = .value b0 := by
        rcases h_split : (LExpr.eval n' F env t).snd with _ | b0 | _
        · rw [h_split] at hv; simp [LExpr.EvalResult.combineValueFlag] at hv
        · exact ⟨b0, rfl⟩
        · rw [h_split] at hv; simp [LExpr.EvalResult.combineValueFlag] at hv
      obtain ⟨b0, hb0⟩ := h_and
      exact ih_eval _ b0 hb0
    · -- c' = .false
      subst hp
      simp only at hv
      have h_and : ∃ b0, (LExpr.eval n' F env f).snd = .value b0 := by
        rcases h_split : (LExpr.eval n' F env f).snd with _ | b0 | _
        · rw [h_split] at hv; simp [LExpr.EvalResult.combineValueFlag] at hv
        · exact ⟨b0, rfl⟩
        · rw [h_split] at hv; simp [LExpr.EvalResult.combineValueFlag] at hv
      obtain ⟨b0, hb0⟩ := h_and
      exact ih_eval _ b0 hb0
    · -- c' = other → (.ite ..., .nonvalue)
      subst hp; simp at hv
  exact key _ rfl h


/-- Helper: if `evalCore` returns `.value _`, the result is canonical.
    Requires an IH for `eval` at the same fuel level. -/
private theorem evalCore_value_isCanonicalValue
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    (ih_eval : ∀ e' b, (LExpr.eval n' F env e').snd = .value b →
        LExpr.isCanonicalValue F (LExpr.eval n' F env e').fst = true)
    {b : Bool} (h : (LExpr.evalCore n' F env e).snd = .value b) :
    LExpr.isCanonicalValue F (LExpr.evalCore n' F env e).fst = true := by
  have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
      p = LExpr.evalCore n' F env e →
      p.snd = .value b → LExpr.isCanonicalValue F p.fst = true := by
    intro p hp hv
    cases e with
    | const m c =>
      simp [LExpr.evalCore] at hp; subst hp; unfold LExpr.isCanonicalValue; rfl
    | op m n args =>
      simp [LExpr.evalCore] at hp; subst hp; simp at hv
    | bvar m n =>
      simp [LExpr.evalCore] at hp; subst hp; simp at hv
    | fvar m x ty =>
      simp only [LExpr.evalCore] at hp
      split at hp
      · -- env x = some v
        subst hp
        rename_i v hx
        simp only at hv
        by_cases hcan : LExpr.isCanonicalValue F v = true
        · rw [if_pos hcan]; exact hcan
        · rw [if_neg hcan] at hv; simp at hv
      · -- env x = none
        subst hp; simp at hv
    | abs m n ty body =>
      simp only [LExpr.evalCore] at hp
      subst hp
      simp only at hv
      by_cases hcan : LExpr.isCanonicalValue F (LExpr.substFvarsFromEnv env (.abs m n ty body)) = true
      · rw [if_pos hcan]; exact hcan
      · rw [if_neg hcan] at hv; simp at hv
    | quant m q n ty tr body =>
      simp only [LExpr.evalCore] at hp
      subst hp
      simp only at hv
      by_cases hcan : LExpr.isCanonicalValue F (LExpr.substFvarsFromEnv env (.quant m q n ty tr body)) = true
      · rw [if_pos hcan]; exact hcan
      · rw [if_neg hcan] at hv; simp at hv
    | app m e1 e2 =>
      simp only [LExpr.evalCore] at hp
      subst hp
      exact evalApp_value_isCanonicalValue n' F env _ _ _ ih_eval hv
    | eq m e1 e2 =>
      simp only [LExpr.evalCore] at hp
      subst hp
      exact evalEq_value_isCanonicalValue n' F env _ _ _ ih_eval hv
    | ite m c t f =>
      simp only [LExpr.evalCore] at hp
      subst hp
      exact evalIte_value_isCanonicalValue n' F env _ _ _ _ ih_eval hv
  exact key _ rfl h


/-- If `eval` returns `.value _`, the resulting expression satisfies `isCanonicalValue`. -/
theorem eval_value_isCanonicalValue
    (n : Nat) (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    {b : Bool} (h : (LExpr.eval n F env e).snd = .value b) :
    LExpr.isCanonicalValue F (LExpr.eval n F env e).fst = true := by
  induction n generalizing e b with
  | zero =>
    have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
        p = LExpr.eval 0 F env e →
        p.snd = .value b → LExpr.isCanonicalValue F p.fst = true := by
      intro p hp hv
      simp only [LExpr.eval] at hp
      subst hp
      by_cases hcan : LExpr.isCanonicalValue F e = true
      · rw [if_pos hcan]; exact hcan
      · rw [if_neg hcan] at hv; simp at hv
    exact key _ rfl h
  | succ n' ih =>
    have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
        p = LExpr.eval (n' + 1) F env e →
        p.snd = .value b → LExpr.isCanonicalValue F p.fst = true := by
      intro p hp hv
      simp only [LExpr.eval, LExpr.List_map_fst_map_eval,
        LExpr.List_all_snd_isValueTrue_map_eval, LExpr.combineEvalResValueFlag_eq_pair] at hp
      split at hp
      · -- isCanonicalValue F e = true
        rename_i h_can
        subst hp; exact h_can
      · -- isCanonicalValue F e = false
        rename_i h_not_can
        split at hp
        · -- callOfLFunc = some (op_expr, args, lfunc)
          rename_i op_expr args lfunc h_call
          subst hp
          split
          · -- dite true branch: match computeTypeSubst
            rename_i h_cond
            simp only [h_cond, dite_true] at hv
            split
            · -- computeTypeSubst = some tySubst → (eval n' F env ...).fst
              rename_i tySubst h_subst
              simp only [h_subst] at hv
              generalize h_target : LExpr.substFvarsLifting
                ((lfunc.body.get _).applySubst tySubst)
                (lfunc.inputs.keys.zip (List.map (fun a => (LExpr.eval n' F env a).fst) args)) = target at hv ⊢
              have h_and : ∃ b0, (LExpr.eval n' F env target).snd = .value b0 := by
                rcases h_split : (LExpr.eval n' F env target).snd with _ | b0 | _
                · rw [h_split] at hv; simp [LExpr.EvalResult.combineValueFlag] at hv
                · exact ⟨b0, rfl⟩
                · rw [h_split] at hv; simp [LExpr.EvalResult.combineValueFlag] at hv
              obtain ⟨b0, hb0⟩ := h_and
              exact ih _ hb0
            · -- computeTypeSubst = none → (e, .nonvalue).fst
              rename_i h_subst
              simp only [h_subst] at hv
              exact absurd hv LExpr.EvalResult.noConfusion
          · -- dite false branch: if eval_cond then ... else ...
            rename_i h_not_cond
            rw [dif_neg h_not_cond] at hv
            cases h_fEC : Strata.DL.Util.FuncAttr.findEvalIfConstr lfunc.attr <;>
            cases h_fEV : Strata.DL.Util.FuncAttr.findEvalIfCanonical lfunc.attr <;> (
              simp only [h_fEC, h_fEV] at hv ⊢
              split at hv
              · -- inner if true: match concreteEval ...
                rename_i h_eval_cond
                rw [if_pos h_eval_cond]
                split at hv
                · -- concreteEval = none → (new_e, .nonvalue)
                  rename_i h_ceval
                  exact absurd hv LExpr.EvalResult.noConfusion
                · -- concreteEval = some ceval: match ceval ...
                  rename_i ceval h_ceval
                  split at hv
                  · -- ceval returns some e' → (eval n' F env e').fst
                    rename_i e' h_ceval_res
                    have h_and : ∃ b0, (LExpr.eval n' F env e').snd = .value b0 := by
                      rcases h_split : (LExpr.eval n' F env e').snd with _ | b0 | _
                      · rw [h_split] at hv; simp [LExpr.EvalResult.combineValueFlag] at hv
                      · exact ⟨b0, rfl⟩
                      · rw [h_split] at hv; simp [LExpr.EvalResult.combineValueFlag] at hv
                    obtain ⟨b0, hb0⟩ := h_and
                    exact ih _ hb0
                  · -- ceval returns none → (new_e, .nonvalue)
                    rename_i h_ceval_res
                    exact absurd hv LExpr.EvalResult.noConfusion
              · -- inner if false: (new_e, .nonvalue)
                rename_i h_not_eval_cond
                exact absurd hv LExpr.EvalResult.noConfusion
            )
        · -- callOfLFunc = none → evalCore
          subst hp
          exact evalCore_value_isCanonicalValue n' F env e (fun e' b' h' => ih e' h') hv
    exact key _ rfl h

end eval_value_isCanonicalValue

/-! ### `eval_canonical_identity`

If `e` is canonical (`isCanonicalValue F e = true`), `eval` at any fuel returns
`(e, .value true)`.  A short one-line lemma — no helpers needed. -/

section eval_canonical_identity

/-- If `isCanonicalValue F e = true`, eval returns `(e, .value true)`. -/
theorem eval_canonical_identity
    (n : Nat) (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    (hcan : LExpr.isCanonicalValue F e = true) :
    LExpr.eval n F env e = (e, .value true) := by
  cases n <;> (simp only [LExpr.eval]; rw [if_pos hcan])

end eval_canonical_identity

/-! ### `eval_getVars_subset`

`eval` does not introduce free variables: every free variable in the result
was already free in the input.  Preceded by per-sub-evaluator `getVars_subset`
helpers, chained by induction on fuel. -/

section eval_getVars_subset

/-- `evalIte` does not introduce free variables outside the `.ite`. -/
theorem evalIte_getVars_subset (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m : Tbase.Metadata) (c t f : LExpr Tbase.mono)
    (ih : ∀ e', ∀ z ∈ LExpr.LExpr.getVars (LExpr.eval n' F env e').fst, z ∈ LExpr.LExpr.getVars e')
    (y : Tbase.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars (LExpr.evalIte n' F env m c t f).fst) :
    y ∈ LExpr.LExpr.getVars (LExpr.ite m c t f) := by
  have hvc := ih c; have hvt := ih t; have hvf := ih f
  simp only [LExpr.LExpr.getVars, List.mem_append]
  simp only [LExpr.evalIte] at hy
  split at hy
  · exact Or.inl (Or.inr (hvt y hy))
  · exact Or.inr (hvf y hy)
  · simp only [LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with (h | h) | h
    · exact Or.inl (Or.inl (hvc y h))
    · exact Or.inl (Or.inr (hvt y h))
    · exact Or.inr (hvf y h)

/-- `evalEq` does not introduce free variables outside the `.eq`. -/
theorem evalEq_getVars_subset (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m : Tbase.Metadata) (e1 e2 : LExpr Tbase.mono)
    (ih : ∀ e', ∀ z ∈ LExpr.LExpr.getVars (LExpr.eval n' F env e').fst, z ∈ LExpr.LExpr.getVars e')
    (y : Tbase.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars (LExpr.evalEq n' F env m e1 e2).fst) :
    y ∈ LExpr.LExpr.getVars (LExpr.eq m e1 e2) := by
  have hv1 := ih e1; have hv2 := ih e2
  simp only [LExpr.LExpr.getVars, List.mem_append]
  simp only [LExpr.evalEq] at hy
  split at hy
  · simp [LExpr.LExpr.getVars] at hy
  · simp only [LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with h | h
    · exact Or.inl (hv1 y h)
    · exact Or.inr (hv2 y h)

/-- `evalApp` does not introduce free variables outside the application. -/
theorem evalApp_getVars_subset (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m : Tbase.Metadata) (e1 e2 : LExpr Tbase.mono)
    (ih : ∀ e', ∀ z ∈ LExpr.LExpr.getVars (LExpr.eval n' F env e').fst, z ∈ LExpr.LExpr.getVars e')
    (y : Tbase.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars (LExpr.evalApp n' F env (LExpr.app m e1 e2) e1 e2).fst) :
    y ∈ LExpr.LExpr.getVars (LExpr.app m e1 e2) := by
  have hv1 := ih e1; have hv2 := ih e2
  simp only [LExpr.LExpr.getVars, List.mem_append]
  simp only [LExpr.evalApp] at hy
  split at hy
  · -- abs arm
    rename_i mAbs nm ty0 body1' heq
    split at hy
    · simp only [LExpr.LExpr.getVars, List.mem_append] at hy; exact hy
    · have h1 := ih _ y hy
      simp only [LExpr.subst] at h1
      rcases getVars_substK_mem 0 _ body1' y h1 with hb | ⟨mv, hmv⟩
      · refine Or.inl (hv1 y ?_); rw [heq]; exact hb
      · rw [getVars_replaceMetadata1] at hmv; exact Or.inr (hv2 y hmv)
  · -- default arm
    split at hy
    · simp only [LExpr.LExpr.getVars, List.mem_append] at hy; exact hy
    · have h1 := ih _ y hy
      simp only [LExpr.LExpr.getVars, List.mem_append] at h1
      rcases h1 with h | h
      · exact Or.inl (hv1 y h)
      · exact Or.inr (hv2 y h)

/-- `evalCore` does not introduce free variables. -/
theorem evalCore_getVars_subset (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (henv : ∀ x v, env x = some v → LExpr.LExpr.getVars v = [])
    (e : LExpr Tbase.mono)
    (ih : ∀ e', ∀ z ∈ LExpr.LExpr.getVars (LExpr.eval n' F env e').fst, z ∈ LExpr.LExpr.getVars e')
    (y : Tbase.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars (LExpr.evalCore n' F env e).fst) :
    y ∈ LExpr.LExpr.getVars e := by
  cases e with
  | const _ _ => simp only [LExpr.evalCore] at hy; exact hy
  | op _ _ _ => simp only [LExpr.evalCore] at hy; exact hy
  | bvar _ _ => simp only [LExpr.evalCore] at hy; exact hy
  | fvar m x ty =>
    simp only [LExpr.evalCore] at hy
    cases hv : env x with
    | none => simp only [hv] at hy; exact hy
    | some v => simp only [hv] at hy; rw [henv x v hv] at hy; simp at hy
  | abs m n ty body =>
    simp only [LExpr.evalCore] at hy
    exact getVars_substFvarsFromEnv_mem env henv _ y hy
  | quant m qk n ty tr body =>
    simp only [LExpr.evalCore] at hy
    exact getVars_substFvarsFromEnv_mem env henv _ y hy
  | app m e1 e2 =>
    simp only [LExpr.evalCore] at hy
    exact evalApp_getVars_subset n' F env m e1 e2 ih y hy
  | eq m e1 e2 =>
    simp only [LExpr.evalCore] at hy
    exact evalEq_getVars_subset n' F env m e1 e2 ih y hy
  | ite m c t f =>
    simp only [LExpr.evalCore] at hy
    exact evalIte_getVars_subset n' F env m c t f ih y hy

/-- `eval` does not introduce free variables: every free variable in the result
    was already free in the input.  Requires a well-formed factory, an
    environment mapping to closed expressions, and a `concreteEval` that
    introduces no fresh free variables. -/
theorem eval_getVars_subset
    (hIdent : ∀ a b : Tbase.Identifier, a.name = b.name → a = b)
    (F : @Factory Tbase) (env : Env Tbase) (hWF : FactoryWF F)
    (henv : ∀ x v, env x = some v → LExpr.LExpr.getVars v = [])
    (n : Nat) :
    ∀ (e : LExpr Tbase.mono) (y : Tbase.Identifier),
      y ∈ LExpr.LExpr.getVars (LExpr.eval n F env e).fst → y ∈ LExpr.LExpr.getVars e := by
  induction n with
  | zero => intro e y hy; simp only [LExpr.eval] at hy; exact hy
  | succ n' ih =>
    intro e y hy
    simp only [LExpr.eval, LExpr.List_map_fst_map_eval,
      LExpr.List_all_snd_isValueTrue_map_eval, LExpr.combineEvalResValueFlag_eq_pair] at hy
    revert hy
    split
    · -- canonical: (e, .value)
      intro hy; exact hy
    · split
      · -- factory call
        rename_i op_expr args lfunc h_call
        have h_mem := callOfLFunc_func_mem F _ _ _ lfunc false h_call
        have h_wf := hWF.lfuncs_wf lfunc h_mem
        obtain ⟨mo, no, to, hop_eq, _, h_arity⟩ := callOfLFunc_eq_some h_call
        split
        · -- inline
          rename_i h_cond
          split
          · -- computeTypeSubst = some tySubst → eval n' new_e
            rename_i tySubst h_ts
            intro hy
            have h1 := ih _ y hy
            rcases getVars_substFvarsLifting_mem _ _ y h1 with ⟨hin, hnone⟩ | ⟨k, v, hk, hv⟩
            · exfalso
              rw [getVars_applySubst] at hin
              have hsome : lfunc.body.isSome = true := by
                simp only [Bool.and_eq_true] at h_cond; exact h_cond.1
              have hbody_eq : lfunc.body = some (lfunc.body.get hsome) := by
                simp [Option.some_get]
              have hy_key := lfunc_body_getVars_subset_keys hIdent lfunc h_wf _ hbody_eq y hin
              have h_len : lfunc.inputs.keys.length =
                  (args.map (fun a => (LExpr.eval n' F env a).fst)).length := by
                rw [ListMap.keys_eq_map_fst]; simp [h_arity]
              have h_mem_keys : y ∈ Map.keys (lfunc.inputs.keys.zip
                  (args.map (fun a => (LExpr.eval n' F env a).fst))) := by
                rw [Map.keys_eq_map_fst, List.map_fst_zip (by omega)]
                exact hy_key
              exact Map_find?_ne_none_of_mem_keys _ y h_mem_keys hnone
            · have hv_mem : v ∈ (lfunc.inputs.keys.zip
                  (args.map (fun a => (LExpr.eval n' F env a).fst))).map Prod.snd :=
                Map_find?_some_mem_values _ k v hk
              have hv_args' : v ∈ args.map (fun a => (LExpr.eval n' F env a).fst) :=
                List.mem_map_snd_zip _ _ v hv_mem
              rw [List.mem_map] at hv_args'
              obtain ⟨a, ha_mem, ha_eq⟩ := hv_args'
              have hya : y ∈ LExpr.LExpr.getVars a := by
                apply ih a y; rw [ha_eq]; exact hv
              exact callOfLFunc_getVars_args F e op_expr args lfunc h_call a ha_mem y hya
          · -- computeTypeSubst = none → (e, .nonvalue)
            intro hy; exact hy
        · -- non-inline
          cases h_fEC : Strata.DL.Util.FuncAttr.findEvalIfConstr lfunc.attr <;>
          cases h_fEV : Strata.DL.Util.FuncAttr.findEvalIfCanonical lfunc.attr <;> (
            simp only []
            split
            · -- canonical/constr condition holds
              split
              · -- concreteEval = none → (mkApp, .nonvalue)
                intro hy
                rcases getVars_mkApp_mem _ _ _ y hy with hop | ⟨a, ha_mem, hya⟩
                · rw [hop_eq] at hop; simp [LExpr.LExpr.getVars] at hop
                · rw [List.mem_map] at ha_mem
                  obtain ⟨a0, ha0_mem, ha0_eq⟩ := ha_mem
                  have hya0 : y ∈ LExpr.LExpr.getVars a0 := by
                    apply ih a0 y; rw [ha0_eq]; exact hya
                  exact callOfLFunc_getVars_args F e op_expr args lfunc h_call a0 ha0_mem y hya0
              · -- concreteEval = some ceval
                rename_i ceval h_ce
                split
                · -- ceval succeeds → eval n' e'
                  rename_i e'c h_ceval_eq
                  intro hy
                  have h1 := ih _ y hy
                  have hexists := h_wf.concreteEval_freeVars ceval h_ce _ _ e'c h_ceval_eq y h1
                  obtain ⟨a, ha_mem, hya⟩ := hexists
                  rw [List.mem_map] at ha_mem
                  obtain ⟨a0, ha0_mem, ha0_eq⟩ := ha_mem
                  have hya0 : y ∈ LExpr.LExpr.getVars a0 := by
                    apply ih a0 y; rw [ha0_eq]; exact hya
                  exact callOfLFunc_getVars_args F e op_expr args lfunc h_call a0 ha0_mem y hya0
                · -- ceval fails → (mkApp, .nonvalue)
                  intro hy
                  rcases getVars_mkApp_mem _ _ _ y hy with hop | ⟨a, ha_mem, hya⟩
                  · rw [hop_eq] at hop; simp [LExpr.LExpr.getVars] at hop
                  · rw [List.mem_map] at ha_mem
                    obtain ⟨a0, ha0_mem, ha0_eq⟩ := ha_mem
                    have hya0 : y ∈ LExpr.LExpr.getVars a0 := by
                      apply ih a0 y; rw [ha0_eq]; exact hya
                    exact callOfLFunc_getVars_args F e op_expr args lfunc h_call a0 ha0_mem y hya0
            · -- symbolic args → (mkApp, .nonvalue)
              intro hy
              rcases getVars_mkApp_mem _ _ _ y hy with hop | ⟨a, ha_mem, hya⟩
              · rw [hop_eq] at hop; simp [LExpr.LExpr.getVars] at hop
              · rw [List.mem_map] at ha_mem
                obtain ⟨a0, ha0_mem, ha0_eq⟩ := ha_mem
                have hya0 : y ∈ LExpr.LExpr.getVars a0 := by
                  apply ih a0 y; rw [ha0_eq]; exact hya
                exact callOfLFunc_getVars_args F e op_expr args lfunc h_call a0 ha0_mem y hya0
          )
      · -- evalCore
        rename_i h_nocall
        intro hy
        exact evalCore_getVars_subset n' F env henv e ih y hy

end eval_getVars_subset

/-! ### `eval_env_congr`

`eval` respects environment agreement: if two well-formed stores agree on
`e`'s free variables, the two `eval` calls produce the same result.  Preceded
by per-sub-evaluator `env_congr` helpers. -/

section eval_env_congr

/-- `evalIte` respects environment agreement. -/
theorem evalIte_env_congr (n' : Nat) (F : @Factory Tbase) (env₁ env₂ : Env Tbase)
    (m : Tbase.Metadata) (c t f : LExpr Tbase.mono)
    (ih_congr : ∀ e', (∀ x ∈ LExpr.LExpr.getVars e', env₁ x = env₂ x) →
      LExpr.eval n' F env₁ e' = LExpr.eval n' F env₂ e')
    (hag : ∀ x ∈ LExpr.LExpr.getVars (LExpr.ite m c t f), env₁ x = env₂ x) :
    LExpr.evalIte n' F env₁ m c t f = LExpr.evalIte n' F env₂ m c t f := by
  have hc := ih_congr c (fun x hx => hag x (by
    simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl (Or.inl hx)))
  have ht := ih_congr t (fun x hx => hag x (by
    simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl (Or.inr hx)))
  have hf := ih_congr f (fun x hx => hag x (by
    simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hx))
  simp only [LExpr.evalIte, hc, ht, hf]

/-- `evalEq` respects environment agreement. -/
theorem evalEq_env_congr (n' : Nat) (F : @Factory Tbase) (env₁ env₂ : Env Tbase)
    (m : Tbase.Metadata) (e1 e2 : LExpr Tbase.mono)
    (ih_congr : ∀ e', (∀ x ∈ LExpr.LExpr.getVars e', env₁ x = env₂ x) →
      LExpr.eval n' F env₁ e' = LExpr.eval n' F env₂ e')
    (hag : ∀ x ∈ LExpr.LExpr.getVars (LExpr.eq m e1 e2), env₁ x = env₂ x) :
    LExpr.evalEq n' F env₁ m e1 e2 = LExpr.evalEq n' F env₂ m e1 e2 := by
  have he1 := ih_congr e1 (fun x hx => hag x (by
    simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hx))
  have he2 := ih_congr e2 (fun x hx => hag x (by
    simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hx))
  simp only [LExpr.evalEq, he1, he2]

/-- `evalApp` respects environment agreement. -/
theorem evalApp_env_congr
    (hIdent : ∀ a b : Tbase.Identifier, a.name = b.name → a = b)
    (F : @Factory Tbase) (env₁ env₂ : Env Tbase) (hWF : FactoryWF F)
    (henv₂ : ∀ x v, env₂ x = some v → LExpr.LExpr.getVars v = [])
    (n' : Nat) (m : Tbase.Metadata) (e1 e2 : LExpr Tbase.mono)
    (ih_congr : ∀ e', (∀ x ∈ LExpr.LExpr.getVars e', env₁ x = env₂ x) →
      LExpr.eval n' F env₁ e' = LExpr.eval n' F env₂ e')
    (hag : ∀ x ∈ LExpr.LExpr.getVars (LExpr.app m e1 e2), env₁ x = env₂ x) :
    LExpr.evalApp n' F env₁ (LExpr.app m e1 e2) e1 e2 =
    LExpr.evalApp n' F env₂ (LExpr.app m e1 e2) e1 e2 := by
  have he1 := ih_congr e1 (fun x hx => hag x (by
    simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hx))
  have he2 := ih_congr e2 (fun x hx => hag x (by
    simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hx))
  simp only [LExpr.evalApp, he1, he2]
  split
  · -- abs arm
    rename_i mAbs nm ty0 body1' heq
    split
    · rfl
    · have h_ih : LExpr.eval n' F env₁
          (LExpr.subst (fun metaReplacementVar =>
            LExpr.replaceMetadata1
              (LExpr.mergeMetadataForSubst mAbs (LExpr.eval n' F env₂ e2).fst.metadata metaReplacementVar)
              (LExpr.eval n' F env₂ e2).fst) body1')
          = LExpr.eval n' F env₂
          (LExpr.subst (fun metaReplacementVar =>
            LExpr.replaceMetadata1
              (LExpr.mergeMetadataForSubst mAbs (LExpr.eval n' F env₂ e2).fst.metadata metaReplacementVar)
              (LExpr.eval n' F env₂ e2).fst) body1') := by
        apply ih_congr
        intro x hx
        simp only [LExpr.subst] at hx
        rcases getVars_substK_mem 0 _ body1' x hx with hb | ⟨mv, hmv⟩
        · have hx1 : x ∈ LExpr.LExpr.getVars e1 := by
            apply eval_getVars_subset hIdent F env₂ hWF henv₂ n' e1 x; rw [heq]; exact hb
          exact hag x (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hx1)
        · rw [getVars_replaceMetadata1] at hmv
          have hx2 : x ∈ LExpr.LExpr.getVars e2 :=
            eval_getVars_subset hIdent F env₂ hWF henv₂ n' e2 x hmv
          exact hag x (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hx2)
      rw [h_ih]
  · -- default arm
    split
    · rfl
    · have h_ih : LExpr.eval n' F env₁
          (LExpr.app (LExpr.app m e1 e2).metadata (LExpr.eval n' F env₂ e1).fst (LExpr.eval n' F env₂ e2).fst)
          = LExpr.eval n' F env₂
          (LExpr.app (LExpr.app m e1 e2).metadata (LExpr.eval n' F env₂ e1).fst (LExpr.eval n' F env₂ e2).fst) := by
        apply ih_congr
        intro x hx
        simp only [LExpr.LExpr.getVars, List.mem_append] at hx
        rcases hx with h | h
        · have hx1 : x ∈ LExpr.LExpr.getVars e1 :=
            eval_getVars_subset hIdent F env₂ hWF henv₂ n' e1 x h
          exact hag x (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hx1)
        · have hx2 : x ∈ LExpr.LExpr.getVars e2 :=
            eval_getVars_subset hIdent F env₂ hWF henv₂ n' e2 x h
          exact hag x (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hx2)
      rw [h_ih]

/-- `evalCore` respects environment agreement. -/
theorem evalCore_env_congr
    (hIdent : ∀ a b : Tbase.Identifier, a.name = b.name → a = b)
    (F : @Factory Tbase) (env₁ env₂ : Env Tbase) (hWF : FactoryWF F)
    (henv₂ : ∀ x v, env₂ x = some v → LExpr.LExpr.getVars v = [])
    (n' : Nat) (e : LExpr Tbase.mono)
    (ih_congr : ∀ e', (∀ x ∈ LExpr.LExpr.getVars e', env₁ x = env₂ x) →
      LExpr.eval n' F env₁ e' = LExpr.eval n' F env₂ e')
    (hag : ∀ x ∈ LExpr.LExpr.getVars e, env₁ x = env₂ x) :
    LExpr.evalCore n' F env₁ e = LExpr.evalCore n' F env₂ e := by
  cases e with
  | const _ _ => simp only [LExpr.evalCore]
  | op _ _ _ => simp only [LExpr.evalCore]
  | bvar _ _ => simp only [LExpr.evalCore]
  | fvar m x ty =>
    simp only [LExpr.evalCore]
    rw [hag x (by simp [LExpr.LExpr.getVars])]
  | abs m n ty body =>
    simp only [LExpr.evalCore]
    rw [substFvarsFromEnv_env_congr env₁ env₂ (LExpr.abs m n ty body) hag]
  | quant m qk n ty tr body =>
    simp only [LExpr.evalCore]
    rw [substFvarsFromEnv_env_congr env₁ env₂ (LExpr.quant m qk n ty tr body) hag]
  | app m e1 e2 =>
    simp only [LExpr.evalCore]
    exact evalApp_env_congr hIdent F env₁ env₂ hWF henv₂ n' m e1 e2 ih_congr hag
  | eq m e1 e2 =>
    simp only [LExpr.evalCore]
    exact evalEq_env_congr n' F env₁ env₂ m e1 e2 ih_congr hag
  | ite m c t f =>
    simp only [LExpr.evalCore]
    exact evalIte_env_congr n' F env₁ env₂ m c t f ih_congr hag

/-- `eval` respects store agreement on free variables: if two stores agree on
    all free variables of an expression, `eval` produces the same result.
    Requires a well-formed factory, environments mapping only to closed
    expressions, identifiers determined by their name, and a `concreteEval`
    introducing no fresh free variables. -/
theorem eval_env_congr
    (hIdent : ∀ a b : Tbase.Identifier, a.name = b.name → a = b)
    (n : Nat) (F : @Factory Tbase) (env₁ env₂ : Env Tbase) (hWF : FactoryWF F)
    (henv₂ : ∀ x v, env₂ x = some v → LExpr.LExpr.getVars v = [])
    (e : LExpr Tbase.mono)
    (hagree : ∀ x ∈ LExpr.LExpr.getVars e, env₁ x = env₂ x) :
    LExpr.eval n F env₁ e = LExpr.eval n F env₂ e := by
  suffices H : ∀ (n : Nat) (e : LExpr Tbase.mono),
      (∀ x ∈ LExpr.LExpr.getVars e, env₁ x = env₂ x) →
      LExpr.eval n F env₁ e = LExpr.eval n F env₂ e from H n e hagree
  intro n
  induction n with
  | zero => intro e hag; simp only [LExpr.eval]
  | succ n' ih =>
    intro e hag
    simp only [LExpr.eval, LExpr.List_map_fst_map_eval,
      LExpr.List_all_snd_isValueTrue_map_eval, LExpr.combineEvalResValueFlag_eq_pair]
    split
    · rfl
    · split
      · -- callOfLFunc = some
        rename_i op_expr args lfunc h_call
        have h_mem := callOfLFunc_func_mem F _ _ _ lfunc false h_call
        have h_wf := hWF.lfuncs_wf lfunc h_mem
        obtain ⟨mo, no, to, hop_eq, _, h_arity⟩ := callOfLFunc_eq_some h_call
        have hmap : (args.map (fun a => (LExpr.eval n' F env₁ a).fst)) =
            (args.map (fun a => (LExpr.eval n' F env₂ a).fst)) := by
          apply List.map_congr_left
          intro a ha
          have hae : LExpr.eval n' F env₁ a = LExpr.eval n' F env₂ a := by
            apply ih a
            intro x hx
            exact hag x (callOfLFunc_getVars_args F e op_expr args lfunc h_call a ha x hx)
          rw [hae]
        simp only [hmap]
        -- The argsAllFull expression depends on `env`, so it's not automatically
        -- unified.  We need to establish it separately.
        have h_argsFull : (args.all fun a => (LExpr.eval n' F env₁ a).snd.isValueTrue) =
                          (args.all fun a => (LExpr.eval n' F env₂ a).snd.isValueTrue) := by
          have h_all_mem : ∀ a ∈ args, LExpr.eval n' F env₁ a = LExpr.eval n' F env₂ a := by
            intro a ha
            apply ih a
            intro x hx
            exact hag x (callOfLFunc_getVars_args F e op_expr args lfunc h_call a ha x hx)
          have h_aux : ∀ (l : List (LExpr Tbase.mono)),
              (∀ a ∈ l, LExpr.eval n' F env₁ a = LExpr.eval n' F env₂ a) →
              (l.all fun a => (LExpr.eval n' F env₁ a).snd.isValueTrue) =
              (l.all fun a => (LExpr.eval n' F env₂ a).snd.isValueTrue) := by
            intro l hl
            induction l with
            | nil => rfl
            | cons a as ih_as =>
              simp only [List.all_cons]
              have h_a : LExpr.eval n' F env₁ a = LExpr.eval n' F env₂ a :=
                hl a (by simp)
              rw [h_a]
              have h_rest : ∀ a' ∈ as, LExpr.eval n' F env₁ a' = LExpr.eval n' F env₂ a' :=
                fun a' ha' => hl a' (by simp [ha'])
              rw [ih_as h_rest]
          exact h_aux args h_all_mem
        simp only [h_argsFull]
        split
        · -- inline
          rename_i h_cond
          split
          · -- computeTypeSubst some → eval env new_e
            rename_i tySubst h_ts
            generalize h_new_e :
              LExpr.substFvarsLifting
                ((lfunc.body.get (by simp only [Bool.and_eq_true] at h_cond; exact h_cond.1)).applySubst tySubst)
                (lfunc.inputs.keys.zip
                  (List.map (fun a => (LExpr.eval n' F env₂ a).fst) args)) = new_e
            have h_ih_new : LExpr.eval n' F env₁ new_e = LExpr.eval n' F env₂ new_e := by
              apply ih
              intro x hx
              rw [← h_new_e] at hx
              rcases getVars_substFvarsLifting_mem _ _ x hx with ⟨hin, hnone⟩ | ⟨k, v, hk, hv⟩
              · exfalso
                rw [getVars_applySubst] at hin
                have hsome : lfunc.body.isSome = true := by
                  simp only [Bool.and_eq_true] at h_cond; exact h_cond.1
                have hbody_eq : lfunc.body = some (lfunc.body.get hsome) := by
                  simp [Option.some_get]
                have hy_key := lfunc_body_getVars_subset_keys hIdent lfunc h_wf _ hbody_eq x hin
                have h_len : lfunc.inputs.keys.length =
                    (args.map (fun a => (LExpr.eval n' F env₂ a).fst)).length := by
                  rw [ListMap.keys_eq_map_fst]; simp [h_arity]
                have h_mem_keys : x ∈ Map.keys (lfunc.inputs.keys.zip
                    (args.map (fun a => (LExpr.eval n' F env₂ a).fst))) := by
                  rw [Map.keys_eq_map_fst, List.map_fst_zip (by omega)]
                  exact hy_key
                exact Map_find?_ne_none_of_mem_keys _ x h_mem_keys hnone
              · have hv_mem := Map_find?_some_mem_values _ k v hk
                have hv_args' := List.mem_map_snd_zip _ _ v hv_mem
                rw [List.mem_map] at hv_args'
                obtain ⟨a, ha_mem, ha_eq⟩ := hv_args'
                have hxa : x ∈ LExpr.LExpr.getVars a := by
                  apply eval_getVars_subset hIdent F env₂ hWF henv₂ n' a x
                  rw [ha_eq]; exact hv
                exact hag x (callOfLFunc_getVars_args F e op_expr args lfunc h_call a ha_mem x hxa)
            rw [h_ih_new]
          · -- computeTypeSubst none
            rfl
        · -- non-inline
          cases h_fEC : Strata.DL.Util.FuncAttr.findEvalIfConstr lfunc.attr <;>
          cases h_fEV : Strata.DL.Util.FuncAttr.findEvalIfCanonical lfunc.attr <;> (
            simp only []
            split
            · -- canonical/constr cond holds
              split
              · -- concreteEval none
                rfl
              · -- concreteEval some ceval
                rename_i ceval h_ce
                split
                · -- ceval succeeds → eval env e'
                  rename_i e'c h_ceval_eq
                  have h_ih_new : LExpr.eval n' F env₁ e'c = LExpr.eval n' F env₂ e'c := by
                    apply ih
                    intro x hx
                    have hexists := h_wf.concreteEval_freeVars ceval h_ce _ _ e'c h_ceval_eq x hx
                    obtain ⟨a, ha_mem, hxa'⟩ := hexists
                    rw [List.mem_map] at ha_mem
                    obtain ⟨a0, ha0_mem, ha0_eq⟩ := ha_mem
                    have hxa : x ∈ LExpr.LExpr.getVars a0 := by
                      apply eval_getVars_subset hIdent F env₂ hWF henv₂ n' a0 x
                      rw [ha0_eq]; exact hxa'
                    exact hag x (callOfLFunc_getVars_args F e op_expr args lfunc h_call a0 ha0_mem x hxa)
                  rw [h_ih_new]
                · -- ceval fails
                  rfl
            · -- symbolic args
              rfl
          )
      · -- callOfLFunc none → evalCore
        rename_i h_nocall
        exact evalCore_env_congr hIdent F env₁ env₂ hWF henv₂ n' e ih hag

end eval_env_congr

/-! ## Part II: Properties of `LExpr.evalFullyAux` and `LExpr.evalFully`

`evalFully` is defined via `evalFullyAux`, which incrementally increases the
fuel handed to `eval` (starting from `0`), always re-evaluating the *original*
`e`, until the result becomes `.value true`. -/

/-! ### Relation between `evalFullyAux` and `eval`. -/

section evalFullyAux

/-- **Forward characterization.** If `evalFullyAux` starting at `fuel` returns
    `some v`, then there is a least fuel `n ≥ fuel` at which `eval` yields exactly
    `(v, .value true)` — "least" in the sense that no fuel in `[fuel, n)` yields a
    `.value true`. -/
theorem evalFullyAux_some_exists
    (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono) (fuel : Nat)
    (v : LExpr Tbase.mono) (h : LExpr.evalFullyAux F env e fuel = some v) :
    ∃ n, fuel ≤ n ∧ LExpr.eval n F env e = (v, .value true) ∧
      ∀ k, fuel ≤ k → k < n → (LExpr.eval k F env e).snd ≠ LExpr.EvalResult.value true := by
  refine LExpr.evalFullyAux.partial_correctness F env e
    (motive := fun fuel v => ∃ n, fuel ≤ n ∧ LExpr.eval n F env e = (v, .value true) ∧
      ∀ k, fuel ≤ k → k < n → (LExpr.eval k F env e).snd ≠ LExpr.EvalResult.value true)
    ?_ fuel v h
  intro g ih fuel r hbody
  rcases hev : LExpr.eval fuel F env e with ⟨e', res⟩
  rw [hev] at hbody
  cases res with
  | value b =>
    cases b with
    | true =>
      simp only [Option.some.injEq] at hbody
      subst hbody
      exact ⟨fuel, Nat.le_refl _, hev, fun k hk1 hk2 => absurd hk2 (by omega)⟩
    | false =>
      simp only at hbody
      obtain ⟨n, hn1, hn2, hn3⟩ := ih (fuel + 1) r hbody
      refine ⟨n, by omega, hn2, ?_⟩
      intro k hk1 hk2
      rcases Nat.lt_or_ge k (fuel + 1) with hk | hk
      · have : k = fuel := by omega
        subst this; rw [hev]; exact fun hc => by cases hc
      · exact hn3 k hk hk2
  | nonvalue =>
    simp only at hbody
    obtain ⟨n, hn1, hn2, hn3⟩ := ih (fuel + 1) r hbody
    refine ⟨n, by omega, hn2, ?_⟩
    intro k hk1 hk2
    rcases Nat.lt_or_ge k (fuel + 1) with hk | hk
    · have : k = fuel := by omega
      subst this; rw [hev]; exact fun hc => by cases hc
    · exact hn3 k hk hk2
  | outOfFuel =>
    simp only at hbody
    obtain ⟨n, hn1, hn2, hn3⟩ := ih (fuel + 1) r hbody
    refine ⟨n, by omega, hn2, ?_⟩
    intro k hk1 hk2
    rcases Nat.lt_or_ge k (fuel + 1) with hk | hk
    · have : k = fuel := by omega
      subst this; rw [hev]; exact fun hc => by cases hc
    · exact hn3 k hk hk2

/-- **Backward characterization.** If `eval n` yields `(v, .value true)` and no fuel in
    `[fuel, n)` yields a `.value true`, then `evalFullyAux` starting at `fuel` returns
    `some v`. -/
theorem evalFullyAux_of_eval
    (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    (n : Nat) (v : LExpr Tbase.mono)
    (hn : LExpr.eval n F env e = (v, .value true)) (fuel : Nat) (hfuel : fuel ≤ n)
    (hlt : ∀ k, fuel ≤ k → k < n → (LExpr.eval k F env e).snd ≠ LExpr.EvalResult.value true) :
    LExpr.evalFullyAux F env e fuel = some v := by
  obtain ⟨d, hd⟩ : ∃ d, n = fuel + d := ⟨n - fuel, by omega⟩
  clear hfuel
  induction d generalizing fuel with
  | zero =>
    have hfn : fuel = n := by omega
    subst hfn
    rw [LExpr.evalFullyAux.eq_def, hn]
  | succ d ih =>
    rw [LExpr.evalFullyAux.eq_def]
    have hfuel_lt : fuel < n := by omega
    have hne : (LExpr.eval fuel F env e).snd ≠ LExpr.EvalResult.value true :=
      hlt fuel (Nat.le_refl _) hfuel_lt
    rcases hev : LExpr.eval fuel F env e with ⟨e', res⟩
    have hres : res ≠ LExpr.EvalResult.value true := by rw [hev] at hne; exact hne
    cases res with
    | value b =>
      cases b with
      | true => exact absurd rfl hres
      | false =>
        simp only
        exact ih (fuel + 1) (fun k hk1 hk2 => hlt k (by omega) hk2) (by omega)
    | nonvalue =>
      simp only
      exact ih (fuel + 1) (fun k hk1 hk2 => hlt k (by omega) hk2) (by omega)
    | outOfFuel =>
      simp only
      exact ih (fuel + 1) (fun k hk1 hk2 => hlt k (by omega) hk2) (by omega)

/-- If no fuel `≥ fuel` ever yields a `.value true`, `evalFullyAux` returns `none`. -/
theorem evalFullyAux_none
    (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono) (fuel : Nat)
    (h : ∀ n, fuel ≤ n → (LExpr.eval n F env e).snd ≠ LExpr.EvalResult.value true) :
    LExpr.evalFullyAux F env e fuel = none := by
  cases hres : LExpr.evalFullyAux F env e fuel with
  | none => rfl
  | some v =>
    obtain ⟨n, hn1, hn2, _⟩ := evalFullyAux_some_exists F env e fuel v hres
    have hne := h n hn1
    rw [hn2] at hne
    exact absurd rfl hne

/-- Congruence of `evalFullyAux` in the environment: if `eval` agrees at every
    fuel, then so does `evalFullyAux`. -/
theorem evalFullyAux_congr
    (F : @Factory Tbase) (env₁ env₂ : Env Tbase) (e : LExpr Tbase.mono) (fuel : Nat)
    (hagree : ∀ k, LExpr.eval k F env₁ e = LExpr.eval k F env₂ e) :
    LExpr.evalFullyAux F env₁ e fuel = LExpr.evalFullyAux F env₂ e fuel := by
  cases h1 : LExpr.evalFullyAux F env₁ e fuel with
  | some v =>
    obtain ⟨n, hle, hn, hlt⟩ := evalFullyAux_some_exists F env₁ e fuel v h1
    symm
    apply evalFullyAux_of_eval F env₂ e n v (by rw [← hagree]; exact hn) fuel hle
    intro k hk1 hk2; rw [← hagree]; exact hlt k hk1 hk2
  | none =>
    cases h2 : LExpr.evalFullyAux F env₂ e fuel with
    | none => rfl
    | some v =>
      obtain ⟨n, hle, hn, hlt⟩ := evalFullyAux_some_exists F env₂ e fuel v h2
      have hcontra : LExpr.evalFullyAux F env₁ e fuel = some v :=
        evalFullyAux_of_eval F env₁ e n v (by rw [hagree]; exact hn) fuel hle
          (fun k hk1 hk2 => by rw [hagree]; exact hlt k hk1 hk2)
      rw [h1] at hcontra; exact absurd hcontra (by simp)

end evalFullyAux

/-! ### `evalFully` suite

The fuel-free `evalFully = evalFullyAux 0` wrapper: existence characterization,
canonical-value outputs, identity on canonical values, `fvar` store lookup,
and environment congruence. -/

section evalFully

/-- **Existence:** `evalFully F env e = some v` iff there is a least fuel `n` at
    which `eval n F env e = (v, .value true)`. -/
theorem evalFully_some_exists
    (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    (v : LExpr Tbase.mono) (heval : LExpr.evalFully F env e = some v) :
    ∃ n, LExpr.eval n F env e = (v, .value true) ∧
      ∀ k, k < n → (LExpr.eval k F env e).snd ≠ LExpr.EvalResult.value true := by
  unfold LExpr.evalFully at heval
  obtain ⟨n, _, hn, hlt⟩ := evalFullyAux_some_exists F env e 0 v heval
  exact ⟨n, hn, fun k hk => hlt k (by omega) hk⟩

/-- `evalFully` only outputs canonical values. -/
theorem evalFully_outputs_canonical
    (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    (v : LExpr Tbase.mono) (heval : LExpr.evalFully F env e = some v) :
    LExpr.isCanonicalValue F v = true := by
  obtain ⟨n, hn, _⟩ := evalFully_some_exists F env e v heval
  have := eval_value_isCanonicalValue n F env e (b := true) (by rw [hn])
  rw [hn] at this; exact this

/-- `evalFully` is the identity on canonical values. -/
theorem evalFully_value_identity
    (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    (hcan : LExpr.isCanonicalValue F e = true) :
    LExpr.evalFully F env e = some e := by
  unfold LExpr.evalFully
  refine evalFullyAux_of_eval F env e 0 e (eval_canonical_identity 0 F env e hcan)
    0 (Nat.le_refl _) (fun k hk1 hk2 => absurd hk2 (by omega))

/-- `evalFully` on a free variable returns the store binding (given a well-formed store). -/
theorem evalFully_fvar_store
    (F : @Factory Tbase) (env : Env Tbase)
    (hwfs : ∀ x v, env x = some v → LExpr.isCanonicalValue F v = true)
    (m : Tbase.Metadata) (v : Tbase.Identifier) (ty : Option Tbase.mono.TypeType) :
    LExpr.evalFully F env (.fvar m v ty) = env v := by
  have hnotcan : LExpr.isCanonicalValue F (.fvar m v ty : LExpr Tbase.mono) = false := by
    apply Bool.eq_false_iff.mpr
    intro hcan
    have h_no_vars := isCanonicalValue_getVars_nil F _ hcan
    simp [LExpr.LExpr.getVars] at h_no_vars
  have eval0 : LExpr.eval 0 F env (.fvar m v ty : LExpr Tbase.mono) =
      (.fvar m v ty, .outOfFuel) := by
    simp only [LExpr.eval]; rw [if_neg (Bool.eq_false_iff.mp hnotcan)]
  have heval_succ : ∀ n', LExpr.eval (n' + 1) F env (.fvar m v ty : LExpr Tbase.mono) =
      LExpr.evalCore n' F env (.fvar m v ty : LExpr Tbase.mono) := by
    intro n'
    unfold LExpr.eval
    rw [if_neg (Bool.eq_false_iff.mp hnotcan)]
    split
    · rename_i heq; rw [callOfLFunc_fvar_none F m v ty] at heq; exact absurd heq (by simp)
    · rfl
  cases hσv : env v with
  | none =>
    -- The store has no binding: `eval` never produces a value, so `evalFully = none`.
    unfold LExpr.evalFully
    apply evalFullyAux_none
    intro n _
    cases n with
    | zero => rw [eval0]; exact fun hc => by cases hc
    | succ n' =>
      rw [heval_succ n']
      unfold LExpr.evalCore
      rw [hσv]
      exact fun hc => by cases hc
  | some val =>
    -- The store binds `v` to a canonical value; `eval 1` already yields it.
    have hval : LExpr.isCanonicalValue F val = true := hwfs v val hσv
    have h1 : LExpr.eval 1 F env (.fvar m v ty : LExpr Tbase.mono) = (val, .value true) := by
      rw [heval_succ 0]; unfold LExpr.evalCore; rw [hσv]; simp [hval]
    unfold LExpr.evalFully
    refine evalFullyAux_of_eval F env _ 1 val h1 0 (by omega) ?_
    intro k _ hk2
    have hk0 : k = 0 := by omega
    subst hk0
    rw [eval0]; exact fun hc => by cases hc

/-- `evalFully` respects store agreement on free variables.
    This is the `WellFormedSemanticEvalExprCongr` property for `evalFully`. -/
theorem evalFully_env_congr
    (hIdent : ∀ a b : Tbase.Identifier, a.name = b.name → a = b)
    (F : @Factory Tbase) (env₁ env₂ : Env Tbase) (hWF : FactoryWF F)
    (henv₂ : ∀ x v, env₂ x = some v → LExpr.LExpr.getVars v = [])
    (e : LExpr Tbase.mono)
    (hagree : ∀ x ∈ LExpr.LExpr.getVars e, env₁ x = env₂ x) :
    LExpr.evalFully F env₁ e = LExpr.evalFully F env₂ e := by
  unfold LExpr.evalFully
  exact evalFullyAux_congr F env₁ env₂ e 0
    (fun k => eval_env_congr hIdent k F env₁ env₂ hWF henv₂ e hagree)

end evalFully

/-! ## Part III: Fuel monotonicity for `.value true` (`eval_value_true_mono`)

If `eval m F env e` produces `(v, .value true)`, then adding fuel does not
disturb the result: `eval (m+1) F env e = (v, .value true)`.
The key insight is that `.value true` propagates through
`EvalResult.combineValueFlag` only when both operands are `.value true`, so a
top-level `.value true` at fuel `n'+1` forces every recursive `eval n' F env _`
call to itself return `.value true`.
-/

section eval_value_true_mono

/-- Small helper: `res.isValueTrue = true` iff `res = .value true`.  Used in
    the mono proofs to convert `.snd.isValueTrue = true` into a `.snd = .value
    true` equation that `ih_eval` accepts as a premise. -/
private theorem isValueTrue_eq_true_iff (res : LExpr.EvalResult) :
    res.isValueTrue = true ↔ res = LExpr.EvalResult.value true := by
  cases res with
  | value b => cases b <;> simp [LExpr.EvalResult.isValueTrue]
  | outOfFuel => simp [LExpr.EvalResult.isValueTrue]
  | nonvalue => simp [LExpr.EvalResult.isValueTrue]

/-- Small helper: `.snd.combineValueFlag b = .value true` iff `.snd = .value true`
    AND `b = true`.  Bundles the two-way conclusions of the andValue analysis. -/
private theorem andValue_eq_valueTrue_iff (res : LExpr.EvalResult) (b : Bool) :
    res.combineValueFlag b = LExpr.EvalResult.value true ↔
      res = LExpr.EvalResult.value true ∧ b = true := by
  cases res with
  | value c => cases c <;> cases b <;> simp [LExpr.EvalResult.combineValueFlag]
  | outOfFuel => simp [LExpr.EvalResult.combineValueFlag]
  | nonvalue => simp [LExpr.EvalResult.combineValueFlag]

/-- `List.all` respects pointwise equality of predicates on the list's elements.
    Used to lift the "all args are `.value true`" fact from fuel `n'` to fuel
    `n'+1` in the mono theorems below. -/
private theorem list_all_congr {α : Type _} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.all_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- Helper: if `evalIte` returns `(v, .value true)`, adding fuel preserves the
    result. -/
private theorem evalIte_value_true_mono
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m : Tbase.Metadata) (c t f v : LExpr Tbase.mono)
    (ih_eval : ∀ e' v', LExpr.eval n' F env e' = (v', .value true) →
        LExpr.eval (n'+1) F env e' = (v', .value true))
    (h : LExpr.evalIte n' F env m c t f = (v, .value true)) :
    LExpr.evalIte (n'+1) F env m c t f = (v, .value true) := by
  simp only [LExpr.evalIte] at h ⊢
  -- One common closer for the `.true` and `.false` branches: identify the
  -- taken branch as `br`, deduce (eval n' c).snd = .value true and
  -- (eval n' br).snd = .value true via andValue-analysis, then lift both
  -- with `ih_eval`.
  have closer : ∀ (br : LExpr Tbase.mono) (mc : Tbase.Metadata)
      (bcond : Bool)
      (_h_c_eq : (LExpr.eval n' F env c).fst = LExpr.const mc (LConst.boolConst bcond))
      (h : ((LExpr.eval n' F env br).fst,
             (LExpr.eval n' F env br).snd.combineValueFlag
               (LExpr.eval n' F env c).snd.isValueTrue) = (v, .value true)),
      LExpr.eval (n'+1) F env c = (LExpr.const mc (LConst.boolConst bcond), .value true) ∧
      LExpr.eval (n'+1) F env br = (v, .value true) := by
    intro br mc bcond h_c_eq h
    have h_fst : (LExpr.eval n' F env br).fst = v := by
      have := congrArg Prod.fst h; simp at this; exact this
    have h_snd_and : (LExpr.eval n' F env br).snd.combineValueFlag
        (LExpr.eval n' F env c).snd.isValueTrue = .value true := by
      have := congrArg Prod.snd h; simp at this; exact this
    have h_and := (andValue_eq_valueTrue_iff _ _).mp h_snd_and
    have h_c_snd : LExpr.eval n' F env c =
        ((LExpr.eval n' F env c).fst, .value true) := by
      rw [← (isValueTrue_eq_true_iff _).mp h_and.2]
    have h_br_snd : LExpr.eval n' F env br =
        ((LExpr.eval n' F env br).fst, .value true) := by rw [← h_and.1]
    refine ⟨?_, ?_⟩
    · have h_c_lift := ih_eval c _ h_c_snd; rw [h_c_eq] at h_c_lift; exact h_c_lift
    · have h_br_lift := ih_eval _ _ h_br_snd; rw [h_fst] at h_br_lift; exact h_br_lift
  split at h
  · rename_i mc h_c_eq
    obtain ⟨h_c_lift, h_t_lift⟩ := closer t mc true h_c_eq h
    rw [h_c_lift, h_t_lift]
    simp [LExpr.EvalResult.combineValueFlag, LExpr.EvalResult.isValueTrue]
  · rename_i mc h_c_eq
    obtain ⟨h_c_lift, h_f_lift⟩ := closer f mc false h_c_eq h
    rw [h_c_lift, h_f_lift]
    simp [LExpr.EvalResult.combineValueFlag, LExpr.EvalResult.isValueTrue]
  · exfalso; have := congrArg Prod.snd h; simp at this

/-- Helper: if `evalEq` returns `(v, .value true)`, adding fuel preserves the
    result. -/
private theorem evalEq_value_true_mono
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m : Tbase.Metadata) (e1 e2 v : LExpr Tbase.mono)
    (ih_eval : ∀ e' v', LExpr.eval n' F env e' = (v', .value true) →
        LExpr.eval (n'+1) F env e' = (v', .value true))
    (h : LExpr.evalEq n' F env m e1 e2 = (v, .value true)) :
    LExpr.evalEq (n'+1) F env m e1 e2 = (v, .value true) := by
  simp only [LExpr.evalEq] at h ⊢
  split at h
  · -- eql = some b
    rename_i b0 h_eql
    have h_fst : LExpr.const m (LConst.boolConst b0) = v := by
      have := congrArg Prod.fst h; simp at this; exact this
    have h_snd_pair : (LExpr.eval n' F env e1).snd.isValueTrue = true ∧
                      (LExpr.eval n' F env e2).snd.isValueTrue = true := by
      have := congrArg Prod.snd h; simp at this; exact this
    have h_e1_snd : LExpr.eval n' F env e1 =
        ((LExpr.eval n' F env e1).fst, .value true) := by
      rw [← (isValueTrue_eq_true_iff _).mp h_snd_pair.1]
    have h_e2_snd : LExpr.eval n' F env e2 =
        ((LExpr.eval n' F env e2).fst, .value true) := by
      rw [← (isValueTrue_eq_true_iff _).mp h_snd_pair.2]
    rw [ih_eval _ _ h_e1_snd, ih_eval _ _ h_e2_snd]
    simp only
    rw [h_eql]
    simp [LExpr.EvalResult.isValueTrue]
    exact h_fst
  · -- eql = none → (.eq, .nonvalue), contradicting .value true
    exfalso
    have := congrArg Prod.snd h; simp at this

/-- Helper: if `evalApp` returns `(v, .value true)`, adding fuel preserves the
    result. -/
private theorem evalApp_value_true_mono
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (e e1 e2 v : LExpr Tbase.mono)
    (ih_eval : ∀ e' v', LExpr.eval n' F env e' = (v', .value true) →
        LExpr.eval (n'+1) F env e' = (v', .value true))
    (h : LExpr.evalApp n' F env e e1 e2 = (v, .value true)) :
    LExpr.evalApp (n'+1) F env e e1 e2 = (v, .value true) := by
  simp only [LExpr.evalApp] at h ⊢
  -- Common closer for the abs and default branches (both share the shape
  -- `((eval n' inner).fst, (eval n' inner).snd.combineValueFlag subsFull) = (v, .value true)`).
  -- It returns lifted equations for `e1`, `e2`, and `inner`.
  have closer : ∀ (inner : LExpr Tbase.mono)
      (h : ((LExpr.eval n' F env inner).fst,
             (LExpr.eval n' F env inner).snd.combineValueFlag
               ((LExpr.eval n' F env e1).snd.isValueTrue &&
                (LExpr.eval n' F env e2).snd.isValueTrue)) = (v, .value true)),
      LExpr.eval (n'+1) F env e1 = ((LExpr.eval n' F env e1).fst, .value true) ∧
      LExpr.eval (n'+1) F env e2 = ((LExpr.eval n' F env e2).fst, .value true) ∧
      LExpr.eval (n'+1) F env inner = (v, .value true) := by
    intro inner h
    have h_fst : (LExpr.eval n' F env inner).fst = v := by
      have := congrArg Prod.fst h; simp at this; exact this
    have h_snd : (LExpr.eval n' F env inner).snd.combineValueFlag
        ((LExpr.eval n' F env e1).snd.isValueTrue &&
         (LExpr.eval n' F env e2).snd.isValueTrue) = .value true := by
      have := congrArg Prod.snd h; simp at this; exact this
    have h_and := (andValue_eq_valueTrue_iff _ _).mp h_snd
    have h_e12 : (LExpr.eval n' F env e1).snd.isValueTrue = true ∧
                 (LExpr.eval n' F env e2).snd.isValueTrue = true := by
      rw [Bool.and_eq_true] at h_and; exact h_and.2
    have h_e1_snd : LExpr.eval n' F env e1 =
        ((LExpr.eval n' F env e1).fst, .value true) := by
      rw [← (isValueTrue_eq_true_iff _).mp h_e12.1]
    have h_e2_snd : LExpr.eval n' F env e2 =
        ((LExpr.eval n' F env e2).fst, .value true) := by
      rw [← (isValueTrue_eq_true_iff _).mp h_e12.2]
    have h_inner_snd : LExpr.eval n' F env inner =
        ((LExpr.eval n' F env inner).fst, .value true) := by rw [← h_and.1]
    refine ⟨ih_eval _ _ h_e1_snd, ih_eval _ _ h_e2_snd, ?_⟩
    have := ih_eval _ _ h_inner_snd; rw [h_fst] at this; exact this
  split at h
  · -- (eval n' e1).fst = .abs mAbs prettyName ty0 body1'
    rename_i mAbs prettyName ty0 body1' h_e1_eq
    split at h
    · -- eqModuloMeta e e' → (e, .nonvalue), contradicts .value true
      exfalso; have := congrArg Prod.snd h; simp at this
    · rename_i h_neq
      obtain ⟨h_e1_lift, h_e2_lift, h_inner_lift⟩ := closer _ h
      rw [h_e1_lift, h_e2_lift]
      rw [h_e1_eq]
      simp only
      rw [if_neg h_neq, h_inner_lift]
      simp [LExpr.EvalResult.isValueTrue, LExpr.EvalResult.combineValueFlag]
  · -- (eval n' e1).fst is not .abs
    rename_i h_e1_not_abs
    split at h
    · exfalso; have := congrArg Prod.snd h; simp at this
    · rename_i h_neq
      obtain ⟨h_e1_lift, h_e2_lift, h_inner_lift⟩ := closer _ h
      rw [h_e1_lift, h_e2_lift]
      split
      · rename_i mAbs' nm' ty' body' h_abs_eq
        exact absurd h_abs_eq (h_e1_not_abs mAbs' nm' ty' body')
      · rename_i h_other
        rw [if_neg h_neq, h_inner_lift]
        simp [LExpr.EvalResult.isValueTrue, LExpr.EvalResult.combineValueFlag]

/-- Helper: if `evalCore` returns `(v, .value true)`, adding fuel preserves the
    result. -/
private theorem evalCore_value_true_mono
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase) (e v : LExpr Tbase.mono)
    (ih_eval : ∀ e' v', LExpr.eval n' F env e' = (v', .value true) →
        LExpr.eval (n'+1) F env e' = (v', .value true))
    (h : LExpr.evalCore n' F env e = (v, .value true)) :
    LExpr.evalCore (n'+1) F env e = (v, .value true) := by
  cases e with
  | const m c =>
    simp only [LExpr.evalCore] at h ⊢; exact h
  | op m n args =>
    simp only [LExpr.evalCore] at h
    exfalso
    have := congrArg Prod.snd h; simp at this
  | bvar m n =>
    simp only [LExpr.evalCore] at h
    exfalso
    have := congrArg Prod.snd h; simp at this
  | fvar m x ty =>
    simp only [LExpr.evalCore] at h ⊢
    grind
  | abs m n ty body =>
    simp only [LExpr.evalCore] at h ⊢
    exact h
  | quant m qk n ty tr body =>
    simp only [LExpr.evalCore] at h ⊢
    exact h
  | app m e1 e2 =>
    simp only [LExpr.evalCore] at h ⊢
    exact evalApp_value_true_mono n' F env _ _ _ _ ih_eval h
  | eq m e1 e2 =>
    simp only [LExpr.evalCore] at h ⊢
    exact evalEq_value_true_mono n' F env _ _ _ _ ih_eval h
  | ite m c t f =>
    simp only [LExpr.evalCore] at h ⊢
    exact evalIte_value_true_mono n' F env _ _ _ _ _ ih_eval h

/-- **Fuel monotonicity for `.value true`.** If `eval m F env e = (v, .value true)`,
    then `eval (m+1) F env e = (v, .value true)`. -/
theorem eval_value_true_mono (F : @Factory Tbase) (env : Env Tbase)
    (m : Nat) (e : LExpr Tbase.mono) (v : LExpr Tbase.mono)
    (h : LExpr.eval m F env e = (v, .value true)) :
    LExpr.eval (m+1) F env e = (v, .value true) := by
  induction m generalizing e v with
  | zero =>
    simp only [LExpr.eval] at h
    by_cases hcan : LExpr.isCanonicalValue F e = true
    · rw [if_pos hcan] at h
      have hfe : v = e := by
        have := congrArg Prod.fst h; simp at this; exact this.symm
      subst hfe
      exact eval_canonical_identity (0 + 1) F env v hcan
    · rw [if_neg hcan] at h
      have := congrArg Prod.snd h; simp at this
  | succ n' ih =>
    -- The inductive step factors two common lemmas: `arg_lift` (each fully-reduced
    -- arg has its eval-result stable across fuel increments), and `args_lift`
    -- (the same lift extended to the whole args list — `.map` and `.all` versions).
    have arg_lift : ∀ a, (LExpr.eval n' F env a).snd.isValueTrue = true →
        LExpr.eval (n'+1) F env a = ((LExpr.eval n' F env a).fst, .value true) := by
      intro a h_ivt
      have h_a_snd : LExpr.eval n' F env a =
          ((LExpr.eval n' F env a).fst, .value true) := by
        rw [← (isValueTrue_eq_true_iff _).mp h_ivt]
      exact ih _ _ h_a_snd
    -- Deduce the "all args fully-reduced" fact from a top-level `.combineValueFlag …`
    -- equation.  This bundles two `rcases` chains that appeared 3× in the old
    -- proof (inline body, ceval, and default).
    have args_from_andValue : ∀ (inner : LExpr Tbase.mono)
        (args : List (LExpr Tbase.mono)),
        (LExpr.eval n' F env inner).snd.combineValueFlag
          (args.all (fun a => (LExpr.eval n' F env a).snd.isValueTrue))
            = LExpr.EvalResult.value true →
        LExpr.eval n' F env inner =
          ((LExpr.eval n' F env inner).fst, .value true) ∧
        (∀ a ∈ args, (LExpr.eval n' F env a).snd.isValueTrue = true) := by
      intro inner args h_snd
      have h_and := (andValue_eq_valueTrue_iff _ _).mp h_snd
      refine ⟨?_, ?_⟩
      · rw [← h_and.1]
      · rw [← List.all_eq_true]; exact h_and.2
    -- Lift the whole args list from fuel n' to fuel n'+1 (both projections).
    have list_lifts : ∀ (args : List (LExpr Tbase.mono))
        (h_all : ∀ a ∈ args, (LExpr.eval n' F env a).snd.isValueTrue = true),
        args.map (fun a => (LExpr.eval (n'+1) F env a).fst) =
          args.map (fun a => (LExpr.eval n' F env a).fst) ∧
        (args.all fun a => (LExpr.eval (n'+1) F env a).snd.isValueTrue) = true := by
      intro args h_all
      refine ⟨?_, ?_⟩
      · apply List.map_congr_left
        intro a ha; rw [arg_lift a (h_all a ha)]
      · rw [List.all_eq_true]
        intro a ha; rw [arg_lift a (h_all a ha)]
        simp [LExpr.EvalResult.isValueTrue]
    -- Now the main analysis: split on `eval (n'+1) F env e`'s outer structure.
    simp only [LExpr.eval] at h
    revert h
    split
    · rename_i hcan; intro h
      have hfe : v = e := by
        have := congrArg Prod.fst h; simp at this; exact this.symm
      subst hfe
      exact eval_canonical_identity (n' + 1 + 1) F env v hcan
    · rename_i h_not_can
      split
      · rename_i op_expr args lfunc h_call
        split
        · -- inline branch
          rename_i h_cond
          have h_body_isSome : lfunc.body.isSome = true := by
            simp only [Bool.and_eq_true] at h_cond; exact h_cond.1
          split
          · -- computeTypeSubst = some tySubst
            rename_i tySubst h_ts
            intro h
            -- `inner` is the substituted body evaluated at fuel n'.
            let inner := LExpr.substFvarsLifting
                ((lfunc.body.get h_body_isSome).applySubst tySubst)
                (lfunc.inputs.keys.zip
                  (List.map (fun a => (LExpr.eval n' F env a).fst) args))
            have h_fst : (LExpr.eval n' F env inner).fst = v := by
              have := congrArg Prod.fst h; simp at this; exact this
            have h_snd_and : (LExpr.eval n' F env inner).snd.combineValueFlag
                (args.all fun a => (LExpr.eval n' F env a).snd.isValueTrue) = .value true := by
              have := congrArg Prod.snd h; simp at this; exact this
            obtain ⟨h_inner_snd, h_argsAllFull⟩ := args_from_andValue inner args h_snd_and
            obtain ⟨h_map_eq', h_argsAllFull_lift⟩ := list_lifts args h_argsAllFull
            have h_new_lift := ih _ _ h_inner_snd
            have h_map_eq'_prod : List.map Prod.fst
                (args.map (fun a => LExpr.eval (n'+1) F env a)) =
                List.map Prod.fst (args.map (fun a => LExpr.eval n' F env a)) := by
              rw [LExpr.List_map_fst_map_eval, LExpr.List_map_fst_map_eval]; exact h_map_eq'
            show LExpr.eval (n'+1+1) F env e = (v, .value true)
            conv => lhs; rw [LExpr.eval]
            rw [if_neg h_not_can, h_call]
            dsimp only
            split
            · rename_i h_cond_lift
              rw [h_map_eq'_prod, h_ts]
              simp only [LExpr.EvalResult.combineValueFlag,
                LExpr.List_map_fst_map_eval, LExpr.List_all_snd_isValueTrue_map_eval, LExpr.combineEvalResValueFlag_eq_pair]
              rw [h_new_lift]
              simp only [h_argsAllFull_lift, h_fst]
              simp
            · rename_i h_cond_lift
              exfalso; apply h_cond_lift; rw [h_map_eq'_prod]; exact h_cond
          · intro h
            exfalso; have := congrArg Prod.snd h; simp at this
        · -- non-inline branch
          rename_i h_cond
          split
          · rename_i h_eval_cond
            split
            · intro h; exfalso; have := congrArg Prod.snd h; simp at this
            · rename_i ceval h_ceval
              split
              · rename_i e' h_ceval_res
                intro h
                have h_fst : (LExpr.eval n' F env e').fst = v := by
                  have := congrArg Prod.fst h; simp at this; exact this
                have h_snd_and : (LExpr.eval n' F env e').snd.combineValueFlag
                    (args.all fun a => (LExpr.eval n' F env a).snd.isValueTrue) = .value true := by
                  have := congrArg Prod.snd h; simp at this; exact this
                obtain ⟨h_e'_snd, h_argsAllFull⟩ := args_from_andValue _ _ h_snd_and
                obtain ⟨h_map_eq, h_argsAllFull_lift⟩ := list_lifts args h_argsAllFull
                have h_map_eq_prod : List.map Prod.fst
                    (args.map (fun a => LExpr.eval (n'+1) F env a)) =
                    List.map Prod.fst (args.map (fun a => LExpr.eval n' F env a)) := by
                  rw [LExpr.List_map_fst_map_eval, LExpr.List_map_fst_map_eval]; exact h_map_eq
                have h_e'_lift := ih _ _ h_e'_snd
                show LExpr.eval (n'+1+1) F env e = (v, .value true)
                conv => lhs; rw [LExpr.eval]
                rw [if_neg h_not_can, h_call]
                dsimp only
                split
                · rename_i h_cond_lift
                  exfalso; apply h_cond; rw [← h_map_eq_prod]; exact h_cond_lift
                · rename_i h_cond_lift
                  simp only [LExpr.List_map_fst_map_eval] at h_ceval_res
                  rw [h_map_eq_prod, if_pos h_eval_cond]
                  simp only [LExpr.List_map_fst_map_eval]
                  rw [h_ceval]
                  dsimp only
                  rw [h_ceval_res]
                  simp only [LExpr.combineEvalResValueFlag_eq_pair]
                  rw [h_e'_lift]
                  simp only [LExpr.EvalResult.combineValueFlag,
                    LExpr.List_all_snd_isValueTrue_map_eval]
                  rw [h_argsAllFull_lift, h_fst]
                  simp
              · intro h; exfalso; have := congrArg Prod.snd h; simp at this
          · intro h; exfalso; have := congrArg Prod.snd h; simp at this
      · rename_i h_nocall
        intro h
        have h_ec := evalCore_value_true_mono n' F env e v
          (fun e' v' hev => ih e' v' hev) h
        simp only [LExpr.eval]
        rw [if_neg h_not_can, h_nocall]
        exact h_ec

end eval_value_true_mono

/-! ### `eval_value_true_add_fuel` and `eval_value_true_deterministic`

Iterating one-step monotonicity gives that adding *any* amount of fuel to a
`.value true` witness preserves it (`eval_value_true_add_fuel`).  The
determinism corollary follows: any two `.value true` witnesses at any fuels
agree on the resulting `.fst`. -/

section eval_value_true_add_fuel

/-- Iterated fuel monotonicity: adding any amount of fuel preserves a `.value true` result. -/
theorem eval_value_true_add_fuel (F : @Factory Tbase) (env : Env Tbase)
    (m k : Nat) (e : LExpr Tbase.mono) (v : LExpr Tbase.mono)
    (h : LExpr.eval m F env e = (v, .value true)) :
    LExpr.eval (m+k) F env e = (v, .value true) := by
  induction k with
  | zero => exact h
  | succ k' ih =>
    have := eval_value_true_mono F env (m + k') e v ih
    -- Rewrite m + (k' + 1) = (m + k') + 1
    have h_eq : m + (k' + 1) = (m + k') + 1 := by omega
    rw [h_eq]
    exact this

/-- Two `.value true` outputs of `eval` at different fuel levels agree on the resulting expression. -/
theorem eval_value_true_deterministic (F : @Factory Tbase) (env : Env Tbase)
    (m k : Nat) (e : LExpr Tbase.mono) (v w : LExpr Tbase.mono)
    (h1 : LExpr.eval m F env e = (v, .value true))
    (h2 : LExpr.eval k F env e = (w, .value true)) : v = w := by
  -- Take the max of m and k and lift both.
  rcases Nat.le_or_ge m k with hle | hge
  · obtain ⟨d, hd⟩ : ∃ d, k = m + d := ⟨k - m, by omega⟩
    subst hd
    have h1' := eval_value_true_add_fuel F env m d e v h1
    rw [h1'] at h2
    have := Prod.mk.inj h2
    exact this.1
  · obtain ⟨d, hd⟩ : ∃ d, m = k + d := ⟨m - k, by omega⟩
    subst hd
    have h2' := eval_value_true_add_fuel F env k d e w h2
    rw [h2'] at h1
    have := Prod.mk.inj h1
    exact this.1.symm

end eval_value_true_add_fuel

/-! ### `evalFully_of_value_true`

If *any* fuel `m` produces `(v, .value true)`, then `evalFully = some v`.
This is the closure that discharges the reverse direction of
`coreEvaluator_WellFormedSemanticEvalBool` without needing an external axiom.
Requires the min-fuel witness lemma `eval_least_fuel_value_true`. -/

section evalFully_of_value_true

/-- Helper: find the least fuel ≤ m that produces `.value true`. -/
private theorem eval_least_fuel_value_true
    (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    (m : Nat) (v : LExpr Tbase.mono) (h : LExpr.eval m F env e = (v, .value true)) :
    ∃ n, n ≤ m ∧ LExpr.eval n F env e = (v, .value true) ∧
      ∀ k, k < n → (LExpr.eval k F env e).snd ≠ .value true := by
  induction m generalizing v with
  | zero =>
    refine ⟨0, Nat.le_refl _, h, ?_⟩
    intro k hk; omega
  | succ m' ih =>
    -- Either eval m' produces .value true (then apply IH), or not (then m'+1 is minimal).
    by_cases hm : ∃ v', LExpr.eval m' F env e = (v', .value true)
    · obtain ⟨v', hv'⟩ := hm
      obtain ⟨n, hn_le, hn_eq, hn_min⟩ := ih v' hv'
      -- v' = v by determinism
      have := eval_value_true_deterministic F env m' (m'+1) e v' v hv' h
      subst this
      exact ⟨n, by omega, hn_eq, hn_min⟩
    · -- eval m' doesn't produce .value true; so m'+1 is minimal at fuel m'+1
      refine ⟨m'+1, Nat.le_refl _, h, ?_⟩
      intro k hk hc
      -- Need to derive contradiction with hm using hc at some k ≤ m'
      -- We know k ≤ m'. By determinism plus add_fuel, eval k = (v, .value true) → eval m' = (v, .value true).
      have hk_le : k ≤ m' := by omega
      obtain ⟨d, hd⟩ : ∃ d, m' = k + d := ⟨m' - k, by omega⟩
      have hp : LExpr.eval k F env e = ((LExpr.eval k F env e).fst, .value true) := by rw [← hc]
      have h_lift := eval_value_true_add_fuel F env k d e (LExpr.eval k F env e).fst hp
      rw [← hd] at h_lift
      exact hm ⟨(LExpr.eval k F env e).fst, h_lift⟩

/-- If some fuel `m` produces `(v, .value true)`, then `evalFully` returns `some v`. -/
theorem evalFully_of_value_true (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    (m : Nat) (v : LExpr Tbase.mono) (h : LExpr.eval m F env e = (v, .value true)) :
    LExpr.evalFully F env e = some v := by
  obtain ⟨n, _, hn_eq, hn_min⟩ := eval_least_fuel_value_true F env e m v h
  unfold LExpr.evalFully
  exact evalFullyAux_of_eval F env e n v hn_eq 0 (Nat.zero_le _)
    (fun k _ hk => hn_min k hk)

end evalFully_of_value_true

end Lambda
