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
  needing an external assumption.
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
                · -- concreteEval = none: the rebuilt call is certified exactly
                  -- when it is canonical
                  rename_i h_ceval
                  split at hv
                  · rename_i h_can_new
                    simpa using h_can_new
                  · simp [LExpr.EvalResult.combineValueFlag] at hv
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
    (F : @Factory Tbase) (env : Env Tbase) (hWF : FactoryWF F) (hClosed : FactoryClosed F)
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
        have h_closed := hClosed.lfuncs_closed lfunc h_mem
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
              have hy_key := lfunc_body_getVars_subset_keys hIdent lfunc h_closed _ hbody_eq y hin
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
    (F : @Factory Tbase) (env₁ env₂ : Env Tbase) (hWF : FactoryWF F) (hClosed : FactoryClosed F)
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
            apply eval_getVars_subset hIdent F env₂ hWF hClosed henv₂ n' e1 x; rw [heq]; exact hb
          exact hag x (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hx1)
        · rw [getVars_replaceMetadata1] at hmv
          have hx2 : x ∈ LExpr.LExpr.getVars e2 :=
            eval_getVars_subset hIdent F env₂ hWF hClosed henv₂ n' e2 x hmv
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
            eval_getVars_subset hIdent F env₂ hWF hClosed henv₂ n' e1 x h
          exact hag x (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hx1)
        · have hx2 : x ∈ LExpr.LExpr.getVars e2 :=
            eval_getVars_subset hIdent F env₂ hWF hClosed henv₂ n' e2 x h
          exact hag x (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hx2)
      rw [h_ih]

/-- `evalCore` respects environment agreement. -/
theorem evalCore_env_congr
    (hIdent : ∀ a b : Tbase.Identifier, a.name = b.name → a = b)
    (F : @Factory Tbase) (env₁ env₂ : Env Tbase) (hWF : FactoryWF F) (hClosed : FactoryClosed F)
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
    exact evalApp_env_congr hIdent F env₁ env₂ hWF hClosed henv₂ n' m e1 e2 ih_congr hag
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
    (n : Nat) (F : @Factory Tbase) (env₁ env₂ : Env Tbase) (hWF : FactoryWF F) (hClosed : FactoryClosed F)
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
        have h_closed := hClosed.lfuncs_closed lfunc h_mem
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
                have hy_key := lfunc_body_getVars_subset_keys hIdent lfunc h_closed _ hbody_eq x hin
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
                  apply eval_getVars_subset hIdent F env₂ hWF hClosed henv₂ n' a x
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
                      apply eval_getVars_subset hIdent F env₂ hWF hClosed henv₂ n' a0 x
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
        exact evalCore_env_congr hIdent F env₁ env₂ hWF hClosed henv₂ n' e ih hag

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
    (F : @Factory Tbase) (env₁ env₂ : Env Tbase) (hWF : FactoryWF F) (hClosed : FactoryClosed F)
    (henv₂ : ∀ x v, env₂ x = some v → LExpr.LExpr.getVars v = [])
    (e : LExpr Tbase.mono)
    (hagree : ∀ x ∈ LExpr.LExpr.getVars e, env₁ x = env₂ x) :
    LExpr.evalFully F env₁ e = LExpr.evalFully F env₂ e := by
  unfold LExpr.evalFully
  exact evalFullyAux_congr F env₁ env₂ e 0
    (fun k => eval_env_congr hIdent k F env₁ env₂ hWF hClosed henv₂ e hagree)

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
theorem isValueTrue_eq_true_iff (res : LExpr.EvalResult) :
    res.isValueTrue = true ↔ res = LExpr.EvalResult.value true := by
  cases res with
  | value b => cases b <;> simp [LExpr.EvalResult.isValueTrue]
  | outOfFuel => simp [LExpr.EvalResult.isValueTrue]
  | nonvalue => simp [LExpr.EvalResult.isValueTrue]

/-- Small helper: `.snd.combineValueFlag b = .value true` iff `.snd = .value true`
    AND `b = true`.  Bundles the two-way conclusions of the andValue analysis. -/
theorem andValue_eq_valueTrue_iff (res : LExpr.EvalResult) (b : Bool) :
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
            · -- concreteEval = none: certified when the rebuilt call is
              -- canonical on fully evaluated arguments
              rename_i h_ceval_none
              intro h
              simp only [LExpr.combineEvalResValueFlag_eq_pair, Prod.mk.injEq] at h
              obtain ⟨h_fst, h_snd⟩ := h
              split at h_snd
              case isFalse =>
                exact absurd h_snd (by simp [LExpr.EvalResult.combineValueFlag])
              rename_i h_can
              have h_argsAllFull :
                  (args.map (fun a => LExpr.eval n' F env a)).all
                    (fun r => r.snd.isValueTrue) = true := by
                simpa [LExpr.EvalResult.combineValueFlag] using h_snd
              obtain ⟨h_map_eq, h_argsAllFull_lift⟩ :=
                list_lifts args (fun a ha =>
                  List.all_eq_true.mp h_argsAllFull _ (List.mem_map_of_mem ha))
              have h_map_eq_prod : List.map Prod.fst
                  (args.map (fun a => LExpr.eval (n'+1) F env a)) =
                  List.map Prod.fst (args.map (fun a => LExpr.eval n' F env a)) := by
                rw [LExpr.List_map_fst_map_eval, LExpr.List_map_fst_map_eval]
                exact h_map_eq
              show LExpr.eval (n'+1+1) F env e = (v, .value true)
              conv => lhs; rw [LExpr.eval]
              rw [if_neg h_not_can, h_call]
              dsimp only
              split
              · rename_i h_cond_lift
                exfalso; apply h_cond; rw [← h_map_eq_prod]; exact h_cond_lift
              · rw [h_map_eq_prod, if_pos h_eval_cond]
                simp only [LExpr.List_map_fst_map_eval]
                rw [h_ceval_none]
                dsimp only
                simp only [LExpr.List_all_snd_isValueTrue_map_eval]
                rw [h_argsAllFull_lift]
                simp only [LExpr.List_map_fst_map_eval] at h_can h_fst
                have h_can_v : LExpr.isCanonicalValue F v = true :=
                  h_fst ▸ h_can
                simp [h_fst, h_can_v, LExpr.EvalResult.combineValueFlag]
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
`coreEvaluator_WellFormedSemanticEvalBool` without needing an external
assumption. Requires the min-fuel witness lemma `eval_least_fuel_value_true`. -/

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

/-! ## Part IV: Store-extension frame for `.value true` (`eval_frame`)

A fully-reduced (`.value true`) evaluation result is preserved when the
environment is extended pointwise (`EnvExtends`).  This is the store-extension
monotonicity the Imperative pipeline needs of the evaluator; it culminates in
`evalFully_mono`.

Contrast with `eval_env_congr` (Part I): that lemma demands the two environments
*agree* on every free variable of `e` (`∀ x ∈ getVars e, env₁ x = env₂ x`).  A
`.value true` evaluation, however, need not read every syntactic free variable —
e.g. an untaken `ite` branch's variables are in `getVars e` yet never consulted,
so they may be undefined in `env` and defined in `env'`.  Such an `(env, env')`
pair satisfies `EnvExtends` but *not* `eval_env_congr`'s agreement premise, so
congruence cannot discharge the pipeline's obligation.  The frame lemma relies
instead on the weaker `EnvExtends`: the `.value true` flag certifies every
variable the evaluation actually read resolved in `env`, and extension leaves
those bindings unchanged, so the result is preserved.
-/

section eval_frame

/-- Frame for `evalIte`: transport a `.value true` result from `env` to `env'`
at the same fuel, given the sub-evaluation transport `ih_eval`. -/
private theorem evalIte_frame
    (n' : Nat) (F : @Factory Tbase) (env env' : Env Tbase)
    (m : Tbase.Metadata) (c t f v : LExpr Tbase.mono)
    (ih_eval : ∀ e' v', LExpr.eval n' F env e' = (v', .value true) →
        LExpr.eval n' F env' e' = (v', .value true))
    (h : LExpr.evalIte n' F env m c t f = (v, .value true)) :
    LExpr.evalIte n' F env' m c t f = (v, .value true) := by
  simp only [LExpr.evalIte] at h ⊢
  have closer : ∀ (br : LExpr Tbase.mono) (mc : Tbase.Metadata)
      (bcond : Bool)
      (_h_c_eq : (LExpr.eval n' F env c).fst = LExpr.const mc (LConst.boolConst bcond))
      (h : ((LExpr.eval n' F env br).fst,
             (LExpr.eval n' F env br).snd.combineValueFlag
               (LExpr.eval n' F env c).snd.isValueTrue) = (v, .value true)),
      LExpr.eval n' F env' c = (LExpr.const mc (LConst.boolConst bcond), .value true) ∧
      LExpr.eval n' F env' br = (v, .value true) := by
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

/-- Frame for `evalEq`. -/
private theorem evalEq_frame
    (n' : Nat) (F : @Factory Tbase) (env env' : Env Tbase)
    (m : Tbase.Metadata) (e1 e2 v : LExpr Tbase.mono)
    (ih_eval : ∀ e' v', LExpr.eval n' F env e' = (v', .value true) →
        LExpr.eval n' F env' e' = (v', .value true))
    (h : LExpr.evalEq n' F env m e1 e2 = (v, .value true)) :
    LExpr.evalEq n' F env' m e1 e2 = (v, .value true) := by
  simp only [LExpr.evalEq] at h ⊢
  split at h
  · rename_i b0 h_eql
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
  · exfalso
    have := congrArg Prod.snd h; simp at this

/-- Frame for `evalApp`. -/
private theorem evalApp_frame
    (n' : Nat) (F : @Factory Tbase) (env env' : Env Tbase)
    (e e1 e2 v : LExpr Tbase.mono)
    (ih_eval : ∀ e' v', LExpr.eval n' F env e' = (v', .value true) →
        LExpr.eval n' F env' e' = (v', .value true))
    (h : LExpr.evalApp n' F env e e1 e2 = (v, .value true)) :
    LExpr.evalApp n' F env' e e1 e2 = (v, .value true) := by
  simp only [LExpr.evalApp] at h ⊢
  have closer : ∀ (inner : LExpr Tbase.mono)
      (h : ((LExpr.eval n' F env inner).fst,
             (LExpr.eval n' F env inner).snd.combineValueFlag
               ((LExpr.eval n' F env e1).snd.isValueTrue &&
                (LExpr.eval n' F env e2).snd.isValueTrue)) = (v, .value true)),
      LExpr.eval n' F env' e1 = ((LExpr.eval n' F env e1).fst, .value true) ∧
      LExpr.eval n' F env' e2 = ((LExpr.eval n' F env e2).fst, .value true) ∧
      LExpr.eval n' F env' inner = (v, .value true) := by
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
  · rename_i mAbs prettyName ty0 body1' h_e1_eq
    split at h
    · exfalso; have := congrArg Prod.snd h; simp at this
    · rename_i h_neq
      obtain ⟨h_e1_lift, h_e2_lift, h_inner_lift⟩ := closer _ h
      rw [h_e1_lift, h_e2_lift]
      rw [h_e1_eq]
      simp only
      rw [if_neg h_neq, h_inner_lift]
      simp [LExpr.EvalResult.isValueTrue, LExpr.EvalResult.combineValueFlag]
  · rename_i h_e1_not_abs
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

/-- Frame for `evalCore`. -/
private theorem evalCore_frame
    (n' : Nat) (F : @Factory Tbase) (env env' : Env Tbase)
    (hext : EnvExtends env env') (e v : LExpr Tbase.mono)
    (ih_eval : ∀ e' v', LExpr.eval n' F env e' = (v', .value true) →
        LExpr.eval n' F env' e' = (v', .value true))
    (h : LExpr.evalCore n' F env e = (v, .value true)) :
    LExpr.evalCore n' F env' e = (v, .value true) := by
  cases e with
  | const m c =>
    simp only [LExpr.evalCore] at h ⊢; exact h
  | op m n args =>
    simp only [LExpr.evalCore] at h
    exfalso; have := congrArg Prod.snd h; simp at this
  | bvar m n =>
    simp only [LExpr.evalCore] at h
    exfalso; have := congrArg Prod.snd h; simp at this
  | fvar m x ty =>
    simp only [LExpr.evalCore] at h ⊢
    cases hxb : env x with
    | none =>
      rw [hxb] at h
      exfalso; have := congrArg Prod.snd h; simp at this
    | some w =>
      rw [hxb] at h
      rw [hext x w hxb]
      exact h
  | abs m n ty body =>
    simp only [LExpr.evalCore] at h ⊢
    rw [Prod.mk.injEq] at h
    obtain ⟨h_fst, h_snd⟩ := h
    split at h_snd
    · rename_i hcan
      have hnil := isCanonicalValue_getVars_nil F _ hcan
      have hag := env_agree_of_subst_getVars_nil env env' hext (LExpr.abs m n ty body) hnil
      have hsub_eq : LExpr.substFvarsFromEnv env' (LExpr.abs m n ty body) =
          LExpr.substFvarsFromEnv env (LExpr.abs m n ty body) :=
        substFvarsFromEnv_env_congr env' env (LExpr.abs m n ty body)
          (fun x hx => (hag x hx).symm)
      rw [hsub_eq, if_pos hcan, h_fst]
    · exact absurd h_snd (by simp)
  | quant m qk n ty tr body =>
    simp only [LExpr.evalCore] at h ⊢
    rw [Prod.mk.injEq] at h
    obtain ⟨h_fst, h_snd⟩ := h
    split at h_snd
    · rename_i hcan
      have hnil := isCanonicalValue_getVars_nil F _ hcan
      have hag := env_agree_of_subst_getVars_nil env env' hext (LExpr.quant m qk n ty tr body) hnil
      have hsub_eq : LExpr.substFvarsFromEnv env' (LExpr.quant m qk n ty tr body) =
          LExpr.substFvarsFromEnv env (LExpr.quant m qk n ty tr body) :=
        substFvarsFromEnv_env_congr env' env (LExpr.quant m qk n ty tr body)
          (fun x hx => (hag x hx).symm)
      rw [hsub_eq, if_pos hcan, h_fst]
    · exact absurd h_snd (by simp)
  | app m e1 e2 =>
    simp only [LExpr.evalCore] at h ⊢
    exact evalApp_frame n' F env env' _ _ _ _ ih_eval h
  | eq m e1 e2 =>
    simp only [LExpr.evalCore] at h ⊢
    exact evalEq_frame n' F env env' _ _ _ _ ih_eval h
  | ite m c t f =>
    simp only [LExpr.evalCore] at h ⊢
    exact evalIte_frame n' F env env' _ _ _ _ _ ih_eval h

/-- **Store-extension frame lemma for `LExpr.eval`.** A fully-reduced result is
preserved under any pointwise extension of the environment.

Unlike `eval_env_congr`, which requires the two environments to agree on *all*
of `e`'s free variables, this lemma only requires `env' ⊇ env` (`EnvExtends`).
The `.value true` result flag certifies that every free variable actually
consulted resolved in `env` — so extension, which cannot disturb an existing
binding, preserves the result even when `env` and `env'` disagree on variables
`eval` never reads (e.g. those under an untaken `ite` branch). -/
theorem eval_frame
    (F : @Factory Tbase) (env env' : Env Tbase) (hext : EnvExtends env env') :
    ∀ (n : Nat) (e v : LExpr Tbase.mono),
      LExpr.eval n F env e = (v, LExpr.EvalResult.value true) →
      LExpr.eval n F env' e = (v, LExpr.EvalResult.value true) := by
  intro n
  induction n with
  | zero =>
    intro e v h
    simp only [LExpr.eval] at h
    by_cases hcan : LExpr.isCanonicalValue F e = true
    · rw [if_pos hcan] at h
      have hfe : v = e := by
        have := congrArg Prod.fst h; simp at this; exact this.symm
      subst hfe
      exact eval_canonical_identity 0 F env' v hcan
    · rw [if_neg hcan] at h
      have := congrArg Prod.snd h; simp at this
  | succ n' ih =>
    intro e v h
    have arg_lift : ∀ a, (LExpr.eval n' F env a).snd.isValueTrue = true →
        LExpr.eval n' F env' a = ((LExpr.eval n' F env a).fst, .value true) := by
      intro a h_ivt
      have h_a_snd : LExpr.eval n' F env a =
          ((LExpr.eval n' F env a).fst, .value true) := by
        rw [← (isValueTrue_eq_true_iff _).mp h_ivt]
      exact ih _ _ h_a_snd
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
    have list_lifts : ∀ (args : List (LExpr Tbase.mono))
        (h_all : ∀ a ∈ args, (LExpr.eval n' F env a).snd.isValueTrue = true),
        args.map (fun a => (LExpr.eval n' F env' a).fst) =
          args.map (fun a => (LExpr.eval n' F env a).fst) ∧
        (args.all fun a => (LExpr.eval n' F env' a).snd.isValueTrue) = true := by
      intro args h_all
      refine ⟨?_, ?_⟩
      · apply List.map_congr_left
        intro a ha; rw [arg_lift a (h_all a ha)]
      · rw [List.all_eq_true]
        intro a ha; rw [arg_lift a (h_all a ha)]
        simp [LExpr.EvalResult.isValueTrue]
    simp only [LExpr.eval] at h
    revert h
    split
    · rename_i hcan; intro h
      have hfe : v = e := by
        have := congrArg Prod.fst h; simp at this; exact this.symm
      subst hfe
      exact eval_canonical_identity (n' + 1) F env' v hcan
    · rename_i h_not_can
      split
      · rename_i op_expr args lfunc h_call
        split
        · -- inline branch
          rename_i h_cond
          have h_body_isSome : lfunc.body.isSome = true := by
            simp only [Bool.and_eq_true] at h_cond; exact h_cond.1
          split
          · rename_i tySubst h_ts
            intro h
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
                (args.map (fun a => LExpr.eval n' F env' a)) =
                List.map Prod.fst (args.map (fun a => LExpr.eval n' F env a)) := by
              rw [LExpr.List_map_fst_map_eval, LExpr.List_map_fst_map_eval]; exact h_map_eq'
            show LExpr.eval (n'+1) F env' e = (v, .value true)
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
            · -- concreteEval = none: certified when the rebuilt call is
              -- canonical on fully evaluated arguments
              rename_i h_ceval_none
              intro h
              simp only [LExpr.combineEvalResValueFlag_eq_pair, Prod.mk.injEq] at h
              obtain ⟨h_fst, h_snd⟩ := h
              split at h_snd
              case isFalse =>
                exact absurd h_snd (by simp [LExpr.EvalResult.combineValueFlag])
              rename_i h_can
              have h_argsAllFull :
                  (args.map (fun a => LExpr.eval n' F env a)).all
                    (fun r => r.snd.isValueTrue) = true := by
                simpa [LExpr.EvalResult.combineValueFlag] using h_snd
              obtain ⟨h_map_eq, h_argsAllFull_lift⟩ :=
                list_lifts args (fun a ha =>
                  List.all_eq_true.mp h_argsAllFull _ (List.mem_map_of_mem ha))
              have h_map_eq_prod : List.map Prod.fst
                  (args.map (fun a => LExpr.eval n' F env' a)) =
                  List.map Prod.fst (args.map (fun a => LExpr.eval n' F env a)) := by
                rw [LExpr.List_map_fst_map_eval, LExpr.List_map_fst_map_eval]
                exact h_map_eq
              show LExpr.eval (n'+1) F env' e = (v, .value true)
              conv => lhs; rw [LExpr.eval]
              rw [if_neg h_not_can, h_call]
              dsimp only
              split
              · rename_i h_cond_lift
                exfalso; apply h_cond; rw [← h_map_eq_prod]; exact h_cond_lift
              · rw [h_map_eq_prod, if_pos h_eval_cond]
                simp only [LExpr.List_map_fst_map_eval]
                rw [h_ceval_none]
                dsimp only
                simp only [LExpr.List_all_snd_isValueTrue_map_eval]
                rw [h_argsAllFull_lift]
                simp only [LExpr.List_map_fst_map_eval] at h_can h_fst
                have h_can_v : LExpr.isCanonicalValue F v = true :=
                  h_fst ▸ h_can
                simp [h_fst, h_can_v, LExpr.EvalResult.combineValueFlag]
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
                    (args.map (fun a => LExpr.eval n' F env' a)) =
                    List.map Prod.fst (args.map (fun a => LExpr.eval n' F env a)) := by
                  rw [LExpr.List_map_fst_map_eval, LExpr.List_map_fst_map_eval]; exact h_map_eq
                have h_e'_lift := ih _ _ h_e'_snd
                show LExpr.eval (n'+1) F env' e = (v, .value true)
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
        have h_ec := evalCore_frame n' F env env' hext e v
          (fun e' v' hev => ih e' v' hev) h
        simp only [LExpr.eval]
        rw [if_neg h_not_can, h_nocall]
        exact h_ec

/-- **Store-extension monotonicity of `LExpr.evalFully`.**  A successful
`evalFully` is preserved when the environment retains every binding it held.
This is the `WellFormedSemanticEvalMono` property for the concrete evaluator. -/
theorem evalFully_mono
    (F : @Factory Tbase) (env env' : Env Tbase) (hext : EnvExtends env env')
    (e v : LExpr Tbase.mono)
    (heval : LExpr.evalFully F env e = some v) :
    LExpr.evalFully F env' e = some v := by
  obtain ⟨n, hn, _⟩ := evalFully_some_exists F env e v heval
  exact evalFully_of_value_true F env' e n v (eval_frame F env env' hext n e v hn)

end eval_frame


/-! ## Invariance under variable substitution (rename commutation)

`evalFully`-level commutation of a variable-only renaming with the store: under
`VarOnly`/`TargetsDefined`, evaluating the renamed expression in the renamed
store agrees with evaluating the original in the pulled-back store.  Consumed by
the call-elimination correctness stack. -/

section rename_commute

/-- Rename map values are all bare free variables. -/
def VarOnly (sm : Map Tbase.Identifier (LExpr Tbase.mono)) : Prop :=
  ∀ k v, sm.find? k = some v → ∃ m x ty, v = .fvar m x ty

/-- Every rename target is defined in the store. -/
def TargetsDefined (σ' : Env Tbase) (sm : Map Tbase.Identifier (LExpr Tbase.mono)) : Prop :=
  ∀ k m x ty, sm.find? k = some (.fvar m x ty) → (σ' x).isSome

/-- Pull the renamed store back along `sm`: read `x` through its rename target. -/
def substStoreExpr (σ' : Env Tbase) (sm : Map Tbase.Identifier (LExpr Tbase.mono)) : Env Tbase :=
  fun x =>
    match sm.find? x with
    | some (.fvar _ y _) => σ' y
    | _ => σ' x

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- Core syntactic composition lemma over `substFvarsAux` (no empty-map guard).
    Substituting a variable-only renaming `sm` and then reading the renamed store
    `σ'` deeply is the same as reading the pulled-back store on the original. -/
theorem substFvarsFromEnv_substFvarsAux
    (σ' : Env Tbase)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (hVar : VarOnly sm) (hTgt : TargetsDefined σ' sm)
    (e : LExpr Tbase.mono) :
    LExpr.substFvarsFromEnv σ' (LExpr.substFvars.substFvarsAux e sm)
      = LExpr.substFvarsFromEnv (substStoreExpr σ' sm) e := by
  induction e with
  | const m c => rfl
  | op m n t => rfl
  | bvar m i => rfl
  | fvar m name ty =>
    simp only [LExpr.substFvars.substFvarsAux, LExpr.substFvarsFromEnv, substStoreExpr]
    cases hf : sm.find? name with
    | none => rfl
    | some to =>
      obtain ⟨m', x, ty', rfl⟩ := hVar name to hf
      have hsome : (σ' x).isSome := hTgt name m' x ty' hf
      simp only [LExpr.substFvarsFromEnv]
      cases hx : σ' x with
      | none => rw [hx] at hsome; simp at hsome
      | some v => rfl
  | abs m n t b ih =>
    simp only [LExpr.substFvars.substFvarsAux, LExpr.substFvarsFromEnv, ih]
  | quant m qk n ty tr b iht ihb =>
    simp only [LExpr.substFvars.substFvarsAux, LExpr.substFvarsFromEnv, iht, ihb]
  | app m f a ihf iha =>
    simp only [LExpr.substFvars.substFvarsAux, LExpr.substFvarsFromEnv, ihf, iha]
  | eq m l r ihl ihr =>
    simp only [LExpr.substFvars.substFvarsAux, LExpr.substFvarsFromEnv, ihl, ihr]
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.substFvars.substFvarsAux, LExpr.substFvarsFromEnv, ihc, iht, ihf]

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
theorem substFvarsFromEnv_substFvars
    (σ' : Env Tbase)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (hVar : VarOnly sm) (hTgt : TargetsDefined σ' sm)
    (e : LExpr Tbase.mono) :
    LExpr.substFvarsFromEnv σ' (LExpr.substFvars e sm)
      = LExpr.substFvarsFromEnv (substStoreExpr σ' sm) e := by
  unfold LExpr.substFvars
  split
  · rename_i hempty
    have : substStoreExpr σ' sm = σ' := by
      funext x
      unfold substStoreExpr
      have : sm.find? x = none := by
        cases sm with
        | nil => rfl
        | cons p rest => simp [Map.isEmpty] at hempty
      rw [this]
    rw [this]
  · exact substFvarsFromEnv_substFvarsAux σ' sm hVar hTgt e

/-! ### Enabling facts for the twisted per-fuel invariant.

The naive per-fuel EQUALITY `eval n σ' (substFvars e sm) = eval n (pullback) e` is
FALSE: at fuel 0, `eval` returns the residual verbatim, so its `.fst` is
`substFvars e sm` (renamed) on the left but `e` on the right. The runs only
converge at the canonical fixpoint. The correct per-fuel invariant is
substFvars-TWISTED:
  `eval n σ' (substFvars e sm) = (substFvars (eval n (pullback) e).fst sm,
                                  (eval n (pullback) e).snd)`.
At the least-fuel `.value true` witness the residual is canonical hence closed, so
`substFvars` collapses to the identity and the two runs return the same value. -/

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- Variable-only renaming preserves the set of free variables' emptiness. -/
theorem getVars_substFvarsAux_nil_iff
    (sm : Map Tbase.Identifier (LExpr Tbase.mono)) (hVar : VarOnly sm)
    (e : LExpr Tbase.mono) :
    LExpr.LExpr.getVars (LExpr.substFvars.substFvarsAux e sm) = [] ↔
      LExpr.LExpr.getVars e = [] := by
  induction e with
  | const m c => simp [LExpr.substFvars.substFvarsAux, LExpr.LExpr.getVars]
  | op m n t => simp [LExpr.substFvars.substFvarsAux, LExpr.LExpr.getVars]
  | bvar m i => simp [LExpr.substFvars.substFvarsAux, LExpr.LExpr.getVars]
  | fvar m name ty =>
    simp only [LExpr.substFvars.substFvarsAux, LExpr.LExpr.getVars]
    cases hf : sm.find? name with
    | none => simp [LExpr.LExpr.getVars]
    | some to =>
      obtain ⟨m', x, ty', rfl⟩ := hVar name to hf
      simp [LExpr.LExpr.getVars]
  | abs m n t b ih =>
    simp only [LExpr.substFvars.substFvarsAux, LExpr.LExpr.getVars]; exact ih
  | quant m qk n ty tr b iht ihb =>
    simp only [LExpr.substFvars.substFvarsAux, LExpr.LExpr.getVars,
      List.append_eq_nil_iff, iht, ihb]
  | app m f a ihf iha =>
    simp only [LExpr.substFvars.substFvarsAux, LExpr.LExpr.getVars,
      List.append_eq_nil_iff, ihf, iha]
  | eq m l r ihl ihr =>
    simp only [LExpr.substFvars.substFvarsAux, LExpr.LExpr.getVars,
      List.append_eq_nil_iff, ihl, ihr]
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.substFvars.substFvarsAux, LExpr.LExpr.getVars,
      List.append_eq_nil_iff, ihc, iht, ihf]

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- `substFvarsAux` is the identity on expressions with no free variables. -/
theorem substFvarsAux_getVars_nil_id
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (e : LExpr Tbase.mono) (h : LExpr.LExpr.getVars e = []) :
    LExpr.substFvars.substFvarsAux e sm = e := by
  induction e with
  | const m c => rfl
  | op m n t => rfl
  | bvar m i => rfl
  | fvar m name ty => simp [LExpr.LExpr.getVars] at h
  | abs m n t b ih =>
    simp only [LExpr.LExpr.getVars] at h
    simp only [LExpr.substFvars.substFvarsAux]
    rw [ih h]
  | quant m qk n ty tr b iht ihb =>
    simp only [LExpr.LExpr.getVars, List.append_eq_nil_iff] at h
    simp only [LExpr.substFvars.substFvarsAux]
    rw [iht h.1, ihb h.2]
  | app m f a ihf iha =>
    simp only [LExpr.LExpr.getVars, List.append_eq_nil_iff] at h
    simp only [LExpr.substFvars.substFvarsAux]
    rw [ihf h.1, iha h.2]
  | eq m l r ihl ihr =>
    simp only [LExpr.LExpr.getVars, List.append_eq_nil_iff] at h
    simp only [LExpr.substFvars.substFvarsAux]
    rw [ihl h.1, ihr h.2]
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.LExpr.getVars, List.append_eq_nil_iff] at h
    simp only [LExpr.substFvars.substFvarsAux]
    rw [ihc h.1.1, iht h.1.2, ihf h.2]

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- `substFvars` is the identity on canonical values (which are closed). -/
theorem substFvars_canonical_id
    (F : @Factory Tbase)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (v : LExpr Tbase.mono) (hv : LExpr.isCanonicalValue F v = true) :
    LExpr.substFvars v sm = v := by
  have hnil := isCanonicalValue_getVars_nil F v hv
  unfold LExpr.substFvars
  split
  · rfl
  · exact substFvarsAux_getVars_nil_id sm v hnil

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- `substFvars` is the identity on expressions with no free variables. -/
theorem substFvars_getVars_nil_id
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (e : LExpr Tbase.mono) (h : LExpr.LExpr.getVars e = []) :
    LExpr.substFvars e sm = e := by
  unfold LExpr.substFvars
  split
  · rfl
  · exact substFvarsAux_getVars_nil_id sm e h

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- `isCanonicalValue` is invariant under a variable-only renaming.
    Key insight: canonical values are closed (`getVars = []`), and `substFvars`
    is the identity on closed terms; if `e` has free variables so does the
    renamed term (variable-only), so neither is canonical. -/
theorem isCanonicalValue_substFvars_eq
    (F : @Factory Tbase)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono)) (hVar : VarOnly sm)
    (e : LExpr Tbase.mono) :
    LExpr.isCanonicalValue F (LExpr.substFvars e sm)
      = LExpr.isCanonicalValue F e := by
  by_cases hnil : LExpr.LExpr.getVars e = []
  · rw [substFvars_getVars_nil_id sm e hnil]
  · -- e has free vars ⟹ both sides non-canonical
    have hlhs : LExpr.isCanonicalValue F (LExpr.substFvars e sm) = false := by
      apply Bool.eq_false_iff.mpr
      intro hcan
      have := isCanonicalValue_getVars_nil F _ hcan
      -- getVars (substFvars e sm) = [] ⟹ getVars e = []
      have hnil' : LExpr.LExpr.getVars e = [] := by
        unfold LExpr.substFvars at this
        split at this
        · exact this
        · exact (getVars_substFvarsAux_nil_iff sm hVar e).mp this
      exact hnil hnil'
    have hrhs : LExpr.isCanonicalValue F e = false := by
      apply Bool.eq_false_iff.mpr
      intro hcan
      exact hnil (isCanonicalValue_getVars_nil F e hcan)
    rw [hlhs, hrhs]

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- `callOfLFunc` commutes with a variable-only `substFvars`: renaming the
    expression renames exactly the argument list, preserving the callee `.op` and
    the resolved `LFunc`. -/
theorem callOfLFunc_substFvars
    (F : @Factory Tbase) (e : LExpr Tbase.mono)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (op_expr : LExpr Tbase.mono) (args : List (LExpr Tbase.mono)) (lfunc : LFunc Tbase)
    (h : F.callOfLFunc e = some (op_expr, args, lfunc)) :
    F.callOfLFunc (LExpr.substFvars e sm)
      = some (op_expr, args.map (LExpr.substFvars · sm), lfunc) := by
  have hgl : getLFuncCall e = (op_expr, args) := callOfLFunc_getLFuncCall h
  obtain ⟨mo, no, to, hop_eq, hlookup⟩ := Factory.callOfLFunc_getElem? h
  subst hop_eq
  have hgo : getLFuncCall.go (LExpr.substFvars e sm) [] =
      (LExpr.op mo no to, args.map (LExpr.substFvars · sm)) := by
    have := getLFuncCall_go_substFvars e [] sm mo no to args hgl
    simpa using this
  -- Extract the arity/lookup facts from the original call.
  simp only [Factory.callOfLFunc, hgl] at h
  simp only [Factory.callOfLFunc, getLFuncCall, hgo]
  cases hf : F[no.name]? with
  | none => simp [hf] at h
  | some func =>
    simp only [hf] at h ⊢
    simp only [List.length_map]
    split at h <;> simp_all

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- Under a variable-only rename, `getLFuncCall.go` on the renamed expression has
    the SAME operator head as on the original (a rename never turns a non-`.op`
    head into an `.op`, since fvars map to fvars). This gives the reverse
    direction needed to transport a `callOfLFunc = none`. -/
theorem getLFuncCall_go_substFvars_op_head
    (sm : Map Tbase.Identifier (LExpr Tbase.mono)) (hVar : VarOnly sm)
    (e : LExpr Tbase.mono) (acc accs : List (LExpr Tbase.mono))
    (m_op : Tbase.Metadata) (name_op : Lambda.Identifier Tbase.IDMeta) (ty_op : Option LMonoTy)
    (args : List (LExpr Tbase.mono))
    (h : getLFuncCall.go (LExpr.substFvars.substFvarsAux e sm) accs = (LExpr.op m_op name_op ty_op, args)) :
    ∃ args0, getLFuncCall.go e acc = (LExpr.op m_op name_op ty_op, args0) := by
  match e with
  | .app m1 (.app m2 e' arg1) arg2 =>
    simp only [LExpr.substFvars.substFvarsAux, getLFuncCall.go] at h
    obtain ⟨args0, h0⟩ := getLFuncCall_go_substFvars_op_head sm hVar e'
      ([arg1, arg2] ++ acc) ([LExpr.substFvars.substFvarsAux arg1 sm,
        LExpr.substFvars.substFvarsAux arg2 sm] ++ accs) m_op name_op ty_op args h
    exact ⟨args0, by simp only [getLFuncCall.go]; exact h0⟩
  | .app m1 (.op m2 fn ty) arg1 =>
    simp only [LExpr.substFvars.substFvarsAux, getLFuncCall.go,
      Prod.mk.injEq] at h ⊢
    obtain ⟨hop, _⟩ := h
    simp only [LExpr.op.injEq] at hop
    obtain ⟨rfl, rfl, rfl⟩ := hop
    exact ⟨[arg1] ++ acc, ⟨rfl, rfl⟩⟩
  | .app m1 (.const m2 c) arg2 =>
    simp only [LExpr.substFvars.substFvarsAux, getLFuncCall.go,
      Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .app m1 (.bvar m2 i) arg2 =>
    simp only [LExpr.substFvars.substFvarsAux, getLFuncCall.go,
      Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .app m1 (.fvar m2 x ty) arg2 =>
    -- fvar maps to a fvar (VarOnly) or stays fvar; neither is `.op`.
    simp only [LExpr.substFvars.substFvarsAux] at h
    cases hfnd : sm.find? x with
    | none =>
      simp only [hfnd, getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
    | some to =>
      obtain ⟨m', y, ty', rfl⟩ := hVar x to hfnd
      simp only [hfnd, getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .app m1 (.abs m2 n ty body) arg2 =>
    simp only [LExpr.substFvars.substFvarsAux, getLFuncCall.go,
      Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .app m1 (.quant m2 k n ty tr body) arg2 =>
    simp only [LExpr.substFvars.substFvarsAux, getLFuncCall.go, Prod.mk.injEq] at h
    obtain ⟨h, _⟩ := h; cases h
  | .app m1 (.ite m2 c t f) arg2 =>
    simp only [LExpr.substFvars.substFvarsAux, getLFuncCall.go, Prod.mk.injEq] at h
    obtain ⟨h, _⟩ := h; cases h
  | .app m1 (.eq m2 e1 e2) arg2 =>
    simp only [LExpr.substFvars.substFvarsAux, getLFuncCall.go, Prod.mk.injEq] at h
    obtain ⟨h, _⟩ := h; cases h
  | .const _ _ =>
    simp only [LExpr.substFvars.substFvarsAux, getLFuncCall.go, Prod.mk.injEq] at h
    obtain ⟨h, _⟩ := h; cases h
  | .op m n t =>
    simp only [LExpr.substFvars.substFvarsAux, getLFuncCall.go,
      Prod.mk.injEq] at h ⊢
    obtain ⟨hop, _⟩ := h
    simp only [LExpr.op.injEq] at hop
    obtain ⟨rfl, rfl, rfl⟩ := hop
    exact ⟨acc, ⟨rfl, rfl⟩⟩
  | .bvar _ _ =>
    simp only [LExpr.substFvars.substFvarsAux, getLFuncCall.go, Prod.mk.injEq] at h
    obtain ⟨h, _⟩ := h; cases h
  | .fvar m x ty =>
    simp only [LExpr.substFvars.substFvarsAux] at h
    cases hfnd : sm.find? x with
    | none =>
      simp only [hfnd, getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
    | some to =>
      obtain ⟨m', y, ty', rfl⟩ := hVar x to hfnd
      simp only [hfnd, getLFuncCall.go, Prod.mk.injEq] at h; obtain ⟨h, _⟩ := h; cases h
  | .abs _ _ _ _ =>
    simp only [LExpr.substFvars.substFvarsAux, getLFuncCall.go, Prod.mk.injEq] at h
    obtain ⟨h, _⟩ := h; cases h
  | .quant _ _ _ _ _ _ =>
    simp only [LExpr.substFvars.substFvarsAux, getLFuncCall.go, Prod.mk.injEq] at h
    obtain ⟨h, _⟩ := h; cases h
  | .ite _ _ _ _ =>
    simp only [LExpr.substFvars.substFvarsAux, getLFuncCall.go, Prod.mk.injEq] at h
    obtain ⟨h, _⟩ := h; cases h
  | .eq _ _ _ =>
    simp only [LExpr.substFvars.substFvarsAux, getLFuncCall.go, Prod.mk.injEq] at h
    obtain ⟨h, _⟩ := h; cases h
  termination_by e.sizeOf

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- `callOfLFunc = none` transports across a variable-only rename. -/
theorem callOfLFunc_substFvars_none
    (F : @Factory Tbase) (e : LExpr Tbase.mono)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono)) (hVar : VarOnly sm)
    (h : F.callOfLFunc e = none) :
    F.callOfLFunc (LExpr.substFvars e sm) = none := by
  cases hsome0 : F.callOfLFunc (LExpr.substFvars e sm) with
  | none => rfl
  | some triple =>
  exfalso
  obtain ⟨op_expr, args, lfunc⟩ := triple
  have hsome := hsome0
  -- The renamed expr resolves; recover an `.op` head, hence `e` does too.
  obtain ⟨mo, no, to, hop_eq, hlookup⟩ := Factory.callOfLFunc_getElem? hsome
  have hgl : getLFuncCall (LExpr.substFvars e sm) = (op_expr, args) :=
    callOfLFunc_getLFuncCall hsome
  subst hop_eq
  -- `getLFuncCall x = getLFuncCall.go x []`, so recover the op-head on `e`.
  have hgl_go : getLFuncCall.go (LExpr.substFvars e sm) [] = (LExpr.op mo no to, args) := by
    unfold getLFuncCall at hgl; exact hgl
  by_cases hempty : sm.isEmpty
  · have hid : LExpr.substFvars e sm = e := by unfold LExpr.substFvars; rw [if_pos hempty]
    rw [hid] at hsome; rw [hsome] at h; simp at h
  · have haux : LExpr.substFvars.substFvarsAux e sm = LExpr.substFvars e sm := by
      unfold LExpr.substFvars; rw [if_neg hempty]
    obtain ⟨args0, hgo0⟩ := getLFuncCall_go_substFvars_op_head sm hVar e [] []
      mo no to args (by rw [haux]; exact hgl_go)
    have hgl0 : getLFuncCall e = (LExpr.op mo no to, args0) := by
      unfold getLFuncCall; exact hgo0
    simp only [Factory.callOfLFunc, hgl0, hlookup] at h
    simp only [Factory.callOfLFunc, hgl, hlookup] at hsome
    have hargs_eq : args = args0.map (LExpr.substFvars · sm) := by
      have hcomm := getLFuncCall_go_substFvars e [] sm mo no to args0 hgl0
      simp only [List.map_nil] at hcomm
      have : getLFuncCall.go (LExpr.substFvars e sm) [] =
          (LExpr.op mo no to, args0.map (LExpr.substFvars · sm)) := hcomm
      rw [this] at hgl_go
      exact ((Prod.mk.injEq .. |>.mp hgl_go).2).symm
    have hlen : args.length = args0.length := by rw [hargs_eq]; simp
    rw [hlen] at hsome
    split at hsome
    · simp at hsome; split at h
      · simp at h
      · rename_i hne2; simp_all
    · simp at hsome

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- If `substStoreExpr σ' sm z = none` then `z` is not renamed by `sm`. Under
    `VarOnly` all targets are `.fvar`s, and `TargetsDefined` makes their store
    lookup defined; so an undefined pullback forces `z ∉ dom(sm)`. -/
theorem pullback_none_find_none
    (σ' : Env Tbase) (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (hVar : VarOnly sm) (hTgt : TargetsDefined σ' sm) (z : Tbase.Identifier)
    (h : substStoreExpr σ' sm z = none) : sm.find? z = none := by
  cases hf : sm.find? z with
  | none => rfl
  | some to =>
    exfalso
    obtain ⟨m', y, ty', rfl⟩ := hVar z to hf
    simp only [substStoreExpr, hf] at h
    have := hTgt z m' y ty' hf
    rw [h] at this; simp at this

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- `substStoreExpr` maps only to closed (canonical) expressions. -/
theorem pullback_closed
    (F : @Factory Tbase) (σ' : Env Tbase)
    (hwfs : ∀ x v, σ' x = some v → LExpr.isCanonicalValue F v = true)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono)) (hVar : VarOnly sm)
    (z : Tbase.Identifier) (v : LExpr Tbase.mono)
    (h : substStoreExpr σ' sm z = some v) :
    LExpr.isCanonicalValue F v = true := by
  simp only [substStoreExpr] at h
  cases hf : sm.find? z with
  | none => rw [hf] at h; exact hwfs z v h
  | some to =>
    obtain ⟨m', y, ty', rfl⟩ := hVar z to hf
    rw [hf] at h; exact hwfs y v h

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- `substFvars sm` is the identity on `substFvarsFromEnv (substStoreExpr σ' sm) e`:
    every residual free variable is an undefined key of the pulled-back store,
    hence (by `TargetsDefined`) not in `sm`'s domain; store values are closed. -/
theorem substFvars_substFvarsFromEnv_pullback_id
    (F : @Factory Tbase) (σ' : Env Tbase)
    (hwfs : ∀ x v, σ' x = some v → LExpr.isCanonicalValue F v = true)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (hVar : VarOnly sm) (hTgt : TargetsDefined σ' sm)
    (e : LExpr Tbase.mono) :
    LExpr.substFvars (LExpr.substFvarsFromEnv (substStoreExpr σ' sm) e) sm
      = LExpr.substFvarsFromEnv (substStoreExpr σ' sm) e := by
  induction e with
  | const m c => simp [LExpr.substFvarsFromEnv]
  | op m n t => simp [LExpr.substFvarsFromEnv]
  | bvar m i => simp [LExpr.substFvarsFromEnv]
  | fvar m x ty =>
    simp only [LExpr.substFvarsFromEnv]
    cases hpb : substStoreExpr σ' sm x with
    | none =>
      have hfn : sm.find? x = none := pullback_none_find_none σ' sm hVar hTgt x hpb
      exact LExpr.substFvars_fvar_none m x ty sm hfn
    | some v =>
      have hcan : LExpr.isCanonicalValue F v = true :=
        pullback_closed F σ' hwfs sm hVar x v hpb
      exact substFvars_canonical_id F sm v hcan
  | abs m n ty body ih =>
    simp only [LExpr.substFvarsFromEnv, LExpr.substFvars_abs, ih]
  | quant m qk n ty tr body iht ihb =>
    simp only [LExpr.substFvarsFromEnv, LExpr.substFvars_quant, iht, ihb]
  | app m f a ihf iha =>
    simp only [LExpr.substFvarsFromEnv, LExpr.substFvars_app, ihf, iha]
  | eq m l r ihl ihr =>
    simp only [LExpr.substFvarsFromEnv, LExpr.substFvars_eq, ihl, ihr]
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.substFvarsFromEnv, LExpr.substFvars_ite, ihc, iht, ihf]

omit [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- `ite` heads are never canonical values (their head is not an `.op`). -/
theorem isCanonicalValue_ite_false
    (F : @Factory Tbase) (m : Tbase.Metadata) (c t f : LExpr Tbase.mono) :
    LExpr.isCanonicalValue F (.ite m c t f) = false := by
  rw [LExpr.isCanonicalValue.eq_def]
  simp only [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]

omit [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- `eq` heads are never canonical values. -/
theorem isCanonicalValue_eq_false
    (F : @Factory Tbase) (m : Tbase.Metadata) (e1 e2 : LExpr Tbase.mono) :
    LExpr.isCanonicalValue F (.eq m e1 e2) = false := by
  rw [LExpr.isCanonicalValue.eq_def]
  simp only [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]

/-- Bridge: a per-fuel TWISTED equality at fuel `n` yields the value-true
    biconditional at that fuel. Because a `.value true` residual is a canonical
    value, hence closed, `substFvars` collapses to the identity, so the twisting
    disappears exactly at the points the biconditional talks about. -/
theorem bicond_of_twisted
    (F : @Factory Tbase) (σ' : Env Tbase)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (n : Nat) (e : LExpr Tbase.mono)
    (h : LExpr.eval n F σ' (LExpr.substFvars e sm)
      = ((LExpr.substFvars (LExpr.eval n F (substStoreExpr σ' sm) e).fst sm),
         (LExpr.eval n F (substStoreExpr σ' sm) e).snd)) :
    ∀ (v : LExpr Tbase.mono),
      LExpr.eval n F σ' (LExpr.substFvars e sm) = (v, .value true)
    ↔ LExpr.eval n F (substStoreExpr σ' sm) e = (v, .value true) := by
  intro v
  constructor
  · intro hL
    rw [hL] at h
    have hf : v = LExpr.substFvars (LExpr.eval n F (substStoreExpr σ' sm) e).fst sm :=
      (Prod.mk.injEq ..).mp h |>.1
    have hs : LExpr.EvalResult.value true = (LExpr.eval n F (substStoreExpr σ' sm) e).snd :=
      (Prod.mk.injEq ..).mp h |>.2
    have hcanσ : LExpr.isCanonicalValue F (LExpr.eval n F (substStoreExpr σ' sm) e).fst = true :=
      eval_value_isCanonicalValue n F (substStoreExpr σ' sm) e (b := true) hs.symm
    rw [substFvars_canonical_id F sm _ hcanσ] at hf
    rw [← Prod.eta (LExpr.eval n F (substStoreExpr σ' sm) e), ← hs, ← hf]
  · intro hR
    rw [hR] at h
    simp only at h
    have hcan : LExpr.isCanonicalValue F v = true := by
      have := eval_value_isCanonicalValue n F (substStoreExpr σ' sm) e (b := true) (by rw [hR])
      rw [hR] at this; exact this
    rw [h, substFvars_canonical_id F sm v hcan]

omit [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- `callOfLFunc` is `none` on an `ite` head. -/
theorem callOfLFunc_ite_none
    (F : @Factory Tbase) (m : Tbase.Metadata) (c t f : LExpr Tbase.mono) :
    F.callOfLFunc (.ite m c t f) = none := by
  simp only [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]

omit [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- `callOfLFunc` is `none` on an `eq` head. -/
theorem callOfLFunc_eq_none
    (F : @Factory Tbase) (m : Tbase.Metadata) (e1 e2 : LExpr Tbase.mono) :
    F.callOfLFunc (.eq m e1 e2) = none := by
  simp only [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]

/-- One-step reduction of `eval` on an `ite` head. -/
theorem eval_succ_ite
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m : Tbase.Metadata) (c t f : LExpr Tbase.mono) :
    LExpr.eval (n' + 1) F env (.ite m c t f) = LExpr.evalIte n' F env m c t f := by
  rw [LExpr.eval]
  rw [if_neg (by rw [isCanonicalValue_ite_false]; simp)]
  rw [callOfLFunc_ite_none]
  simp only [LExpr.evalCore]

/-- One-step reduction of `eval` on an `eq` head. -/
theorem eval_succ_eq
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m : Tbase.Metadata) (e1 e2 : LExpr Tbase.mono) :
    LExpr.eval (n' + 1) F env (.eq m e1 e2) = LExpr.evalEq n' F env m e1 e2 := by
  rw [LExpr.eval]
  rw [if_neg (by rw [isCanonicalValue_eq_false]; simp)]
  rw [callOfLFunc_eq_none]
  simp only [LExpr.evalCore]

/-- One-step reduction of `eval` on an `app` head that is not a factory call. -/
theorem eval_succ_app_none
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m : Tbase.Metadata) (e1 e2 : LExpr Tbase.mono)
    (hncan : LExpr.isCanonicalValue F (.app m e1 e2) = false)
    (hcall : F.callOfLFunc (.app m e1 e2) = none) :
    LExpr.eval (n' + 1) F env (.app m e1 e2)
      = LExpr.evalApp n' F env (.app m e1 e2) e1 e2 := by
  rw [LExpr.eval]
  rw [if_neg (by rw [hncan]; simp)]
  rw [hcall]
  simp only [LExpr.evalCore]

omit [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- One-directional core for the `evalIte` value-true sync. Given directional
    value-true transfers for condition and both branches, a value-true result of
    the left match transfers to the right. The two runs differ only by
    store/rename, captured abstractly here as six eval-result pairs. -/
theorem ite_match_imp
    (m : Tbase.Metadata)
    (Lc Rc Lt Rt Lf Rf : LExpr Tbase.mono × LExpr.EvalResult)
    (v : LExpr Tbase.mono)
    (hc : ∀ cv, Lc = (cv, .value true) → Rc = (cv, .value true))
    (ht : ∀ tv, Lt = (tv, .value true) → Rt = (tv, .value true))
    (hf : ∀ fv, Lf = (fv, .value true) → Rf = (fv, .value true))
    (hL : (match Lc.fst with
        | .const _ (.boolConst true) =>
            (Lt.fst, Lt.snd.combineValueFlag Lc.snd.isValueTrue)
        | .const _ (.boolConst false) =>
            (Lf.fst, Lf.snd.combineValueFlag Lc.snd.isValueTrue)
        | _ => (LExpr.ite m Lc.fst Lt.fst Lf.fst, LExpr.EvalResult.nonvalue))
      = (v, LExpr.EvalResult.value true)) :
    (match Rc.fst with
        | .const _ (.boolConst true) =>
            (Rt.fst, Rt.snd.combineValueFlag Rc.snd.isValueTrue)
        | .const _ (.boolConst false) =>
            (Rf.fst, Rf.snd.combineValueFlag Rc.snd.isValueTrue)
        | _ => (LExpr.ite m Rc.fst Rt.fst Rf.fst, LExpr.EvalResult.nonvalue))
      = (v, LExpr.EvalResult.value true) := by
  split at hL
  · -- condition reduced to `true`
    rename_i mc hLc
    have hLt_fst : Lt.fst = v := congrArg Prod.fst hL
    have hLt_and : Lt.snd.combineValueFlag Lc.snd.isValueTrue = .value true :=
      congrArg Prod.snd hL
    obtain ⟨hLt_snd, hLc_vt⟩ := (andValue_eq_valueTrue_iff _ _).mp hLt_and
    have hLc_snd : Lc.snd = .value true := (isValueTrue_eq_true_iff _).mp hLc_vt
    have hLc_eq : Lc = (LExpr.const mc (LConst.boolConst true), .value true) := by
      rw [← hLc, ← hLc_snd, Prod.eta]
    have hRc := hc _ hLc_eq
    have hLt_eq : Lt = (v, .value true) := by rw [← hLt_fst, ← hLt_snd, Prod.eta]
    have hRt := ht _ hLt_eq
    simp only [hRc, hRt, LExpr.EvalResult.isValueTrue, LExpr.EvalResult.combineValueFlag,
      Bool.and_self]
  · -- condition reduced to `false`
    rename_i mc hLc
    have hLf_fst : Lf.fst = v := congrArg Prod.fst hL
    have hLf_and : Lf.snd.combineValueFlag Lc.snd.isValueTrue = .value true :=
      congrArg Prod.snd hL
    obtain ⟨hLf_snd, hLc_vt⟩ := (andValue_eq_valueTrue_iff _ _).mp hLf_and
    have hLc_snd : Lc.snd = .value true := (isValueTrue_eq_true_iff _).mp hLc_vt
    have hLc_eq : Lc = (LExpr.const mc (LConst.boolConst false), .value true) := by
      rw [← hLc, ← hLc_snd, Prod.eta]
    have hRc := hc _ hLc_eq
    have hLf_eq : Lf = (v, .value true) := by rw [← hLf_fst, ← hLf_snd, Prod.eta]
    have hRf := hf _ hLf_eq
    simp only [hRc, hRf, LExpr.EvalResult.isValueTrue, LExpr.EvalResult.combineValueFlag,
      Bool.and_self]
  · -- default arm returns `.nonvalue`, contradicting `.value true`
    exfalso
    have := congrArg Prod.snd hL
    simp only at this
    exact absurd this (by simp)

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- `eqModuloMeta X Y = true` forces `X` and `Y` to have the same free variables
    (metadata does not affect `getVars`). -/
theorem gv_eq_of_eqModuloMeta (X Y : LExpr Tbase.mono)
    (h : LExpr.eqModuloMeta X Y = true) :
    LExpr.LExpr.getVars X = LExpr.LExpr.getVars Y := by
  have heq : X.eraseMetadata = Y.eraseMetadata := by
    unfold LExpr.eqModuloMeta at h; exact (LExpr.beq_eq _ _).mp h
  have hfv := LExpr.freeVars_of_eraseMetadata_eq X Y heq
  rw [getVars_eq_freeVars_idents X, getVars_eq_freeVars_idents Y, hfv]

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- Against a CLOSED comparand `X`, the `eqModuloMeta` guard is invariant under a
    variable-only rename of `A`: if either side matches, that side (hence both)
    is closed and the rename is the identity on it. -/
theorem eqModuloMeta_substFvars_congr_closed
    (sm : Map Tbase.Identifier (LExpr Tbase.mono)) (hVar : VarOnly sm)
    (A X : LExpr Tbase.mono) (hX : LExpr.LExpr.getVars X = []) :
    LExpr.eqModuloMeta (LExpr.substFvars A sm) X = LExpr.eqModuloMeta A X := by
  by_cases hT : LExpr.eqModuloMeta A X = true
  · have hAnil : LExpr.LExpr.getVars A = [] := by
      rw [gv_eq_of_eqModuloMeta A X hT]; exact hX
    rw [substFvars_getVars_nil_id sm A hAnil, hT]
  · have hTfalse : LExpr.eqModuloMeta A X = false := Bool.eq_false_iff.mpr hT
    cases hb : LExpr.eqModuloMeta (LExpr.substFvars A sm) X with
    | false => rw [hTfalse]
    | true =>
      exfalso
      have hSnil : LExpr.LExpr.getVars (LExpr.substFvars A sm) = [] := by
        rw [gv_eq_of_eqModuloMeta _ X hb]; exact hX
      have hAnil : LExpr.LExpr.getVars A = [] := by
        unfold LExpr.substFvars at hSnil
        split at hSnil
        · exact hSnil
        · exact (getVars_substFvarsAux_nil_iff sm hVar A).mp hSnil
      rw [substFvars_getVars_nil_id sm A hAnil] at hb
      rw [hb] at hTfalse; simp at hTfalse

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- Shared tail for both `app_dir` match arms: once the reduct `e'` is closed and
    the left guard is false, the right if-expression collapses to `(v, .value true)`. -/
theorem app_reduct_transfer
    (AgL AgR v e' : LExpr Tbase.mono)
    (he'nil : LExpr.LExpr.getVars e' = [])
    (hgf : LExpr.eqModuloMeta AgL e' = false)
    (hguard : ∀ (X : LExpr Tbase.mono), LExpr.LExpr.getVars X = [] →
        LExpr.eqModuloMeta AgL X = LExpr.eqModuloMeta AgR X)
    (evL evR : LExpr Tbase.mono → LExpr Tbase.mono × LExpr.EvalResult)
    (hev : ∀ e, LExpr.LExpr.getVars e = [] → evL e = evR e)
    (hfst : (evL e').fst = v) (hinner : (evL e').snd = .value true) :
    (if LExpr.eqModuloMeta AgR e' = true then (AgR, LExpr.EvalResult.nonvalue)
     else ((evR e').fst, (evR e').snd.combineValueFlag
       ((LExpr.EvalResult.value true).isValueTrue && (LExpr.EvalResult.value true).isValueTrue)))
      = (v, LExpr.EvalResult.value true) := by
  have hgf' : LExpr.eqModuloMeta AgR e' = false := by rw [← hguard e' he'nil]; exact hgf
  rw [if_neg (by rw [hgf']; simp), ← hev e' he'nil, hinner, hfst]
  simp only [LExpr.EvalResult.isValueTrue, LExpr.EvalResult.combineValueFlag, Bool.true_and]

omit [Inhabited Tbase.IDMeta] in
/-- One-directional core for the `evalApp` value-true sync. Both runs share the
    same metadata `m` and comparand-application structure; they differ only by
    store (`env₁`/`env₂`) and by the fact that the left operands are renamed
    (`substFvars`) while the guard comparand `AL` is `substFvars`-related to `AR`.
    The directional transfers `h1`/`h2` (operand value-true sync, from the IH) and
    store-independence on closed inner terms (`hev`) close it.

    All four operand results, and the closed residuals they force, are the concrete
    `eval` calls; `A`gL/`A`gR are the guard comparands. -/
theorem app_dir
    (r1L r1R r2L r2R : LExpr Tbase.mono × LExpr.EvalResult)
    (AgL AgR : LExpr Tbase.mono) (v : LExpr Tbase.mono)
    -- operand value-true transfers (from the IH)
    (h1 : ∀ w, r1L = (w, .value true) → r1R = (w, .value true))
    (h2 : ∀ w, r2L = (w, .value true) → r2R = (w, .value true))
    -- value-true residuals are closed
    (hcl1 : ∀ w, r1L = (w, .value true) → LExpr.LExpr.getVars w = [])
    (hcl2 : ∀ w, r2L = (w, .value true) → LExpr.LExpr.getVars w = [])
    -- guard comparands agree once the compared body is closed (from the rename)
    (hguard : ∀ (X : LExpr Tbase.mono), LExpr.LExpr.getVars X = [] →
        LExpr.eqModuloMeta AgL X = LExpr.eqModuloMeta AgR X)
    -- inner eval agrees on closed terms (store independence)
    (evL evR : LExpr Tbase.mono → LExpr Tbase.mono × LExpr.EvalResult)
    (hev : ∀ e, LExpr.LExpr.getVars e = [] → evL e = evR e)
    (hL : (match r1L.fst with
        | .abs mAbs _ _ body =>
          let e' := LExpr.subst (fun mv => LExpr.replaceMetadata1
            (LExpr.mergeMetadataForSubst mAbs r2L.fst.metadata mv) r2L.fst) body
          if LExpr.eqModuloMeta AgL e' = true then (AgL, LExpr.EvalResult.nonvalue)
          else ((evL e').fst, (evL e').snd.combineValueFlag
            (r1L.snd.isValueTrue && r2L.snd.isValueTrue))
        | _ =>
          let e' := LExpr.app AgL.metadata r1L.fst r2L.fst
          if LExpr.eqModuloMeta AgL e' = true then (AgL, LExpr.EvalResult.nonvalue)
          else ((evL e').fst, (evL e').snd.combineValueFlag
            (r1L.snd.isValueTrue && r2L.snd.isValueTrue)))
      = (v, LExpr.EvalResult.value true))
    (hmeta : AgL.metadata = AgR.metadata) :
    (match r1R.fst with
        | .abs mAbs _ _ body =>
          let e' := LExpr.subst (fun mv => LExpr.replaceMetadata1
            (LExpr.mergeMetadataForSubst mAbs r2R.fst.metadata mv) r2R.fst) body
          if LExpr.eqModuloMeta AgR e' = true then (AgR, LExpr.EvalResult.nonvalue)
          else ((evR e').fst, (evR e').snd.combineValueFlag
            (r1R.snd.isValueTrue && r2R.snd.isValueTrue))
        | _ =>
          let e' := LExpr.app AgR.metadata r1R.fst r2R.fst
          if LExpr.eqModuloMeta AgR e' = true then (AgR, LExpr.EvalResult.nonvalue)
          else ((evR e').fst, (evR e').snd.combineValueFlag
            (r1R.snd.isValueTrue && r2R.snd.isValueTrue)))
      = (v, LExpr.EvalResult.value true) := by
  -- A closer that, from a value-true else-branch, extracts guard-false, both
  -- operands value-true, and the inner eval value-true.
  have closer : ∀ (e' : LExpr Tbase.mono)
      (hbr : (if LExpr.eqModuloMeta AgL e' = true then (AgL, LExpr.EvalResult.nonvalue)
              else ((evL e').fst, (evL e').snd.combineValueFlag
                (r1L.snd.isValueTrue && r2L.snd.isValueTrue)))
            = (v, LExpr.EvalResult.value true)),
      LExpr.eqModuloMeta AgL e' = false ∧ r1L.snd = .value true ∧ r2L.snd = .value true ∧
      (evL e').fst = v ∧ (evL e').snd = .value true := by
    intro e' hbr
    by_cases hg : LExpr.eqModuloMeta AgL e' = true
    · rw [if_pos hg] at hbr
      exfalso; have := congrArg Prod.snd hbr
      exact absurd this (by simp)
    · have hgf : LExpr.eqModuloMeta AgL e' = false := Bool.eq_false_iff.mpr hg
      rw [if_neg hg] at hbr
      have hfst : (evL e').fst = v := congrArg Prod.fst hbr
      have hsnd : (evL e').snd.combineValueFlag (r1L.snd.isValueTrue && r2L.snd.isValueTrue)
          = .value true := congrArg Prod.snd hbr
      obtain ⟨hinner, hsub⟩ := (andValue_eq_valueTrue_iff _ _).mp hsnd
      have hs1 : r1L.snd.isValueTrue = true := by
        rcases hbb : r1L.snd.isValueTrue with _ | _ <;> simp [hbb] at hsub ⊢
      have hs2 : r2L.snd.isValueTrue = true := by
        rcases hbb : r2L.snd.isValueTrue with _ | _ <;> simp [hbb] at hsub ⊢
      exact ⟨hgf, (isValueTrue_eq_true_iff _).mp hs1, (isValueTrue_eq_true_iff _).mp hs2,
        hfst, hinner⟩
  -- The residuals `r1L.fst`, `r2L.fst` at value-true are closed.
  have r2Lnil : r2L.snd = .value true → LExpr.LExpr.getVars r2L.fst = [] := by
    intro h; apply hcl2; rw [← h, Prod.eta]
  split at hL
  · -- left discriminant `r1L.fst = .abs ...`
    rename_i mAbs prettyName ty body hLabs
    obtain ⟨hgf, hs1, hs2, hfst, hinner⟩ := closer _ hL
    have hr1R : r1R = (LExpr.abs mAbs prettyName ty body, .value true) := by
      apply h1; rw [← hLabs, ← hs1, Prod.eta]
    have hr2R : r2R = (r2L.fst, .value true) := by apply h2; rw [← hs2, Prod.eta]
    have hw1nil : LExpr.LExpr.getVars (LExpr.abs mAbs prettyName ty body) = [] := by
      apply hcl1; rw [← hLabs, ← hs1, Prod.eta]
    have hw2nil : LExpr.LExpr.getVars r2L.fst = [] := r2Lnil hs2
    obtain ⟨e', he'⟩ : ∃ e', e' = LExpr.subst (fun mv => LExpr.replaceMetadata1
      (LExpr.mergeMetadataForSubst mAbs r2L.fst.metadata mv) r2L.fst) body := ⟨_, rfl⟩
    rw [← he'] at hgf hinner hfst
    have he'nil : LExpr.LExpr.getVars e' = [] := by
      rw [he']
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro y hy
      rcases getVars_substK_mem 0 _ body y hy with hb | ⟨mv, hmv⟩
      · rw [show LExpr.LExpr.getVars body = LExpr.LExpr.getVars
            (LExpr.abs mAbs prettyName ty body) from rfl, hw1nil] at hb; simp at hb
      · rw [getVars_replaceMetadata1, hw2nil] at hmv; simp at hmv
    rw [hr1R, hr2R]
    simp only
    rw [← he']
    exact app_reduct_transfer AgL AgR v e' he'nil hgf hguard evL evR hev hfst hinner
  · -- left discriminant not `.abs`
    rename_i hnotabs
    obtain ⟨hgf, hs1, hs2, hfst, hinner⟩ := closer _ hL
    have hr1R : r1R = (r1L.fst, .value true) := by apply h1; rw [← hs1, Prod.eta]
    have hr2R : r2R = (r2L.fst, .value true) := by apply h2; rw [← hs2, Prod.eta]
    have hw1nil : LExpr.LExpr.getVars r1L.fst = [] := by apply hcl1; rw [← hs1, Prod.eta]
    have hw2nil : LExpr.LExpr.getVars r2L.fst = [] := r2Lnil hs2
    obtain ⟨e', he'⟩ : ∃ e', e' = LExpr.app AgL.metadata r1L.fst r2L.fst := ⟨_, rfl⟩
    rw [← he'] at hgf hinner hfst
    have he'nil : LExpr.LExpr.getVars e' = [] := by
      rw [he']; simp only [LExpr.LExpr.getVars, List.append_eq_nil_iff]; exact ⟨hw1nil, hw2nil⟩
    rw [hr1R, hr2R]
    -- The right discriminant `r1L.fst` is also not `.abs`, so the default arm fires.
    split
    · rename_i mAbs' pn' ty' body' habs'
      exact absurd habs' (hnotabs mAbs' pn' ty' body')
    · have he'R : LExpr.app AgR.metadata r1L.fst r2L.fst = e' := by rw [he', hmeta]
      rw [he'R]
      exact app_reduct_transfer AgL AgR v e' he'nil hgf hguard evL evR hev hfst hinner

omit [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- One-directional core for the `evalEq` value-true sync. A `.value true` result
    forces both operands to `.value true`, so (by the directional transfers) their
    residuals are identical on both sides; hence `eql` sees identical inputs and
    returns the same Boolean. -/
theorem eq_match_imp
    (F : @Factory Tbase) (m : Tbase.Metadata)
    (L1 R1 L2 R2 : LExpr Tbase.mono × LExpr.EvalResult)
    (v : LExpr Tbase.mono)
    (h1 : ∀ w, L1 = (w, .value true) → R1 = (w, .value true))
    (h2 : ∀ w, L2 = (w, .value true) → R2 = (w, .value true))
    (hL : (match LExpr.eql F L1.fst L2.fst with
        | some b => (LExpr.const m (LConst.boolConst b),
            LExpr.EvalResult.value (L1.snd.isValueTrue && L2.snd.isValueTrue))
        | none => (LExpr.eq m L1.fst L2.fst, LExpr.EvalResult.nonvalue))
      = (v, LExpr.EvalResult.value true)) :
    (match LExpr.eql F R1.fst R2.fst with
        | some b => (LExpr.const m (LConst.boolConst b),
            LExpr.EvalResult.value (R1.snd.isValueTrue && R2.snd.isValueTrue))
        | none => (LExpr.eq m R1.fst R2.fst, LExpr.EvalResult.nonvalue))
      = (v, LExpr.EvalResult.value true) := by
  split at hL
  · rename_i b hLeql
    have hfst : LExpr.const m (LConst.boolConst b) = v := congrArg Prod.fst hL
    have hsnd : LExpr.EvalResult.value (L1.snd.isValueTrue && L2.snd.isValueTrue)
        = .value true := congrArg Prod.snd hL
    have hand : L1.snd.isValueTrue && L2.snd.isValueTrue = true := by
      have := LExpr.EvalResult.value.injEq _ _ ▸ hsnd; simpa using this
    have h1v : L1.snd.isValueTrue = true := by
      rcases hb : L1.snd.isValueTrue with _ | _ <;> simp [hb] at hand ⊢
    have h2v : L2.snd.isValueTrue = true := by
      rcases hb : L2.snd.isValueTrue with _ | _ <;> simp [hb] at hand ⊢
    have hL1_eq : L1 = (L1.fst, .value true) := by
      rw [← (isValueTrue_eq_true_iff _).mp h1v, Prod.eta]
    have hL2_eq : L2 = (L2.fst, .value true) := by
      rw [← (isValueTrue_eq_true_iff _).mp h2v, Prod.eta]
    have hR1 := h1 _ hL1_eq
    have hR2 := h2 _ hL2_eq
    rw [hR1, hR2, hLeql, ← hfst]
    simp only [LExpr.EvalResult.isValueTrue, Bool.and_self]
  · exfalso
    have := congrArg Prod.snd hL
    simp only at this
    exact absurd this (by simp)

/-- Per-argument value-true synchronization derived from the fuel-`n'` IH:
    the `isValueTrue` bit agrees across the rename, and whenever it holds the
    residual `.fst` values coincide. -/
theorem call_arg_sync
    (n' : Nat) (F : @Factory Tbase) (σ' : Env Tbase)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (ih : ∀ (e v : LExpr Tbase.mono),
      LExpr.eval n' F σ' (e.substFvars sm) = (v, .value true) ↔
        LExpr.eval n' F (substStoreExpr σ' sm) e = (v, .value true))
    (a : LExpr Tbase.mono) :
    (LExpr.eval n' F σ' (a.substFvars sm)).snd.isValueTrue
        = (LExpr.eval n' F (substStoreExpr σ' sm) a).snd.isValueTrue ∧
    ((LExpr.eval n' F σ' (a.substFvars sm)).snd.isValueTrue = true →
      LExpr.eval n' F σ' (a.substFvars sm) = LExpr.eval n' F (substStoreExpr σ' sm) a) := by
  refine ⟨?_, ?_⟩
  · cases hL : (LExpr.eval n' F σ' (a.substFvars sm)).snd.isValueTrue with
    | true =>
      have hLp : LExpr.eval n' F σ' (a.substFvars sm)
          = ((LExpr.eval n' F σ' (a.substFvars sm)).fst, .value true) := by
        rw [← (isValueTrue_eq_true_iff _).mp hL, Prod.eta]
      have hR := (ih a _).mp hLp
      rw [hR]; simp [LExpr.EvalResult.isValueTrue]
    | false =>
      cases hR : (LExpr.eval n' F (substStoreExpr σ' sm) a).snd.isValueTrue with
      | false => rfl
      | true =>
        exfalso
        have hRp : LExpr.eval n' F (substStoreExpr σ' sm) a
            = ((LExpr.eval n' F (substStoreExpr σ' sm) a).fst, .value true) := by
          rw [← (isValueTrue_eq_true_iff _).mp hR, Prod.eta]
        have hLback := (ih a _).mpr hRp
        rw [hLback] at hL; simp [LExpr.EvalResult.isValueTrue] at hL
  · intro hvt
    have hLp : LExpr.eval n' F σ' (a.substFvars sm)
        = ((LExpr.eval n' F σ' (a.substFvars sm)).fst, .value true) := by
      rw [← (isValueTrue_eq_true_iff _).mp hvt, Prod.eta]
    have hR := (ih a _).mp hLp
    rw [hLp, hR]

omit [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- `substFvars` preserves top-level metadata on any non-`fvar` head. -/
theorem substFvars_metadata_of_ne_fvar
    (e : LExpr Tbase.mono) (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (h : ∀ m x ty, e ≠ .fvar m x ty) :
    (LExpr.substFvars e sm).metadata = e.metadata := by
  cases e <;> rw [LExpr.substFvars_unfold] <;>
    simp only [LExpr.metadata] <;> try rfl
  case fvar m x ty => exact absurd rfl (h m x ty)

/-- The `argsAllFull` bit agrees across the rename, for a whole argument list. -/
theorem call_argsAllFull_eq
    (n' : Nat) (F : @Factory Tbase) (σ' : Env Tbase)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (ih : ∀ (e v : LExpr Tbase.mono),
      LExpr.eval n' F σ' (e.substFvars sm) = (v, .value true) ↔
        LExpr.eval n' F (substStoreExpr σ' sm) e = (v, .value true))
    (args : List (LExpr Tbase.mono)) :
    ((args.map (LExpr.substFvars · sm)).all
        fun a => (LExpr.eval n' F σ' a).snd.isValueTrue)
      = (args.all fun a => (LExpr.eval n' F (substStoreExpr σ' sm) a).snd.isValueTrue) := by
  induction args with
  | nil => rfl
  | cons a rest iht =>
    simp only [List.map_cons, List.all_cons]
    rw [(call_arg_sync n' F σ' sm ih a).1, iht]

/-- When `argsAllFull` holds on the renamed side, the residual `.fst` lists on the
    two sides coincide. -/
theorem call_args_fst_eq
    (n' : Nat) (F : @Factory Tbase) (σ' : Env Tbase)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (ih : ∀ (e v : LExpr Tbase.mono),
      LExpr.eval n' F σ' (e.substFvars sm) = (v, .value true) ↔
        LExpr.eval n' F (substStoreExpr σ' sm) e = (v, .value true))
    (args : List (LExpr Tbase.mono))
    (hall : (args.map (LExpr.substFvars · sm)).all
        fun a => (LExpr.eval n' F σ' a).snd.isValueTrue = true) :
    (args.map (LExpr.substFvars · sm)).map (fun a => (LExpr.eval n' F σ' a).fst)
      = args.map (fun a => (LExpr.eval n' F (substStoreExpr σ' sm) a).fst) := by
  induction args with
  | nil => rfl
  | cons a rest iht =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at hall ⊢
    obtain ⟨ha, hrest⟩ := hall
    have hsync := (call_arg_sync n' F σ' sm ih a).2 (by simpa using ha)
    rw [hsync, iht hrest]

/-- When a factory call's arguments are NOT all fully reduced, the call result is
    never a fully-reduced `.value true`: `eval` combines the reduct's value flag
    with `argsAllFull = false` (or returns `.nonvalue`), so the `.snd` cannot be
    `.value true`. -/
theorem eval_call_not_full_snd
    (n : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (e : LExpr Tbase.mono)
    (triple : LExpr Tbase.mono × List (LExpr Tbase.mono) × LFunc Tbase)
    (hcall : F.callOfLFunc e = some triple)
    (hcanF : LExpr.isCanonicalValue F e = false)
    (hfull : (triple.2.1.all fun a => (LExpr.eval n F env a).snd.isValueTrue) = false) :
    (LExpr.eval (n + 1) F env e).snd ≠ .value true := by
  obtain ⟨op_expr, args, lfunc⟩ := triple
  simp only at hfull
  simp only [LExpr.eval, LExpr.List_map_fst_map_eval,
    LExpr.List_all_snd_isValueTrue_map_eval, LExpr.combineEvalResValueFlag_eq_pair,
    hcanF, hcall, hfull]
  -- Every leaf is either under an impossible `false = true`, or `.nonvalue`, or
  -- `combineValueFlag _ false`; none is `.value true`.
  repeat' split
  all_goals
    first
      | exact absurd ‹false = true› (by simp)
      | (intro hbad
         simp only [LExpr.EvalResult.combineValueFlag] at hbad
         split at hbad <;> simp_all [LExpr.EvalResult.isValueTrue])
      | simp [LExpr.EvalResult.combineValueFlag]
      | simp

/-- When a factory call's arguments ARE all fully reduced, evaluating the renamed
    call in the renamed store equals evaluating the original call in the pulled-back
    store: the residual `.fst` lists coincide (each argument value-syncs), and the
    shared reduct is CLOSED (its free variables come only from the canonical — hence
    closed — argument residuals), so `eval` is store-independent on it. -/
theorem call_node_eval_eq
    (hIdent : ∀ a b : Tbase.Identifier, a.name = b.name → a = b)
    (n' : Nat) (F : @Factory Tbase) (σ' : Env Tbase) (hWF : FactoryWF F) (hClosed : FactoryClosed F)
    (hwfs : ∀ x v, σ' x = some v → LExpr.isCanonicalValue F v = true)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (hVar : VarOnly sm)
    (e : LExpr Tbase.mono)
    (op_expr : LExpr Tbase.mono) (args : List (LExpr Tbase.mono)) (lfunc : LFunc Tbase)
    (hcall : F.callOfLFunc e = some (op_expr, args, lfunc))
    (hcanF : LExpr.isCanonicalValue F e = false)
    (hfull : (args.all fun a => (LExpr.eval n' F (substStoreExpr σ' sm) a).snd.isValueTrue) = true)
    (ih : ∀ (e v : LExpr Tbase.mono),
      LExpr.eval n' F σ' (e.substFvars sm) = (v, .value true) ↔
        LExpr.eval n' F (substStoreExpr σ' sm) e = (v, .value true))
    (v : LExpr Tbase.mono) :
    (LExpr.eval (n' + 1) F σ' (LExpr.substFvars e sm) = (v, .value true))
      ↔ (LExpr.eval (n' + 1) F (substStoreExpr σ' sm) e = (v, .value true)) := by
  -- Both stores bind only closed (canonical) values.
  have henvσ' : ∀ x v, σ' x = some v → LExpr.LExpr.getVars v = [] := by
    intro x v hx; exact isCanonicalValue_getVars_nil F v (hwfs x v hx)
  have henvPB : ∀ x v, substStoreExpr σ' sm x = some v → LExpr.LExpr.getVars v = [] := by
    intro x v hx
    exact isCanonicalValue_getVars_nil F v (pullback_closed F σ' hwfs sm hVar x v hx)
  -- The renamed and pullback argument residual lists coincide, and the
  -- `argsAllFull` bit agrees.
  have hfullL : ((args.map (LExpr.substFvars · sm)).all
      fun a => (LExpr.eval n' F σ' a).snd.isValueTrue) = true := by
    rw [call_argsAllFull_eq n' F σ' sm ih args]; exact hfull
  have hfst := call_args_fst_eq n' F σ' sm ih args (by simpa using hfullL)
  have hbit := call_argsAllFull_eq n' F σ' sm ih args
  have hcanFL : LExpr.isCanonicalValue F (LExpr.substFvars e sm) = false := by
    rw [isCanonicalValue_substFvars_eq F sm hVar e]; exact hcanF
  have hcallL : F.callOfLFunc (LExpr.substFvars e sm)
      = some (op_expr, args.map (LExpr.substFvars · sm), lfunc) :=
    callOfLFunc_substFvars F e sm op_expr args lfunc hcall
  -- Each reduct that is actually evaluated is closed, so `eval_env_congr` makes the
  -- two evaluations (in `σ'` vs `substStoreExpr σ' sm`) agree on it.
  have hstore_indep : ∀ (r : LExpr Tbase.mono),
      LExpr.LExpr.getVars r = [] →
      LExpr.eval n' F σ' r = LExpr.eval n' F (substStoreExpr σ' sm) r :=
    fun r hr => eval_env_congr hIdent n' F σ' (substStoreExpr σ' sm) hWF hClosed henvPB r
      (fun x hx => by rw [hr] at hx; simp at hx)
  -- Each pullback-side argument residual is fully reduced, hence canonical, hence
  -- closed (`getVars = []`).
  have hargClosed : ∀ a ∈ args,
      LExpr.LExpr.getVars (LExpr.eval n' F (substStoreExpr σ' sm) a).fst = [] := by
    intro a ha
    have haVT : (LExpr.eval n' F (substStoreExpr σ' sm) a).snd.isValueTrue = true := by
      have := (List.all_eq_true).mp hfull a ha
      simpa using this
    have hsnd : (LExpr.eval n' F (substStoreExpr σ' sm) a).snd = .value true := by
      cases hs : (LExpr.eval n' F (substStoreExpr σ' sm) a).snd with
      | value b => cases b with
        | true => rfl
        | false => rw [hs] at haVT; simp [LExpr.EvalResult.isValueTrue] at haVT
      | nonvalue => rw [hs] at haVT; simp [LExpr.EvalResult.isValueTrue] at haVT
      | outOfFuel => rw [hs] at haVT; simp [LExpr.EvalResult.isValueTrue] at haVT
    have hcana := eval_value_isCanonicalValue n' F (substStoreExpr σ' sm) a (b := true) hsnd
    exact isCanonicalValue_getVars_nil F _ hcana
  -- Bundled facts needed to bound the reducts' free variables.
  have h_mem := callOfLFunc_func_mem F _ _ _ lfunc false hcall
  have h_wf := hWF.lfuncs_wf lfunc h_mem
  have h_closed := hClosed.lfuncs_closed lfunc h_mem
  obtain ⟨mo, no, to, hop_eq, _, h_arity⟩ := callOfLFunc_eq_some hcall
  -- Every element of the pullback-side residual list is closed.
  have hRclosed : ∀ r ∈ args.map (fun a => (LExpr.eval n' F (substStoreExpr σ' sm) a).fst),
      LExpr.LExpr.getVars r = [] := by
    intro r hr; rw [List.mem_map] at hr
    obtain ⟨a, ha, rfl⟩ := hr; exact hargClosed a ha
  -- The two evaluations either coincide (shared closed reduct + store independence)
  -- or are both `.nonvalue`.  Phrased as a plain disjunction, the shared branch
  -- structure is `split`-able (unlike the biconditional, whose `dite`s straddle the
  -- `↔`).  After the rewrites both sides share every scrutinee, so a single `split`
  -- drives both in lockstep; we then lift the disjunction to the biconditional.
  have hpair :
      LExpr.eval (n' + 1) F σ' (LExpr.substFvars e sm)
        = LExpr.eval (n' + 1) F (substStoreExpr σ' sm) e
      ∨ ((LExpr.eval (n' + 1) F σ' (LExpr.substFvars e sm)).snd ≠ .value true
        ∧ (LExpr.eval (n' + 1) F (substStoreExpr σ' sm) e).snd ≠ .value true) := by
    have hmeta : (LExpr.substFvars e sm).metadata = e.metadata :=
      substFvars_metadata_of_ne_fvar e sm (fun m x ty heq => by
        rw [heq, callOfLFunc_fvar_none F m x ty] at hcall
        simp at hcall)
    simp only [LExpr.eval, LExpr.List_map_fst_map_eval,
      LExpr.List_all_snd_isValueTrue_map_eval, LExpr.combineEvalResValueFlag_eq_pair,
      hcanFL, hcallL, hcanF, hcall, hfst, hbit, hmeta]
    split
    · -- `isCanonicalValue` guard: rewritten to `false`, so this branch is impossible.
      exact absurd ‹false = true› (by simp)
    · split
      · -- inline branch
        rename_i h_cond
        split
        · -- computeTypeSubst = some: shared closed reduct, store-independent.
          rename_i tySubst h_ts
          have hclosed : LExpr.LExpr.getVars
              (((lfunc.body.get (by simp only [Bool.and_eq_true] at h_cond; exact h_cond.1)).applySubst tySubst).substFvarsLifting
                (lfunc.inputs.keys.zip
                  (args.map (fun a => (LExpr.eval n' F (substStoreExpr σ' sm) a).fst)))) = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro x hx
            rcases getVars_substFvarsLifting_mem _ _ x hx with ⟨hin, hnone⟩ | ⟨k, v, hk, hv⟩
            · rw [getVars_applySubst] at hin
              have hsome : lfunc.body.isSome = true := by
                simp only [Bool.and_eq_true] at h_cond; exact h_cond.1
              have hbody_eq : lfunc.body = some (lfunc.body.get hsome) := by simp [Option.some_get]
              have hy_key := lfunc_body_getVars_subset_keys hIdent lfunc h_closed _ hbody_eq x hin
              have h_len : lfunc.inputs.keys.length =
                  (args.map (fun a => (LExpr.eval n' F (substStoreExpr σ' sm) a).fst)).length := by
                rw [ListMap.keys_eq_map_fst]; simp [h_arity]
              have h_mem_keys : x ∈ Map.keys (lfunc.inputs.keys.zip
                  (args.map (fun a => (LExpr.eval n' F (substStoreExpr σ' sm) a).fst))) := by
                rw [Map.keys_eq_map_fst, List.map_fst_zip (by omega)]; exact hy_key
              exact Map_find?_ne_none_of_mem_keys _ x h_mem_keys hnone
            · have hv_mem := Map_find?_some_mem_values _ k v hk
              have hv_R := List.mem_map_snd_zip _ _ v hv_mem
              have := hRclosed v hv_R
              rw [this] at hv; exact absurd hv (List.not_mem_nil)
          left; rw [hstore_indep _ hclosed]
        · -- computeTypeSubst = none: both `.nonvalue`.
          right; exact ⟨by simp, by simp⟩
      · -- non-inline branch
        cases h_fEC : Strata.DL.Util.FuncAttr.findEvalIfConstr lfunc.attr <;>
        cases h_fEV : Strata.DL.Util.FuncAttr.findEvalIfCanonical lfunc.attr <;> (
          simp only []
          split
          · split
            · -- concreteEval none: the (now possibly certifying) results
              -- coincide on both sides after the residual rewrites.
              left; rfl
            · rename_i ceval h_ce
              split
              · -- ceval succeeds: shared closed reduct, store-independent.
                rename_i e'c h_ceval_eq
                have hclosed : LExpr.LExpr.getVars e'c = [] := by
                  apply List.eq_nil_iff_forall_not_mem.mpr
                  intro x hx
                  have hexists := h_wf.concreteEval_freeVars ceval h_ce _ _ e'c h_ceval_eq x hx
                  obtain ⟨a, ha_mem, hxa'⟩ := hexists
                  have := hRclosed a ha_mem
                  rw [this] at hxa'; exact absurd hxa' (List.not_mem_nil)
                left; rw [hstore_indep _ hclosed]
              · -- ceval fails: both `.nonvalue`.
                right; exact ⟨by simp, by simp⟩
          · -- symbolic args: both `.nonvalue`.
            right; exact ⟨by simp, by simp⟩
        )
  rcases hpair with heq | ⟨hL, hR⟩
  · rw [heq]
  · constructor <;> intro h
    · exact absurd (congrArg Prod.snd h) hL
    · exact absurd (congrArg Prod.snd h) hR

/-- The per-fuel `eval`-level rename commutation, as a value-true SYNC
    BICONDITIONAL: at every fuel, the renamed syntax evaluated in the renamed
    store reaches a fully-reduced value `v` iff the original expression in the
    pulled-back store reaches the *same* `v`. This is what `evalFully` actually
    observes, and — unlike the twisted equality — it holds even for non-injective
    `sm`, because a `.value true` residual is closed and `substFvars` is the
    identity on it. -/
theorem eval_rename_commute
    (hIdent : ∀ a b : Tbase.Identifier, a.name = b.name → a = b)
    (n : Nat)
    (F : @Factory Tbase) (σ' : Env Tbase) (hWF : FactoryWF F) (hClosed : FactoryClosed F)
    (hwfs : ∀ x v, σ' x = some v → LExpr.isCanonicalValue F v = true)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (hVar : VarOnly sm) (hTgt : TargetsDefined σ' sm)
    (e : LExpr Tbase.mono) :
    ∀ (v : LExpr Tbase.mono),
      LExpr.eval n F σ' (LExpr.substFvars e sm) = (v, .value true)
    ↔ LExpr.eval n F (substStoreExpr σ' sm) e = (v, .value true) := by
  induction n generalizing e with
  | zero =>
    apply bicond_of_twisted F σ' sm 0 e
    simp only [LExpr.eval]
    rw [isCanonicalValue_substFvars_eq F sm hVar e]
  | succ n' ih =>
    -- Leaf/structural arms reuse the TWISTED equality (which holds there) via
    -- `bicond_of_twisted`; the recursive walls (ite/app/eq/callOfLFunc-some) are
    -- proved directly at value-true using the biconditional IH.
    cases hcall : F.callOfLFunc e with
    | some triple =>
      obtain ⟨op_expr, args, lfunc⟩ := triple
      intro v
      by_cases hcan : LExpr.isCanonicalValue F e = true
      · apply bicond_of_twisted F σ' sm (n' + 1) e
        simp only [LExpr.eval, LExpr.combineEvalResValueFlag_eq_pair]
        rw [isCanonicalValue_substFvars_eq F sm hVar e]
        rw [if_pos hcan, if_pos hcan]
      · have hcanF : LExpr.isCanonicalValue F e = false :=
          Bool.eq_false_iff.mpr (by simpa using hcan)
        have hcanFL : LExpr.isCanonicalValue F (LExpr.substFvars e sm) = false := by
          rw [isCanonicalValue_substFvars_eq F sm hVar e]; exact hcanF
        have hcallL : F.callOfLFunc (LExpr.substFvars e sm)
            = some (op_expr, args.map (LExpr.substFvars · sm), lfunc) :=
          callOfLFunc_substFvars F e sm op_expr args lfunc hcall
        -- Case on whether the pullback-side arguments are all fully reduced.
        by_cases hfull :
            (args.all fun a => (LExpr.eval n' F (substStoreExpr σ' sm) a).snd.isValueTrue) = true
        · -- All args full: the residual `.fst` lists coincide and every reducing
          -- leaf shares a CLOSED reduct, so the value-true biconditional holds.
          exact call_node_eval_eq hIdent n' F σ' hWF hClosed hwfs sm hVar e op_expr args lfunc
            hcall hcanF hfull ih v
        · -- Some arg not full: neither call node reaches `.value true`, so both
          -- directions of the biconditional are vacuous.
          have hfullFalse : (args.all fun a =>
              (LExpr.eval n' F (substStoreExpr σ' sm) a).snd.isValueTrue) = false := by
            simpa using hfull
          have hfullFalseL : ((args.map (LExpr.substFvars · sm)).all
              fun a => (LExpr.eval n' F σ' a).snd.isValueTrue) = false := by
            rw [call_argsAllFull_eq n' F σ' sm ih args]; exact hfullFalse
          constructor
          · intro hL
            exact absurd (congrArg Prod.snd hL)
              (eval_call_not_full_snd n' F σ' (LExpr.substFvars e sm)
                (op_expr, args.map (LExpr.substFvars · sm), lfunc) hcallL hcanFL
                hfullFalseL)
          · intro hR
            exact absurd (congrArg Prod.snd hR)
              (eval_call_not_full_snd n' F (substStoreExpr σ' sm) e
                (op_expr, args, lfunc) hcall hcanF hfullFalse)
    | none =>
      cases e with
      | const m c =>
        apply bicond_of_twisted F σ' sm (n' + 1) (.const m c)
        simp only [LExpr.eval, LExpr.combineEvalResValueFlag_eq_pair]
        rw [isCanonicalValue_substFvars_eq F sm hVar (.const m c)]
        split
        · rfl
        · rw [callOfLFunc_substFvars_none F (.const m c) sm hVar hcall, hcall]
          simp only [LExpr.substFvars_const', LExpr.evalCore]
      | op m nm t =>
        apply bicond_of_twisted F σ' sm (n' + 1) (.op m nm t)
        simp only [LExpr.eval, LExpr.combineEvalResValueFlag_eq_pair]
        rw [isCanonicalValue_substFvars_eq F sm hVar (.op m nm t)]
        split
        · rfl
        · rw [callOfLFunc_substFvars_none F (.op m nm t) sm hVar hcall, hcall]
          simp only [LExpr.substFvars_op', LExpr.evalCore]
      | bvar m i =>
        apply bicond_of_twisted F σ' sm (n' + 1) (.bvar m i)
        simp only [LExpr.eval, LExpr.combineEvalResValueFlag_eq_pair]
        rw [isCanonicalValue_substFvars_eq F sm hVar (.bvar m i)]
        split
        · rfl
        · rw [callOfLFunc_substFvars_none F (.bvar m i) sm hVar hcall, hcall]
          simp only [LExpr.substFvars_bvar, LExpr.evalCore]
      | fvar m x ty =>
        apply bicond_of_twisted F σ' sm (n' + 1) (.fvar m x ty)
        simp only [LExpr.eval, LExpr.combineEvalResValueFlag_eq_pair]
        rw [isCanonicalValue_substFvars_eq F sm hVar (.fvar m x ty)]
        split
        · rfl
        · rw [callOfLFunc_substFvars_none F (.fvar m x ty) sm hVar hcall, hcall]
          cases hfnd : sm.find? x with
          | none =>
            rw [LExpr.substFvars_fvar_none m x ty sm hfnd]
            simp only [LExpr.evalCore]
            have hpb : substStoreExpr σ' sm x = σ' x := by
              simp only [substStoreExpr, hfnd]
            rw [hpb]
            cases hσx : σ' x with
            | none => simp [LExpr.substFvars_fvar_none m x ty sm hfnd]
            | some v =>
              have hcanv : LExpr.isCanonicalValue F v = true := hwfs x v hσx
              simp only [hcanv, if_true]
              rw [substFvars_canonical_id F sm v hcanv]
          | some to =>
            obtain ⟨m', y, ty', rfl⟩ := hVar x to hfnd
            rw [LExpr.substFvars_fvar_find m x ty sm _ hfnd]
            simp only [LExpr.evalCore]
            have hpb : substStoreExpr σ' sm x = σ' y := by
              simp only [substStoreExpr, hfnd]
            rw [hpb]
            have hsome : (σ' y).isSome := hTgt x m' y ty' hfnd
            cases hσy : σ' y with
            | none => rw [hσy] at hsome; simp at hsome
            | some v =>
              have hcanv : LExpr.isCanonicalValue F v = true := hwfs y v hσy
              simp only [hcanv, if_true]
              rw [substFvars_canonical_id F sm v hcanv]
      | abs m nm ty body =>
        apply bicond_of_twisted F σ' sm (n' + 1) (.abs m nm ty body)
        simp only [LExpr.eval, LExpr.combineEvalResValueFlag_eq_pair]
        rw [isCanonicalValue_substFvars_eq F sm hVar (.abs m nm ty body)]
        split
        · rfl
        · rw [callOfLFunc_substFvars_none F (.abs m nm ty body) sm hVar hcall, hcall]
          rw [LExpr.substFvars_abs]
          simp only [LExpr.evalCore]
          rw [← LExpr.substFvars_abs (sm := sm)]
          have hcomp := substFvarsFromEnv_substFvars σ' sm hVar hTgt (LExpr.abs m nm ty body)
          rw [hcomp]
          rw [substFvars_substFvarsFromEnv_pullback_id F σ' hwfs sm hVar hTgt
            (LExpr.abs m nm ty body)]
      | quant m qk nm ty tr body =>
        apply bicond_of_twisted F σ' sm (n' + 1) (.quant m qk nm ty tr body)
        simp only [LExpr.eval, LExpr.combineEvalResValueFlag_eq_pair]
        rw [isCanonicalValue_substFvars_eq F sm hVar (.quant m qk nm ty tr body)]
        split
        · rfl
        · rw [callOfLFunc_substFvars_none F (.quant m qk nm ty tr body) sm hVar hcall, hcall]
          rw [LExpr.substFvars_quant]
          simp only [LExpr.evalCore]
          rw [← LExpr.substFvars_quant (sm := sm)]
          have hcomp := substFvarsFromEnv_substFvars σ' sm hVar hTgt
            (LExpr.quant m qk nm ty tr body)
          rw [hcomp]
          rw [substFvars_substFvarsFromEnv_pullback_id F σ' hwfs sm hVar hTgt
            (LExpr.quant m qk nm ty tr body)]
      | app m e1 e2 =>
        intro v
        by_cases hcan : LExpr.isCanonicalValue F (.app m e1 e2) = true
        · -- canonical (e.g. partial constructor application): closed, identity.
          apply bicond_of_twisted F σ' sm (n' + 1) (.app m e1 e2)
          simp only [LExpr.eval, LExpr.combineEvalResValueFlag_eq_pair]
          rw [isCanonicalValue_substFvars_eq F sm hVar (.app m e1 e2)]
          rw [if_pos hcan, if_pos hcan]
        · -- non-canonical, not a factory call: goes through `evalApp` (beta).
          have hcanF : LExpr.isCanonicalValue F (.app m e1 e2) = false :=
            Bool.eq_false_iff.mpr (by simpa using hcan)
          have hcanL : LExpr.isCanonicalValue F
              (.app m (LExpr.substFvars e1 sm) (LExpr.substFvars e2 sm)) = false := by
            rw [← LExpr.substFvars_app, isCanonicalValue_substFvars_eq F sm hVar (.app m e1 e2)]
            exact hcanF
          have hcallL : F.callOfLFunc
              (.app m (LExpr.substFvars e1 sm) (LExpr.substFvars e2 sm)) = none := by
            rw [← LExpr.substFvars_app]
            exact callOfLFunc_substFvars_none F (.app m e1 e2) sm hVar hcall
          -- Store-value closedness facts for `eval_env_congr`.
          have hσcl : ∀ x w, σ' x = some w → LExpr.LExpr.getVars w = [] :=
            fun x w h => isCanonicalValue_getVars_nil F w (hwfs x w h)
          have hpbcl : ∀ x w, substStoreExpr σ' sm x = some w → LExpr.LExpr.getVars w = [] :=
            fun x w h => isCanonicalValue_getVars_nil F w (pullback_closed F σ' hwfs sm hVar x w h)
          -- Residual-closedness of value-true operands (both stores).
          have hcl1L : ∀ w, LExpr.eval n' F σ' (LExpr.substFvars e1 sm) = (w, .value true)
              → LExpr.LExpr.getVars w = [] := fun w hw =>
            isCanonicalValue_getVars_nil F w (by
              have := eval_value_isCanonicalValue n' F σ' (LExpr.substFvars e1 sm)
                (b := true) (by rw [hw]); rw [hw] at this; exact this)
          have hcl2L : ∀ w, LExpr.eval n' F σ' (LExpr.substFvars e2 sm) = (w, .value true)
              → LExpr.LExpr.getVars w = [] := fun w hw =>
            isCanonicalValue_getVars_nil F w (by
              have := eval_value_isCanonicalValue n' F σ' (LExpr.substFvars e2 sm)
                (b := true) (by rw [hw]); rw [hw] at this; exact this)
          have hcl1R : ∀ w, LExpr.eval n' F (substStoreExpr σ' sm) e1 = (w, .value true)
              → LExpr.LExpr.getVars w = [] := fun w hw =>
            isCanonicalValue_getVars_nil F w (by
              have := eval_value_isCanonicalValue n' F (substStoreExpr σ' sm) e1
                (b := true) (by rw [hw]); rw [hw] at this; exact this)
          have hcl2R : ∀ w, LExpr.eval n' F (substStoreExpr σ' sm) e2 = (w, .value true)
              → LExpr.LExpr.getVars w = [] := fun w hw =>
            isCanonicalValue_getVars_nil F w (by
              have := eval_value_isCanonicalValue n' F (substStoreExpr σ' sm) e2
                (b := true) (by rw [hw]); rw [hw] at this; exact this)
          -- Guard agreement across the rename (comparand closed).
          have hguardLR : ∀ (X : LExpr Tbase.mono), LExpr.LExpr.getVars X = [] →
              LExpr.eqModuloMeta (.app m (LExpr.substFvars e1 sm) (LExpr.substFvars e2 sm)) X
                = LExpr.eqModuloMeta (.app m e1 e2) X := by
            intro X hX
            rw [show LExpr.app m (LExpr.substFvars e1 sm) (LExpr.substFvars e2 sm)
                = LExpr.substFvars (.app m e1 e2) sm from (LExpr.substFvars_app ..).symm]
            exact eqModuloMeta_substFvars_congr_closed sm hVar (.app m e1 e2) X hX
          -- Store independence on closed terms.
          have hevLR : ∀ e, LExpr.LExpr.getVars e = [] →
              LExpr.eval n' F σ' e = LExpr.eval n' F (substStoreExpr σ' sm) e := fun e he =>
            eval_env_congr hIdent n' F σ' (substStoreExpr σ' sm) hWF hClosed hpbcl e
              (fun x hx => by rw [he] at hx; simp at hx)
          rw [LExpr.substFvars_app]
          rw [eval_succ_app_none n' F σ' m _ _ hcanL hcallL]
          rw [eval_succ_app_none n' F (substStoreExpr σ' sm) m e1 e2 hcanF hcall]
          simp only [LExpr.evalApp]
          constructor
          · intro hL
            exact app_dir (LExpr.eval n' F σ' (LExpr.substFvars e1 sm))
              (LExpr.eval n' F (substStoreExpr σ' sm) e1)
              (LExpr.eval n' F σ' (LExpr.substFvars e2 sm))
              (LExpr.eval n' F (substStoreExpr σ' sm) e2)
              (.app m (LExpr.substFvars e1 sm) (LExpr.substFvars e2 sm)) (.app m e1 e2) v
              (fun w => (ih e1 w).mp) (fun w => (ih e2 w).mp) hcl1L hcl2L hguardLR
              (LExpr.eval n' F σ') (LExpr.eval n' F (substStoreExpr σ' sm)) hevLR hL rfl
          · intro hR
            exact app_dir (LExpr.eval n' F (substStoreExpr σ' sm) e1)
              (LExpr.eval n' F σ' (LExpr.substFvars e1 sm))
              (LExpr.eval n' F (substStoreExpr σ' sm) e2)
              (LExpr.eval n' F σ' (LExpr.substFvars e2 sm))
              (.app m e1 e2) (.app m (LExpr.substFvars e1 sm) (LExpr.substFvars e2 sm)) v
              (fun w => (ih e1 w).mpr) (fun w => (ih e2 w).mpr) hcl1R hcl2R
              (fun X hX => (hguardLR X hX).symm)
              (LExpr.eval n' F (substStoreExpr σ' sm)) (LExpr.eval n' F σ')
              (fun e he => (hevLR e he).symm) hR rfl
      | eq m e1 e2 =>
        intro v
        simp only [LExpr.substFvars_eq, eval_succ_eq, LExpr.evalEq]
        constructor
        · exact eq_match_imp F m _ _ _ _ v (fun w => (ih e1 w).mp) (fun w => (ih e2 w).mp)
        · exact eq_match_imp F m _ _ _ _ v (fun w => (ih e1 w).mpr) (fun w => (ih e2 w).mpr)
      | ite m c t f =>
        intro v
        simp only [LExpr.substFvars_ite, eval_succ_ite, LExpr.evalIte]
        constructor
        · exact ite_match_imp m _ _ _ _ _ _ v
            (fun cv => (ih c cv).mp) (fun tv => (ih t tv).mp) (fun fv => (ih f fv).mp)
        · exact ite_match_imp m _ _ _ _ _ _ v
            (fun cv => (ih c cv).mpr) (fun tv => (ih t tv).mpr) (fun fv => (ih f fv).mpr)

theorem rename_commute
    (hIdent : ∀ a b : Tbase.Identifier, a.name = b.name → a = b)
    (F : @Factory Tbase) (σ' : Env Tbase) (hWF : FactoryWF F) (hClosed : FactoryClosed F)
    (hwfs : ∀ x v, σ' x = some v → LExpr.isCanonicalValue F v = true)
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (hVar : VarOnly sm) (hTgt : TargetsDefined σ' sm)
    (e : LExpr Tbase.mono) :
    LExpr.evalFully F σ' (LExpr.substFvars e sm)
      = LExpr.evalFully F (substStoreExpr σ' sm) e := by
  -- The per-fuel value-true sync biconditional; `hfst_at_val`/`_rev` are its two
  -- directions. `hsnd'` lifts it to the `.snd = .value true` agreement the
  -- `evalFullyAux` assembly needs (full `.snd` equality is not required).
  have hfst_at_val : ∀ k v, LExpr.eval k F (substStoreExpr σ' sm) e = (v, .value true) →
      LExpr.eval k F σ' (LExpr.substFvars e sm) = (v, .value true) := by
    intro k v hk
    exact (eval_rename_commute hIdent k F σ' hWF hClosed hwfs sm hVar hTgt e v).mpr hk
  have hfst_at_val_rev : ∀ k v, LExpr.eval k F σ' (LExpr.substFvars e sm) = (v, .value true) →
      LExpr.eval k F (substStoreExpr σ' sm) e = (v, .value true) := by
    intro k v hk
    exact (eval_rename_commute hIdent k F σ' hWF hClosed hwfs sm hVar hTgt e v).mp hk
  have hsnd' : ∀ k, (LExpr.eval k F σ' (LExpr.substFvars e sm)).snd = .value true
      ↔ (LExpr.eval k F (substStoreExpr σ' sm) e).snd = .value true := by
    intro k
    constructor
    · intro hL
      have hL' : LExpr.eval k F σ' (LExpr.substFvars e sm)
          = ((LExpr.eval k F σ' (LExpr.substFvars e sm)).fst, .value true) := by
        rw [← hL, Prod.eta]
      rw [(hfst_at_val_rev k _ hL')]
    · intro hR
      have hR' : LExpr.eval k F (substStoreExpr σ' sm) e
          = ((LExpr.eval k F (substStoreExpr σ' sm) e).fst, .value true) := by
        rw [← hR, Prod.eta]
      rw [(hfst_at_val k _ hR')]
  unfold LExpr.evalFully
  cases h1 : LExpr.evalFullyAux F σ' (LExpr.substFvars e sm) 0 with
  | some v =>
    obtain ⟨n, hle, hn, hlt⟩ := evalFullyAux_some_exists F σ' (LExpr.substFvars e sm) 0 v h1
    symm
    apply evalFullyAux_of_eval F (substStoreExpr σ' sm) e n v (hfst_at_val_rev n v hn) 0 hle
    intro k hk1 hk2
    exact fun hc => hlt k hk1 hk2 ((hsnd' k).mpr hc)
  | none =>
    cases h2 : LExpr.evalFullyAux F (substStoreExpr σ' sm) e 0 with
    | none => rfl
    | some v =>
      obtain ⟨n, hle, hn, hlt⟩ := evalFullyAux_some_exists F (substStoreExpr σ' sm) e 0 v h2
      have hcontra : LExpr.evalFullyAux F σ' (LExpr.substFvars e sm) 0 = some v :=
        evalFullyAux_of_eval F σ' (LExpr.substFvars e sm) n v (hfst_at_val n v hn) 0 hle
          (fun k hk1 hk2 => fun hc => hlt k hk1 hk2 ((hsnd' k).mp hc))
      rw [h1] at hcontra; exact absurd hcontra (by simp)

end rename_commute

end Lambda
