/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.FactoryProps
import Strata.DL.Lambda.Semantics

/-!
## Properties of the Lambda expression evaluator

- `eval_value_isCanonicalValue` — if `eval` returns `.value`, the result is canonical
-/

namespace Lambda
open Strata
open Std (ToFormat Format format)

variable {Tbase : LExprParams}
  [DecidableEq Tbase.IDMeta]
  [Inhabited Tbase.IDMeta]
  [Traceable LExpr.EvalProvenance Tbase.Metadata]


/-- Helper: if `evalApp` returns `.value`, the result is canonical. -/
private theorem evalApp_value_isCanonicalValue
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (e e1 e2 : LExpr Tbase.mono)
    (ih_eval : ∀ e', (LExpr.eval n' F env e').snd = .value →
        LExpr.isCanonicalValue F (LExpr.eval n' F env e').fst = true)
    (h : (LExpr.evalApp n' F env e e1 e2).snd = .value) :
    LExpr.isCanonicalValue F (LExpr.evalApp n' F env e e1 e2).fst = true := by
  have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
      p = LExpr.evalApp n' F env e e1 e2 →
      p.snd = .value → LExpr.isCanonicalValue F p.fst = true := by
    intro p hp hv
    simp only [LExpr.evalApp] at hp
    generalize (LExpr.eval n' F env e1).fst = e1' at hp
    generalize (LExpr.eval n' F env e2).fst = e2' at hp
    split at hp
    · -- e1' is .abs
      split at hp
      · -- eqModuloMeta = true → p = (e, .nonvalue)
        subst hp; simp at hv
      · -- eqModuloMeta = false → p = eval n' F env e'
        subst hp; exact ih_eval _ hv
    · -- e1' is not .abs
      split at hp
      · subst hp; simp at hv
      · subst hp; exact ih_eval _ hv
  exact key _ rfl h


/-- Helper: if `evalEq` returns `.value`, the result is canonical. -/
private theorem evalEq_value_isCanonicalValue
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m : Tbase.Metadata) (e1 e2 : LExpr Tbase.mono)
    (_ih_eval : ∀ e', (LExpr.eval n' F env e').snd = .value →
        LExpr.isCanonicalValue F (LExpr.eval n' F env e').fst = true)
    (h : (LExpr.evalEq n' F env m e1 e2).snd = .value) :
    LExpr.isCanonicalValue F (LExpr.evalEq n' F env m e1 e2).fst = true := by
  have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
      p = LExpr.evalEq n' F env m e1 e2 →
      p.snd = .value → LExpr.isCanonicalValue F p.fst = true := by
    intro p hp hv
    simp only [LExpr.evalEq] at hp
    generalize (LExpr.eval n' F env e1).fst = e1' at hp
    generalize (LExpr.eval n' F env e2).fst = e2' at hp
    generalize LExpr.eql F e1' e2' = eql_res at hp
    cases eql_res with
    | some b => subst hp; unfold LExpr.isCanonicalValue; rfl
    | none => subst hp; simp at hv
  exact key _ rfl h


/-- Helper: if `evalIte` returns `.value`, the result is canonical. -/
private theorem evalIte_value_isCanonicalValue
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m : Tbase.Metadata) (c t f : LExpr Tbase.mono)
    (ih_eval : ∀ e', (LExpr.eval n' F env e').snd = .value →
        LExpr.isCanonicalValue F (LExpr.eval n' F env e').fst = true)
    (h : (LExpr.evalIte n' F env m c t f).snd = .value) :
    LExpr.isCanonicalValue F (LExpr.evalIte n' F env m c t f).fst = true := by
  have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
      p = LExpr.evalIte n' F env m c t f →
      p.snd = .value → LExpr.isCanonicalValue F p.fst = true := by
    intro p hp hv
    simp only [LExpr.evalIte] at hp
    generalize (LExpr.eval n' F env c).fst = c' at hp
    split at hp
    · -- c' = .true _ → eval n' F env t
      subst hp; exact ih_eval _ hv
    · -- c' = .false _ → eval n' F env f
      subst hp; exact ih_eval _ hv
    · -- c' = other → (.ite ..., .nonvalue)
      subst hp; simp at hv
  exact key _ rfl h


/-- Helper: if `evalCore` returns `.value`, the result is canonical.
    Requires an IH for `eval` at the same fuel level. -/
private theorem evalCore_value_isCanonicalValue
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    (ih_eval : ∀ e', (LExpr.eval n' F env e').snd = .value →
        LExpr.isCanonicalValue F (LExpr.eval n' F env e').fst = true)
    (h : (LExpr.evalCore n' F env e).snd = .value) :
    LExpr.isCanonicalValue F (LExpr.evalCore n' F env e).fst = true := by
  have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
      p = LExpr.evalCore n' F env e →
      p.snd = .value → LExpr.isCanonicalValue F p.fst = true := by
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
        subst hp; simp at hv; exact hv
      · -- env x = none
        subst hp; simp at hv
    | abs m n ty body =>
      simp only [LExpr.evalCore] at hp
      subst hp; simp at hv; exact hv
    | quant m q n ty tr body =>
      simp only [LExpr.evalCore] at hp
      subst hp; simp at hv; exact hv
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


/-- If `eval` returns `.value`, the resulting expression satisfies `isCanonicalValue`. -/
theorem eval_value_isCanonicalValue
    (n : Nat) (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    (h : (LExpr.eval n F env e).snd = .value) :
    LExpr.isCanonicalValue F (LExpr.eval n F env e).fst = true := by
  induction n generalizing e with
  | zero =>
    have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
        p = LExpr.eval 0 F env e →
        p.snd = .value → LExpr.isCanonicalValue F p.fst = true := by
      intro p hp hv
      simp only [LExpr.eval] at hp
      subst hp; simp at hv; exact hv
    exact key _ rfl h
  | succ n' ih =>
    have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
        p = LExpr.eval (n' + 1) F env e →
        p.snd = .value → LExpr.isCanonicalValue F p.fst = true := by
      intro p hp hv
      simp only [LExpr.eval] at hp
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
              exact ih _ hv
            · -- computeTypeSubst = none → (e, .nonvalue).fst
              rename_i h_subst
              simp only [h_subst] at hv
              exact absurd hv LExpr.EvalResult.noConfusion
          · -- dite false branch: if eval_cond then ... else ...
            rename_i h_not_cond
            rw [dif_neg h_not_cond] at hv
            split
            · -- inner if true: match concreteEval ...
              rename_i h_eval_cond
              rw [if_pos h_eval_cond] at hv
              split
              · -- concreteEval = none → (new_e, .nonvalue)
                rename_i h_ceval
                rw [h_ceval] at hv
                exact absurd hv LExpr.EvalResult.noConfusion
              · -- concreteEval = some ceval: match ceval ...
                rename_i ceval h_ceval
                simp only [h_ceval] at hv
                split
                · -- ceval returns some e' → (eval n' F env e').fst
                  rename_i e' h_ceval_res
                  simp only [h_ceval_res] at hv
                  exact ih _ hv
                · -- ceval returns none → (new_e, .nonvalue)
                  rename_i h_ceval_res
                  simp only [h_ceval_res] at hv
                  exact absurd hv LExpr.EvalResult.noConfusion
            · -- inner if false: (new_e, .nonvalue)
              rename_i h_not_eval_cond
              rw [if_neg h_not_eval_cond] at hv
              exact absurd hv LExpr.EvalResult.noConfusion
        · -- callOfLFunc = none → evalCore
          subst hp
          exact evalCore_value_isCanonicalValue n' F env e (fun e' h' => ih e' h') hv
    exact key _ rfl h

/-- If `isCanonicalValue F e = true` and fuel is at least 1, eval returns `(e, .value)`. -/
theorem eval_canonical_identity
    (n : Nat) (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    (hcan : LExpr.isCanonicalValue F e = true) :
    LExpr.eval n F env e = (e, .value) := by
  cases n <;> (simp only [LExpr.eval]; rw [if_pos hcan])

/-! ## Properties of `LExpr.evalFully` -/

/-- `evalFully` only outputs canonical values. -/
theorem evalFully_outputs_canonical
    (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    (v : LExpr Tbase.mono) (heval : LExpr.evalFully F env e = some v) :
    LExpr.isCanonicalValue F v = true :=
  LExpr.evalFully.partial_correctness F env
    (motive := fun _e v => LExpr.isCanonicalValue F v = true)
    (fun approx ih e' r hbody => by
      have hfst := congrArg Prod.fst (id rfl : LExpr.eval 200 F env e' = LExpr.eval 200 F env e')
      match hm : (LExpr.eval 200 F env e').snd, (LExpr.eval 200 F env e').fst, hfst with
      | .value, _, _ =>
        simp [hm] at hbody; subst hbody
        exact eval_value_isCanonicalValue 200 F env e' hm
      | .nonvalue, _, _ => simp [hm] at hbody
      | .outOfFuel, _, _ => simp [hm] at hbody; exact ih _ _ hbody)
    e v heval

/-- `evalFully` is the identity on canonical values. -/
theorem evalFully_value_identity
    (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    (hcan : LExpr.isCanonicalValue F e = true) :
    LExpr.evalFully F env e = some e := by
  unfold LExpr.evalFully
  have h := eval_canonical_identity 200 F env e hcan
  simp [h]

/-- `evalFully` on a free variable returns the store binding (given a well-formed store). -/
theorem evalFully_fvar_store
    (F : @Factory Tbase) (env : Env Tbase)
    (hwfs : ∀ x v, env x = some v → LExpr.isCanonicalValue F v = true)
    (m : Tbase.Metadata) (v : Tbase.Identifier) (ty : Option Tbase.mono.TypeType) :
    LExpr.evalFully F env (.fvar m v ty) = env v := by
  unfold LExpr.evalFully
  have hnotcan : LExpr.isCanonicalValue F (.fvar m v ty : LExpr Tbase.mono) = false := by
    apply Bool.eq_false_iff.mpr
    intro hcan
    have h_no_vars := isCanonicalValue_getVars_nil F _ hcan
    simp [LExpr.LExpr.getVars] at h_no_vars
  have heval : LExpr.eval 200 F env (.fvar m v ty : LExpr Tbase.mono) =
    LExpr.evalCore 199 F env (.fvar m v ty : LExpr Tbase.mono) := by
    unfold LExpr.eval
    rw [if_neg (Bool.eq_false_iff.mp hnotcan)]
    split
    · rename_i heq; rw [callOfLFunc_fvar_none F m v ty] at heq; exact absurd heq (by simp)
    · rfl
  rw [heval]
  unfold LExpr.evalCore
  cases hσv : env v with
  | none => simp
  | some val =>
    simp only
    have hval : LExpr.isCanonicalValue F val = true := hwfs v val hσv
    simp [hval]

end Lambda
