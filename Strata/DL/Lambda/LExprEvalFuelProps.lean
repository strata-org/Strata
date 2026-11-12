/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.DL.Lambda.LExprEvalFully
public import Strata.DL.Lambda.FactoryWF
public import Strata.DL.Lambda.LStateProps
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprEvalFully
import all Strata.DL.Lambda.LExprType
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprWFProps
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.LState
import all Strata.DL.Lambda.LStateProps
import all Strata.DL.Lambda.LExprProps
import all Strata.DL.Lambda.LExprEvalProps
import Strata.DL.Lambda.OperationalSemanticsProps
import Strata.Util.PtrCacheProps

/-! # Properties of the fuel-bounded evaluator `LExpr.eval` and of `evalFully`

Facts about the syntactic, fuel-bounded evaluator `LExpr.eval` over expression stores
(`Env`), and about `evalFully` (`LExprEvalFully`), which retries `eval` at increasing fuel.

Key theorems:
- `eval_value_isValue`: a `.value _` result of `eval` is a value (`isValue`);
  `eval_value_identity`: `eval` returns a value unchanged, at every fuel.
- `eval_getVars_origin`, `eval_getVars_subset`: every free variable of `eval`'s result comes
  from the input (through the store, when the store is idempotent).
- `eval_env_congr`: on a well-formed factory, two stores that agree on the free variables of
  `e`, the second holding only closed expressions, give the same `eval` result.
- `eval_value_true_mono`, `eval_value_true_mono_le`, `eval_value_true_add_fuel`,
  `eval_value_true_deterministic`, `eval_least_fuel_value_true`: a fully reduced result
  (`.value true`) persists under more fuel, and is unique.
- `eval_frame`: a fully reduced result persists when the store is extended (`EnvExtends`).
- `evalFully_some_exists`, `evalFully_of_value_true`, `evalFully_env_congr`: `evalFully`
  returns exactly the fully reduced results of `eval`, and it respects store agreement.
- `isValue_const_true`: literals are values.

Key definitions: `EnvExtends` (store extension), `Env.Idempotent` (no stored value mentions a
bound variable), `VarOrigin` (where a free variable of a result comes from).
-/

/-! ## Free variables under substitution and call decomposition -/

namespace Lambda
public section
open Strata

variable {Tbase : LExprParams}
  [DecidableEq Tbase.IDMeta]

omit [DecidableEq Tbase.IDMeta] in
/-- `liftBVars` does not change the free variables (only shifts de Bruijn indices). -/
theorem getVars_liftBVars (k : Nat) (e : LExpr Tbase.mono) (c : Nat) :
    LExpr.LExpr.getVars (LExpr.liftBVars k e c) = LExpr.LExpr.getVars e := by
  induction e generalizing c with
  | const | op | fvar => rfl
  | bvar m i => simp only [LExpr.liftBVars]; split <;> rfl
  | abs _ _ _ _ ih => simp only [LExpr.liftBVars, LExpr.LExpr.getVars]; exact ih (c + 1)
  | quant _ _ _ _ _ _ iht ihb =>
    simp only [LExpr.liftBVars, LExpr.LExpr.getVars]; rw [iht (c + 1), ihb (c + 1)]
  | app _ _ _ ih1 ih2 => simp only [LExpr.liftBVars, LExpr.LExpr.getVars]; rw [ih1 c, ih2 c]
  | ite _ _ _ _ ih1 ih2 ih3 =>
    simp only [LExpr.liftBVars, LExpr.LExpr.getVars]; rw [ih1 c, ih2 c, ih3 c]
  | eq _ _ _ ih1 ih2 => simp only [LExpr.liftBVars, LExpr.LExpr.getVars]; rw [ih1 c, ih2 c]

omit [DecidableEq Tbase.IDMeta] in
/-- `replaceUserProvidedType` does not change the free variables. -/
theorem getVars_replaceUserProvidedType (e : LExpr Tbase.mono)
    (f : LMonoTy → LMonoTy) :
    LExpr.LExpr.getVars (LExpr.replaceUserProvidedType e f) = LExpr.LExpr.getVars e := by
  induction e with
  | const | op | bvar | fvar => rfl
  | abs _ _ _ _ ih => simp only [LExpr.replaceUserProvidedType, LExpr.LExpr.getVars]; exact ih
  | quant _ _ _ _ _ _ iht ihb =>
    simp only [LExpr.replaceUserProvidedType, LExpr.LExpr.getVars]; rw [iht, ihb]
  | app _ _ _ ih1 ih2 => simp only [LExpr.replaceUserProvidedType, LExpr.LExpr.getVars]; rw [ih1, ih2]
  | ite _ _ _ _ ih1 ih2 ih3 =>
    simp only [LExpr.replaceUserProvidedType, LExpr.LExpr.getVars]; rw [ih1, ih2, ih3]
  | eq _ _ _ ih1 ih2 => simp only [LExpr.replaceUserProvidedType, LExpr.LExpr.getVars]; rw [ih1, ih2]

omit [DecidableEq Tbase.IDMeta] in
/-- `applyTypeSubst` does not change the free variables (only type annotations). -/
theorem getVars_applyTypeSubst (e : LExpr Tbase.mono) (S : Subst) :
    LExpr.LExpr.getVars (e.applyTypeSubst S) = LExpr.LExpr.getVars e := by
  unfold LExpr.applyTypeSubst
  split
  · rfl
  · exact getVars_replaceUserProvidedType e _

omit [DecidableEq Tbase.IDMeta] in
/-- `replaceMetadata1` does not change the free variables. -/
theorem getVars_replaceMetadata1 (r : Tbase.Metadata) (e : LExpr Tbase.mono) :
    LExpr.LExpr.getVars (LExpr.replaceMetadata1 r e) = LExpr.LExpr.getVars e := by
  cases e <;> rfl

omit [DecidableEq Tbase.IDMeta] in
/-- Free variables introduced by `mkApp` come from the head or an argument. -/
theorem getVars_mkApp_mem (m : Tbase.Metadata) (op : LExpr Tbase.mono)
    (args : List (LExpr Tbase.mono)) (y : Tbase.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars (LExpr.mkApp m op args)) :
    y ∈ LExpr.LExpr.getVars op ∨ ∃ a ∈ args, y ∈ LExpr.LExpr.getVars a := by
  induction args generalizing op with
  | nil => simp only [LExpr.mkApp] at hy; exact Or.inl hy
  | cons a rest ih =>
    simp only [LExpr.mkApp] at hy
    rcases ih (.app m op a) hy with h | ⟨b, hb, hby⟩
    · simp only [LExpr.LExpr.getVars, List.mem_append] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨a, List.mem_cons.mpr (Or.inl rfl), h⟩
    · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hby⟩

/-- Characterize the free variables introduced by `substFvarsLifting.go`. -/
private theorem getVars_substFvarsLifting_go_mem
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (e : LExpr Tbase.mono) (depth : Nat) (y : Tbase.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars (LExpr.substFvarsLifting.go sm e depth)) :
    (y ∈ LExpr.LExpr.getVars e ∧ Map.find? sm y = none) ∨
    (∃ k v, Map.find? sm k = some v ∧ y ∈ LExpr.LExpr.getVars v) := by
  induction e generalizing depth with
  | const | op | bvar =>
    simp only [LExpr.substFvarsLifting.go, LExpr.LExpr.getVars] at hy
    simp at hy
  | fvar m x ty =>
    simp only [LExpr.substFvarsLifting.go] at hy
    cases hf : Map.find? sm x with
    | none =>
      rw [hf] at hy
      simp only [LExpr.LExpr.getVars, List.mem_singleton] at hy
      subst hy
      exact Or.inl ⟨by simp [LExpr.LExpr.getVars], hf⟩
    | some v =>
      rw [hf] at hy
      rw [getVars_liftBVars] at hy
      exact Or.inr ⟨x, v, hf, hy⟩
  | abs _ _ _ _ ih =>
    simp only [LExpr.substFvarsLifting.go, LExpr.LExpr.getVars] at hy
    exact ih (depth + 1) hy
  | quant _ _ _ _ _ _ iht ihb =>
    simp only [LExpr.substFvarsLifting.go, LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with h | h
    · rcases iht (depth + 1) h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hin, hn⟩
      · exact Or.inr hr
    · rcases ihb (depth + 1) h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hin, hn⟩
      · exact Or.inr hr
  | app _ _ _ ih1 ih2 =>
    simp only [LExpr.substFvarsLifting.go, LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with h | h
    · rcases ih1 depth h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hin, hn⟩
      · exact Or.inr hr
    · rcases ih2 depth h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hin, hn⟩
      · exact Or.inr hr
  | ite _ _ _ _ ih1 ih2 ih3 =>
    simp only [LExpr.substFvarsLifting.go, LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with (h | h) | h
    · rcases ih1 depth h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl (Or.inl hin), hn⟩
      · exact Or.inr hr
    · rcases ih2 depth h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl (Or.inr hin), hn⟩
      · exact Or.inr hr
    · rcases ih3 depth h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hin, hn⟩
      · exact Or.inr hr
  | eq _ _ _ ih1 ih2 =>
    simp only [LExpr.substFvarsLifting.go, LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with h | h
    · rcases ih1 depth h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl hin, hn⟩
      · exact Or.inr hr
    · rcases ih2 depth h with ⟨hin, hn⟩ | hr
      · exact Or.inl ⟨by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hin, hn⟩
      · exact Or.inr hr

/-- Characterize the free variables introduced by `substFvarsLifting`. -/
theorem getVars_substFvarsLifting_mem
    (sm : Map Tbase.Identifier (LExpr Tbase.mono))
    (e : LExpr Tbase.mono) (y : Tbase.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars (LExpr.substFvarsLifting e sm)) :
    (y ∈ LExpr.LExpr.getVars e ∧ Map.find? sm y = none) ∨
    (∃ k v, Map.find? sm k = some v ∧ y ∈ LExpr.LExpr.getVars v) := by
  unfold LExpr.substFvarsLifting at hy
  split at hy
  · rename_i h_empty
    refine Or.inl ⟨hy, ?_⟩
    cases sm with
    | nil => rfl
    | cons p m => simp [Map.isEmpty] at h_empty
  · exact getVars_substFvarsLifting_go_mem sm e 0 y hy

omit [DecidableEq Tbase.IDMeta] in
/-- Free variables of the arguments extracted by `getLFuncCall.go` are contained
    in the free variables of the whole expression together with the accumulator. -/
private theorem getLFuncCall_go_getVars_mem
    (e : LExpr Tbase.mono) (acc : List (LExpr Tbase.mono))
    (op : LExpr Tbase.mono) (args : List (LExpr Tbase.mono))
    (h : getLFuncCall.go e acc = (op, args))
    (a : LExpr Tbase.mono) (ha : a ∈ args)
    (y : Tbase.Identifier) (hy : y ∈ LExpr.LExpr.getVars a) :
    y ∈ LExpr.LExpr.getVars e ∨ (∃ b ∈ acc, y ∈ LExpr.LExpr.getVars b) := by
  match e with
  | .app m1 (.app m2 e' arg1) arg2 =>
    simp only [getLFuncCall.go] at h
    rcases getLFuncCall_go_getVars_mem e' ([arg1, arg2] ++ acc) op args h a ha y hy with h1 | ⟨b, hb, hby⟩
    · exact Or.inl (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl (Or.inl h1))
    · simp only [List.cons_append, List.nil_append, List.mem_cons] at hb
      rcases hb with rfl | rfl | hb'
      · exact Or.inl (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inl (Or.inr hby))
      · exact Or.inl (by simp only [LExpr.LExpr.getVars, List.mem_append]; exact Or.inr hby)
      · exact Or.inr ⟨b, hb', hby⟩
  | .app m1 (.op m2 fn ty) arg1 =>
    simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h
    simp only [List.cons_append, List.nil_append, List.mem_cons] at ha
    rcases ha with rfl | ha'
    · exact Or.inl (by
        simp only [LExpr.LExpr.getVars, List.mem_append, List.not_mem_nil, false_or]; exact hy)
    · exact Or.inr ⟨a, ha', hy⟩
  | .app m1 (.const _ _) arg2 => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .app m1 (.bvar _ _) arg2 => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .app m1 (.fvar _ _ _) arg2 => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .app m1 (.abs _ _ _ _) arg2 => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .app m1 (.quant _ _ _ _ _ _) arg2 => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .app m1 (.ite _ _ _ _) arg2 => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .app m1 (.eq _ _ _) arg2 => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .const _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .op _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .bvar _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .fvar _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .abs _ _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .quant _ _ _ _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .ite _ _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  | .eq _ _ _ => simp only [getLFuncCall.go] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨a, ha, hy⟩
  termination_by e.sizeOf

omit [DecidableEq Tbase.IDMeta] in
/-- Free variables of a `callOfLFunc` argument are contained in the whole
    expression's free variables. -/
theorem callOfLFunc_getVars_args (F : @Factory Tbase) (e : LExpr Tbase.mono)
    (op : LExpr Tbase.mono) (args : List (LExpr Tbase.mono)) (f : LFunc Tbase)
    (h : F.callOfLFunc e = some (op, args, f))
    (a : LExpr Tbase.mono) (ha : a ∈ args)
    (y : Tbase.Identifier) (hy : y ∈ LExpr.LExpr.getVars a) :
    y ∈ LExpr.LExpr.getVars e := by
  have hget : getLFuncCall e = (op, args) := callOfLFunc_getLFuncCall h
  unfold getLFuncCall at hget
  rcases getLFuncCall_go_getVars_mem e [] op args hget a ha y hy with h1 | ⟨b, hb, _⟩
  · exact h1
  · simp at hb

omit [DecidableEq Tbase.IDMeta] in
/-- The free variables of a well-formed function body are among its inputs. -/
theorem lfunc_body_getVars_subset_keys
    (hIdent : ∀ a b : Tbase.Identifier, a.name = b.name → a = b)
    (lfunc : LFunc Tbase) (hwf : LFuncWF lfunc)
    (body : LExpr Tbase.mono) (hbody : lfunc.body = some body)
    (y : Tbase.Identifier) (hy : y ∈ LExpr.LExpr.getVars body) :
    y ∈ lfunc.inputs.keys := by
  rw [getVars_eq_freeVars_idents, List.mem_map] at hy
  obtain ⟨p, hp_mem, hp_eq⟩ := hy
  have hbf := hwf.toFuncWF.body_freevars body hbody
  have hname : y.name ∈ lfunc.inputs.map (fun q => q.1.name) := by
    apply hbf
    rw [List.mem_map]
    exact ⟨p, hp_mem, by rw [hp_eq]⟩
  obtain ⟨q, hq_mem, hq_eq⟩ := List.mem_map.mp hname
  have hyq : y = q.fst := (hIdent q.1 y hq_eq).symm
  rw [hyq, ListMap.keys_eq_map_fst]
  exact List.mem_map_of_mem hq_mem

end -- public section
end Lambda

/-! ## Stores: substitution, origins of variables, extension -/

namespace Lambda
public section
open Strata

/-- `substFvarsFromEnv` agrees on expressions when the environments agree on the
    free variables. -/
theorem substFvarsFromEnv_env_congr {Tbase : LExprParams}
    (env₁ env₂ : Env Tbase) (e : LExpr Tbase.mono)
    (hagree : ∀ x ∈ LExpr.LExpr.getVars e, env₁ x = env₂ x) :
    LExpr.substFvarsFromEnv env₁ e = LExpr.substFvarsFromEnv env₂ e := by
  induction e with
  | const | op | bvar => rfl
  | fvar m x ty =>
    simp only [LExpr.substFvarsFromEnv]
    rw [hagree x (by simp [LExpr.LExpr.getVars])]
  | abs _ _ _ _ ih => simp only [LExpr.substFvarsFromEnv]; rw [ih hagree]
  | quant _ _ _ _ _ _ iht ihb =>
    simp only [LExpr.substFvarsFromEnv]
    rw [iht (fun x hx => hagree x (List.mem_append_left _ hx)),
        ihb (fun x hx => hagree x (List.mem_append_right _ hx))]
  | app _ _ _ ih1 ih2 =>
    simp only [LExpr.substFvarsFromEnv]
    rw [ih1 (fun x hx => hagree x (List.mem_append_left _ hx)),
        ih2 (fun x hx => hagree x (List.mem_append_right _ hx))]
  | ite _ _ _ _ ih1 ih2 ih3 =>
    simp only [LExpr.substFvarsFromEnv]
    rw [ih1 (fun x hx => hagree x (List.mem_append_left _ (List.mem_append_left _ hx))),
        ih2 (fun x hx => hagree x (List.mem_append_left _ (List.mem_append_right _ hx))),
        ih3 (fun x hx => hagree x (List.mem_append_right _ hx))]
  | eq _ _ _ ih1 ih2 =>
    simp only [LExpr.substFvarsFromEnv]
    rw [ih1 (fun x hx => hagree x (List.mem_append_left _ hx)),
        ih2 (fun x hx => hagree x (List.mem_append_right _ hx))]

/-- No value the store holds mentions a variable the store binds. -/
@[expose] public def Env.Idempotent {T : LExprParams} (env : Env T) : Prop :=
  ∀ x v, env x = some v → ∀ y ∈ LExpr.LExpr.getVars v, env y = none

/-- `y` is an unbound variable of `e` or a variable of the value `env` gives a variable of `e`. -/
@[expose] public def VarOrigin {T : LExprParams} (env : Env T) (e : LExpr T.mono)
    (y : T.Identifier) : Prop :=
  (y ∈ LExpr.LExpr.getVars e ∧ env y = none) ∨
    ∃ x v, x ∈ LExpr.LExpr.getVars e ∧ env x = some v ∧ y ∈ LExpr.LExpr.getVars v

/-- A store whose values have no variables is idempotent. -/
public theorem Env.idempotent_of_getVars_nil {T : LExprParams} {env : Env T}
    (henv : ∀ x v, env x = some v → LExpr.LExpr.getVars v = []) : env.Idempotent := by
  intro x v hv y hy; rw [henv x v hv] at hy; simp at hy

/-- An origin of `y` in `a` is an origin in `b` when every variable of `a` is one of `b`. -/
theorem getVars_origin_mono {Tbase : LExprParams} {env : Env Tbase}
    {a b : LExpr Tbase.mono} {y : Tbase.Identifier}
    (hab : ∀ z ∈ LExpr.LExpr.getVars a, z ∈ LExpr.LExpr.getVars b)
    (hy : VarOrigin env a y) : VarOrigin env b y := by
  rcases hy with ⟨hya, hnone⟩ | ⟨x, v, hxa, hxv, hyv⟩
  · exact Or.inl ⟨hab y hya, hnone⟩
  · exact Or.inr ⟨x, v, hab x hxa, hxv, hyv⟩

/-- Every variable of `substFvarsFromEnv env e` is a variable of `e` that `env` does not
    bind, or a variable of the value `env` gives a variable of `e`. -/
theorem getVars_substFvarsFromEnv_origin {Tbase : LExprParams} (env : Env Tbase)
    (e : LExpr Tbase.mono) (y : Tbase.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars (LExpr.substFvarsFromEnv env e)) :
    VarOrigin env e y := by
  induction e with
  | const | op | bvar => simp [LExpr.substFvarsFromEnv, LExpr.LExpr.getVars] at hy
  | fvar m x ty =>
    simp only [LExpr.substFvarsFromEnv] at hy
    cases hv : env x with
    | none =>
      rw [hv] at hy
      simp only [LExpr.LExpr.getVars, List.mem_singleton] at hy
      subst hy
      exact Or.inl ⟨by simp [LExpr.LExpr.getVars], hv⟩
    | some v => rw [hv] at hy; exact Or.inr ⟨x, v, by simp [LExpr.LExpr.getVars], hv, hy⟩
  | abs _ _ _ _ ih => exact ih hy
  | quant _ _ _ _ _ _ iht ihb =>
    simp only [LExpr.substFvarsFromEnv, LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with h | h
    · exact getVars_origin_mono (fun z hz => by simp [LExpr.LExpr.getVars, hz]) (iht h)
    · exact getVars_origin_mono (fun z hz => by simp [LExpr.LExpr.getVars, hz]) (ihb h)
  | app _ _ _ ih1 ih2 =>
    simp only [LExpr.substFvarsFromEnv, LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with h | h
    · exact getVars_origin_mono (fun z hz => by simp [LExpr.LExpr.getVars, hz]) (ih1 h)
    · exact getVars_origin_mono (fun z hz => by simp [LExpr.LExpr.getVars, hz]) (ih2 h)
  | ite _ _ _ _ ih1 ih2 ih3 =>
    simp only [LExpr.substFvarsFromEnv, LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with (h | h) | h
    · exact getVars_origin_mono (fun z hz => by simp [LExpr.LExpr.getVars, hz]) (ih1 h)
    · exact getVars_origin_mono (fun z hz => by simp [LExpr.LExpr.getVars, hz]) (ih2 h)
    · exact getVars_origin_mono (fun z hz => by simp [LExpr.LExpr.getVars, hz]) (ih3 h)
  | eq _ _ _ ih1 ih2 =>
    simp only [LExpr.substFvarsFromEnv, LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with h | h
    · exact getVars_origin_mono (fun z hz => by simp [LExpr.LExpr.getVars, hz]) (ih1 h)
    · exact getVars_origin_mono (fun z hz => by simp [LExpr.LExpr.getVars, hz]) (ih2 h)

/-- `env'` extends `env`: every binding present in `env` is present, identically,
    in `env'`. -/
@[expose] def EnvExtends {T : LExprParams} (env env' : Env T) : Prop :=
  ∀ x w, env x = some w → env' x = some w

/-- If `x` is a free variable of `e` unbound by `env`, it survives
    `substFvarsFromEnv`: an unbound variable is left in place. -/
theorem getVars_mem_substFvarsFromEnv_of_none {Tbase : LExprParams}
    (env : Env Tbase) (e : LExpr Tbase.mono) (x : Tbase.Identifier)
    (hx : x ∈ LExpr.LExpr.getVars e) (hnone : env x = none) :
    x ∈ LExpr.LExpr.getVars (LExpr.substFvarsFromEnv env e) := by
  induction e with
  | const | op | bvar => simp [LExpr.LExpr.getVars] at hx
  | fvar m name ty =>
    simp only [LExpr.LExpr.getVars, List.mem_singleton] at hx
    subst hx
    simp only [LExpr.substFvarsFromEnv, hnone, LExpr.LExpr.getVars, List.mem_singleton]
  | abs _ _ _ _ ih => exact ih hx
  | quant _ _ _ _ _ _ iht ihb =>
    simp only [LExpr.substFvarsFromEnv, LExpr.LExpr.getVars, List.mem_append]
    simp only [LExpr.LExpr.getVars, List.mem_append] at hx
    rcases hx with h | h
    · exact Or.inl (iht h)
    · exact Or.inr (ihb h)
  | app _ _ _ ih1 ih2 =>
    simp only [LExpr.substFvarsFromEnv, LExpr.LExpr.getVars, List.mem_append]
    simp only [LExpr.LExpr.getVars, List.mem_append] at hx
    rcases hx with h | h
    · exact Or.inl (ih1 h)
    · exact Or.inr (ih2 h)
  | ite _ _ _ _ ih1 ih2 ih3 =>
    simp only [LExpr.substFvarsFromEnv, LExpr.LExpr.getVars, List.mem_append]
    simp only [LExpr.LExpr.getVars, List.mem_append] at hx
    rcases hx with (h | h) | h
    · exact Or.inl (Or.inl (ih1 h))
    · exact Or.inl (Or.inr (ih2 h))
    · exact Or.inr (ih3 h)
  | eq _ _ _ ih1 ih2 =>
    simp only [LExpr.substFvarsFromEnv, LExpr.LExpr.getVars, List.mem_append]
    simp only [LExpr.LExpr.getVars, List.mem_append] at hx
    rcases hx with h | h
    · exact Or.inl (ih1 h)
    · exact Or.inr (ih2 h)

/-- If `substFvarsFromEnv env e` is closed (no free variables), then `env` and
    any extension `env'` agree on all free variables of `e`: every such variable
    must be bound by `env` (else it would survive per
    `getVars_mem_substFvarsFromEnv_of_none`), and extension preserves those
    bindings. -/
theorem env_agree_of_subst_getVars_nil {Tbase : LExprParams}
    (env env' : Env Tbase) (hext : EnvExtends env env') (e : LExpr Tbase.mono)
    (hnil : LExpr.LExpr.getVars (LExpr.substFvarsFromEnv env e) = []) :
    ∀ x ∈ LExpr.LExpr.getVars e, env x = env' x := by
  intro x hx
  cases hxb : env x with
  | none =>
    exfalso
    have hmem := getVars_mem_substFvarsFromEnv_of_none env e x hx hxb
    rw [hnil] at hmem
    exact absurd hmem (by simp)
  | some w => rw [hext x w hxb]

end -- public section
end Lambda

namespace Lambda
public section
open Strata
open Std (ToFormat Format format)

variable {Tbase : LExprParams}
  [DecidableEq Tbase.IDMeta]
  [Inhabited Tbase.IDMeta]
  [Traceable LExpr.EvalProvenance Tbase.Metadata]

/-! ## Part I: Properties of `eval` -/

/-! ### `eval_value_isValue`

If `eval n F env e = (_, .value _)`, the `.fst` component satisfies
`isValue F _ = true`.  The main theorem `eval_value_isValue`
is preceded by per-sub-evaluator helpers (`evalApp_value_isValue`,
`evalEq_value_isValue`, `evalIte_value_isValue`,
`evalCore_value_isValue`) that carry the same statement at the
recursive level and are chained together by the top-level induction. -/

section eval_value_isValue

/-- Helper: if `evalApp` returns `.value _`, the result is a value. -/
private theorem evalApp_value_isValue
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (e e1 e2 : LExpr Tbase.mono)
    (ih_eval : ∀ e' b, (LExpr.eval n' F env e').snd = .value b →
        LExpr.isValue F (LExpr.eval n' F env e').fst = true)
    {b : Bool} (h : (LExpr.evalApp n' F env e e1 e2).snd = .value b) :
    LExpr.isValue F (LExpr.evalApp n' F env e e1 e2).fst = true := by
  have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
      p = LExpr.evalApp n' F env e e1 e2 →
      p.snd = .value b → LExpr.isValue F p.fst = true := by
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

/-- Helper: if `evalEq` returns `.value _`, the result is a value. -/
private theorem evalEq_value_isValue
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m : Tbase.Metadata) (e1 e2 : LExpr Tbase.mono)
    (_ih_eval : ∀ e' b, (LExpr.eval n' F env e').snd = .value b →
        LExpr.isValue F (LExpr.eval n' F env e').fst = true)
    {b : Bool} (h : (LExpr.evalEq n' F env m e1 e2).snd = .value b) :
    LExpr.isValue F (LExpr.evalEq n' F env m e1 e2).fst = true := by
  have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
      p = LExpr.evalEq n' F env m e1 e2 →
      p.snd = .value b → LExpr.isValue F p.fst = true := by
    intro p hp hv
    simp only [LExpr.evalEq] at hp
    generalize LExpr.eval n' F env e1 = r1 at hp
    generalize LExpr.eval n' F env e2 = r2 at hp
    generalize LExpr.eql F r1.fst r2.fst = eql_res at hp
    cases eql_res with
    | some b0 => subst hp; unfold LExpr.isValue; rfl
    | none => subst hp; simp at hv
  exact key _ rfl h

/-- Helper: if `evalIte` returns `.value _`, the result is a value. -/
private theorem evalIte_value_isValue
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m : Tbase.Metadata) (c t f : LExpr Tbase.mono)
    (ih_eval : ∀ e' b, (LExpr.eval n' F env e').snd = .value b →
        LExpr.isValue F (LExpr.eval n' F env e').fst = true)
    {b : Bool} (h : (LExpr.evalIte n' F env m c t f).snd = .value b) :
    LExpr.isValue F (LExpr.evalIte n' F env m c t f).fst = true := by
  have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
      p = LExpr.evalIte n' F env m c t f →
      p.snd = .value b → LExpr.isValue F p.fst = true := by
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

/-- Helper: if `evalCore` returns `.value _`, the result is a value.
    Requires an IH for `eval` at the same fuel level. -/
private theorem evalCore_value_isValue
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    (ih_eval : ∀ e' b, (LExpr.eval n' F env e').snd = .value b →
        LExpr.isValue F (LExpr.eval n' F env e').fst = true)
    {b : Bool} (h : (LExpr.evalCore n' F env e).snd = .value b) :
    LExpr.isValue F (LExpr.evalCore n' F env e).fst = true := by
  have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
      p = LExpr.evalCore n' F env e →
      p.snd = .value b → LExpr.isValue F p.fst = true := by
    intro p hp hv
    cases e with
    | const m c =>
      simp only [LExpr.evalCore] at hp ; subst hp; unfold LExpr.isValue; rfl
    | op m n args =>
      simp only [LExpr.evalCore] at hp ; subst hp; simp at hv
    | bvar m n =>
      simp only [LExpr.evalCore] at hp; subst hp; simp at hv
    | fvar m x ty =>
      simp only [LExpr.evalCore] at hp
      split at hp
      · -- env x = some v
        subst hp
        rename_i v hx
        simp only at hv
        by_cases hcan : LExpr.isValue F v = true
        · rw [ite_eq_left hcan]; exact hcan
        · rw [ite_eq_right hcan] at hv; simp at hv
      · -- env x = none
        subst hp; simp at hv
    | abs m n ty body =>
      simp only [LExpr.evalCore] at hp
      subst hp
      simp only at hv
      by_cases hcan : LExpr.isValue F (LExpr.substFvarsFromEnv env (.abs m n ty body)) = true
      · rw [ite_eq_left hcan]; exact hcan
      · rw [ite_eq_right hcan] at hv; simp at hv
    | quant m q n ty tr body =>
      simp only [LExpr.evalCore] at hp
      subst hp
      cases hv
    | app m e1 e2 =>
      simp only [LExpr.evalCore] at hp
      subst hp
      exact evalApp_value_isValue n' F env _ _ _ ih_eval hv
    | eq m e1 e2 =>
      simp only [LExpr.evalCore] at hp
      subst hp
      exact evalEq_value_isValue n' F env _ _ _ ih_eval hv
    | ite m c t f =>
      simp only [LExpr.evalCore] at hp
      subst hp
      exact evalIte_value_isValue n' F env _ _ _ _ ih_eval hv
  exact key _ rfl h

/-- Helper: if `evalShortCircuit` returns `.value _`, the result is a value. -/
private theorem evalShortCircuit_value_isValue
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (e op_expr a : LExpr Tbase.mono) (rest : List (LExpr Tbase.mono))
    (ceval : ConcreteEval Tbase)
    (ih_eval : ∀ e' b, (LExpr.eval n' F env e').snd = .value b →
        LExpr.isValue F (LExpr.eval n' F env e').fst = true)
    {b : Bool} (h : (LExpr.evalShortCircuit n' F env e op_expr a rest ceval).snd = .value b) :
    LExpr.isValue F (LExpr.evalShortCircuit n' F env e op_expr a rest ceval).fst = true := by
  simp only [LExpr.evalShortCircuit, LExpr.combineEvalResValueFlag_eq_pair] at h ⊢
  split
  · rename_i e' _
    rename_i heq
    simp only [heq] at h
    rcases h_split : (LExpr.eval n' F env e').snd with _ | b0 | _
    · rw [h_split] at h; simp [LExpr.EvalResult.combineValueFlag] at h
    · exact ih_eval _ b0 h_split
    · rw [h_split] at h; simp [LExpr.EvalResult.combineValueFlag] at h
  · rename_i heq
    simp only [heq] at h
    exact absurd h LExpr.EvalResult.noConfusion

/-- If `eval` returns `.value _`, the resulting expression satisfies `isValue`. -/
theorem eval_value_isValue
    (n : Nat) (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    {b : Bool} (h : (LExpr.eval n F env e).snd = .value b) :
    LExpr.isValue F (LExpr.eval n F env e).fst = true := by
  induction n generalizing e b with
  | zero =>
    have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
        p = LExpr.eval 0 F env e →
        p.snd = .value b → LExpr.isValue F p.fst = true := by
      intro p hp hv
      simp only [LExpr.eval] at hp
      subst hp
      by_cases hcan : LExpr.isValue F e = true
      · rw [ite_eq_left hcan]; exact hcan
      · rw [ite_eq_right hcan] at hv; simp at hv
    exact key _ rfl h
  | succ n' ih =>
    have key : ∀ (p : LExpr Tbase.mono × LExpr.EvalResult),
        p = LExpr.eval (n' + 1) F env e →
        p.snd = .value b → LExpr.isValue F p.fst = true := by
      intro p hp hv
      simp only [LExpr.eval, LExpr.List_map_fst_map_eval,
        LExpr.List_all_snd_isValueTrue_map_eval, LExpr.combineEvalResValueFlag_eq_pair] at hp
      split at hp
      · -- isValue F e = true
        rename_i h_can
        subst hp; exact h_can
      · -- isValue F e = false
        rename_i h_not_can
        split at hp
        · -- callOfLFunc = some (op_expr, args, lfunc)
          rename_i op_expr args lfunc h_call
          split at hp
          · -- shortCircuit call
            subst hp
            exact evalShortCircuit_value_isValue n' F env e op_expr _ _ _
              (fun e' b' h' => ih e' h') hv
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
                ((lfunc.body.get _).applyTypeSubst tySubst)
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
            rw [dite_eq_right h_not_cond] at hv
            cases h_fEC : Strata.DL.Util.FuncAttr.findEvalIfConstr lfunc.attr <;>
            cases h_fEV : Strata.DL.Util.FuncAttr.findEvalIfValue lfunc.attr <;> (
              simp only [h_fEC, h_fEV] at hv ⊢
              split at hv
              · -- inner if true: match concreteEval ...
                rename_i h_eval_cond
                rw [ite_eq_left h_eval_cond]
                split at hv
                · -- concreteEval = none: the rebuilt call is certified exactly
                  -- when it is a value
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
          exact evalCore_value_isValue n' F env e (fun e' b' h' => ih e' h') hv
    exact key _ rfl h

end eval_value_isValue

/-! ### `eval_value_identity`

If `e` is a value (`isValue F e = true`), `eval` at any fuel returns
`(e, .value true)`.  A short one-line lemma — no helpers needed. -/

section eval_value_identity

/-- If `isValue F e = true`, eval returns `(e, .value true)`. -/
theorem eval_value_identity
    (n : Nat) (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono)
    (hcan : LExpr.isValue F e = true) :
    LExpr.eval n F env e = (e, .value true) := by
  cases n <;> (simp only [LExpr.eval]; rw [ite_eq_left hcan])

end eval_value_identity

/-! ### `eval_getVars_origin`

Under an idempotent store, every free variable of `eval`'s result has an origin
in the input.  Preceded by per-sub-evaluator `getVars_origin` helpers, chained by induction on
fuel.  `eval_getVars_subset` follows. -/

section eval_getVars_origin

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

omit [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta]
  [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- Under an idempotent store, an origin of `y` in `a` is an origin in `b` when every
    variable of `a` is one of `b` or has an origin in `b`. -/
private theorem getVars_origin_trans {env : Env Tbase}
    (hidem : env.Idempotent)
    {a b : LExpr Tbase.mono} {y : Tbase.Identifier}
    (hab : ∀ z ∈ LExpr.LExpr.getVars a, z ∈ LExpr.LExpr.getVars b ∨ VarOrigin env b z)
    (hy : VarOrigin env a y) : VarOrigin env b y := by
  rcases hy with ⟨hya, hnone⟩ | ⟨x, v, hxa, hxv, hyv⟩
  · rcases hab y hya with h | h
    · exact Or.inl ⟨h, hnone⟩
    · exact h
  · rcases hab x hxa with h | ⟨_, hnone⟩ | ⟨x', v', _, hx'v', hxv'⟩
    · exact Or.inr ⟨x, v, h, hxv, hyv⟩
    · rw [hnone] at hxv; cases hxv
    · rw [hidem x' v' hx'v' x hxv'] at hxv; cases hxv

/-- Every free variable of `evalIte`'s result has an origin in the `.ite`. -/
private theorem evalIte_getVars_origin (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m : Tbase.Metadata) (c t f : LExpr Tbase.mono)
    (ih : ∀ e', ∀ z ∈ LExpr.LExpr.getVars (LExpr.eval n' F env e').fst, VarOrigin env e' z)
    (y : Tbase.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars (LExpr.evalIte n' F env m c t f).fst) :
    VarOrigin env (LExpr.ite m c t f) y := by
  have sub : ∀ a, (∀ z ∈ LExpr.LExpr.getVars a, z ∈ LExpr.LExpr.getVars (LExpr.ite m c t f)) →
      y ∈ LExpr.LExpr.getVars (LExpr.eval n' F env a).fst → _ :=
    fun a hsub hya => getVars_origin_mono hsub (ih a y hya)
  simp only [LExpr.evalIte] at hy
  split at hy
  · exact sub t (fun z hz => by simp [LExpr.LExpr.getVars, hz]) hy
  · exact sub f (fun z hz => by simp [LExpr.LExpr.getVars, hz]) hy
  · simp only [LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with (h | h) | h
    · exact sub c (fun z hz => by simp [LExpr.LExpr.getVars, hz]) h
    · exact sub t (fun z hz => by simp [LExpr.LExpr.getVars, hz]) h
    · exact sub f (fun z hz => by simp [LExpr.LExpr.getVars, hz]) h

/-- Every free variable of `evalEq`'s result has an origin in the `.eq`. -/
private theorem evalEq_getVars_origin (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (m : Tbase.Metadata) (e1 e2 : LExpr Tbase.mono)
    (ih : ∀ e', ∀ z ∈ LExpr.LExpr.getVars (LExpr.eval n' F env e').fst, VarOrigin env e' z)
    (y : Tbase.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars (LExpr.evalEq n' F env m e1 e2).fst) :
    VarOrigin env (LExpr.eq m e1 e2) y := by
  simp only [LExpr.evalEq] at hy
  split at hy
  · simp [LExpr.LExpr.getVars] at hy
  · simp only [LExpr.LExpr.getVars, List.mem_append] at hy
    rcases hy with h | h
    · exact getVars_origin_mono (fun z hz => by simp [LExpr.LExpr.getVars, hz]) (ih e1 y h)
    · exact getVars_origin_mono (fun z hz => by simp [LExpr.LExpr.getVars, hz]) (ih e2 y h)

/-- Every free variable of `evalApp`'s result has an origin in the application. -/
private theorem evalApp_getVars_origin (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (hidem : env.Idempotent)
    (m : Tbase.Metadata) (e1 e2 : LExpr Tbase.mono)
    (ih : ∀ e', ∀ z ∈ LExpr.LExpr.getVars (LExpr.eval n' F env e').fst, VarOrigin env e' z)
    (y : Tbase.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars (LExpr.evalApp n' F env (LExpr.app m e1 e2) e1 e2).fst) :
    VarOrigin env (LExpr.app m e1 e2) y := by
  have h1 := fun z hz => getVars_origin_mono (b := LExpr.app m e1 e2)
    (fun w hw => by simp [LExpr.LExpr.getVars, hw]) (ih e1 z hz)
  have h2 := fun z hz => getVars_origin_mono (b := LExpr.app m e1 e2)
    (fun w hw => by simp [LExpr.LExpr.getVars, hw]) (ih e2 z hz)
  simp only [LExpr.evalApp] at hy
  split at hy
  · -- abs arm: every variable of the substituted body has an origin in the application
    rename_i mAbs nm ty0 body1' heq
    have key : ∀ (s : Tbase.Metadata → LExpr Tbase.mono),
        (∀ md, LExpr.LExpr.getVars (s md) = LExpr.LExpr.getVars (LExpr.eval n' F env e2).fst) →
        ∀ z ∈ LExpr.LExpr.getVars (LExpr.subst s body1'),
          VarOrigin env (LExpr.app m e1 e2) z := by
      intro s hs z hz
      simp only [LExpr.subst] at hz
      rcases getVars_substK_mem 0 _ body1' z hz with hb | ⟨mv, hmv⟩
      · exact h1 z (by rw [heq]; exact hb)
      · rw [hs] at hmv; exact h2 z hmv
    split at hy
    · rename_i h_eq
      rw [gv_eq_of_eqModuloMeta _ _ h_eq] at hy
      exact key _ (fun _ => getVars_replaceMetadata1 _ _) y hy
    · exact getVars_origin_trans hidem
        (fun z hz => Or.inr (key _ (fun _ => getVars_replaceMetadata1 _ _) z hz)) (ih _ y hy)
  · -- default arm
    have key : ∀ z ∈ LExpr.LExpr.getVars (LExpr.app m (LExpr.eval n' F env e1).fst
        (LExpr.eval n' F env e2).fst),
          VarOrigin env (LExpr.app m e1 e2) z := by
      intro z hz
      simp only [LExpr.LExpr.getVars, List.mem_append] at hz
      rcases hz with h | h
      · exact h1 z h
      · exact h2 z h
    split at hy
    · rename_i h_eq
      rw [gv_eq_of_eqModuloMeta _ _ h_eq] at hy
      exact key y hy
    · exact getVars_origin_trans hidem (fun z hz => Or.inr (key z hz)) (ih _ y hy)

/-- Every free variable of `evalCore`'s result has an origin in its input. -/
private theorem evalCore_getVars_origin (n' : Nat) (F : @Factory Tbase) (env : Env Tbase)
    (hidem : env.Idempotent)
    (e : LExpr Tbase.mono)
    (ih : ∀ e', ∀ z ∈ LExpr.LExpr.getVars (LExpr.eval n' F env e').fst, VarOrigin env e' z)
    (y : Tbase.Identifier)
    (hy : y ∈ LExpr.LExpr.getVars (LExpr.evalCore n' F env e).fst) :
    VarOrigin env e y := by
  cases e with
  | const _ _ => simp [LExpr.evalCore, LExpr.LExpr.getVars] at hy
  | op _ _ _ => simp [LExpr.evalCore, LExpr.LExpr.getVars] at hy
  | bvar _ _ => simp [LExpr.evalCore, LExpr.LExpr.getVars] at hy
  | fvar m x ty =>
    simp only [LExpr.evalCore] at hy
    cases hv : env x with
    | none =>
      simp only [hv, LExpr.LExpr.getVars, List.mem_singleton] at hy
      subst hy
      exact Or.inl ⟨by simp [LExpr.LExpr.getVars], hv⟩
    | some v =>
      simp only [hv] at hy
      exact Or.inr ⟨x, v, by simp [LExpr.LExpr.getVars], hv, hy⟩
  | abs m n ty body =>
    simp only [LExpr.evalCore] at hy
    exact getVars_substFvarsFromEnv_origin env _ y hy
  | quant m qk n ty tr body =>
    simp only [LExpr.evalCore] at hy
    exact getVars_substFvarsFromEnv_origin env _ y hy
  | app m e1 e2 =>
    simp only [LExpr.evalCore] at hy
    exact evalApp_getVars_origin n' F env hidem m e1 e2 ih y hy
  | eq m e1 e2 =>
    simp only [LExpr.evalCore] at hy
    exact evalEq_getVars_origin n' F env m e1 e2 ih y hy
  | ite m c t f =>
    simp only [LExpr.evalCore] at hy
    exact evalIte_getVars_origin n' F env m c t f ih y hy

/-- If no value the store holds mentions a variable the store binds (`Env.Idempotent`), then
    every variable of `eval`'s result is an unbound variable of `e`, or a variable of the value
    the store gives a variable of `e` (`VarOrigin`). -/
public theorem eval_getVars_origin
    (hIdent : ∀ a b : Tbase.Identifier, a.name = b.name → a = b)
    (F : @Factory Tbase) (env : Env Tbase) (n : Nat) (e : LExpr Tbase.mono)
    (hWF : FactoryWF F)
    (hidem : env.Idempotent) :
    ∀ y ∈ LExpr.LExpr.getVars (LExpr.eval n F env e).fst, VarOrigin env e y := by
  induction n generalizing e with
  | zero =>
    intro y hy; simp only [LExpr.eval] at hy
    split at hy
    · rename_i hv; rw [isValue_getVars_nil F e hv] at hy; simp at hy
    · exact getVars_substFvarsFromEnv_origin env e y hy
  | succ n' ih =>
    intro y hy
    simp only [LExpr.eval, LExpr.List_map_fst_map_eval,
      LExpr.List_all_snd_isValueTrue_map_eval, LExpr.combineEvalResValueFlag_eq_pair] at hy
    revert hy
    split
    · -- value: (e, .value), which has no free variables
      rename_i hv; intro hy; rw [isValue_getVars_nil F e hv] at hy; simp at hy
    · split
      · -- factory call
        rename_i op_expr args lfunc h_call
        have h_mem := callOfLFunc_func_mem F _ _ _ lfunc false h_call
        have h_wf := hWF.lfuncs_wf lfunc h_mem
        obtain ⟨mo, no, to, hop_eq, _, h_arity⟩ := callOfLFunc_eq_some h_call
        -- a free variable of an evaluated argument has an origin in `e`
        have h_arg : ∀ a ∈ args, ∀ z ∈ LExpr.LExpr.getVars (LExpr.eval n' F env a).fst, _ :=
          fun a ha z hz => getVars_origin_mono
            (callOfLFunc_getVars_args F e op_expr args lfunc h_call a ha) (ih a z hz)
        -- so does a free variable of the call rebuilt from the evaluated arguments
        have h_app : ∀ z ∈ LExpr.LExpr.getVars (@LExpr.mkApp Tbase.mono e.metadata op_expr
            (args.map (fun a => (LExpr.eval n' F env a).fst))),
              VarOrigin env e z := by
          intro z hz
          rcases getVars_mkApp_mem _ _ _ z hz with hop | ⟨a, ha_mem, hza⟩
          · rw [hop_eq] at hop; simp [LExpr.LExpr.getVars] at hop
          · rw [List.mem_map] at ha_mem
            obtain ⟨a0, ha0_mem, ha0_eq⟩ := ha_mem
            exact h_arg a0 ha0_mem z (by rw [ha0_eq]; exact hza)
        split
        · -- shortCircuit call
          rename_i a rest ceval h_sc
          obtain ⟨h_args, h_ce⟩ := LExpr.shortCircuitCall?_some h_sc
          subst h_args
          simp only [LExpr.evalShortCircuit, LExpr.combineEvalResValueFlag_eq_pair]
          split
          · rename_i e' h_if
            intro hy
            have h_ceval :
                ceval e.metadata op_expr.opTy? ((LExpr.eval n' F env a).fst :: rest) = some e' := by
              split at h_if
              · exact h_if
              · simp at h_if
            refine getVars_origin_trans hidem (fun z hz => ?_) (ih _ y hy)
            obtain ⟨x, hx_mem, hzx⟩ :=
              h_wf.concreteEval_freeVars ceval h_ce _ _ _ e' h_ceval z hz
            rcases List.mem_cons.mp hx_mem with rfl | hx_rest
            · exact Or.inr (h_arg a (by simp) z hzx)
            · exact Or.inl (callOfLFunc_getVars_args F e op_expr _ lfunc h_call x
                (by simp [hx_rest]) z hzx)
          · intro hy
            rcases getVars_mkApp_mem _ _ _ y hy with hop | ⟨x, hx_mem, hyx⟩
            · rw [hop_eq] at hop; simp [LExpr.LExpr.getVars] at hop
            · rcases List.mem_cons.mp hx_mem with rfl | hx_rest
              · exact h_arg a (by simp) y hyx
              · rw [List.mem_map] at hx_rest
                obtain ⟨x0, hx0, rfl⟩ := hx_rest
                exact h_arg x0 (by simp [hx0]) y hyx
        split
        · -- inline
          rename_i h_cond
          split
          · -- computeTypeSubst = some tySubst → eval n' new_e
            rename_i tySubst h_ts
            intro hy
            refine getVars_origin_trans hidem (fun z hz => Or.inr ?_) (ih _ y hy)
            rcases getVars_substFvarsLifting_mem _ _ z hz with ⟨hin, hnone⟩ | ⟨k, v, hk, hv⟩
            · exfalso
              rw [getVars_applyTypeSubst] at hin
              have hsome : lfunc.body.isSome = true := by
                simp only [Bool.and_eq_true] at h_cond; exact h_cond.1
              have hbody_eq : lfunc.body = some (lfunc.body.get hsome) := by
                simp [Option.some_get]
              have hz_key := lfunc_body_getVars_subset_keys hIdent lfunc h_wf _ hbody_eq z hin
              have h_len : lfunc.inputs.keys.length =
                  (args.map (fun a => (LExpr.eval n' F env a).fst)).length := by
                rw [ListMap.keys_eq_map_fst]; exact (List.length_map _).trans (h_arity.symm.trans (List.length_map _).symm)
              have h_mem_keys : z ∈ Map.keys (lfunc.inputs.keys.zip
                  (args.map (fun a => (LExpr.eval n' F env a).fst))) := by
                rw [Map.keys_eq_map_fst (lfunc.inputs.keys.zip _), List.map_fst_zip (by omega)]
                exact hz_key
              exact Map_find?_ne_none_of_mem_keys _ z h_mem_keys hnone
            · have hv_mem : v ∈ (lfunc.inputs.keys.zip
                  (args.map (fun a => (LExpr.eval n' F env a).fst))).map Prod.snd :=
                Map_find?_some_mem_values _ k v hk
              have hv_args' : v ∈ args.map (fun a => (LExpr.eval n' F env a).fst) :=
                List.mem_map_snd_zip _ _ v hv_mem
              rw [List.mem_map] at hv_args'
              obtain ⟨a, ha_mem, ha_eq⟩ := hv_args'
              exact h_arg a ha_mem z (by rw [ha_eq]; exact hv)
          · -- computeTypeSubst = none → (mkApp, .nonvalue)
            exact h_app y
        · -- non-inline
          cases h_fEC : Strata.DL.Util.FuncAttr.findEvalIfConstr lfunc.attr <;>
          cases h_fEV : Strata.DL.Util.FuncAttr.findEvalIfValue lfunc.attr <;> (
            simp only []
            split
            · -- value/constr condition holds
              split
              · -- concreteEval = none → (mkApp, .nonvalue)
                exact h_app y
              · -- concreteEval = some ceval
                rename_i ceval h_ce
                split
                · -- ceval succeeds → eval n' e'
                  rename_i e'c h_ceval_eq
                  intro hy
                  refine getVars_origin_trans hidem (fun z hz => Or.inr ?_) (ih _ y hy)
                  obtain ⟨a, ha_mem, hza⟩ :=
                    h_wf.concreteEval_freeVars ceval h_ce _ _ _ e'c h_ceval_eq z hz
                  rw [List.mem_map] at ha_mem
                  obtain ⟨a0, ha0_mem, ha0_eq⟩ := ha_mem
                  exact h_arg a0 ha0_mem z (by rw [ha0_eq]; exact hza)
                · -- ceval fails → (mkApp, .nonvalue)
                  exact h_app y
            · -- symbolic args → (mkApp, .nonvalue)
              exact h_app y
          )
      · -- evalCore
        intro hy
        exact evalCore_getVars_origin n' F env hidem e ih y hy

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
  intro e y hy
  rcases eval_getVars_origin hIdent F env n e hWF (Env.idempotent_of_getVars_nil henv) y hy with
    ⟨h, _⟩ | ⟨x, v, _, hv, hyv⟩
  · exact h
  · rw [henv x v hv] at hyv; simp at hyv

end eval_getVars_origin

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
  | zero => intro e hag; simp only [LExpr.eval, substFvarsFromEnv_env_congr env₁ env₂ e hag]
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
        · -- shortCircuit call
          rename_i a rest ceval h_sc
          obtain ⟨h_args, h_ce⟩ := LExpr.shortCircuitCall?_some h_sc
          subst h_args
          have h_arg : ∀ x ∈ a :: rest, LExpr.eval n' F env₁ x = LExpr.eval n' F env₂ x := by
            intro x hx; apply ih x; intro z hz
            exact hag z (callOfLFunc_getVars_args F e op_expr (a :: rest) lfunc h_call x hx z hz)
          simp only [LExpr.evalShortCircuit, LExpr.combineEvalResValueFlag_eq_pair]
          rw [h_arg a (by simp)]
          split
          · rename_i e' h_if
            have h_ceval :
                ceval e.metadata op_expr.opTy? ((LExpr.eval n' F env₂ a).fst :: rest) =
                  some e' := by
              split at h_if
              · exact h_if
              · simp at h_if
            have h_ih_new : LExpr.eval n' F env₁ e' = LExpr.eval n' F env₂ e' := by
              apply ih; intro x hx
              obtain ⟨y, hy_mem, hxy⟩ :=
                h_wf.concreteEval_freeVars ceval h_ce _ _ _ e' h_ceval x hx
              rcases List.mem_cons.mp hy_mem with rfl | hy_rest
              · exact hag x (callOfLFunc_getVars_args F e op_expr _ lfunc h_call a (by simp) x
                  (eval_getVars_subset hIdent F env₂ hWF henv₂ n' a x hxy))
              · exact hag x (callOfLFunc_getVars_args F e op_expr _ lfunc h_call y
                  (by simp [hy_rest]) x hxy)
            rw [h_ih_new]
          · have hrest : rest.map (fun x => (LExpr.eval n' F env₁ x).fst) =
                rest.map (fun x => (LExpr.eval n' F env₂ x).fst) :=
              List.map_congr_left (fun x hx => by rw [h_arg x (by simp [hx])])
            rw [hrest]
        split
        · -- inline
          rename_i h_cond
          split
          · -- computeTypeSubst some → eval env new_e
            rename_i tySubst h_ts
            generalize h_new_e :
              LExpr.substFvarsLifting
                ((lfunc.body.get (by simp only [Bool.and_eq_true] at h_cond; exact h_cond.1)).applyTypeSubst tySubst)
                (lfunc.inputs.keys.zip
                  (List.map (fun a => (LExpr.eval n' F env₂ a).fst) args)) = new_e
            have h_ih_new : LExpr.eval n' F env₁ new_e = LExpr.eval n' F env₂ new_e := by
              apply ih
              intro x hx
              rw [← h_new_e] at hx
              rcases getVars_substFvarsLifting_mem _ _ x hx with ⟨hin, hnone⟩ | ⟨k, v, hk, hv⟩
              · exfalso
                rw [getVars_applyTypeSubst] at hin
                have hsome : lfunc.body.isSome = true := by
                  simp only [Bool.and_eq_true] at h_cond; exact h_cond.1
                have hbody_eq : lfunc.body = some (lfunc.body.get hsome) := by
                  simp [Option.some_get]
                have hy_key := lfunc_body_getVars_subset_keys hIdent lfunc h_wf _ hbody_eq x hin
                have h_len : lfunc.inputs.keys.length =
                    (args.map (fun a => (LExpr.eval n' F env₂ a).fst)).length := by
                  rw [ListMap.keys_eq_map_fst]; exact (List.length_map _).trans (h_arity.symm.trans (List.length_map _).symm)
                have h_mem_keys : x ∈ Map.keys (lfunc.inputs.keys.zip
                    (args.map (fun a => (LExpr.eval n' F env₂ a).fst))) := by
                  rw [Map.keys_eq_map_fst (lfunc.inputs.keys.zip _), List.map_fst_zip (by omega)]
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
          cases h_fEV : Strata.DL.Util.FuncAttr.findEvalIfValue lfunc.attr <;> (
            simp only []
            split
            · -- value/constr cond holds
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
                    have hexists := h_wf.concreteEval_freeVars ceval h_ce _ _ _ e'c h_ceval_eq x hx
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

The fuel-free `evalFully = evalFullyAux 0` wrapper: existence characterization and
environment congruence. -/

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
      have := congrArg Prod.fst h; simp only at this; exact this
    have h_snd_and : (LExpr.eval n' F env br).snd.combineValueFlag
        (LExpr.eval n' F env c).snd.isValueTrue = .value true := by
      have := congrArg Prod.snd h; simp only at this; exact this
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
      have := congrArg Prod.fst h; simp only at this; exact this
    have h_snd_pair : (LExpr.eval n' F env e1).snd.isValueTrue = true ∧
                      (LExpr.eval n' F env e2).snd.isValueTrue = true := by
      have := congrArg Prod.snd h; simp only [LExpr.EvalResult.value.injEq, Bool.and_eq_true] at this ; exact this
    have h_e1_snd : LExpr.eval n' F env e1 =
        ((LExpr.eval n' F env e1).fst, .value true) := by
      rw [← (isValueTrue_eq_true_iff _).mp h_snd_pair.1]
    have h_e2_snd : LExpr.eval n' F env e2 =
        ((LExpr.eval n' F env e2).fst, .value true) := by
      rw [← (isValueTrue_eq_true_iff _).mp h_snd_pair.2]
    rw [ih_eval _ _ h_e1_snd, ih_eval _ _ h_e2_snd]
    simp only
    rw [h_eql]
    simp only [LExpr.EvalResult.isValueTrue, Bool.and_self, Prod.mk.injEq, and_true]
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
      have := congrArg Prod.fst h; simp only at this; exact this
    have h_snd : (LExpr.eval n' F env inner).snd.combineValueFlag
        ((LExpr.eval n' F env e1).snd.isValueTrue &&
         (LExpr.eval n' F env e2).snd.isValueTrue) = .value true := by
      have := congrArg Prod.snd h; simp only at this; exact this
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
      rw [ite_eq_right h_neq, h_inner_lift]
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
        rw [ite_eq_right h_neq, h_inner_lift]
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

/-- A fully-reduced `evalShortCircuit` result carries over to any fuel and
    environment at which `eval` reproduces the fully-reduced results of the first
    fuel and environment. Gives both fuel monotonicity and the frame lemma. -/
private theorem evalShortCircuit_value_true_transfer
    (n₁ n₂ : Nat) (F : @Factory Tbase) (env₁ env₂ : Env Tbase)
    (e op_expr a : LExpr Tbase.mono) (rest : List (LExpr Tbase.mono))
    (ceval : ConcreteEval Tbase)
    (v : LExpr Tbase.mono)
    (ih_eval : ∀ e' v', LExpr.eval n₁ F env₁ e' = (v', .value true) →
        LExpr.eval n₂ F env₂ e' = (v', .value true))
    (h : LExpr.evalShortCircuit n₁ F env₁ e op_expr a rest ceval = (v, .value true)) :
    LExpr.evalShortCircuit n₂ F env₂ e op_expr a rest ceval = (v, .value true) := by
  unfold LExpr.evalShortCircuit at h ⊢
  simp only [LExpr.combineEvalResValueFlag_eq_pair] at h ⊢
  split at h
  · rename_i e' h_if
    simp only [Prod.mk.injEq] at h
    obtain ⟨h_fst, h_snd⟩ := h
    obtain ⟨h_e', h_a⟩ := (andValue_eq_valueTrue_iff _ _).mp h_snd
    have ha_lift := ih_eval a _ (Prod.ext rfl ((isValueTrue_eq_true_iff _).mp h_a))
    have he_lift := ih_eval e' _ (Prod.ext h_fst h_e')
    rw [ha_lift]
    dsimp only
    rw [h_if]
    dsimp only
    rw [he_lift]
    simp [LExpr.EvalResult.combineValueFlag, LExpr.EvalResult.isValueTrue]
  · simp at h

/-- **Fuel monotonicity for `.value true`.** If `eval m F env e = (v, .value true)`,
    then `eval (m+1) F env e = (v, .value true)`. -/
theorem eval_value_true_mono (F : @Factory Tbase) (env : Env Tbase)
    (m : Nat) (e : LExpr Tbase.mono) (v : LExpr Tbase.mono)
    (h : LExpr.eval m F env e = (v, .value true)) :
    LExpr.eval (m+1) F env e = (v, .value true) := by
  induction m generalizing e v with
  | zero =>
    simp only [LExpr.eval] at h
    by_cases hcan : LExpr.isValue F e = true
    · rw [ite_eq_left hcan] at h
      have hfe : v = e := by
        have := congrArg Prod.fst h; simp only at this; exact this.symm
      subst hfe
      exact eval_value_identity (0 + 1) F env v hcan
    · rw [ite_eq_right hcan] at h
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
        have := congrArg Prod.fst h; simp only at this; exact this.symm
      subst hfe
      exact eval_value_identity (n' + 1 + 1) F env v hcan
    · rename_i h_not_can
      split
      · rename_i op_expr args lfunc h_call
        split
        · -- shortCircuit call
          rename_i a rest ceval h_sc
          intro h
          have h_lift := evalShortCircuit_value_true_transfer n' (n'+1) F env env e op_expr
            a rest ceval v (fun e' v' hev => ih e' v' hev) h
          simp only [LExpr.eval]
          rw [ite_eq_right h_not_can, h_call]
          dsimp only
          rw [h_sc]
          exact h_lift
        rename_i h_sc
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
                ((lfunc.body.get h_body_isSome).applyTypeSubst tySubst)
                (lfunc.inputs.keys.zip
                  (List.map (fun a => (LExpr.eval n' F env a).fst) args))
            have h_fst : (LExpr.eval n' F env inner).fst = v := by
              have := congrArg Prod.fst h; simp only [List.all_map, List.map_map, LExpr.combineEvalResValueFlag_eq_pair] at this ; exact this
            have h_snd_and : (LExpr.eval n' F env inner).snd.combineValueFlag
                (args.all fun a => (LExpr.eval n' F env a).snd.isValueTrue) = .value true := by
              have := congrArg Prod.snd h; simp only [List.all_map, List.map_map, LExpr.combineEvalResValueFlag_eq_pair] at this ; exact this
            obtain ⟨h_inner_snd, h_argsAllFull⟩ := args_from_andValue inner args h_snd_and
            obtain ⟨h_map_eq', h_argsAllFull_lift⟩ := list_lifts args h_argsAllFull
            have h_new_lift := ih _ _ h_inner_snd
            have h_map_eq'_prod : List.map Prod.fst
                (args.map (fun a => LExpr.eval (n'+1) F env a)) =
                List.map Prod.fst (args.map (fun a => LExpr.eval n' F env a)) := by
              rw [LExpr.List_map_fst_map_eval, LExpr.List_map_fst_map_eval]; exact h_map_eq'
            show LExpr.eval (n'+1+1) F env e = (v, .value true)
            conv => lhs; rw [LExpr.eval]
            rw [ite_eq_right h_not_can, h_call]
            dsimp only
            rw [h_sc]
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
              -- a value on fully evaluated arguments
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
              rw [ite_eq_right h_not_can, h_call]
              dsimp only
              rw [h_sc]
              dsimp only
              split
              · rename_i h_cond_lift
                exfalso; apply h_cond; rw [← h_map_eq_prod]; exact h_cond_lift
              · rw [h_map_eq_prod, ite_eq_left h_eval_cond]
                simp only [LExpr.List_map_fst_map_eval]
                rw [h_ceval_none]
                dsimp only
                simp only [LExpr.List_all_snd_isValueTrue_map_eval]
                rw [h_argsAllFull_lift]
                simp only [LExpr.List_map_fst_map_eval] at h_can h_fst
                have h_can_v : LExpr.isValue F v = true :=
                  h_fst ▸ h_can
                simp [h_fst, h_can_v, LExpr.EvalResult.combineValueFlag]
            · rename_i ceval h_ceval
              split
              · rename_i e' h_ceval_res
                intro h
                have h_fst : (LExpr.eval n' F env e').fst = v := by
                  have := congrArg Prod.fst h; simp only [List.all_map, LExpr.combineEvalResValueFlag_eq_pair] at this ; exact this
                have h_snd_and : (LExpr.eval n' F env e').snd.combineValueFlag
                    (args.all fun a => (LExpr.eval n' F env a).snd.isValueTrue) = .value true := by
                  have := congrArg Prod.snd h; simp only [List.all_map, LExpr.combineEvalResValueFlag_eq_pair] at this; exact this
                obtain ⟨h_e'_snd, h_argsAllFull⟩ := args_from_andValue _ _ h_snd_and
                obtain ⟨h_map_eq, h_argsAllFull_lift⟩ := list_lifts args h_argsAllFull
                have h_map_eq_prod : List.map Prod.fst
                    (args.map (fun a => LExpr.eval (n'+1) F env a)) =
                    List.map Prod.fst (args.map (fun a => LExpr.eval n' F env a)) := by
                  rw [LExpr.List_map_fst_map_eval, LExpr.List_map_fst_map_eval]; exact h_map_eq
                have h_e'_lift := ih _ _ h_e'_snd
                show LExpr.eval (n'+1+1) F env e = (v, .value true)
                conv => lhs; rw [LExpr.eval]
                rw [ite_eq_right h_not_can, h_call]
                dsimp only
                rw [h_sc]
                dsimp only
                split
                · rename_i h_cond_lift
                  exfalso; apply h_cond; rw [← h_map_eq_prod]; exact h_cond_lift
                · rename_i h_cond_lift
                  simp only [LExpr.List_map_fst_map_eval] at h_ceval_res
                  rw [h_map_eq_prod, ite_eq_left h_eval_cond]
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
        rw [ite_eq_right h_not_can, h_nocall]
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

/-- Two `.value true` outputs of `eval` at different fuel levels agree on the
    resulting expression. This is the evaluator-level confluence statement:
    `Step` itself is not confluent (e.g. `(fun x => fun y => x) (1 + 1)` steps
    to both `fun y => 2` and `fun y => (1 + 1)`, and both are values), but
    `eval`'s fixed operands-first strategy makes the fully-reduced result
    unique regardless of fuel. Together with `evalFully_of_value_true` this
    says `evalFully` assigns a normal form to the fragment the
    evaluator can fully reduce. -/
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

/-- **Fuel monotonicity, `≤` form**: a fully-reduced (`.value true`) result is
    stable under any larger fuel. Corollary of `eval_value_true_add_fuel`. -/
theorem eval_value_true_mono_le (F : @Factory Tbase) (env : Env Tbase)
    (m n : Nat) (h_le : m ≤ n) (e v : LExpr Tbase.mono)
    (h : LExpr.eval m F env e = (v, .value true)) :
    LExpr.eval n F env e = (v, .value true) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  exact eval_value_true_add_fuel F env m d e v h

end evalFully_of_value_true

/-! ## Part IV: Store-extension frame for `.value true` (`eval_frame`)

A fully-reduced (`.value true`) evaluation result is preserved when the
environment is extended pointwise (`EnvExtends`).  This is the store-extension
monotonicity the Imperative pipeline needs of the evaluator.

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
      have := congrArg Prod.fst h; simp only at this; exact this
    have h_snd_and : (LExpr.eval n' F env br).snd.combineValueFlag
        (LExpr.eval n' F env c).snd.isValueTrue = .value true := by
      have := congrArg Prod.snd h; simp only at this; exact this
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
      have := congrArg Prod.fst h; simp only at this; exact this
    have h_snd_pair : (LExpr.eval n' F env e1).snd.isValueTrue = true ∧
                      (LExpr.eval n' F env e2).snd.isValueTrue = true := by
      have := congrArg Prod.snd h; simp only [LExpr.EvalResult.value.injEq, Bool.and_eq_true] at this ; exact this
    have h_e1_snd : LExpr.eval n' F env e1 =
        ((LExpr.eval n' F env e1).fst, .value true) := by
      rw [← (isValueTrue_eq_true_iff _).mp h_snd_pair.1]
    have h_e2_snd : LExpr.eval n' F env e2 =
        ((LExpr.eval n' F env e2).fst, .value true) := by
      rw [← (isValueTrue_eq_true_iff _).mp h_snd_pair.2]
    rw [ih_eval _ _ h_e1_snd, ih_eval _ _ h_e2_snd]
    simp only
    rw [h_eql]
    simp only [LExpr.EvalResult.isValueTrue, Bool.and_self, Prod.mk.injEq, and_true]
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
      have := congrArg Prod.fst h; simp only at this; exact this
    have h_snd : (LExpr.eval n' F env inner).snd.combineValueFlag
        ((LExpr.eval n' F env e1).snd.isValueTrue &&
         (LExpr.eval n' F env e2).snd.isValueTrue) = .value true := by
      have := congrArg Prod.snd h; simp only at this; exact this
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
      rw [ite_eq_right h_neq, h_inner_lift]
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
        rw [ite_eq_right h_neq, h_inner_lift]
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
      have hnil := isValue_getVars_nil F _ hcan
      have hag := env_agree_of_subst_getVars_nil env env' hext (LExpr.abs m n ty body) hnil
      have hsub_eq : LExpr.substFvarsFromEnv env' (LExpr.abs m n ty body) =
          LExpr.substFvarsFromEnv env (LExpr.abs m n ty body) :=
        substFvarsFromEnv_env_congr env' env (LExpr.abs m n ty body)
          (fun x hx => (hag x hx).symm)
      rw [hsub_eq, ite_eq_left hcan, h_fst]
    · exact absurd h_snd (by simp)
  | quant m qk n ty tr body =>
    simp only [LExpr.evalCore, Prod.mk.injEq] at h
    cases h.2
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
    by_cases hcan : LExpr.isValue F e = true
    · rw [ite_eq_left hcan] at h
      have hfe : v = e := by
        have := congrArg Prod.fst h; simp only at this; exact this.symm
      subst hfe
      exact eval_value_identity 0 F env' v hcan
    · rw [ite_eq_right hcan] at h
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
        have := congrArg Prod.fst h; simp only at this; exact this.symm
      subst hfe
      exact eval_value_identity (n' + 1) F env' v hcan
    · rename_i h_not_can
      split
      · rename_i op_expr args lfunc h_call
        split
        · -- shortCircuit call
          rename_i a rest ceval h_sc
          intro h
          have h_lift := evalShortCircuit_value_true_transfer n' n' F env env' e op_expr
            a rest ceval v (fun e' v' hev => ih e' v' hev) h
          simp only [LExpr.eval]
          rw [ite_eq_right h_not_can, h_call]
          dsimp only
          rw [h_sc]
          exact h_lift
        rename_i h_sc
        split
        · -- inline branch
          rename_i h_cond
          have h_body_isSome : lfunc.body.isSome = true := by
            simp only [Bool.and_eq_true] at h_cond; exact h_cond.1
          split
          · rename_i tySubst h_ts
            intro h
            let inner := LExpr.substFvarsLifting
                ((lfunc.body.get h_body_isSome).applyTypeSubst tySubst)
                (lfunc.inputs.keys.zip
                  (List.map (fun a => (LExpr.eval n' F env a).fst) args))
            have h_fst : (LExpr.eval n' F env inner).fst = v := by
              have := congrArg Prod.fst h; simp only [List.all_map, List.map_map, LExpr.combineEvalResValueFlag_eq_pair] at this ; exact this
            have h_snd_and : (LExpr.eval n' F env inner).snd.combineValueFlag
                (args.all fun a => (LExpr.eval n' F env a).snd.isValueTrue) = .value true := by
              have := congrArg Prod.snd h; simp only [List.all_map, List.map_map, LExpr.combineEvalResValueFlag_eq_pair] at this ; exact this
            obtain ⟨h_inner_snd, h_argsAllFull⟩ := args_from_andValue inner args h_snd_and
            obtain ⟨h_map_eq', h_argsAllFull_lift⟩ := list_lifts args h_argsAllFull
            have h_new_lift := ih _ _ h_inner_snd
            have h_map_eq'_prod : List.map Prod.fst
                (args.map (fun a => LExpr.eval n' F env' a)) =
                List.map Prod.fst (args.map (fun a => LExpr.eval n' F env a)) := by
              rw [LExpr.List_map_fst_map_eval, LExpr.List_map_fst_map_eval]; exact h_map_eq'
            show LExpr.eval (n'+1) F env' e = (v, .value true)
            conv => lhs; rw [LExpr.eval]
            rw [ite_eq_right h_not_can, h_call]
            dsimp only
            rw [h_sc]
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
              -- a value on fully evaluated arguments
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
              rw [ite_eq_right h_not_can, h_call]
              dsimp only
              rw [h_sc]
              dsimp only
              split
              · rename_i h_cond_lift
                exfalso; apply h_cond; rw [← h_map_eq_prod]; exact h_cond_lift
              · rw [h_map_eq_prod, ite_eq_left h_eval_cond]
                simp only [LExpr.List_map_fst_map_eval]
                rw [h_ceval_none]
                dsimp only
                simp only [LExpr.List_all_snd_isValueTrue_map_eval]
                rw [h_argsAllFull_lift]
                simp only [LExpr.List_map_fst_map_eval] at h_can h_fst
                have h_can_v : LExpr.isValue F v = true :=
                  h_fst ▸ h_can
                simp [h_fst, h_can_v, LExpr.EvalResult.combineValueFlag]
            · rename_i ceval h_ceval
              split
              · rename_i e' h_ceval_res
                intro h
                have h_fst : (LExpr.eval n' F env e').fst = v := by
                  have := congrArg Prod.fst h; simp only [List.all_map, LExpr.combineEvalResValueFlag_eq_pair] at this ; exact this
                have h_snd_and : (LExpr.eval n' F env e').snd.combineValueFlag
                    (args.all fun a => (LExpr.eval n' F env a).snd.isValueTrue) = .value true := by
                  have := congrArg Prod.snd h; simp only [List.all_map, LExpr.combineEvalResValueFlag_eq_pair] at this; exact this
                obtain ⟨h_e'_snd, h_argsAllFull⟩ := args_from_andValue _ _ h_snd_and
                obtain ⟨h_map_eq, h_argsAllFull_lift⟩ := list_lifts args h_argsAllFull
                have h_map_eq_prod : List.map Prod.fst
                    (args.map (fun a => LExpr.eval n' F env' a)) =
                    List.map Prod.fst (args.map (fun a => LExpr.eval n' F env a)) := by
                  rw [LExpr.List_map_fst_map_eval, LExpr.List_map_fst_map_eval]; exact h_map_eq
                have h_e'_lift := ih _ _ h_e'_snd
                show LExpr.eval (n'+1) F env' e = (v, .value true)
                conv => lhs; rw [LExpr.eval]
                rw [ite_eq_right h_not_can, h_call]
                dsimp only
                rw [h_sc]
                dsimp only
                split
                · rename_i h_cond_lift
                  exfalso; apply h_cond; rw [← h_map_eq_prod]; exact h_cond_lift
                · rename_i h_cond_lift
                  simp only [LExpr.List_map_fst_map_eval] at h_ceval_res
                  rw [h_map_eq_prod, ite_eq_left h_eval_cond]
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
        rw [ite_eq_right h_not_can, h_nocall]
        exact h_ec

end eval_frame

/-! ## Literals -/

section evalFully_forms

omit [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta] [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- Literals are values in every factory. -/
theorem isValue_const_true
    (F : @Factory Tbase) (m : Tbase.Metadata) (κ : LConst) :
    LExpr.isValue F (.const m κ : LExpr Tbase.mono) = true := by
  rw [LExpr.isValue.eq_def]

end evalFully_forms

end -- public section
end Lambda

