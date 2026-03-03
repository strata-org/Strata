/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LExprT

/-! ## Typing Relation for Lambda Expressions

Specification of Lambda's type inference. See `Strata.DL.Lambda.LExprT` for the
implementation.

The inductive relation `HasType` characterizes well-typed `LExpr`s. We
specify a Hindley-Milner type system here, but note that at this time, we
do not have `let`s in `LExpr`, so we do not tackle let-polymorphism yet.

TODO: prove that the implementation conforms to the specification here.
-/

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)

namespace LExpr
open LTy

variable {IDMeta : Type} [DecidableEq IDMeta]

/--
Close `ty` by `x`, i.e., add `x` as a bound type variable.
-/
def LTy.close (x : TyIdentifier) (ty : LTy) : LTy :=
  match ty with
  | .forAll vars lty => .forAll (x :: vars) lty

/--
Open `ty` by instantiating the bound type variable `x` with `xty`.
-/
def LTy.open (x : TyIdentifier) (xty : LMonoTy) (ty : LTy) : LTy :=
  match ty with
  | .forAll vars lty =>
    if x ∈ vars then
      let S := [(x, xty)]
      .forAll (vars.removeAll [x]) (LMonoTy.subst [S] lty)
    else
      ty

/--
Open `ty` by instantiating all its bound variables with `tys`, giving the
`LMonoTy` that results. `tys` should have length equal to the number of bound
variables in `ty`.
-/
def LTy.openFull (ty: LTy) (tys: List LMonoTy) : LMonoTy :=
  LMonoTy.subst [(List.zip (LTy.boundVars ty) tys)] (LTy.toMonoTypeUnsafe ty)

/--
Typing relation for `LExpr`s with respect to `LTy`.

The typing relation is parameterized by two contexts. An `LContext` contains
known types and functions while a `TContext` associates free variables with
their types.
-/
inductive HasType {T: LExprParams} [DecidableEq T.IDMeta] (C: LContext T):
  (TContext T.IDMeta) → LExpr T.mono → LTy → Prop where

  /-- A boolean constant has type `.bool` if `bool` is a known type in this
  context. -/
  | tbool_const : ∀ Γ m b,
            C.knownTypes.containsName "bool" →
            HasType C Γ (.boolConst m b) (.forAll [] .bool)

  /-- An integer constant has type `.int` if `int` is a known type in this
  context. -/
  | tint_const : ∀ Γ m n,
            C.knownTypes.containsName "int" →
            HasType C Γ (.intConst m n) (.forAll [] .int)

  /-- A real constant has type `.real` if `real` is a known type in this
  context. -/
  | treal_const : ∀ Γ m r,
            C.knownTypes.containsName "real" →
            HasType C Γ (.realConst m r) (.forAll [] .real)

  /-- A string constant has type `.string` if `string` is a known type in this
  context. -/
  | tstr_const : ∀ Γ m s,
            C.knownTypes.containsName "string" →
            HasType C Γ (.strConst m s) (.forAll [] .string)

  /-- A bit vector constant of size `n` has type `.bitvec n` if `bitvec` is a
  known type in this context. -/
  | tbitvec_const : ∀ Γ m n b,
            C.knownTypes.containsName "bitvec" →
            HasType C Γ (.bitvecConst m n b) (.forAll [] (.bitvec n))

  /-- An un-annotated variable has the type recorded for it in `Γ`, if any. -/
  | tvar : ∀ Γ m x ty, Γ.types.find? x = some ty → HasType C Γ (.fvar m x none) ty

  /--
  An annotated free variable has its claimed type `ty_s` if `ty_s` is an
  instantiation of the type `ty_o` recorded for it in `Γ`.
  -/
  | tvar_annotated : ∀ Γ m x ty_o ty_s tys,
            Γ.types.find? x = some ty_o →
            tys.length = ty_o.boundVars.length →
            LTy.openFull ty_o tys = ty_s →
            HasType C Γ (.fvar m x (some ty_s)) (.forAll [] ty_s)

  /--
  An abstraction `λ x.e` has type `x_ty → e_ty` if the claimed type of `x` is
  `x_ty` or None and if `e` has type `e_ty` when `Γ` is extended with the
  binding `(x → x_ty)`.
  -/
  | tabs : ∀ Γ m x x_ty e e_ty o,
            LExpr.fresh x e →
            (hx : LTy.isMonoType x_ty) →
            (he : LTy.isMonoType e_ty) →
            HasType C { Γ with types := Γ.types.insert x.fst x_ty} (LExpr.varOpen 0 x e) e_ty →
            o = none ∨ o = some (x_ty.toMonoType hx) →
            HasType C Γ (.abs m o e)
                      (.forAll [] (.tcons "arrow" [(LTy.toMonoType x_ty hx),
                                                   (LTy.toMonoType e_ty he)]))

  /--
  An application `e₁e₂` has type `t1` if `e₁` has type `t2 → t1` and `e₂` has
  type `t2`.
  -/
  | tapp : ∀ Γ m e1 e2 t1 t2,
            (h1 : LTy.isMonoType t1) →
            (h2 : LTy.isMonoType t2) →
            HasType C Γ e1 (.forAll [] (.tcons "arrow" [(LTy.toMonoType t2 h2),
                                                     (LTy.toMonoType t1 h1)])) →
            HasType C Γ e2 t2 →
            HasType C Γ (.app m e1 e2) t1

  /--
  If expression `e` has type `ty` and `ty` is more general than `e_ty`,
  then `e` has type `e_ty` (i.e. we can instantiate `ty` with `e_ty`).
  -/
  | tinst : ∀ Γ e ty e_ty x x_ty,
            HasType C Γ e ty →
            e_ty = LTy.open x x_ty ty →
            HasType C Γ e e_ty

  /--
  If `e` has type `ty`, it also has type `∀ a. ty` as long as `a` is fresh.
  For instance, `(·ftvar "a") → (.ftvar "a")` (or `a → a`)
  can be generalized to `(.btvar 0) → (.btvar 0)` (or `∀a. a → a`), assuming
 `a` is not in the context.
  -/
  | tgen : ∀ Γ e a ty,
            HasType C Γ e ty →
            TContext.isFresh a Γ →
            HasType C Γ e (LTy.close a ty)

  /-- If `e1` and `e2` have the same type `ty`, and `c` has type `.bool`, then
  `.ite c e1 e2` has type `ty`. -/
  | tif : ∀ Γ m c e1 e2 ty,
          HasType C Γ c (.forAll [] .bool) →
          HasType C Γ e1 ty →
          HasType C Γ e2 ty →
          HasType C Γ (.ite m c e1 e2) ty

  /-- If `e1` and `e2` have the same type `ty`, then `.eq e1 e2` has type
  `.bool`. -/
  | teq : ∀ Γ m e1 e2 ty,
          HasType C Γ e1 ty →
          HasType C Γ e2 ty →
          HasType C Γ (.eq m e1 e2) (.forAll [] .bool)

  /--
  A quantifier `∀/∃ {x: tr}.e` has type `bool` if the claimed type of `x` is
  `x_ty` or None, and if, when `Γ` is extended with the binding `(x → x_ty)`,
  `e` has type `bool` and `tr` is well-typed.
  -/
  | tquant: ∀ Γ m k tr tr_ty x x_ty e o,
            LExpr.fresh x e →
            (hx : LTy.isMonoType x_ty) →
            HasType C { Γ with types := Γ.types.insert x.fst x_ty} (LExpr.varOpen 0 x e) (.forAll [] .bool) →
            HasType C {Γ with types := Γ.types.insert x.fst x_ty} (LExpr.varOpen 0 x tr) tr_ty →
            o = none ∨ o = some (x_ty.toMonoType hx) →
            HasType C Γ (.quant m k o tr e) (.forAll [] .bool)

  /--
  An un-annotated operator has the type recorded for it in `C.functions`, if any.
  -/
  | top: ∀ Γ m f op ty,
            C.functions.find? (fun fn => fn.name == op) = some f →
            f.type = .ok ty →
            HasType C Γ (.op m op none) ty
  /--
  Similarly to free variables, an annotated operator has its claimed type `ty_s` if `ty_s` is an
  instantiation of the type `ty_o` recorded for it in `C.functions`.
  -/
  | top_annotated: ∀ Γ m f op ty_o ty_s tys,
            C.functions.find? (fun fn => fn.name == op) = some f →
            f.type = .ok ty_o →
            tys.length = ty_o.boundVars.length →
            LTy.openFull ty_o tys = ty_s →
            HasType C Γ (.op m op (some ty_s)) (.forAll [] ty_s)

/--
If `LExpr e` is well-typed, then it is well-formed, i.e., contains no dangling
bound variables.
-/
theorem HasType.regularity [DecidableEq T.IDMeta] (h : HasType (T := T) C Γ e ty) :
  LExpr.WF e := by
  open LExpr in
  induction h <;> try (solve | simp_all[WF, lcAt])
  case tabs m x x_ty e e_ty hx h_x_mono h_e_mono ht ih =>
    simp_all [WF]
    exact lcAt_varOpen_abs ih (by simp)
  case tquant m k tr tr_ty x x_ty e o h_x_mono hx htr ih ihtr =>
    simp_all [WF]
    exact lcAt_varOpen_quant ih (by omega) ihtr
  done


/-!
### Helper lemmas for `annotate_HasType`
-/

/--
Ground types (from constants) are unaffected by type substitution.
-/
theorem LConst.ty_subst (c : LConst) (S : Subst) :
    LMonoTy.subst S c.ty = c.ty := by
  cases c with
  | intConst i =>
    simp [LConst.ty, LMonoTy.int, LMonoTy.subst, LMonoTys.subst, LMonoTys.subst.substAux]
  | strConst s =>
    simp [LConst.ty, LMonoTy.string, LMonoTy.subst, LMonoTys.subst, LMonoTys.subst.substAux]
  | realConst r =>
    simp [LConst.ty, LMonoTy.real, LMonoTy.subst, LMonoTys.subst, LMonoTys.subst.substAux]
  | bitvecConst n b =>
    simp [LConst.ty, LMonoTy.subst]
  | boolConst b =>
    simp [LConst.ty, LMonoTy.bool, LMonoTy.subst, LMonoTys.subst, LMonoTys.subst.substAux]

/--
`HasType` is preserved under substitution of a single fresh type variable.
If `e` has type `mty` and `a` is fresh in `Γ`, then `e` also has type
`mty[a ↦ t]` for any `t`. This follows from `tgen` (generalize `a`) then
`tinst` (instantiate `a` with `t`).
-/
theorem HasType_subst_fresh {T : LExprParams} [DecidableEq T.IDMeta]
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono) (mty : LMonoTy)
    (a : TyIdentifier) (t : LMonoTy)
    (h : HasType C Γ e (.forAll [] mty))
    (h_fresh : TContext.isFresh a Γ) :
    HasType C Γ e (.forAll [] (LMonoTy.subst [[(a, t)]] mty)) := by
  have h_gen := HasType.tgen Γ e a (.forAll [] mty) h h_fresh
  simp [LTy.close] at h_gen
  have h_inst := HasType.tinst Γ e (.forAll [a] mty)
    (.forAll [] (LMonoTy.subst [[(a, t)]] mty)) a t h_gen
  simp [LTy.open, List.removeAll] at h_inst
  exact h_inst

/--
Helper: `toLMonoTy` commutes with `applySubstT` in the expected way.
For most constructors, `(applySubstT et S).toLMonoTy = LMonoTy.subst S et.toLMonoTy`.
For quantifiers, `toLMonoTy` always returns `LMonoTy.bool`.
-/
theorem applySubstT_toLMonoTy {T : LExprParamsT}
    (et : LExprT T) (S : Subst) :
    (LExpr.applySubstT et S).toLMonoTy = LMonoTy.subst S et.toLMonoTy := by
  cases et with
  | const m c => simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.toLMonoTy]
  | op m o ty => simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.toLMonoTy]
  | bvar m i => simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.toLMonoTy]
  | fvar m x ty => simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.toLMonoTy]
  | app m e1 e2 => simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.toLMonoTy]
  | abs m ty e => simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.toLMonoTy]
  | ite m c t e => simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.toLMonoTy]
  | eq m e1 e2 => simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.toLMonoTy]
  | quant m k ty tr e =>
    simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.toLMonoTy, LMonoTy.bool]
    unfold LMonoTy.subst
    split <;> simp [LMonoTys.subst, LMonoTys.subst.substAux]

/--
Substitution on `LMonoTy.bool` is the identity (ground type).
-/
theorem LMonoTy.subst_bool (S : Subst) : LMonoTy.subst S LMonoTy.bool = LMonoTy.bool := by
  simp [LMonoTy.bool, LMonoTy.subst]
  intro h
  simp [LMonoTys.subst, h, LMonoTys.subst.substAux]

/-!
### Proof architecture for `annotate_HasType`

The proof is structured in three layers:

1. **`resolveAux_HasType`**: The core theorem, proved by induction on `e`.
   States that if `resolveAux C Env e = .ok (et, Env')`, then:
   - `Env'.context = Env.context` (context is preserved), and
   - For any substitution `S` whose keys are all fresh in `Env.context`,
     `HasType C Env.context e (.forAll [] (LMonoTy.subst S et.toLMonoTy))`.

   The `∀ S` quantification is crucial for recursive cases: when composing
   IHs from subexpressions, we can instantiate each with the final
   substitution produced by unification.

2. **`resolveAux_keys_fresh`**: All keys in the substitution produced by
   `resolveAux` are fresh in the input context. This ensures we can
   instantiate `resolveAux_HasType` with `S = Env'.stateSubstInfo.subst`.

3. **`annotate_HasType`**: The top-level theorem. Since `resolve` is just
   `resolveAux` followed by `applySubstT`, we decompose the hypothesis,
   apply `resolveAux_HasType` with the final substitution (justified by
   `resolveAux_keys_fresh`), and use `applySubstT_toLMonoTy` to relate
   the result types.

#### Key supporting lemmas:

- **`HasType_subst_fresh_all`**: If `HasType C Γ e (.forAll [] mty)` and all
  keys of `S` are fresh in `Γ`, then `HasType C Γ e (.forAll [] (subst S mty))`.
  Generalizes `HasType_subst_fresh` from a single variable to a full substitution.

- **`unify_makes_equal`**: If `Constraints.unify [(ty1, ty2)] S_old = .ok S_new`,
  then `LMonoTy.subst S_new.subst ty1 = LMonoTy.subst S_new.subst ty2`.

- **`resolve_of_resolveAux`**: `resolve` decomposes as `resolveAux` + `applySubstT`.

- **`TEnv.updateSubst_context`**: `updateSubst` preserves the context.
-/

/-!
### Definitions and lemmas for the `resolveAux`-based proof strategy
-/

/-- All keys in substitution `S` are fresh w.r.t. context `Γ`. -/
def Subst.allKeysFresh {T : LExprParams} [DecidableEq T.IDMeta]
    (S : Subst) (Γ : TContext T.IDMeta) : Prop :=
  ∀ a, a ∈ Maps.keys S → TContext.isFresh (T := T) a Γ

variable {T : LExprParams} [ToString T.IDMeta] [DecidableEq T.IDMeta]
  [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)]

/--
`HasType` is preserved under substitution of fresh type variables.
If `e` has type `mty` and all keys of `S` are fresh in `Γ`, then `e` also has
type `LMonoTy.subst S mty`.

This generalizes `HasType_subst_fresh` from a single variable to a full
substitution. The proof proceeds by iterating `tgen`/`tinst` for each binding
in `S`.
-/
theorem HasType_subst_fresh_all
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono) (mty : LMonoTy)
    (S : Subst)
    (h : HasType C Γ e (.forAll [] mty))
    (h_fresh : Subst.allKeysFresh S Γ)
    (h_wf : SubstWF S) :
    HasType C Γ e (.forAll [] (LMonoTy.subst S mty)) := by
  sorry

/-- `resolve` is `resolveAux` followed by applying the final substitution. -/
theorem resolve_of_resolveAux
    (C : LContext T) (Env : TEnv T.IDMeta) (e : LExpr T.mono)
    (et : LExprT T.mono) (Env' : TEnv T.IDMeta)
    (h : resolveAux C Env e = .ok (et, Env')) :
    LExpr.resolve C Env e = .ok (applySubstT et Env'.stateSubstInfo.subst, Env') := by
  simp [LExpr.resolve, h, Bind.bind, Except.bind]

/-- `updateSubst` does not change the context. -/
theorem TEnv.updateSubst_context (Env : TEnv IDMeta) (S : SubstInfo) :
    (TEnv.updateSubst Env S).context = Env.context := by
  rfl

private theorem Maps.find?_none_of_not_mem_keys [DecidableEq α]
    (S : Maps α β) (x : α) (h : x ∉ S.keys) : S.find? x = none := by
  match h_eq : S.find? x with
  | none => rfl
  | some v => exact absurd (Maps.find?_mem_keys S h_eq) h

/--
If no key of a substitution `S` appears free in `ty`, then applying `S` to
`ty` leaves it unchanged. This is the key lemma for proving idempotence.
-/
theorem LMonoTy.subst_no_key_free (S : Subst) (ty : LMonoTy)
    (h : S.keys.all (fun k => k ∉ ty.freeVars)) :
    LMonoTy.subst S ty = ty := by
  by_cases hS : S.hasEmptyScopes
  · exact LMonoTy.subst_emptyS hS
  · induction ty with
    | ftvar x =>
      have : x ∉ Maps.keys S := by
        simp [List.all_eq_true] at h; intro h_mem
        exact h x h_mem (by simp [LMonoTy.freeVars])
      unfold LMonoTy.subst; simp [hS, Maps.find?_none_of_not_mem_keys S x this]
    | bitvec n =>
      unfold LMonoTy.subst; simp [hS]
    | tcons name args ih =>
      unfold LMonoTy.subst; simp only [hS, ↓reduceIte]
      suffices h_args : LMonoTys.subst S args = args by rw [h_args]; simp
      rw [LMonoTys.subst_eq_substLogic]
      have hp : ∀ k, k ∈ Maps.keys S → k ∉ (LMonoTy.tcons name args).freeVars := by
        simp [List.all_eq_true] at h; exact h
      induction args with
      | nil => simp [LMonoTys.substLogic, hS]
      | cons a rest ih_rest =>
        simp only [LMonoTys.substLogic, hS, Bool.false_eq_true, ↓reduceIte]
        have h1_b : S.keys.all (fun k => k ∉ a.freeVars) := by
          simp [List.all_eq_true]; intro k hk
          have := hp k hk; simp [LMonoTy.freeVars, LMonoTys.freeVars] at this; exact this.1
        have h2_b : S.keys.all (fun k => k ∉ (LMonoTy.tcons name rest).freeVars) := by
          simp [List.all_eq_true]; intro k hk
          have := hp k hk; simp [LMonoTy.freeVars, LMonoTys.freeVars] at this; exact this.2
        have h2_p : ∀ k, k ∈ Maps.keys S → k ∉ (LMonoTy.tcons name rest).freeVars := by
          simp [List.all_eq_true] at h2_b; exact h2_b
        rw [ih a (.head _) h1_b,
            ih_rest (fun ty h_mem h_b => ih ty (.tail _ h_mem) h_b) h2_b h2_p]

/--
Well-formed substitutions are idempotent: applying the substitution twice
gives the same result as applying it once. Follows from `subst_no_key_free`
and `subst_keys_not_in_substituted_type`.
-/
theorem LMonoTy.subst_idempotent (S : Subst) (hWF : SubstWF S) (ty : LMonoTy) :
    LMonoTy.subst S (LMonoTy.subst S ty) = LMonoTy.subst S ty := by
  exact LMonoTy.subst_no_key_free S (LMonoTy.subst S ty)
    (LMonoTy.subst_keys_not_in_substituted_type hWF)

/--
If `Constraints.unify [(ty1, ty2)] S = .ok S_new`, then there exists a
result `relS` from `Constraint.unifyOne (ty1, ty2) S` such that
`S_new = relS.newS`.
-/
private theorem unify_singleton_eq_unifyOne (ty1 ty2 : LMonoTy) (S S_new : SubstInfo)
    (h : Constraints.unify [(ty1, ty2)] S = .ok S_new) :
    ∃ relS : ValidSubstRelation [(ty1, ty2)] S,
      Constraint.unifyOne (ty1, ty2) S = .ok relS ∧ S_new = relS.newS := by
  simp only [Constraints.unify, Bind.bind, Except.bind] at h
  -- Split on unifyCore result
  split at h
  · simp at h
  · rename_i relS_core h_core
    simp at h; subst h
    -- Now decompose unifyCore [(ty1, ty2)] S
    -- unifyCore for a single-element list calls unifyOne, then unifyCore []
    -- unifyCore [] returns the substitution unchanged
    -- So relS_core.newS = relS_one.newS
    simp only [Constraints.unifyCore, Bind.bind, Except.bind, Except.mapError] at h_core
    -- h_core involves: match (unifyOne ...) |> mapError with ... then match unifyCore [] with ...
    -- The unifyOne result determines everything
    -- Extract the unifyOne result
    revert h_core
    generalize h_one_gen : Constraint.unifyOne (ty1, ty2) S = res_one
    intro h_core
    match res_one with
    | .error e =>
      simp at h_core
    | .ok relS_one =>
      simp at h_core
      exact ⟨relS_one, rfl, congrArg ValidSubstRelation.newS h_core.symm⟩

private theorem Map.find?_insert_self [DecidableEq α]
    (m : Map α β) (x : α) (v : β) : Map.find? (Map.insert m x v) x = some v := by
  induction m with
  | nil => simp [Map.insert, Map.find?]
  | cons hd rest ih => simp only [Map.insert]; split <;> simp_all [Map.find?]

private theorem Maps.find?_update_self [DecidableEq α]
    (ms : Maps α β) (x : α) (v : β) (h : ms.find? x ≠ none) :
    (Maps.update ms x v).find? x = some v := by
  induction ms with
  | nil => simp [Maps.find?] at h
  | cons m rest ih =>
    simp only [Maps.update]; split
    · rename_i h_none; simp only [Maps.find?, h_none]; apply ih
      simp [Maps.find?, h_none] at h; exact h
    · simp [Maps.find?, Map.find?_insert_self]

private theorem Maps.find?_insert_self [DecidableEq α]
    (ms : Maps α β) (x : α) (v : β) :
    Maps.find? (Maps.insert ms x v) x = some v := by
  simp only [Maps.insert]; split
  · match ms with
    | [] => simp [Maps.pop, Maps.push, Maps.newest, Maps.find?, Map.find?_insert_self]
    | _ :: _ => simp [Maps.pop, Maps.push, Maps.newest, Maps.find?, Map.find?_insert_self]
  · exact Maps.find?_update_self ms x v (by simp_all)

/-- After inserting `(id, lty)` into the applied substitution, `subst _ (ftvar id) = lty`. -/
private theorem subst_ftvar_new_binding
    (S : Subst) (id : TyIdentifier) (lty : LMonoTy)
    (_h_none : Maps.find? S id = none) :
    LMonoTy.subst (Maps.insert (Subst.apply [(id, lty)] S) id lty) (LMonoTy.ftvar id) = lty := by
  have h_find := Maps.find?_insert_self (Subst.apply [(id, lty)] S) id lty
  have h_not_empty : ¬Subst.hasEmptyScopes (Maps.insert (Subst.apply [(id, lty)] S) id lty) := by
    intro h_empty
    exact absurd ((Subst.isEmpty_implies_keys_empty h_empty) ▸ Maps.find?_mem_keys _ h_find) (by simp)
  unfold LMonoTy.subst; simp [h_not_empty, h_find]

/-- When `S.find? id = none`, the new substitution absorbs `S` and maps `orig_lty` to `lty`. -/
private theorem subst_orig_new_binding
    (S : Subst) (id : TyIdentifier) (lty orig_lty : LMonoTy)
    (h_none : Maps.find? S id = none)
    (h_lty : lty = LMonoTy.subst S orig_lty)
    (h_occurs : ¬(id ∈ lty.freeVars)) :
    LMonoTy.subst (Maps.insert (Subst.apply [(id, lty)] S) id lty) orig_lty = lty := by
  sorry

/--
Unifying a single constraint produces a substitution that makes the
two types equal. This is the core soundness property for `Constraint.unifyOne`.

The proof requires mutual well-founded induction matching the recursive
structure of `unifyOne`/`unifyCore`. Key cases:
- `t1 == t2`: substitution is unchanged; types are definitionally equal.
- `ftvar id` case with `id` not in `S`: the new substitution maps `id`
  to `subst S orig_lty`, and the occurs check ensures idempotence.
- `ftvar id` case with `id` already in `S`: recursive call on `(S[id], lty)`;
  the IH + extension property give soundness.
- `tcons` case: delegates to `unifyCore` on zipped arguments; each pair
  is equalized by the IH.
-/
private theorem unifyOne_sound (c : Constraint) (S : SubstInfo)
    (relS : ValidSubstRelation [c] S)
    (h : Constraint.unifyOne c S = .ok relS) :
    LMonoTy.subst relS.newS.subst c.1 = LMonoTy.subst relS.newS.subst c.2 := by
  obtain ⟨t1, t2⟩ := c
  simp only [] at *
  -- Unfold unifyOne and case-split on the outer if t1 == t2
  unfold Constraint.unifyOne at h
  split at h
  · -- Case: t1 == t2. Substitution unchanged; types definitionally equal.
    rename_i h_beq
    simp at h
    have h_eq : t1 = t2 := eq_of_beq h_beq
    subst h_eq; simp_all
  · -- Case: t1 ≠ t2. Split on the type constructor match.
    split at h
    · -- Case: .ftvar id on left, orig_lty on right.
      rename_i h_neq_beq id_val orig_val h_neq_match
      -- Further decompose: the do-block starts with let lty := subst S orig, then if/match
      simp [h_neq_match] at h
      split at h
      · -- Subcase: ftvar id = subst S orig_lty. S is unchanged.
        rename_i h_id_eq_lty
        simp at h; subst h
        show LMonoTy.subst S.subst (LMonoTy.ftvar _) = LMonoTy.subst S.subst _
        simp only [h_id_eq_lty, LMonoTy.subst_idempotent S.subst S.isWF _]
      · -- ftvar id ≠ subst S orig_lty
        split at h
        · simp at h  -- Occurs check fails: error
        · split at h
          · -- S.find? id = some sty: recursive unifyOne call.
            -- Requires well-founded mutual induction + extension property:
            -- IH gives subst S' sty = subst S' lty, and extension gives
            -- subst S' (ftvar id) = subst S' sty and subst S' lty = subst S' orig.
            sorry
          · -- S.find? id = none: new binding [id ↦ lty] added.
            rename_i h_neq2 h_not_occurs h_find_none
            simp at h; subst h
            show LMonoTy.subst (Maps.insert (Subst.apply [(_,  LMonoTy.subst S.subst _)] S.subst)
                                 _ (LMonoTy.subst S.subst _)) (LMonoTy.ftvar _) =
                 LMonoTy.subst (Maps.insert (Subst.apply [(_,  LMonoTy.subst S.subst _)] S.subst)
                                 _ (LMonoTy.subst S.subst _)) _
            rw [subst_ftvar_new_binding S.subst _ _ h_find_none,
                subst_orig_new_binding S.subst _ _ _ h_find_none rfl h_not_occurs]
    · -- Case: orig_lty on left, .ftvar id on right. Symmetric to the left case.
      rename_i h_neq_beq id_val orig_val h_neq_match
      simp [h_neq_match] at h
      split at h
      · -- ftvar id = subst S orig_lty. S unchanged. By idempotence (symmetric).
        rename_i h_id_eq_lty
        simp at h; subst h
        show LMonoTy.subst S.subst _ = LMonoTy.subst S.subst (LMonoTy.ftvar _)
        simp only [h_id_eq_lty, LMonoTy.subst_idempotent S.subst S.isWF _]
      · split at h
        · simp at h
        · split at h
          · sorry  -- recursive case (symmetric)
          · -- S.find? id = none (symmetric)
            rename_i h_neq2 h_not_occurs h_find_none
            simp at h; subst h
            show LMonoTy.subst (Maps.insert (Subst.apply [(_,  LMonoTy.subst S.subst _)] S.subst)
                                 _ (LMonoTy.subst S.subst _)) _ =
                 LMonoTy.subst (Maps.insert (Subst.apply [(_,  LMonoTy.subst S.subst _)] S.subst)
                                 _ (LMonoTy.subst S.subst _)) (LMonoTy.ftvar _)
            rw [subst_ftvar_new_binding S.subst _ _ h_find_none,
                subst_orig_new_binding S.subst _ _ _ h_find_none rfl h_not_occurs]
    · -- Case: .bitvec n1, .bitvec n2. Since t1 ≠ t2, we have n1 ≠ n2.
      -- The inner n1 == n2 check either contradicts t1 ≠ t2, or returns error.
      split at h
      · rename_i _t2 _n1 _n2 h_neq _h_match h_nat
        exact absurd (by have := eq_of_beq h_nat; subst this; exact beq_self_eq_true _) h_neq
      · simp at h
    · -- Case: .tcons name1 args1, .tcons name2 args2.
      -- Delegates to unifyCore on (args1.zip args2). Requires mutual induction:
      -- unifyCore_sound gives that each argument pair is equalized,
      -- which implies the full tcons types are equal (same name, equal args).
      sorry
    · simp at h -- Case: .bitvec _, .tcons _ _ — always error
    · simp at h -- Case: .tcons _ _, .bitvec _ — always error

/--
Unification produces a substitution that makes the two types equal.
-/
theorem unify_makes_equal (ty1 ty2 : LMonoTy) (S_old S_new : SubstInfo)
    (h : Constraints.unify [(ty1, ty2)] S_old = .ok S_new) :
    LMonoTy.subst S_new.subst ty1 = LMonoTy.subst S_new.subst ty2 := by
  obtain ⟨relS, h_one, h_eq⟩ := unify_singleton_eq_unifyOne ty1 ty2 S_old S_new h
  subst h_eq
  exact unifyOne_sound (ty1, ty2) S_old relS h_one

/--
All keys in the substitution produced by `resolveAux` are fresh in the input
context. This is because `resolveAux` only adds bindings for type variables
generated by `genTyVar`, which are guaranteed fresh.
-/
theorem resolveAux_keys_fresh :
    ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      Subst.allKeysFresh Env'.stateSubstInfo.subst Env.context := by
  sorry

/-!
### Core theorem: `resolveAux_HasType`

This is the main workhorse. It states that `resolveAux` produces a typed
expression `et` such that for any substitution `S` with fresh keys, the
original expression `e` has type `subst S et.toLMonoTy` under the original
context.

The `∀ S` quantification is the key insight that makes recursive cases work:
- Each recursive call to `resolveAux` gives an IH quantified over all fresh `S`.
- After unification produces `S_unify`, we instantiate both IHs with `S_unify.subst`.
- Context preservation (`Env'.context = Env.context`) lets us use both IHs
  in the same context.
-/
theorem resolveAux_HasType :
    ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      Env'.context = Env.context ∧
      (∀ S, Subst.allKeysFresh S Env.context →
        HasType C (Env.context) e (.forAll [] (LMonoTy.subst S et.toLMonoTy))) := by
  intro e
  induction e with
  | const m c =>
    intro et C Env Env' h
    simp [resolveAux, inferConst] at h
    split at h
    · rename_i h_known
      simp [Bind.bind, Except.bind] at h
      obtain ⟨h_et, h_env⟩ := h
      constructor
      · rw [← h_env]
      · intro S _hS
        rw [← h_et]
        simp [toLMonoTy]
        rw [LConst.ty_subst]
        cases c with
        | boolConst b => exact HasType.tbool_const _ _ _ h_known
        | intConst i => exact HasType.tint_const _ _ _ h_known
        | realConst r => exact HasType.treal_const _ _ _ h_known
        | strConst s => exact HasType.tstr_const _ _ _ h_known
        | bitvecConst n b => exact HasType.tbitvec_const _ _ _ _ h_known
    · exact absurd h (by simp [Bind.bind, Except.bind])
  | bvar m i =>
    intro et C Env Env' h
    simp [resolveAux, Bind.bind, Except.bind] at h
  | fvar m x fty =>
    intro et C Env Env' h
    exact ⟨sorry, sorry⟩
  | op m o oty =>
    intro et C Env Env' h
    exact ⟨sorry, sorry⟩
  | app m e1 e2 ih1 ih2 =>
    intro et C Env Env' h
    exact ⟨sorry, sorry⟩
  | abs m bty e ih =>
    intro et C Env Env' h
    exact ⟨sorry, sorry⟩
  | quant m qk bty tr e ih_tr ih_e =>
    intro et C Env Env' h
    exact ⟨sorry, sorry⟩
  | ite m c t e ih_c ih_t ih_e =>
    intro et C Env Env' h
    exact ⟨sorry, sorry⟩
  | eq m e1 e2 ih1 ih2 =>
    -- resolveAux recurses on e1 and e2, then unifies their types.
    -- Result type is LMonoTy.bool (ground), so subst S bool = bool for any S.
    -- We instantiate both IHs with the unification substitution, justified by
    -- resolveAux_keys_fresh on the whole expression.
    intro et C Env Env' h
    -- Extract freshness before destructing h
    have h_fresh_all := resolveAux_keys_fresh (.eq m e1 e2) et C Env Env' h
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    -- Decompose the nested match in h using split
    -- First: resolveAux C Env e1
    split at h
    · simp at h
    · rename_i v1 h_res1
      obtain ⟨e1t, Env1⟩ := v1
      dsimp at h h_res1
      -- Second: resolveAux C Env1 e2
      split at h
      · simp at h
      · rename_i v2 h_res2
        obtain ⟨e2t, Env2⟩ := v2
        dsimp at h h_res2
        -- Third: Constraints.unify (wrapped in mapError)
        split at h
        · simp at h
        · rename_i v3 h_mapError
          simp at h
          obtain ⟨h_et, h_env'⟩ := h
          -- Extract the underlying unify hypothesis from the mapError wrapper
          have h_unify : Constraints.unify [(e1t.toLMonoTy, e2t.toLMonoTy)]
              Env2.stateSubstInfo = .ok v3 := by
            revert h_mapError
            generalize Constraints.unify [(toLMonoTy e1t, toLMonoTy e2t)]
              Env2.stateSubstInfo = res
            intro h_me
            match res, h_me with
            | .ok val, h_me => simp at h_me; rw [h_me]
            | .error _, h_me => simp at h_me
          have ⟨h_ctx1, h_ty1⟩ := ih1 e1t C Env Env1 h_res1
          have ⟨h_ctx2, h_ty2⟩ := ih2 e2t C Env1 Env2 h_res2
          have h_fresh_v3 : Subst.allKeysFresh v3.subst Env.context := by
            rw [← h_env'] at h_fresh_all
            simp [TEnv.updateSubst] at h_fresh_all
            exact h_fresh_all
          constructor
          · rw [← h_env']
            simp [TEnv.updateSubst, TEnv.context]
            change Env2.context = Env.context
            rw [h_ctx2, h_ctx1]
          · intro S hS
            rw [← h_et]; simp [toLMonoTy]; rw [LMonoTy.subst_bool]
            have h_unify_eq := unify_makes_equal e1t.toLMonoTy e2t.toLMonoTy
              Env2.stateSubstInfo v3 h_unify
            have h_e1_typed := h_ty1 v3.subst h_fresh_v3
            rw [h_ctx1] at h_ty2
            have h_e2_typed := h_ty2 v3.subst h_fresh_v3
            rw [h_unify_eq] at h_e1_typed
            exact HasType.teq Env.context m e1 e2
              (.forAll [] (LMonoTy.subst v3.subst e2t.toLMonoTy))
              h_e1_typed h_e2_typed

/--
### Main theorem: `annotate_HasType`

If `e.resolve C Env` succeeds with `e_typed`, then `e` has type
`e_typed.toLMonoTy` under the original context.

The proof decomposes `resolve` into `resolveAux` + `applySubstT`, then:
1. Applies `resolveAux_HasType` to get typing under any fresh substitution.
2. Uses `resolveAux_keys_fresh` to show the final substitution has fresh keys.
3. Instantiates with the final substitution and uses `applySubstT_toLMonoTy`.
-/
theorem annotate_HasType :
    ∀ (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
      (Env : TEnv T.IDMeta) _env,
      e.resolve C Env = .ok ⟨e_typed, _env⟩ →
      HasType C (Env.context) e (.forAll [] e_typed.toLMonoTy) := by
  intro e e_typed C Env _env h
  -- Decompose resolve into resolveAux + applySubstT
  simp only [LExpr.resolve, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i v h_aux
    obtain ⟨et, Env'⟩ := v
    simp at h
    obtain ⟨h_typed, h_env'⟩ := h
    have ⟨_h_ctx, h_hastype⟩ := resolveAux_HasType e et C Env Env' h_aux
    have h_fresh := resolveAux_keys_fresh e et C Env Env' h_aux
    have h_ty := h_hastype Env'.stateSubstInfo.subst h_fresh
    rw [← h_typed, applySubstT_toLMonoTy]
    exact h_ty

---------------------------------------------------------------------

section Tests

-- Examples of typing derivations using the `HasType` relation.

open LExpr.SyntaxMono LTy.Syntax

macro "solveKnownNames" : tactic =>  `(tactic | simp[KnownTypes.containsName, LTy.toKnownType!, makeKnownTypes, KnownTypes.default, LContext.default])

example : LExpr.HasType LContext.default {} esM[#true] t[bool] := by
  apply LExpr.HasType.tbool_const; solveKnownNames

example : LExpr.HasType LContext.default {} esM[#-1] t[int] := by
  apply LExpr.HasType.tint_const; solveKnownNames

example : LExpr.HasType LContext.default { types := [[(⟨"x", ()⟩, t[∀a. %a])]]} esM[x] t[int] := by
  have h_tinst := @LExpr.HasType.tinst (T := ⟨Unit, Unit⟩) _ LContext.default { types := [[("x", t[∀a. %a])]]} esM[x] t[∀a. %a] t[int] "a" mty[int]
  have h_tvar := @LExpr.HasType.tvar (T := ⟨Unit, Unit⟩) _ LContext.default { types := [[("x", t[∀a. %a])]]} () "x" t[∀a. %a]
  apply h_tinst; apply h_tvar; rfl
  simp +ground; rfl

example : LExpr.HasType LContext.default { types := [[(⟨"m", ()⟩, t[∀a. %a → int])]]}
                        esM[(m #true)]
                        t[int] := by
  apply LExpr.HasType.tapp _ _ _ _ _ t[bool]
  · simp
    apply LExpr.HasType.tinst _ _ t[∀a. %a → int] t[bool → int] "a" mty[bool]
    · apply LExpr.HasType.tvar
      simp +ground
    · simp [LTy.open, List.removeAll,
            LMonoTy.subst, LMonoTys.subst, LMonoTys.subst.substAux,
            Subst.hasEmptyScopes,
            Map.isEmpty, Maps.find?, Map.find?]
  · apply LExpr.HasType.tbool_const
    solveKnownNames
  · simp +ground
  · simp +ground

example : LExpr.HasType {} {} esM[λ %0] t[∀a. %a → %a] := by
  have h_tabs := @LExpr.HasType.tabs (T := ⟨Unit, Unit⟩) _ {} {} () ("a", none) t[%a] esM[%0] t[%a] none
  simp at h_tabs
  have h_tvar := @LExpr.HasType.tvar (T := ⟨Unit, Unit⟩) _ {} { types := [[("a", t[%a])]] }
                 () "a" t[%a]
  simp [Maps.find?, Map.find?] at h_tvar
  specialize (h_tabs (by unfold fresh; unfold LExpr.freeVars; simp only [List.not_mem_nil,
    not_false_eq_true]) rfl rfl h_tvar)
  simp [LTy.toMonoType] at h_tabs
  have h_tgen := @LExpr.HasType.tgen (T := ⟨Unit, Unit⟩) _ {} {} esM[λ %0] "a"
                 t[%a → %a]
                 h_tabs
  simp[TContext.isFresh, Maps.find?] at h_tgen
  assumption
  done

def idFactory : LFunc ⟨Unit, Unit⟩ := {name := "id", typeArgs := ["a"],  inputs := [⟨"x", .ftvar "a"⟩], output := .ftvar "a"}

example : LExpr.HasType (LContext.default.addFactoryFunction idFactory) {} (.op () ⟨"id", ()⟩ none) t[∀a. %a → %a] := by
  apply (LExpr.HasType.top _ _ idFactory) <;> rfl

example : LExpr.HasType (LContext.default.addFactoryFunction idFactory) {} (.op () ⟨"id", ()⟩ mty[int → int]) t[int → int] := by
  apply (LExpr.HasType.top_annotated _ _ idFactory _ t[∀a. %a → %a] _ [.int]) <;> try rfl
  simp only[LTy.openFull, LTy.toMonoTypeUnsafe, List.zip, LTy.boundVars];
  unfold LMonoTy.subst ;
  simp[Subst.hasEmptyScopes, Map.isEmpty, LMonoTys.subst, LMonoTys.subst.substAux, LMonoTy.subst, Maps.find?, Map.find?, LMonoTy.int]

end Tests

---------------------------------------------------------------------
end LExpr
end Lambda
