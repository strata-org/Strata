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
   - `HasType C Env.context e (.forAll [] (subst Env'.subst et.toLMonoTy))`.

   For recursive cases, each IH gives typing under its own output substitution.
   We upgrade these to the final substitution via `HasType_subst_upgrade`,
   justified by the absorption chain built from `resolveAux_absorbs`,
   `unify_absorbs`, and `Subst.absorbs_trans`.

2. **`annotate_HasType`**: The top-level theorem. Since `resolve` is just
   `resolveAux` followed by `applySubstT`, we decompose the hypothesis,
   apply `resolveAux_HasType` directly, and use `applySubstT_toLMonoTy`.

#### Key supporting lemmas:

- **`Subst.absorbs`**: `S_outer` absorbs `S_inner` when every binding in
  `S_inner` is "already known" to `S_outer`.

- **`LMonoTy.subst_absorbs`**: Absorption implies `subst S_outer (subst S_inner mty) = subst S_outer mty`.

- **`HasType_subst_upgrade`**: Upgrade typing from `S_inner` to `S_outer` via
  absorption + `HasType_subst_fresh_all`.

- **`resolveAux_absorbs`**: Each `resolveAux` call absorbs its input substitution.

- **`unify_absorbs`**: Unification absorbs the pre-unification substitution.

- **`unify_makes_equal`**: Unification makes constrained types equal.

- **`resolveAux_keys_fresh`**: Keys produced by `resolveAux` are fresh in the context.

- **`HasType_subst_fresh_all`**: Typing is preserved under substitution of fresh variables.
-/

/-!
#### Substitution lemmas for `HasType_subst_fresh_all`
-/

/-- If no key of `S` appears in `freeVars(mty)`, then `subst S mty = mty`. -/
theorem LMonoTy.subst_no_relevant_keys (S : Subst) (mty : LMonoTy)
    (h : ∀ x, x ∈ LMonoTy.freeVars mty → x ∉ Maps.keys S) :
    LMonoTy.subst S mty = mty := by
  by_cases hS : Subst.hasEmptyScopes S
  · exact LMonoTy.subst_emptyS hS
  · induction mty with
    | ftvar x =>
      simp [LMonoTy.subst, hS]
      rw [Maps.not_mem_keys_find?_none' S x (h x (by simp [LMonoTy.freeVars]))]
    | bitvec n => simp [LMonoTy.subst]
    | tcons name args ih =>
      simp [LMonoTy.subst, LMonoTys.subst_eq_substLogic, hS]
      induction args with
      | nil => simp [LMonoTys.substLogic, hS]
      | cons a rest ih_rest =>
        simp [LMonoTys.substLogic, hS]
        exact ⟨ih a (List.mem_cons.mpr (Or.inl rfl))
                 (fun x hx => h x (by simp [LMonoTy.freeVars, LMonoTys.freeVars]; left; exact hx)),
               ih_rest (fun b hb => ih b (List.mem_cons.mpr (Or.inr hb)))
                 (fun x hx => h x (by simp [LMonoTy.freeVars, LMonoTys.freeVars]; right; exact hx))⟩

/--
If `t` is a value in a well-formed substitution `S` (i.e., `Maps.find? S a = some t`),
then `subst S t = t`. This is because `SubstWF` guarantees no key of `S` appears
in the free variables of any value in `S`.
-/
theorem LMonoTy.subst_idempotent_value (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (h_find : Maps.find? S a = some t) (h_wf : SubstWF S) :
    LMonoTy.subst S t = t := by
  apply LMonoTy.subst_no_relevant_keys
  intro x hx
  have h_x_in_fvs : x ∈ Subst.freeVars S := Subst.freeVars_of_find_subset S h_find hx
  simp [SubstWF] at h_wf
  intro h_x_key
  exact h_wf x h_x_key h_x_in_fvs

/-- Substitution on a singleton map applied to a free type variable. -/
theorem LMonoTy.subst_single_ftvar (a : TyIdentifier) (t : LMonoTy) (x : TyIdentifier) :
    LMonoTy.subst [[(a, t)]] (.ftvar x) = if a = x then t else .ftvar x := by
  unfold LMonoTy.subst
  simp [Subst.hasEmptyScopes, Map.isEmpty]
  rw [show Maps.find? [[(a, t)]] x = if a = x then some t else none from by
    simp [Maps.find?, Map.find?]; split <;> simp_all]
  split <;> simp_all

/-- The number of keys in `S` that appear in `freeVars(mty)`. Used as the
    termination measure for `HasType_subst_fresh_all`. -/
noncomputable def relevantKeys (S : Subst) (mty : LMonoTy) : Nat :=
  ((Maps.keys S).filter (· ∈ LMonoTy.freeVars mty)).length

/-- `hasEmptyScopes S = false` when `S` contains a binding. -/
theorem Subst.hasEmptyScopes_false_of_find
    (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (h : Maps.find? S a = some t) : Subst.hasEmptyScopes S = false := by
  cases h_eq : Subst.hasEmptyScopes S with
  | false => rfl
  | true => exact absurd (Subst.isEmpty_implies_keys_empty h_eq ▸ Maps.find?_mem_keys S h)
                         (by simp_all)

/-- A key in a well-formed substitution does not appear in its own image. -/
theorem SubstWF.not_mem_freeVars_of_find (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (h_find : Maps.find? S a = some t) (h_wf : SubstWF S) :
    a ∉ LMonoTy.freeVars t := by
  simp [SubstWF] at h_wf
  have h_key := Maps.find?_mem_keys S h_find
  have h_fv_subset := Subst.freeVars_of_find_subset S h_find
  intro h_abs
  exact h_wf a h_key (h_fv_subset h_abs)

/-- Absorption for type lists: the single substitution is absorbed element-wise. -/
theorem LMonoTys.subst_absorbs_single (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (mtys : LMonoTys)
    (hS : Subst.hasEmptyScopes S = false)
    (hSingle : Subst.hasEmptyScopes [[(a, t)]] = false)
    (ih : ∀ m, m ∈ mtys → LMonoTy.subst S (LMonoTy.subst [[(a, t)]] m) = LMonoTy.subst S m) :
    LMonoTys.subst S (LMonoTys.subst [[(a, t)]] mtys) = LMonoTys.subst S mtys := by
  rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic]
  induction mtys with
  | nil => simp [LMonoTys.substLogic, hS, hSingle]
  | cons m rest ih_rest =>
    simp only [LMonoTys.substLogic, hS, hSingle, Bool.false_eq_true, ↓reduceIte]
    have h1 := ih m List.mem_cons_self
    have h2 := ih_rest (fun m' hm' => ih m' (List.mem_cons_of_mem m hm'))
    rw [h1, h2]

/--
Absorption: `subst S (subst [(a,t)] mty) = subst S mty` when `Maps.find? S a = some t`
and `SubstWF S`. The single-variable substitution `[(a,t)]` is "absorbed" by `S`
because `S` already maps `a` to `t`.

Proof: by induction on `mty`.
- `ftvar x` with `x = a`: LHS becomes `subst S t = t` (by `subst_idempotent_value`),
  RHS becomes `subst S (ftvar a) = t` (by `h_find`). Both equal `t`.
- `ftvar x` with `x ≠ a`: `subst [(a,t)] (ftvar x) = ftvar x`, so both sides equal.
- `tcons`: reduce to the list case via `LMonoTys.subst_absorbs_single`.
-/
theorem LMonoTy.subst_absorbs_single (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (mty : LMonoTy) (h_find : Maps.find? S a = some t) (h_wf : SubstWF S) :
    LMonoTy.subst S (LMonoTy.subst [[(a, t)]] mty) = LMonoTy.subst S mty := by
  have hS : Subst.hasEmptyScopes S = false :=
    Subst.hasEmptyScopes_false_of_find S a t h_find
  have hSingle : Subst.hasEmptyScopes [[(a, t)]] = false := by
    simp [Subst.hasEmptyScopes, Map.isEmpty]
  induction mty with
  | ftvar x =>
    by_cases h_eq : a = x
    · -- x = a: inner subst gives t, then subst S t = t = subst S (ftvar a)
      subst h_eq
      have h_inner : LMonoTy.subst [[(a, t)]] (.ftvar a) = t := by
        simp [LMonoTy.subst, Subst.hasEmptyScopes, Map.isEmpty, Maps.find?, Map.find?]
      rw [h_inner]
      simp [LMonoTy.subst, hS, h_find]
      exact LMonoTy.subst_idempotent_value S a t h_find h_wf
    · -- x ≠ a: inner subst is identity
      have h_inner : LMonoTy.subst [[(a, t)]] (.ftvar x) = .ftvar x := by
        simp [LMonoTy.subst, Subst.hasEmptyScopes, Map.isEmpty, Maps.find?, Map.find?, h_eq]
      rw [h_inner]
  | bitvec n =>
    simp [LMonoTy.subst]
  | tcons name args ih =>
    simp only [LMonoTy.subst, hSingle, hS, Bool.false_eq_true, ↓reduceIte]
    congr 1
    exact LMonoTys.subst_absorbs_single S a t args hS hSingle ih

/--
Applying a single substitution `[(a,t)]` strictly decreases `relevantKeys`
when `a ∈ freeVars(mty)`, `Maps.find? S a = some t`, and `SubstWF S`.
-/
theorem relevantKeys_decrease (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (mty : LMonoTy) (h_find : Maps.find? S a = some t) (h_wf : SubstWF S)
    (ha_fv : a ∈ LMonoTy.freeVars mty) :
    relevantKeys S (LMonoTy.subst [[(a, t)]] mty) < relevantKeys S mty := by
  unfold relevantKeys
  -- Key fact 1: a ∉ freeVars t (from SubstWF)
  have ha_not_in_t : a ∉ LMonoTy.freeVars t :=
    SubstWF.not_mem_freeVars_of_find S a t h_find h_wf
  -- Key fact 2: SubstWF for the singleton substitution
  have h_wf_single : SubstWF [[(a, t)]] := SubstWF.single_subst a ha_not_in_t
  -- Key fact 3: a ∉ freeVars (subst [[(a,t)]] mty)
  have ha_not_in_subst : a ∉ LMonoTy.freeVars (LMonoTy.subst [[(a, t)]] mty) := by
    have h_keys := LMonoTy.subst_keys_not_in_substituted_type (S := [[(a, t)]]) (ty := mty) h_wf_single
    simp [Maps.keys, Map.keys] at h_keys
    exact h_keys
  -- Key fact 4: no key of S is in freeVars t
  have h_keys_not_in_t : ∀ k, k ∈ Maps.keys S → k ∉ LMonoTy.freeVars t := by
    intro k hk
    simp [SubstWF] at h_wf
    intro hkt
    have h_t_sub : LMonoTy.freeVars t ⊆ Subst.freeVars S :=
      Subst.freeVars_of_find_subset S h_find
    exact h_wf k hk (h_t_sub hkt)
  -- Key fact 5: freeVars after subst ⊆ freeVars mty ++ freeVars t
  have h_fv_subset := LMonoTy.freeVars_of_subst_subset [[(a, t)]] mty
  -- Now prove the filter length decreases
  apply List.filter_length_lt_of_imp_witness
    (a := a)
  · -- Implication: k ∈ freeVars(subst) → k ∈ freeVars(mty) for k ∈ keys S
    intro k hk hk_in_subst
    rw [decide_eq_true_eq] at hk_in_subst ⊢
    have hk_in_union := h_fv_subset hk_in_subst
    rw [List.mem_append] at hk_in_union
    cases hk_in_union with
    | inl h => exact h
    | inr h =>
      have : Subst.freeVars [[(a, t)]] = LMonoTy.freeVars t := by
        simp [Subst.freeVars, Maps.values, Map.values]
      rw [this] at h
      exact absurd h (h_keys_not_in_t k hk)
  · -- a ∈ Maps.keys S
    exact Maps.find?_mem_keys S h_find
  · -- a ∈ freeVars mty
    rw [decide_eq_true_eq]; exact ha_fv
  · -- a ∉ freeVars (subst [[(a,t)]] mty)
    rw [decide_eq_true_eq]; exact ha_not_in_subst

/-- All keys in substitution `S` are fresh w.r.t. context `Γ`. -/
def Subst.allKeysFresh {T : LExprParams} [DecidableEq T.IDMeta]
    (S : Subst) (Γ : TContext T.IDMeta) : Prop :=
  ∀ a, a ∈ Maps.keys S → TContext.isFresh (T := T) a Γ

/-!
#### Absorption: relating substitutions produced by successive resolveAux calls

When `resolveAux` processes subexpressions, each call extends the substitution.
The key property is that later substitutions "absorb" earlier ones: applying the
outer substitution after the inner one is the same as applying the outer alone.

This lets us upgrade typing judgments from an inner substitution to the final one.
-/

/--
`S_outer` absorbs `S_inner` means: for every binding `a ↦ t` in `S_inner`,
`subst S_outer t = subst S_outer (ftvar a)`. In other words, `S_outer` already
"knows about" every binding in `S_inner`.
-/
def Subst.absorbs (S_outer S_inner : Subst) : Prop :=
  ∀ a t, Maps.find? S_inner a = some t →
    LMonoTy.subst S_outer t = LMonoTy.subst S_outer (.ftvar a)

/--
Absorption implies substitution composition collapses:
`subst S_outer (subst S_inner mty) = subst S_outer mty`.
-/
theorem LMonoTy.subst_absorbs (S_outer S_inner : Subst) (mty : LMonoTy)
    (h : Subst.absorbs S_outer S_inner) :
    LMonoTy.subst S_outer (LMonoTy.subst S_inner mty) = LMonoTy.subst S_outer mty := by
  by_cases h_emptyI : Subst.hasEmptyScopes S_inner
  · rw [LMonoTy.subst_emptyS h_emptyI]
  · have hInner : Subst.hasEmptyScopes S_inner = false := by
      revert h_emptyI; cases Subst.hasEmptyScopes S_inner <;> simp
    induction mty with
    | ftvar x =>
      cases h_find : Maps.find? S_inner x with
      | none =>
        have : LMonoTy.subst S_inner (.ftvar x) = .ftvar x := by
          simp [LMonoTy.subst, hInner, h_find]
        rw [this]
      | some t =>
        have : LMonoTy.subst S_inner (.ftvar x) = t := by
          simp [LMonoTy.subst, hInner, h_find]
        rw [this]; exact h x t h_find
    | bitvec n => simp [LMonoTy.subst]
    | tcons name args ih =>
      have h_inner : LMonoTy.subst S_inner (.tcons name args) =
          .tcons name (LMonoTys.subst S_inner args) := by
        unfold LMonoTy.subst; simp only [hInner, Bool.false_eq_true, ↓reduceIte]
      rw [h_inner]
      by_cases h_emptyO : Subst.hasEmptyScopes S_outer
      · rw [LMonoTy.subst_emptyS h_emptyO, LMonoTy.subst_emptyS h_emptyO]
        congr 1
        rw [LMonoTys.subst_eq_substLogic]
        suffices ∀ xs, (∀ m, m ∈ xs → LMonoTy.subst S_inner m = m) →
            LMonoTys.substLogic S_inner xs = xs by
          exact this args (fun m hm => by
            have := ih m hm
            simp only [LMonoTy.subst_emptyS h_emptyO] at this; exact this)
        intro xs; induction xs with
        | nil => intro _; simp [LMonoTys.substLogic, hInner]
        | cons a rest ih_rest =>
          intro ih_cons
          simp only [LMonoTys.substLogic, hInner, Bool.false_eq_true, ↓reduceIte]
          rw [ih_cons a List.mem_cons_self,
              ih_rest (fun m hm => ih_cons m (List.mem_cons_of_mem a hm))]
      · have hOuter : Subst.hasEmptyScopes S_outer = false := by
          revert h_emptyO; cases Subst.hasEmptyScopes S_outer <;> simp
        have h_l : LMonoTy.subst S_outer (.tcons name (LMonoTys.subst S_inner args)) =
            .tcons name (LMonoTys.subst S_outer (LMonoTys.subst S_inner args)) := by
          unfold LMonoTy.subst; simp only [hOuter, Bool.false_eq_true, ↓reduceIte]
        have h_r : LMonoTy.subst S_outer (.tcons name args) =
            .tcons name (LMonoTys.subst S_outer args) := by
          unfold LMonoTy.subst; simp only [hOuter, Bool.false_eq_true, ↓reduceIte]
        rw [h_l, h_r]; congr 1
        rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic,
            LMonoTys.subst_eq_substLogic]
        suffices ∀ xs,
            (∀ m, m ∈ xs → LMonoTy.subst S_outer (LMonoTy.subst S_inner m) =
              LMonoTy.subst S_outer m) →
            LMonoTys.substLogic S_outer (LMonoTys.substLogic S_inner xs) =
              LMonoTys.substLogic S_outer xs by
          exact this args (fun m hm => ih m hm)
        intro xs; induction xs with
        | nil => intro _; simp [LMonoTys.substLogic, hOuter, hInner]
        | cons a rest ih_rest =>
          intro ih_cons
          simp only [LMonoTys.substLogic, hOuter, hInner, Bool.false_eq_true, ↓reduceIte]
          rw [ih_cons a List.mem_cons_self,
              ih_rest (fun m hm => ih_cons m (List.mem_cons_of_mem a hm))]

/-- Every well-formed substitution absorbs itself. -/
theorem Subst.absorbs_refl (S : Subst) (h_wf : SubstWF S) :
    Subst.absorbs S S := by
  intro a t h_find
  have h_not_empty := Subst.hasEmptyScopes_false_of_find S a t h_find
  have : LMonoTy.subst S (.ftvar a) = t := by
    simp [LMonoTy.subst, h_not_empty, h_find]
  rw [this]
  exact LMonoTy.subst_idempotent_value S a t h_find h_wf

/-- Absorption is transitive: if `S2` absorbs `S1` and `S3` absorbs `S2`,
    then `S3` absorbs `S1`. -/
theorem Subst.absorbs_trans (S1 S2 S3 : Subst)
    (h12 : Subst.absorbs S2 S1) (h23 : Subst.absorbs S3 S2) :
    Subst.absorbs S3 S1 := by
  intro a t h_find
  have h1 := h12 a t h_find
  rw [← LMonoTy.subst_absorbs S3 S2 t h23, h1,
      LMonoTy.subst_absorbs S3 S2 (.ftvar a) h23]

/-- Unification produces a substitution that absorbs the input substitution. -/
theorem unify_absorbs (constraints : Constraints) (S_old S_new : SubstInfo)
    (h : Constraints.unify constraints S_old = .ok S_new) :
    Subst.absorbs S_new.subst S_old.subst := by
  sorry

/--
Multi-constraint unification: if `Constraints.unify [(ty1, ty2), (ty3, ty4)] S_old = .ok S_new`,
then both pairs are made equal under `S_new.subst`.
-/
theorem unify_makes_equal₂ (ty1 ty2 ty3 ty4 : LMonoTy) (S_old S_new : SubstInfo)
    (h : Constraints.unify [(ty1, ty2), (ty3, ty4)] S_old = .ok S_new) :
    LMonoTy.subst S_new.subst ty1 = LMonoTy.subst S_new.subst ty2 ∧
    LMonoTy.subst S_new.subst ty3 = LMonoTy.subst S_new.subst ty4 := by
  sorry

/-!
### Context preservation helpers

These lemmas establish that type-environment operations (`genTyVar`, `genTyVars`,
`instantiateEnv`, `tconsAlias`, `resolveAliases`, `instantiate`,
`instantiateWithCheck`) only modify `genEnv.genState` and `stateSubstInfo`,
never `genEnv.context`.

They are parameterized over `IDMeta` directly (not `T : LExprParams`) because
some are used before the `variable` block that introduces `T`.
-/

/--
`genTyVar` preserves the context.

Now that `genTyVar` returns `Except Format` (instead of using `panic`),
we can prove this as a theorem: the error branch never produces an
environment, and the success branch only updates `genState`.
-/
theorem TGenEnv.genTyVar_context {IDMeta : Type} [ToFormat IDMeta]
    (Env : TGenEnv IDMeta) (tv : TyIdentifier) (Env' : TGenEnv IDMeta)
    (h : TGenEnv.genTyVar Env = .ok (tv, Env')) :
    Env'.context = Env.context := by
  simp [TGenEnv.genTyVar] at h
  split at h
  · simp at h
  · simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]

/-- `genTyVars` preserves the context (by induction, using `genTyVar_context`). -/
theorem TGenEnv.genTyVars_context {IDMeta : Type} [ToFormat IDMeta]
    (n : Nat) (Env : TGenEnv IDMeta)
    (tvs : List TyIdentifier) (Env' : TGenEnv IDMeta)
    (h : TGenEnv.genTyVars n Env = .ok (tvs, Env')) :
    Env'.context = Env.context := by
  induction n generalizing Env tvs Env' with
  | zero =>
    simp [TGenEnv.genTyVars] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
  | succ n ih =>
    simp [TGenEnv.genTyVars, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_gen
      obtain ⟨tv, Env1⟩ := v1; simp at h h_gen
      split at h
      · simp at h
      · rename_i v2 h_rest
        obtain ⟨tvs', Env2⟩ := v2; simp at h
        obtain ⟨_, h2⟩ := h; rw [← h2]
        rw [ih Env1 tvs' Env2 h_rest, TGenEnv.genTyVar_context Env tv Env1 h_gen]

/-- `instantiate` (on `TGenEnv`) preserves the context. -/
private theorem LMonoTys.instantiate_context {IDMeta : Type} [ToFormat IDMeta]
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TGenEnv IDMeta)
    (mtys' : LMonoTys) (Env' : TGenEnv IDMeta)
    (h : LMonoTys.instantiate ids mtys Env = .ok (mtys', Env')) :
    Env'.context = Env.context := by
  simp [LMonoTys.instantiate, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i v1 h_gen
    obtain ⟨tvs, Env1⟩ := v1; simp at h h_gen
    obtain ⟨_, h2⟩ := h; rw [← h2]
    exact TGenEnv.genTyVars_context ids.length Env tvs Env1 h_gen

/-- `instantiateEnv` preserves the context. -/
theorem LMonoTys.instantiateEnv_context {IDMeta : Type} [ToFormat IDMeta]
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TEnv IDMeta)
    (mtys' : LMonoTys) (Env' : TEnv IDMeta)
    (h : LMonoTys.instantiateEnv ids mtys Env = .ok (mtys', Env')) :
    Env'.context = Env.context := by
  unfold LMonoTys.instantiateEnv at h
  generalize h_inst : LMonoTys.instantiate ids mtys Env.genEnv = result at h
  match result, h_inst with
  | .error _, _ => simp at h
  | .ok (a, gE), h_inst =>
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    simp [TEnv.context]
    exact LMonoTys.instantiate_context ids mtys Env.genEnv a gE h_inst

/-- `tconsAlias` preserves the context. -/
theorem tconsAlias_context {IDMeta : Type} [ToFormat IDMeta]
    (name : String) (args : LMonoTys) (Env : TEnv IDMeta)
    (mty : LMonoTy) (Env' : TEnv IDMeta)
    (h : LMonoTy.tconsAlias name args Env = .ok (mty, Env')) :
    Env'.context = Env.context := by
  unfold LMonoTy.tconsAlias at h
  generalize h_ma : List.find? _ _ = ma at h
  match ma with
  | none =>
    simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]
  | some alias =>
    simp at h
    split at h
    · simp at h
    · rename_i instTypes updatedEnv h_inst
      generalize h_u : Constraints.unify _ _ = u at h
      match u with
      | .error e => simp at h
      | .ok S =>
        simp [Pure.pure, Except.pure] at h
        obtain ⟨_, h2⟩ := h; rw [← h2]
        simp [TEnv.updateSubst, TEnv.context]
        exact LMonoTys.instantiateEnv_context _ _ Env _ updatedEnv h_inst

mutual
/-- `LMonoTy.resolveAliases` preserves the context. -/
theorem LMonoTy.resolveAliases_context {IDMeta : Type} [ToFormat IDMeta]
    (mty : LMonoTy) (Env : TEnv IDMeta) (mty' : LMonoTy) (Env' : TEnv IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env')) :
    Env'.context = Env.context := by
  match mty with
  | .ftvar _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
  | .bitvec _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_args
      obtain ⟨args', Env1⟩ := v1; simp at h h_args
      split at h
      · simp at h
      · rename_i v2 h_tcons
        obtain ⟨mty'', Env2⟩ := v2
        simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]
        rw [tconsAlias_context name args' Env1 mty'' Env2 h_tcons,
            LMonoTys.resolveAliases_context args Env args' Env1 h_args]
theorem LMonoTys.resolveAliases_context {IDMeta : Type} [ToFormat IDMeta]
    (mtys : LMonoTys) (Env : TEnv IDMeta) (mtys' : LMonoTys) (Env' : TEnv IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env')) :
    Env'.context = Env.context := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_hd
      obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
      split at h
      · simp at h
      · rename_i v2 h_tl
        obtain ⟨mrest', Env2⟩ := v2
        simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]
        rw [LMonoTys.resolveAliases_context mrest Env1 mrest' Env2 h_tl,
            LMonoTy.resolveAliases_context mty Env mty' Env1 h_hd]
end

/-- `LTy.instantiate` preserves the context. -/
theorem LTy.instantiate_context {IDMeta : Type} [ToFormat IDMeta]
    (ty : LTy) (Env : TGenEnv IDMeta)
    (mty : LMonoTy) (Env' : TGenEnv IDMeta)
    (h : LTy.instantiate ty Env = .ok (mty, Env')) :
    Env'.context = Env.context := by
  simp [LTy.instantiate, Bind.bind, Except.bind] at h
  split at h
  · simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
  · split at h
    · simp at h
    · rename_i v1 h_gen
      obtain ⟨tvs, Env1⟩ := v1; simp at h h_gen
      obtain ⟨_, h2⟩ := h; rw [← h2]
      exact TGenEnv.genTyVars_context _ Env tvs Env1 h_gen

/-- `LTy.resolveAliases` preserves the context. -/
theorem LTy.resolveAliases_context {IDMeta : Type} [ToFormat IDMeta]
    (ty : LTy) (Env : TEnv IDMeta) (mty : LMonoTy) (Env' : TEnv IDMeta)
    (h : LTy.resolveAliases ty Env = .ok (mty, Env')) :
    Env'.context = Env.context := by
  simp [LTy.resolveAliases, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i v1 h_inst
    obtain ⟨mty0, genEnv'⟩ := v1; simp at h h_inst
    have h_ra := LMonoTy.resolveAliases_context _ _ mty Env' h
    rw [h_ra]; simp [TEnv.context]
    exact LTy.instantiate_context ty Env.genEnv mty0 genEnv' h_inst

variable {T : LExprParams} [ToString T.IDMeta] [DecidableEq T.IDMeta]
  [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)]

/-!
### Definitions and lemmas for the `resolveAux`-based proof strategy
-/

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
  -- Trivial case: S has empty scopes
  by_cases hS : Subst.hasEmptyScopes S
  · rw [LMonoTy.subst_emptyS hS]; exact h
  · -- Strong induction on relevantKeys S mty
    suffices ∀ (n : Nat) (mty : LMonoTy),
        relevantKeys S mty = n →
        HasType C Γ e (.forAll [] mty) →
        HasType C Γ e (.forAll [] (LMonoTy.subst S mty)) from
      this (relevantKeys S mty) mty rfl h
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro mty h_rk h_ty
      -- Check if any key of S is in freeVars mty
      by_cases h_any : ∃ a, a ∈ Maps.keys S ∧ a ∈ LMonoTy.freeVars mty
      · -- Inductive case: there's a relevant key
        obtain ⟨a, ha_key, ha_fv⟩ := h_any
        obtain ⟨t, h_find⟩ := Maps.find?_of_mem_keys' S a ha_key
        -- Step 1: apply HasType_subst_fresh for the single binding (a, t)
        have h_a_fresh : TContext.isFresh a Γ := h_fresh a ha_key
        have h1 : HasType C Γ e (.forAll [] (LMonoTy.subst [[(a, t)]] mty)) :=
          HasType_subst_fresh C Γ e mty a t h_ty h_a_fresh
        -- Step 2: by induction, apply HasType_subst_fresh_all to the substituted type
        have h_decrease := relevantKeys_decrease S a t mty h_find h_wf ha_fv
        have h2 : HasType C Γ e
            (.forAll [] (LMonoTy.subst S (LMonoTy.subst [[(a, t)]] mty))) :=
          ih (relevantKeys S (LMonoTy.subst [[(a, t)]] mty))
            (h_rk ▸ h_decrease) (LMonoTy.subst [[(a, t)]] mty) rfl h1
        -- Step 3: rewrite using absorption
        rwa [LMonoTy.subst_absorbs_single S a t mty h_find h_wf] at h2
      · -- Base case: no relevant key, so subst S mty = mty
        have h_no_key : ∀ x, x ∈ LMonoTy.freeVars mty → x ∉ Maps.keys S :=
          fun x hx hxk => h_any ⟨x, hxk, hx⟩
        rw [LMonoTy.subst_no_relevant_keys S mty h_no_key]; exact h_ty

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
      unfold LMonoTy.subst; simp [hS, Maps.not_mem_keys_find?_none' S x this]
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
  subst h_lty
  -- Abbreviate: let S' = the new substitution, lty = subst S orig_lty
  -- S' is non-empty (has a binding for id)
  have h_find_S'_id : Maps.find? (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
      id (LMonoTy.subst S orig_lty)) id = some (LMonoTy.subst S orig_lty) :=
    Maps.find?_insert_self _ _ _
  have hS' : Subst.hasEmptyScopes (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
      id (LMonoTy.subst S orig_lty)) = false :=
    Subst.hasEmptyScopes_false_of_find _ id _ h_find_S'_id
  -- The apply preserves keys, so find? (apply ...) id = none
  have h_apply_none : Maps.find? (Subst.apply [(id, LMonoTy.subst S orig_lty)] S) id = none := by
    rw [Subst.find?_apply]; simp [h_none]
  -- For x ≠ id, find? S' x = (find? S x).map (subst [[(id, lty)]])
  have h_find_ne : ∀ x, x ≠ id →
      Maps.find? (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
        id (LMonoTy.subst S orig_lty)) x =
      (Maps.find? S x).map (LMonoTy.subst [[(id, LMonoTy.subst S orig_lty)]]) := fun x hx =>
    (Maps.find?_insert_ne_of_none _ _ _ _ hx h_apply_none).trans (Subst.find?_apply _ _ _)
  -- subst [[(id, lty)]] t = t when id ∉ freeVars t
  have h_single_noop : ∀ t : LMonoTy, ¬(id ∈ t.freeVars) →
      LMonoTy.subst [[(id, LMonoTy.subst S orig_lty)]] t = t := fun t ht =>
    LMonoTy.subst_no_relevant_keys _ _ (fun x hx => by
      simp [Maps.keys, Map.keys]; intro heq; subst heq; exact ht hx)
  by_cases hS : Subst.hasEmptyScopes S
  · -- S has empty scopes: subst S is the identity
    simp only [LMonoTy.subst_emptyS hS] at h_occurs h_find_ne ⊢
    apply LMonoTy.subst_no_relevant_keys
    intro x hx
    have h_ne : x ≠ id := fun h => h_occurs (h ▸ hx)
    exact Maps.find?_of_not_mem_values _ (by
      rw [h_find_ne x h_ne, Maps.not_mem_keys_find?_none' S x
        ((Subst.isEmpty_implies_keys_empty hS) ▸ (by simp))]; simp)
  · -- S doesn't have empty scopes
    have hS_ne : Subst.hasEmptyScopes S = false := by
      revert hS; cases Subst.hasEmptyScopes S <;> simp
    suffices ∀ mty, ¬(id ∈ (LMonoTy.subst S mty).freeVars) →
        LMonoTy.subst (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
          id (LMonoTy.subst S orig_lty)) mty = LMonoTy.subst S mty from
      this orig_lty h_occurs
    intro mty h_nf
    induction mty with
    | ftvar x =>
      by_cases h_id : x = id
      · -- Vacuous: subst S (ftvar id) = ftvar id, so id ∈ freeVars
        subst h_id; exfalso; apply h_nf
        simp [LMonoTy.subst, hS_ne, h_none, LMonoTy.freeVars]
      · -- x ≠ id
        unfold LMonoTy.subst
        simp only [hS', hS_ne, Bool.false_eq_true, ↓reduceIte, h_find_ne x h_id]
        cases h_fx : Maps.find? S x with
        | none => simp
        | some t =>
          simp only [Option.map]
          exact h_single_noop t (by
            have : LMonoTy.subst S (.ftvar x) = t := by
              simp [LMonoTy.subst, hS_ne, h_fx]
            rwa [this] at h_nf)
    | bitvec n => simp [LMonoTy.subst]
    | tcons name args ih =>
      unfold LMonoTy.subst
      simp only [hS', hS_ne, Bool.false_eq_true, ↓reduceIte]
      congr 1
      rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic]
      have h_nf' : ¬(id ∈ LMonoTys.freeVars (LMonoTys.substLogic S args)) := by
        have h_eq : LMonoTy.subst S (.tcons name args) =
            .tcons name (LMonoTys.subst S args) := by
          unfold LMonoTy.subst; simp [hS_ne]
        simp only [h_eq, LMonoTy.freeVars, LMonoTys.subst_eq_substLogic] at h_nf
        exact h_nf
      suffices ∀ xs,
          (∀ m, m ∈ xs → ¬(id ∈ (LMonoTy.subst S m).freeVars) →
            LMonoTy.subst (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
              id (LMonoTy.subst S orig_lty)) m = LMonoTy.subst S m) →
          ¬(id ∈ LMonoTys.freeVars (LMonoTys.substLogic S xs)) →
          LMonoTys.substLogic (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
            id (LMonoTy.subst S orig_lty)) xs = LMonoTys.substLogic S xs by
        exact this args (fun m hm h_nfm => ih m hm h_nfm) h_nf'
      intro xs; induction xs with
      | nil => intros; simp [LMonoTys.substLogic, hS', hS_ne]
      | cons a rest ih_rest =>
        intro ih_xs h_nf_xs
        simp only [LMonoTys.substLogic, hS', hS_ne, Bool.false_eq_true, ↓reduceIte]
        have h_eq_cons : LMonoTys.substLogic S (a :: rest) =
            LMonoTy.subst S a :: LMonoTys.substLogic S rest := by
          simp [LMonoTys.substLogic, hS_ne]
        rw [h_eq_cons, LMonoTys.freeVars_of_cons] at h_nf_xs
        have h1 : ¬(id ∈ (LMonoTy.subst S a).freeVars) :=
          fun h => h_nf_xs (List.mem_append_left _ h)
        have h2 : ¬(id ∈ LMonoTys.freeVars (LMonoTys.substLogic S rest)) :=
          fun h => h_nf_xs (List.mem_append_right _ h)
        rw [ih_xs a (.head _) h1,
            ih_rest (fun m hm => ih_xs m (.tail _ hm)) h2]

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

/--
`resolveAux` produces a substitution that absorbs the input substitution.
This follows from the fact that each step of unification (adding `id ↦ lty`)
builds `S_new = (Subst.apply [(id, lty)] S_old).insert id lty`, and the
well-formedness invariant ensures old values don't contain keys of `S_old`.
-/
theorem resolveAux_absorbs :
    ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  sorry

/--
Upgrade lemma: if `e` has type `subst S_inner mty` and `S_outer` absorbs
`S_inner`, then `e` has type `subst S_outer mty` (provided `S_outer`'s keys
are fresh in the context).

This is the key mechanism for composing IHs in the new formulation: each
recursive call gives typing under its own output substitution, and we upgrade
to the final substitution via absorption.
-/
theorem HasType_subst_upgrade
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono) (mty : LMonoTy)
    (S_inner S_outer : Subst)
    (h_ty : HasType C Γ e (.forAll [] (LMonoTy.subst S_inner mty)))
    (h_absorbs : Subst.absorbs S_outer S_inner)
    (h_fresh : Subst.allKeysFresh S_outer Γ)
    (h_wf : SubstWF S_outer) :
    HasType C Γ e (.forAll [] (LMonoTy.subst S_outer mty)) := by
  have h1 := HasType_subst_fresh_all C Γ e (LMonoTy.subst S_inner mty) S_outer h_ty h_fresh h_wf
  rw [LMonoTy.subst_absorbs S_outer S_inner mty h_absorbs] at h1
  exact h1

/--
Context preservation for `LTy.instantiateWithCheck`.
`instantiateWithCheck` only modifies `genEnv.genState` and `stateSubstInfo`,
never `genEnv.context`.
-/
theorem LTy_instantiateWithCheck_context
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env')) :
    Env'.context = Env.context := by
  simp [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i v1 h_ra
    obtain ⟨mty', Env1⟩ := v1
    split at h
    · simp [Pure.pure, Except.pure] at h
      obtain ⟨_, h2⟩ := h; rw [← h2]
      exact LTy.resolveAliases_context ty Env mty' Env1 h_ra
    · simp at h

/-- Context preservation for `LMonoTy.instantiateWithCheck`. -/
theorem LMonoTy_instantiateWithCheck_context
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (mty, Env')) :
    Env'.context = Env.context := by
  simp [LMonoTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i v1 h_inst
    obtain ⟨instTypes, Env_mid⟩ := v1
    split at h
    · simp at h
    · rename_i v2 h_ra
      obtain ⟨mty', Env2⟩ := v2; simp at h h_ra
      split at h
      · simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]
        rw [LMonoTy.resolveAliases_context _ _ mty' Env2 h_ra]
        exact LMonoTys.instantiateEnv_context _ _ Env _ _ h_inst
      · simp at h

/--
Semantic property of `LTy.instantiateWithCheck` for typing (unannotated case):
If `ty` is in the context for variable `x`, and `instantiateWithCheck ty C Env`
produces `(mty, Env')`, then `(.fvar m x none)` has type
`(.forAll [] (subst Env'.subst mty))`.

This captures the fact that `instantiateWithCheck` produces an instantiation
of the polymorphic type `ty`, and applying the output substitution yields a
valid monomorphic instance.

Proof sketch: `tvar` gives `HasType C Γ (.fvar m x none) ty`. Then
`instantiate` replaces bound vars with fresh vars (justified by `tgen`/`tinst`),
`resolveAliases` resolves type aliases (preserving typing via alias equivalence),
and `subst Env'.subst` applies the accumulated substitution (justified by
`HasType_subst_fresh_all` since all keys are fresh).
-/
theorem instantiateWithCheck_fvar_HasType
    (C : LContext T) (Γ : TContext T.IDMeta) (x : Identifier T.IDMeta)
    (ty : LTy) (mty : LMonoTy) (Env Env' : TEnv T.IDMeta)
    (m : T.mono.base.Metadata)
    (h_find : Γ.types.find? x = some ty)
    (h_ctx : Env.context = Γ)
    (h_inst : LTy.instantiateWithCheck ty C Env = .ok (mty, Env')) :
    HasType C Γ (.fvar m x none)
      (.forAll [] (LMonoTy.subst Env'.stateSubstInfo.subst mty)) := by
  -- Depends on `HasType_subst_fresh_all` and the tgen/tinst bridge connecting
  -- polymorphic type `ty` to monomorphic instance `mty`. See docstring above.
  sorry

/--
Semantic property for the annotated case: if `ty` is in the context for `x`,
`instantiateWithCheck ty` produces `(mty, Env1)`, `instantiateWithCheck fty_val`
produces `(fty_inst, Env2)`, and unification of `(fty_inst, mty)` produces `S`,
then `(.fvar m x (some fty_val))` has type
`(.forAll [] (subst S.subst mty))`.
-/
theorem instantiateWithCheck_fvar_annotated_HasType
    (C : LContext T) (Γ : TContext T.IDMeta) (x : Identifier T.IDMeta)
    (ty : LTy) (mty : LMonoTy) (fty_val fty_inst : LMonoTy)
    (Env Env1 Env2 : TEnv T.IDMeta) (S : SubstInfo)
    (m : T.mono.base.Metadata)
    (h_find : Γ.types.find? x = some ty)
    (h_ctx : Env.context = Γ)
    (h_inst : LTy.instantiateWithCheck ty C Env = .ok (mty, Env1))
    (h_inst2 : LMonoTy.instantiateWithCheck fty_val C Env1 = .ok (fty_inst, Env2))
    (h_unify : Constraints.unify [(fty_inst, mty)] Env2.stateSubstInfo = .ok S) :
    HasType C Γ (.fvar m x (some fty_val))
      (.forAll [] (LMonoTy.subst S.subst mty)) := by
  -- Depends on `HasType_subst_fresh_all` and the tgen/tinst bridge, same as
  -- `instantiateWithCheck_fvar_HasType` but additionally uses `tvar_annotated`
  -- and the unification result to connect the annotation with the inferred type.
  sorry

/--
Helper: `inferFVar` preserves the context and produces a well-typed result.

For the unannotated case (`fty = none`):
  `inferFVar` looks up `x` in context to get `ty_poly`, instantiates bound
  type variables with fresh ones via `LTy.instantiateWithCheck`, and returns
  the instantiated monomorphic type `mty`. The typing follows from `tvar`
  (giving `ty_poly`) composed with `tinst` (instantiating bound vars).

For the annotated case (`fty = some fty_val`):
  Additionally unifies the annotation with the instantiated type. The typing
  follows from `tvar_annotated` or `tvar` + `tinst` + absorption/upgrade.
-/
theorem inferFVar_HasType
    (C : LContext T) (Env : TEnv T.IDMeta) (x : Identifier T.IDMeta)
    (fty : Option LMonoTy) (ty_res : LMonoTy) (Env' : TEnv T.IDMeta)
    (m : T.mono.base.Metadata)
    (h : inferFVar C Env x fty = .ok (ty_res, Env')) :
    Env'.context = Env.context ∧
    HasType C (Env.context) (.fvar m x fty)
      (.forAll [] (LMonoTy.subst Env'.stateSubstInfo.subst ty_res)) := by
  simp only [inferFVar, Bind.bind, Except.bind] at h
  split at h
  · simp at h  -- context lookup failed
  · rename_i ty h_find
    split at h
    · simp at h  -- instantiateWithCheck failed
    · rename_i v1 h_inst
      obtain ⟨mty, Env1⟩ := v1
      simp at h h_inst
      split at h
      · -- Case fty = none: return (mty, Env1)
        simp at h
        obtain ⟨h_ty, h_env⟩ := h
        subst h_ty; subst h_env
        constructor
        · -- Context preservation
          exact LTy_instantiateWithCheck_context ty C Env mty Env1 h_inst
        · -- Typing: delegate to instantiateWithCheck_fvar_HasType
          exact instantiateWithCheck_fvar_HasType C Env.context x ty mty Env Env1 m
            h_find rfl h_inst
      · -- Case fty = some fty_val
        rename_i fty_val
        split at h
        · simp at h  -- LMonoTy.instantiateWithCheck failed
        · rename_i v2 h_inst2
          obtain ⟨fty_inst, Env2⟩ := v2
          simp at h h_inst2
          split at h
          · simp at h  -- unify failed (via mapError)
          · rename_i S h_unify_raw
            simp at h
            obtain ⟨h_ty, h_env⟩ := h
            subst h_ty; subst h_env
            -- Extract unify hypothesis from mapError wrapper
            have h_unify : Constraints.unify [(fty_inst, mty)]
                Env2.stateSubstInfo = .ok S := by
              revert h_unify_raw
              generalize Constraints.unify [(fty_inst, mty)]
                Env2.stateSubstInfo = res
              intro h_me
              match res, h_me with
              | .ok val, h_me => simp [Except.mapError] at h_me; rw [h_me]
              | .error _, h_me => simp [Except.mapError] at h_me
            constructor
            · -- Context preservation
              simp [TEnv.updateSubst, TEnv.context]
              have h1 := LTy_instantiateWithCheck_context ty C Env mty Env1 h_inst
              have h2 := LMonoTy_instantiateWithCheck_context fty_val C Env1
                fty_inst Env2 h_inst2
              simp [TEnv.context] at h1 h2
              rw [h2, h1]
            · -- Typing: delegate to instantiateWithCheck_fvar_annotated_HasType
              simp [TEnv.updateSubst]
              exact instantiateWithCheck_fvar_annotated_HasType C Env.context x ty
                mty fty_val fty_inst Env Env1 Env2 S m h_find rfl h_inst h_inst2
                h_unify

/-!
### Core theorem: `resolveAux_HasType`

This is the main workhorse. It states that `resolveAux` produces a typed
expression `et` such that the original expression `e` has type
`subst Env'.subst et.toLMonoTy` under the original context, where `Env'` is
the output environment.

For recursive cases (e.g., `eq`, `ite`, `app`), each IH gives typing under
its own output substitution. We upgrade these to the final substitution using
`HasType_subst_upgrade`, justified by the absorption chain:
- `resolveAux_absorbs`: each `resolveAux` call absorbs its input substitution
- `unify_absorbs`: unification absorbs the pre-unification substitution
- `Subst.absorbs_trans`: absorption composes transitively
-/
theorem resolveAux_HasType :
    ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      Env'.context = Env.context ∧
      HasType C (Env.context) e
        (.forAll [] (LMonoTy.subst Env'.stateSubstInfo.subst et.toLMonoTy)) := by
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
      · rw [← h_et]; simp [toLMonoTy]
        rw [← h_env]; rw [LConst.ty_subst]
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
    -- resolveAux calls inferFVar, which looks up x in context, instantiates
    -- bound type variables, and optionally unifies with the annotation.
    intro et C Env Env' h
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_infer
      obtain ⟨ty_res, Env_res⟩ := v1
      simp at h
      obtain ⟨h_et, h_env'⟩ := h
      rw [← h_et, ← h_env']
      simp [toLMonoTy]
      exact inferFVar_HasType C Env x fty ty_res Env_res m h_infer
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
    -- resolveAux recurses on c, t, e, then unifies [(cty, bool), (tty, ety)].
    -- Result type is tty (the then-branch type), and the HasType rule is `tif`.
    intro et C Env Env' h
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    -- Decompose: resolveAux C Env c
    split at h
    · simp at h
    · rename_i v1 h_res_c
      obtain ⟨ct, Env1⟩ := v1
      dsimp at h h_res_c
      -- Decompose: resolveAux C Env1 t
      split at h
      · simp at h
      · rename_i v2 h_res_t
        obtain ⟨tht, Env2⟩ := v2
        dsimp at h h_res_t
        -- Decompose: resolveAux C Env2 e
        split at h
        · simp at h
        · rename_i v3 h_res_e
          obtain ⟨elt, Env3⟩ := v3
          dsimp at h h_res_e
          -- Decompose: Constraints.unify (wrapped in mapError)
          split at h
          · simp at h
          · rename_i v4 h_mapError
            simp at h
            obtain ⟨h_et, h_env'⟩ := h
            -- Extract the underlying unify hypothesis from the mapError wrapper
            have h_unify : Constraints.unify [(ct.toLMonoTy, LMonoTy.bool),
                (tht.toLMonoTy, elt.toLMonoTy)]
                Env3.stateSubstInfo = .ok v4 := by
              revert h_mapError
              generalize Constraints.unify [(toLMonoTy ct, LMonoTy.bool),
                (toLMonoTy tht, toLMonoTy elt)]
                Env3.stateSubstInfo = res
              intro h_me
              match res, h_me with
              | .ok val, h_me => simp at h_me; rw [h_me]
              | .error _, h_me => simp at h_me
            -- IHs from recursive calls
            have ⟨h_ctx1, h_ty_c⟩ := ih_c ct C Env Env1 h_res_c
            have ⟨h_ctx2, h_ty_t⟩ := ih_t tht C Env1 Env2 h_res_t
            have ⟨h_ctx3, h_ty_e⟩ := ih_e elt C Env2 Env3 h_res_e
            -- Absorption chain: v4 absorbs Env3 absorbs Env2 absorbs Env1 absorbs Env
            have h_abs_v4_Env3 := unify_absorbs
              [(ct.toLMonoTy, LMonoTy.bool), (tht.toLMonoTy, elt.toLMonoTy)]
              Env3.stateSubstInfo v4 h_unify
            have h_abs_Env3_Env2 := resolveAux_absorbs e elt C Env2 Env3 h_res_e
            have h_abs_Env2_Env1 := resolveAux_absorbs t tht C Env1 Env2 h_res_t
            have h_abs_Env1_Env := resolveAux_absorbs c ct C Env Env1 h_res_c
            have h_abs_v4_Env2 := Subst.absorbs_trans
              Env2.stateSubstInfo.subst Env3.stateSubstInfo.subst v4.subst
              h_abs_Env3_Env2 h_abs_v4_Env3
            have h_abs_v4_Env1 := Subst.absorbs_trans
              Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst v4.subst
              h_abs_Env2_Env1 h_abs_v4_Env2
            -- Freshness of v4.subst keys in Env.context
            have h_fresh_v4 : Subst.allKeysFresh v4.subst Env.context := by
              have := resolveAux_keys_fresh (.ite m c t e)
                (.ite ⟨m, tht.toLMonoTy⟩ ct tht elt) C Env
                (TEnv.updateSubst Env3 v4) (by
                  simp [resolveAux, Bind.bind, Except.bind, Except.mapError,
                    h_res_c, h_res_t, h_res_e]
                  revert h_mapError
                  generalize Constraints.unify [(toLMonoTy ct, LMonoTy.bool),
                    (toLMonoTy tht, toLMonoTy elt)]
                    Env3.stateSubstInfo = res
                  intro h_me
                  match res, h_me with
                  | .ok val, h_me => simp at h_me ⊢; rw [h_me]
                  | .error _, h_me => simp at h_me)
              simp [TEnv.updateSubst] at this
              exact this
            constructor
            · -- Context preservation
              rw [← h_env']
              simp [TEnv.updateSubst, TEnv.context]
              change Env3.context = Env.context
              rw [h_ctx3, h_ctx2, h_ctx1]
            · -- Typing: result type is tht.toLMonoTy, rule is HasType.tif
              rw [← h_et]; simp [toLMonoTy]
              rw [← h_env']; simp [TEnv.updateSubst]
              -- Unification makes: subst v4 cty = bool, subst v4 tty = subst v4 ety
              have ⟨h_eq_bool, h_eq_te⟩ := unify_makes_equal₂
                ct.toLMonoTy LMonoTy.bool tht.toLMonoTy elt.toLMonoTy
                Env3.stateSubstInfo v4 h_unify
              -- Upgrade IH_c: from Env1.subst to v4.subst
              have h_ty_c_up := HasType_subst_upgrade C Env.context c
                ct.toLMonoTy Env1.stateSubstInfo.subst v4.subst
                h_ty_c h_abs_v4_Env1 h_fresh_v4 v4.isWF
              -- Upgrade IH_t: from Env2.subst to v4.subst
              rw [h_ctx1] at h_ty_t
              have h_ty_t_up := HasType_subst_upgrade C Env.context t
                tht.toLMonoTy Env2.stateSubstInfo.subst v4.subst
                h_ty_t h_abs_v4_Env2 h_fresh_v4 v4.isWF
              -- Upgrade IH_e: from Env3.subst to v4.subst
              rw [h_ctx2, h_ctx1] at h_ty_e
              have h_ty_e_up := HasType_subst_upgrade C Env.context e
                elt.toLMonoTy Env3.stateSubstInfo.subst v4.subst
                h_ty_e h_abs_v4_Env3 h_fresh_v4 v4.isWF
              -- Condition has type bool
              rw [h_eq_bool, LMonoTy.subst_bool] at h_ty_c_up
              -- Then and else branches have the same type
              rw [← h_eq_te] at h_ty_e_up
              exact HasType.tif Env.context m c t e
                (.forAll [] (LMonoTy.subst v4.subst tht.toLMonoTy))
                h_ty_c_up h_ty_t_up h_ty_e_up
  | eq m e1 e2 ih1 ih2 =>
    -- resolveAux recurses on e1 and e2, then unifies their types.
    -- Result type is LMonoTy.bool (ground), so subst S bool = bool for any S.
    -- We upgrade both IHs to the final substitution via absorption.
    intro et C Env Env' h
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    -- Decompose: resolveAux C Env e1
    split at h
    · simp at h
    · rename_i v1 h_res1
      obtain ⟨e1t, Env1⟩ := v1
      dsimp at h h_res1
      -- Decompose: resolveAux C Env1 e2
      split at h
      · simp at h
      · rename_i v2 h_res2
        obtain ⟨e2t, Env2⟩ := v2
        dsimp at h h_res2
        -- Decompose: Constraints.unify (wrapped in mapError)
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
          -- IHs from recursive calls
          have ⟨h_ctx1, h_ty1⟩ := ih1 e1t C Env Env1 h_res1
          have ⟨h_ctx2, h_ty2⟩ := ih2 e2t C Env1 Env2 h_res2
          -- Absorption chain: v3 absorbs Env2 absorbs Env1 absorbs Env
          have h_abs_v3_Env2 := unify_absorbs [(e1t.toLMonoTy, e2t.toLMonoTy)]
            Env2.stateSubstInfo v3 h_unify
          have h_abs_Env2_Env1 := resolveAux_absorbs e2 e2t C Env1 Env2 h_res2
          have h_abs_Env1_Env := resolveAux_absorbs e1 e1t C Env Env1 h_res1
          have h_abs_v3_Env1 := Subst.absorbs_trans
            Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst v3.subst
            h_abs_Env2_Env1 h_abs_v3_Env2
          -- Freshness of v3.subst keys in Env.context
          have h_fresh_v3 : Subst.allKeysFresh v3.subst Env.context := by
            have := resolveAux_keys_fresh (.eq m e1 e2) (.eq ⟨m, LMonoTy.bool⟩ e1t e2t) C Env
              (TEnv.updateSubst Env2 v3) (by
                simp [resolveAux, Bind.bind, Except.bind, Except.mapError, h_res1, h_res2]
                revert h_mapError
                generalize Constraints.unify [(toLMonoTy e1t, toLMonoTy e2t)]
                  Env2.stateSubstInfo = res
                intro h_me
                match res, h_me with
                | .ok val, h_me => simp at h_me ⊢; rw [h_me]
                | .error _, h_me => simp at h_me)
            simp [TEnv.updateSubst] at this
            exact this
          constructor
          · -- Context preservation
            rw [← h_env']
            simp [TEnv.updateSubst, TEnv.context]
            change Env2.context = Env.context
            rw [h_ctx2, h_ctx1]
          · -- Typing: result type is bool (ground)
            rw [← h_et]; simp [toLMonoTy]
            rw [← h_env']; simp [TEnv.updateSubst]
            rw [LMonoTy.subst_bool]
            -- Upgrade IH1: from Env1.subst to v3.subst
            have h_ty1_upgraded := HasType_subst_upgrade C Env.context e1
              e1t.toLMonoTy Env1.stateSubstInfo.subst v3.subst
              h_ty1 h_abs_v3_Env1 h_fresh_v3 v3.isWF
            -- Upgrade IH2: from Env2.subst to v3.subst
            rw [h_ctx1] at h_ty2
            have h_ty2_upgraded := HasType_subst_upgrade C Env.context e2
              e2t.toLMonoTy Env2.stateSubstInfo.subst v3.subst
              h_ty2 h_abs_v3_Env2 h_fresh_v3 v3.isWF
            -- Unification makes types equal under v3.subst
            have h_eq := unify_makes_equal e1t.toLMonoTy e2t.toLMonoTy
              Env2.stateSubstInfo v3 h_unify
            rw [h_eq] at h_ty1_upgraded
            exact HasType.teq Env.context m e1 e2
              (.forAll [] (LMonoTy.subst v3.subst e2t.toLMonoTy))
              h_ty1_upgraded h_ty2_upgraded

/--
### Main theorem: `annotate_HasType`

If `e.resolve C Env` succeeds with `e_typed`, then `e` has type
`e_typed.toLMonoTy` under the original context.

The proof decomposes `resolve` into `resolveAux` + `applySubstT`, then
applies `resolveAux_HasType` directly (the new formulation already gives
typing under the output substitution) and uses `applySubstT_toLMonoTy`.
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
    rw [← h_typed, applySubstT_toLMonoTy]
    exact h_hastype

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
