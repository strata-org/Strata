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

/--
Composition lemma: applying a singleton substitution `[[(v, t)]]` followed by
`[ys]` equals applying the merged substitution `[(v, t) :: ys]`, provided
`subst [ys] t = t` (i.e., `t` is stable under `ys`).

This is a key lemma for proving that sequential `tinst` applications
(each substituting one bound variable) produce the same result as a
single parallel substitution with all bindings.
-/
theorem LMonoTy.subst_cons_single
    (v : TyIdentifier) (t : LMonoTy) (ys : SubstOne) (mty : LMonoTy)
    (h_t : LMonoTy.subst [ys] t = t) :
    LMonoTy.subst [ys] (LMonoTy.subst [[(v, t)]] mty) =
    LMonoTy.subst [((v, t) :: ys)] mty := by
  have hSingle : Subst.hasEmptyScopes [[(v, t)]] = false := by
    simp [Subst.hasEmptyScopes, Map.isEmpty]
  have hCons : Subst.hasEmptyScopes [((v, t) :: ys)] = false := by
    simp [Subst.hasEmptyScopes, Map.isEmpty]
  by_cases hYs : Subst.hasEmptyScopes [ys]
  · -- ys is empty, so subst [ys] is identity
    have h_ys_empty : ys = [] := by
      simp [Subst.hasEmptyScopes, Map.isEmpty] at hYs
      cases ys with
      | nil => rfl
      | cons _ _ => simp [Map.isEmpty] at hYs
    subst h_ys_empty
    simp only [LMonoTy.subst_emptyS hYs]
  · have hYs_ne : Subst.hasEmptyScopes [ys] = false := by
      revert hYs; cases Subst.hasEmptyScopes [ys] <;> simp
    induction mty with
    | ftvar x =>
      by_cases h_eq : v = x
      · -- v = x: inner subst gives t, then subst [ys] t = t by h_t
        subst h_eq
        have h_inner : LMonoTy.subst [[(v, t)]] (.ftvar v) = t := by
          simp [LMonoTy.subst, Subst.hasEmptyScopes, Map.isEmpty, Maps.find?, Map.find?]
        rw [h_inner, h_t]
        -- RHS: subst [(v,t)::ys] (ftvar v) = t (first match in (v,t)::ys)
        simp [LMonoTy.subst, hCons, Maps.find?, Map.find?]
      · -- v ≠ x: inner subst is identity, lookup x in ys
        have h_inner : LMonoTy.subst [[(v, t)]] (.ftvar x) = .ftvar x := by
          simp [LMonoTy.subst, Subst.hasEmptyScopes, Map.isEmpty, Maps.find?, Map.find?, h_eq]
        rw [h_inner]
        -- Both sides look up x in ys (since v ≠ x, (v,t)::ys skips (v,t))
        simp [LMonoTy.subst, hYs_ne, hCons, Maps.find?, Map.find?, h_eq]
    | bitvec n =>
      simp [LMonoTy.subst]
    | tcons name args ih =>
      simp only [LMonoTy.subst, hSingle, hYs_ne, hCons, Bool.false_eq_true, ↓reduceIte]
      congr 1
      rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic,
          LMonoTys.subst_eq_substLogic]
      suffices ∀ xs,
          (∀ m, m ∈ xs → LMonoTy.subst [ys] (LMonoTy.subst [[(v, t)]] m) =
            LMonoTy.subst [((v, t) :: ys)] m) →
          LMonoTys.substLogic [ys] (LMonoTys.substLogic [[(v, t)]] xs) =
            LMonoTys.substLogic [((v, t) :: ys)] xs by
        exact this args ih
      intro xs; induction xs with
      | nil => intro _; simp [LMonoTys.substLogic, hSingle, hYs_ne, hCons]
      | cons a rest ih_rest =>
        intro ih_xs
        simp only [LMonoTys.substLogic, hSingle, hYs_ne, hCons, Bool.false_eq_true, ↓reduceIte]
        rw [ih_xs a List.mem_cons_self,
            ih_rest (fun m hm => ih_xs m (List.mem_cons_of_mem a hm))]

-- Helper: applyLogic preserves some bindings.
private theorem Map.find?_applyLogic_some_h' {new old : SubstOne} {a : TyIdentifier} {t : LMonoTy}
    (h : Map.find? old a = some t) :
    Map.find? (SubstOne.applyLogic new old) a = some (LMonoTy.subst [new] t) := by
  induction old with
  | nil => simp [Map.find?] at h
  | cons hd rest ih =>
    simp only [SubstOne.applyLogic, Map.find?]
    simp only [Map.find?] at h
    split at h
    · rename_i h_eq; simp only [Option.some.injEq] at h; subst h; simp [h_eq]
    · rename_i h_ne; simp [h_ne]; exact ih h

-- Helper: applyLogic preserves none bindings.
private theorem Map.find?_applyLogic_none_h' {new old : SubstOne} {a : TyIdentifier}
    (h : Map.find? old a = none) :
    Map.find? (SubstOne.applyLogic new old) a = none := by
  induction old with
  | nil => simp [SubstOne.applyLogic, Map.find?]
  | cons hd rest ih =>
    simp [SubstOne.applyLogic, Map.find?]
    simp [Map.find?] at h
    split at h
    · simp at h
    · rename_i h_ne; simp [h_ne]; exact ih h

-- Helper: Subst.apply preserves some bindings.
private theorem Maps.find?_apply_some_h' {new : SubstOne} {old : Subst} {a : TyIdentifier} {t : LMonoTy}
    (h : Maps.find? old a = some t) :
    Maps.find? (Subst.apply new old) a = some (LMonoTy.subst [new] t) := by
  induction old with
  | nil => simp [Maps.find?] at h
  | cons m rest ih =>
    simp only [Subst.apply, Maps.find?]
    simp only [Maps.find?] at h
    rw [SubstOne.apply_eq_applyLogic]
    cases h_ma : Map.find? m a with
    | none =>
      rw [h_ma] at h
      rw [Map.find?_applyLogic_none_h' h_ma]
      exact ih h
    | some val =>
      rw [h_ma] at h; simp only [Option.some.injEq] at h; subst h
      rw [Map.find?_applyLogic_some_h' h_ma]

-- Helper: Except.mapError preserves ok values.
private theorem Except.mapError_ok_h' {α β γ : Type} {f : α → β} {e : Except α γ} {v : γ}
    (h : Except.mapError f e = .ok v) : e = .ok v := by
  cases e with
  | error a => simp [Except.mapError] at h
  | ok val => simp [Except.mapError] at h; exact congrArg Except.ok h

-- Helper: insert+apply produces an absorbing substitution.
private theorem absorbs_of_insert_apply_h' (S : SubstInfo) (id : TyIdentifier) (lty : LMonoTy)
    (h_none : Maps.find? S.subst id = none)
    (h_wf : SubstWF ((Subst.apply [(id, lty)] S.subst).insert id lty)) :
    Subst.absorbs ((Subst.apply [(id, lty)] S.subst).insert id lty) S.subst := by
  intro a t h_find
  have h_a_ne_id : a ≠ id := by
    intro h_eq; subst h_eq; rw [h_find] at h_none; simp at h_none
  let S_new := (Subst.apply [(id, lty)] S.subst).insert id lty
  have h_apply_a := Maps.find?_apply_some_h' (new := [(id, lty)]) h_find
  have h_find_new : Maps.find? S_new a = some (LMonoTy.subst [[(id, lty)]] t) := by
    show Maps.find? (Maps.insert _ id lty) a = _
    rw [Maps.find?_insert_ne _ _ _ _ h_a_ne_id]
    exact h_apply_a
  have h_find_id : Maps.find? S_new id = some lty := Maps.find?_insert_self _ id lty
  have h_not_empty := Subst.hasEmptyScopes_false_of_find S_new a _ h_find_new
  have h_subst_ftvar : LMonoTy.subst S_new (.ftvar a) = LMonoTy.subst [[(id, lty)]] t := by
    simp [LMonoTy.subst, h_not_empty, h_find_new]
  have h_idem := LMonoTy.subst_idempotent_value S_new a _ h_find_new h_wf
  have h_abs := LMonoTy.subst_absorbs_single S_new id lty t h_find_id h_wf
  rw [h_subst_ftvar, ← h_abs, h_idem]

-- unifyOne produces a substitution that absorbs the input.
private theorem unifyOne_absorbs' (c : Constraint) (S : SubstInfo)
    (relS : ValidSubstRelation [c] S)
    (h : Constraint.unifyOne c S = .ok relS) :
    Subst.absorbs relS.newS.subst S.subst := by
  suffices ∀ relS, Constraint.unifyOne c S = .ok relS →
      Subst.absorbs relS.newS.subst S.subst from this relS h
  apply Constraint.unifyOne.induct
    (motive1 := fun c S => ∀ relS, Constraint.unifyOne c S = .ok relS →
      Subst.absorbs relS.newS.subst S.subst)
    (motive2 := fun cs S => ∀ relS, Constraints.unifyCore cs S = .ok relS →
      Subst.absorbs relS.newS.subst S.subst)
  -- Case 1: t1 == t2
  · intro S t1 t2 h_eq _ relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · simp only [Except.ok.injEq] at h; subst h; exact Subst.absorbs_refl S.subst S.isWF
    · exact absurd h_eq ‹_›
  -- Case 2: ftvar id, orig_lty; ftvar id == lty
  · intro S id orig_lty h_neq _lty _ _ h_eq_lty relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [Except.ok.injEq] at h; subst h; exact Subst.absorbs_refl S.subst S.isWF
  -- Case 3: ftvar id, orig_lty; occurs check
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_occurs relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 4: ftvar id, orig_lty; some sty — recursive
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_not_occurs sty h_some ih_rec relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty' h_some'
        rw [h_some] at h_some'; simp only [Option.some.injEq] at h_some'; subst h_some'
        simp only [bind, Except.bind] at h
        split at h
        · simp at h
        · rename_i relS' h_call
          simp only [Except.ok.injEq] at h; rw [← h]; exact ih_rec relS' h_call
      · rename_i h_none; rw [h_some] at h_none; simp at h_none
  -- Case 5: ftvar id, orig_lty; none — insert+apply
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_not_occurs h_none _ _ _ns h' _nS _ _ relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty h_some; rw [h_none] at h_some; simp at h_some
      · simp only [Except.ok.injEq] at h; rw [← h]; simp only
        exact absorbs_of_insert_apply_h' S id (LMonoTy.subst S.subst orig_lty) h_none
          (SubstWF.cons_of_subst_apply S id orig_lty _ rfl
            (SubstWF.single_subst id h_not_occurs) (SubstWF.apply_one_substituted_type S id orig_lty))
  -- Case 6: orig_lty, ftvar id; ftvar id == lty
  · intro S orig_lty id h_neq _ _lty _ _ h_eq_lty relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [Except.ok.injEq] at h; subst h; exact Subst.absorbs_refl S.subst S.isWF
  -- Case 7: orig_lty, ftvar id; occurs check
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_occurs relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 8: orig_lty, ftvar id; some sty — recursive
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_not_occurs sty h_some ih_rec relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty' h_some'
        rw [h_some] at h_some'; simp only [Option.some.injEq] at h_some'; subst h_some'
        simp only [bind, Except.bind] at h
        split at h
        · simp at h
        · rename_i relS' h_call
          simp only [Except.ok.injEq] at h; rw [← h]; exact ih_rec relS' h_call
      · rename_i h_none; rw [h_some] at h_none; simp at h_none
  -- Case 9: orig_lty, ftvar id; none — insert+apply
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_not_occurs h_none _ _ _ns h' _nS _ _ relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty h_some; rw [h_none] at h_some; simp at h_some
      · simp only [Except.ok.injEq] at h; rw [← h]; simp only
        exact absorbs_of_insert_apply_h' S id (LMonoTy.subst S.subst orig_lty) h_none
          (SubstWF.cons_of_subst_apply S id orig_lty _ rfl
            (SubstWF.single_subst id h_not_occurs) (SubstWF.apply_one_substituted_type S id orig_lty))
  -- Case 10: bitvec n1 == n2 contradiction
  · intro S n1 n2 h_neq h_eq_n relS h
    exfalso; simp [beq_iff_eq] at h_eq_n; subst h_eq_n
    exact h_neq (beq_self_eq_true (LMonoTy.bitvec n1))
  -- Case 11: bitvec n1 ≠ n2 — error
  · intro S n1 n2 h_neq h_neq_n relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 12: tcons match — recursive unifyCore
  · intro S name1 args1 name2 args2 h_neq h_match _nc ih_core relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [bind, Except.bind] at h
      split at h
      · simp at h
      · rename_i relS' h_call
        simp only [Except.ok.injEq] at h; rw [← h]; exact ih_core relS' h_call
  -- Case 13: tcons name/length mismatch — error
  · intro S name1 args1 name2 args2 h_neq h_mismatch relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 14: bitvec, tcons — error
  · intro S size name args h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 15: tcons, bitvec — error
  · intro S name args size h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 16: unifyCore []
  · intro S relS h
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Except.ok.injEq] at h; subst h; exact Subst.absorbs_refl S.subst S.isWF
  -- Case 17: unifyCore c :: rest
  · intro S c c_rest ih1 ih2 relS h
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Bind.bind, Except.bind, Except.mapError] at h
    split at h
    · simp at h
    · rename_i relS_one h_one_raw
      have h_one := Except.mapError_ok_h' h_one_raw
      split at h
      · simp at h
      · rename_i relS_rest h_rest
        simp only [Except.ok.injEq] at h
        have h_eq : relS_rest.newS = relS.newS := by cases h; rfl
        rw [← h_eq]
        exact Subst.absorbs_trans S.subst relS_one.newS.subst relS_rest.newS.subst
          (ih1 relS_one h_one) (ih2 relS_one relS_rest h_rest)

-- unifyCore produces a substitution that absorbs the input.
private theorem unifyCore_absorbs (cs : Constraints) (S : SubstInfo)
    (relS : ValidSubstRelation cs S)
    (h : Constraints.unifyCore cs S = .ok relS) :
    Subst.absorbs relS.newS.subst S.subst := by
  induction cs generalizing S with
  | nil =>
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Except.ok.injEq] at h; subst h
    exact Subst.absorbs_refl S.subst S.isWF
  | cons c rest ih =>
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Bind.bind, Except.bind, Except.mapError] at h
    split at h
    · simp at h
    · rename_i relS_one h_one_raw
      have h_one := Except.mapError_ok_h' h_one_raw
      split at h
      · simp at h
      · rename_i relS_rest h_rest
        simp only [Except.ok.injEq] at h
        have h_eq : relS_rest.newS = relS.newS := by cases h; rfl
        rw [← h_eq]
        exact Subst.absorbs_trans S.subst relS_one.newS.subst relS_rest.newS.subst
          (unifyOne_absorbs' c S relS_one h_one)
          (ih relS_one.newS relS_rest h_rest)

/-- Unification produces a substitution that absorbs the input substitution. -/
theorem unify_absorbs (constraints : Constraints) (S_old S_new : SubstInfo)
    (h : Constraints.unify constraints S_old = .ok S_new) :
    Subst.absorbs S_new.subst S_old.subst := by
  simp only [Constraints.unify, bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i relS h_core
    simp only [Except.ok.injEq] at h; subst h
    exact unifyCore_absorbs constraints S_old relS h_core

/-!
### Context preservation helpers

These lemmas establish that type-environment operations (`genTyVar`, `genTyVars`,
`instantiateEnv`, `tconsAlias`, `resolveAliases`, `instantiate`,
`instantiateWithCheck`) only modify `genEnv.genState` and `stateSubstInfo`,
never `genEnv.context`.

They are parameterized over `IDMeta` directly (not `T : LExprParams`) because
some are used before the `variable` block that introduces `T`.
-/

/-- `genTyVars n` produces exactly `n` fresh type variables. -/
private theorem TGenEnv.genTyVars_length {IDMeta : Type} [ToFormat IDMeta]
    (n : Nat) (Env : TGenEnv IDMeta)
    (tvs : List TyIdentifier) (Env' : TGenEnv IDMeta)
    (h : TGenEnv.genTyVars n Env = .ok (tvs, Env')) :
    tvs.length = n := by
  induction n generalizing Env tvs Env' with
  | zero =>
    simp [TGenEnv.genTyVars] at h
    obtain ⟨h1, _⟩ := h; subst h1; simp
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
        obtain ⟨h1, _⟩ := h; subst h1
        simp [ih Env1 tvs' Env2 h_rest]

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
  suffices ∀ relS, Constraint.unifyOne c S = .ok relS →
      LMonoTy.subst relS.newS.subst c.1 = LMonoTy.subst relS.newS.subst c.2
    from this relS h
  apply Constraint.unifyOne.induct
    (motive1 := fun c S => ∀ relS, Constraint.unifyOne c S = .ok relS →
      LMonoTy.subst relS.newS.subst c.1 = LMonoTy.subst relS.newS.subst c.2)
    (motive2 := fun cs S => ∀ relS, Constraints.unifyCore cs S = .ok relS →
      ∀ p, p ∈ cs → LMonoTy.subst relS.newS.subst p.1 = LMonoTy.subst relS.newS.subst p.2)
  -- Case 1: t1 == t2
  · intro S t1 t2 h_eq _ relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · simp only [Except.ok.injEq] at h; subst h
      have := eq_of_beq h_eq; subst this; rfl
    · exact absurd h_eq ‹_›
  -- Case 2: ftvar id, orig_lty; ftvar id == lty
  · intro S id orig_lty h_neq _lty _ _ h_eq_lty relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [Except.ok.injEq] at h; subst h
      show LMonoTy.subst S.subst (.ftvar id) = LMonoTy.subst S.subst orig_lty
      have h_id_eq : LMonoTy.ftvar id = LMonoTy.subst S.subst orig_lty := eq_of_beq h_eq_lty
      rw [h_id_eq]; exact LMonoTy.subst_idempotent S.subst S.isWF orig_lty
  -- Case 3: ftvar id, orig_lty; occurs check — error
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_occurs relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 4: ftvar id, orig_lty; some sty — recursive
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_not_occurs sty h_some ih_rec relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty' h_some'
        rw [h_some] at h_some'; simp only [Option.some.injEq] at h_some'; subst h_some'
        simp only [bind, Except.bind] at h
        split at h
        · simp at h
        · rename_i relS' h_call
          simp only [Except.ok.injEq] at h; rw [← h]
          -- IH: subst S'.subst sty = subst S'.subst (subst S.subst orig_lty)
          have ih := ih_rec relS' h_call
          simp only [] at ih
          -- S' absorbs S (from unifyOne_absorbs')
          have h_abs := unifyOne_absorbs' (sty, LMonoTy.subst S.subst orig_lty) S relS' h_call
          -- subst S' (ftvar id) = subst S' sty (since S.find? id = some sty, absorption gives this)
          have h_ftvar : LMonoTy.subst relS'.newS.subst (.ftvar id) =
              LMonoTy.subst relS'.newS.subst sty := by
            have := h_abs id sty h_some
            simp only [this]
          -- subst S' (subst S orig) = subst S' orig (by absorption)
          have h_orig : LMonoTy.subst relS'.newS.subst (LMonoTy.subst S.subst orig_lty) =
              LMonoTy.subst relS'.newS.subst orig_lty :=
            LMonoTy.subst_absorbs relS'.newS.subst S.subst orig_lty h_abs
          -- Chain: subst S' (ftvar id) = subst S' sty = subst S' (subst S orig) = subst S' orig
          rw [h_ftvar, ih, h_orig]
      · rename_i h_none; rw [h_some] at h_none; simp at h_none
  -- Case 5: ftvar id, orig_lty; none — insert+apply
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_not_occurs h_none _ _ _ns h' _nS _ _ relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty h_some; rw [h_none] at h_some; simp at h_some
      · simp only [Except.ok.injEq] at h; rw [← h]; simp only
        exact Eq.trans
          (subst_ftvar_new_binding S.subst id (LMonoTy.subst S.subst orig_lty) h_none)
          (subst_orig_new_binding S.subst id (LMonoTy.subst S.subst orig_lty)
            orig_lty h_none rfl h_not_occurs).symm
  -- Case 6: orig_lty, ftvar id; ftvar id == lty
  · intro S orig_lty id h_neq _ _lty _ _ h_eq_lty relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [Except.ok.injEq] at h; subst h
      show LMonoTy.subst S.subst orig_lty = LMonoTy.subst S.subst (.ftvar id)
      have h_id_eq : LMonoTy.ftvar id = LMonoTy.subst S.subst orig_lty := eq_of_beq h_eq_lty
      rw [h_id_eq]; exact (LMonoTy.subst_idempotent S.subst S.isWF orig_lty).symm
  -- Case 7: orig_lty, ftvar id; occurs check — error
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_occurs relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 8: orig_lty, ftvar id; some sty — recursive (symmetric to case 4)
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_not_occurs sty h_some ih_rec relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty' h_some'
        rw [h_some] at h_some'; simp only [Option.some.injEq] at h_some'; subst h_some'
        simp only [bind, Except.bind] at h
        split at h
        · simp at h
        · rename_i relS' h_call
          simp only [Except.ok.injEq] at h; rw [← h]; simp only []
          -- ih: subst S' sty = subst S' (subst S orig_lty)
          have ih := ih_rec relS' h_call; simp only [] at ih
          have h_abs := unifyOne_absorbs' (sty, LMonoTy.subst S.subst orig_lty) S relS' h_call
          have h_ftvar : LMonoTy.subst relS'.newS.subst (.ftvar id) =
              LMonoTy.subst relS'.newS.subst sty := by
            have := h_abs id sty h_some; simp only [this]
          have h_orig : LMonoTy.subst relS'.newS.subst (LMonoTy.subst S.subst orig_lty) =
              LMonoTy.subst relS'.newS.subst orig_lty :=
            LMonoTy.subst_absorbs relS'.newS.subst S.subst orig_lty h_abs
          -- Goal: subst S' orig_lty = subst S' (ftvar id)
          rw [← h_orig, ← ih, h_ftvar]
      · rename_i h_none; rw [h_some] at h_none; simp at h_none
  -- Case 9: orig_lty, ftvar id; none — insert+apply (symmetric to case 5)
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_not_occurs h_none _ _ _ns h' _nS _ _ relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty h_some; rw [h_none] at h_some; simp at h_some
      · simp only [Except.ok.injEq] at h; rw [← h]; simp only
        exact Eq.symm (Eq.trans
          (subst_ftvar_new_binding S.subst id (LMonoTy.subst S.subst orig_lty) h_none)
          (subst_orig_new_binding S.subst id (LMonoTy.subst S.subst orig_lty)
            orig_lty h_none rfl h_not_occurs).symm)
  -- Case 10: bitvec n1 == n2 contradiction
  · intro S n1 n2 h_neq h_eq_n relS h
    exfalso; simp [beq_iff_eq] at h_eq_n; subst h_eq_n
    exact h_neq (beq_self_eq_true (LMonoTy.bitvec n1))
  -- Case 11: bitvec n1 ≠ n2 — error
  · intro S n1 n2 h_neq h_neq_n relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 12: tcons match — recursive unifyCore
  · intro S name1 args1 name2 args2 h_neq h_match _nc ih_core relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [bind, Except.bind] at h
      split at h
      · simp at h
      · rename_i relS' h_call
        simp only [Except.ok.injEq] at h; rw [← h]
        -- h_match : (name1 == name2 && args1.length == args2.length) = true
        have h_name_eq : name1 = name2 := by
          have := (Bool.and_eq_true _ _ ▸ h_match : _ ∧ _).1; exact eq_of_beq this
        have h_len_eq : args1.length = args2.length := by
          have := (Bool.and_eq_true _ _ ▸ h_match : _ ∧ _).2; exact of_decide_eq_true this
        subst h_name_eq
        -- ih_core : all pairs in (args1.zip args2) are equalized under relS'
        -- We need: subst S' (tcons name args1) = subst S' (tcons name args2)
        -- i.e., tcons name (subst_list S' args1) = tcons name (subst_list S' args2)
        -- which requires subst_list S' args1 = subst_list S' args2
        -- Goal: subst S' (.tcons name args1) = subst S' (.tcons name args2)
        -- ih_core gives pointwise equality for zip pairs
        have ih_pw := ih_core relS' h_call
        -- Show LMonoTy.subst equality by showing the args lists are equal after subst
        -- subst S (tcons n args) = if hasEmptyScopes then tcons n args else tcons n (subst_list S args)
        -- We prove the args lists are pointwise equal after substitution
        -- Helper: derive args1 = args2 or LMonoTys.subst S args1 = LMonoTys.subst S args2
        -- from pointwise zip equality
        have h_args_eq : ∀ (l1 l2 : LMonoTys), l1.length = l2.length →
            (∀ p, p ∈ l1.zip l2 →
              LMonoTy.subst relS'.newS.subst p.1 = LMonoTy.subst relS'.newS.subst p.2) →
            LMonoTys.subst relS'.newS.subst l1 = LMonoTys.subst relS'.newS.subst l2 := by
          intro l1 l2 h_len h_pw
          rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic]
          by_cases hS : Subst.hasEmptyScopes relS'.newS.subst
          · -- Empty scopes: substLogic returns the list unchanged
            have h_id : ∀ l, LMonoTys.substLogic relS'.newS.subst l = l := by
              intro l; induction l with
              | nil => simp [LMonoTys.substLogic, hS]
              | cons _ _ _ => simp [LMonoTys.substLogic, hS]
            rw [h_id, h_id]
            -- Need l1 = l2 from pointwise identity-subst equality
            induction l1 generalizing l2 with
            | nil => cases l2 with | nil => rfl | cons _ _ => simp at h_len
            | cons a rest ih_l =>
              cases l2 with
              | nil => simp at h_len
              | cons b rest2 =>
                simp at h_len
                have h_ab := h_pw (a, b) List.mem_cons_self
                simp [LMonoTy.subst_emptyS hS] at h_ab
                rw [h_ab, ih_l rest2 h_len fun p hp => h_pw p (List.mem_cons_of_mem _ hp)]
          · have hS_ne : Subst.hasEmptyScopes relS'.newS.subst = false := by
              revert hS; cases Subst.hasEmptyScopes relS'.newS.subst <;> simp
            induction l1 generalizing l2 with
            | nil => cases l2 with | nil => simp [LMonoTys.substLogic, hS_ne] | cons _ _ => simp at h_len
            | cons a rest ih_l =>
              cases l2 with
              | nil => simp at h_len
              | cons b rest2 =>
                simp at h_len
                simp only [LMonoTys.substLogic, hS_ne, Bool.false_eq_true, ↓reduceIte]
                have h_ab : LMonoTy.subst relS'.newS.subst a = LMonoTy.subst relS'.newS.subst b :=
                  h_pw (a, b) List.mem_cons_self
                rw [h_ab, ih_l rest2 h_len fun p hp => h_pw p (List.mem_cons_of_mem _ hp)]
        -- Now apply: subst S (tcons n args) uses LMonoTys.subst on args
        have h_list := h_args_eq args1 args2 h_len_eq ih_pw
        by_cases hS_final : Subst.hasEmptyScopes relS'.newS.subst
        · -- Empty scopes: subst is identity
          simp [LMonoTy.subst_emptyS hS_final]
          simp [LMonoTys.subst, hS_final] at h_list; rw [h_list]
        · -- Non-empty scopes: subst on tcons applies to args
          have hS_ne : Subst.hasEmptyScopes relS'.newS.subst = false := by
            revert hS_final; cases Subst.hasEmptyScopes relS'.newS.subst <;> simp
          simp [LMonoTy.subst, hS_ne]; exact h_list
  -- Case 13: tcons name/length mismatch — error
  · intro S name1 args1 name2 args2 h_neq h_mismatch relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 14: bitvec, tcons — error
  · intro S size name args h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 15: tcons, bitvec — error
  · intro S name args size h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 16: unifyCore []
  · intro S relS h p hp
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Except.ok.injEq] at h; subst h
    exact absurd hp List.not_mem_nil
  -- Case 17: unifyCore c :: rest
  · intro S c c_rest ih_one ih_core relS h p hp
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Bind.bind, Except.bind, Except.mapError] at h
    split at h
    · simp at h
    · rename_i relS_one h_one_raw
      have h_one := Except.mapError_ok_h' h_one_raw
      split at h
      · simp at h
      · rename_i relS_rest h_rest
        simp only [Except.ok.injEq] at h
        have h_eq : relS_rest.newS = relS.newS := by cases h; rfl
        rw [← h_eq]
        -- p ∈ c :: c_rest: either p = c or p ∈ c_rest
        cases List.mem_cons.mp hp with
        | inl h_pc =>
          -- p = c: use ih_one to get equality under relS_one, then lift via absorption
          subst h_pc
          have h_sound_one := ih_one relS_one h_one
          have h_abs := unifyCore_absorbs c_rest relS_one.newS relS_rest h_rest
          calc LMonoTy.subst relS_rest.newS.subst p.1
              = LMonoTy.subst relS_rest.newS.subst (LMonoTy.subst relS_one.newS.subst p.1) :=
                (LMonoTy.subst_absorbs _ _ _ h_abs).symm
            _ = LMonoTy.subst relS_rest.newS.subst (LMonoTy.subst relS_one.newS.subst p.2) := by
                rw [h_sound_one]
            _ = LMonoTy.subst relS_rest.newS.subst p.2 :=
                LMonoTy.subst_absorbs _ _ _ h_abs
        | inr h_rest_mem =>
          -- p ∈ c_rest: use ih_core
          exact ih_core relS_one relS_rest h_rest p h_rest_mem

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
Multi-constraint unification: if `Constraints.unify [(ty1, ty2), (ty3, ty4)] S_old = .ok S_new`,
then both pairs are made equal under `S_new.subst`.
-/
theorem unify_makes_equal₂ (ty1 ty2 ty3 ty4 : LMonoTy) (S_old S_new : SubstInfo)
    (h : Constraints.unify [(ty1, ty2), (ty3, ty4)] S_old = .ok S_new) :
    LMonoTy.subst S_new.subst ty1 = LMonoTy.subst S_new.subst ty2 ∧
    LMonoTy.subst S_new.subst ty3 = LMonoTy.subst S_new.subst ty4 := by
  -- Decompose Constraints.unify into unifyCore
  simp only [Constraints.unify, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i relS_final h_core
    simp only [Except.ok.injEq] at h; subst h
    -- Decompose unifyCore [(ty1,ty2), (ty3,ty4)] S_old
    simp only [Constraints.unifyCore, Bind.bind, Except.bind, Except.mapError] at h_core
    revert h_core
    generalize h_one1 : Constraint.unifyOne (ty1, ty2) S_old = res1
    intro h_core
    match res1 with
    | .error e => simp at h_core
    | .ok relS1 =>
      simp at h_core
      -- Decompose unifyCore [(ty3,ty4)] relS1.newS
      revert h_core
      generalize h_one2 : Constraint.unifyOne (ty3, ty4) relS1.newS = res2
      intro h_core
      match res2 with
      | .error e => simp at h_core
      | .ok relS2 =>
        simp at h_core
        -- After unifyCore [] on relS2.newS, the result is unchanged
        have h_final_eq : relS_final.newS = relS2.newS :=
          congrArg ValidSubstRelation.newS h_core.symm
        -- unifyOne_sound on each pair
        have h_eq1 : LMonoTy.subst relS1.newS.subst ty1 =
            LMonoTy.subst relS1.newS.subst ty2 :=
          unifyOne_sound (ty1, ty2) S_old relS1 h_one1
        have h_eq2 : LMonoTy.subst relS2.newS.subst ty3 =
            LMonoTy.subst relS2.newS.subst ty4 :=
          unifyOne_sound (ty3, ty4) relS1.newS relS2 h_one2
        -- Lift h_eq1 to the final substitution via absorption
        have h_abs : Subst.absorbs relS2.newS.subst relS1.newS.subst :=
          unifyOne_absorbs' (ty3, ty4) relS1.newS relS2 h_one2
        constructor
        · rw [h_final_eq]
          calc LMonoTy.subst relS2.newS.subst ty1
              = LMonoTy.subst relS2.newS.subst (LMonoTy.subst relS1.newS.subst ty1) :=
                (LMonoTy.subst_absorbs relS2.newS.subst relS1.newS.subst ty1 h_abs).symm
            _ = LMonoTy.subst relS2.newS.subst (LMonoTy.subst relS1.newS.subst ty2) := by
                rw [h_eq1]
            _ = LMonoTy.subst relS2.newS.subst ty2 :=
                LMonoTy.subst_absorbs relS2.newS.subst relS1.newS.subst ty2 h_abs
        · rw [h_final_eq]; exact h_eq2

/-- Removing a key from a substitution preserves freshness of all keys. -/
theorem Subst.allKeysFresh_of_remove
    {S : Subst} {Γ : TContext T.IDMeta} {k : TyIdentifier}
    (h : Subst.allKeysFresh S Γ) :
    Subst.allKeysFresh (Maps.remove S k) Γ := by
  intro a ha
  exact h a (Maps.mem_keys_of_mem_keys_remove S k a ha)

/-- If all keys of `Maps.remove S k` are fresh in `Γ` and `k` itself is fresh
    in `Γ`, then all keys of `S` are fresh in `Γ`. This is the converse
    direction of `allKeysFresh_of_remove`, extended with freshness of `k`. -/
theorem Subst.allKeysFresh_of_allKeysFresh_remove
    {S : Subst} {Γ : TContext T.IDMeta} {k : TyIdentifier}
    (h_remove : Subst.allKeysFresh (Maps.remove S k) Γ)
    (h_k : TContext.isFresh (T := T) k Γ) :
    Subst.allKeysFresh S Γ := by
  intro a ha
  by_cases h_eq : a = k
  · subst h_eq; exact h_k
  · exact h_remove a (Maps.mem_keys_remove_of_ne S k a ha h_eq)

/-- Substitution on a type whose free variables don't include any key of `S`
    is the identity. Variant: if no key of `S_big` is in `freeVars(mty)` and
    `keys(S_small) ⊆ keys(S_big)`, then `subst S_small mty = mty`. Here we
    use the special case where `S_small = Maps.remove S_big k`. -/
theorem LMonoTy.subst_remove_eq_self (S : Subst) (k : TyIdentifier) (mty : LMonoTy)
    (h : S.keys.all (fun x => x ∉ mty.freeVars)) :
    LMonoTy.subst (Maps.remove S k) mty = mty := by
  apply LMonoTy.subst_no_key_free
  simp [List.all_eq_true] at h ⊢
  intro x hx
  exact h x (Maps.mem_keys_of_mem_keys_remove S k x hx)

/-- Key inclusion for `unifyOne`: output keys come from input keys,
    single-constraint free vars, or input value free vars.

    Proof by well-founded recursion matching `unifyOne`'s termination measure.
    The only branch that adds a new key is the `none` case (ftvar id with
    `Maps.find? S.subst id = none`), which inserts `id` — a free variable
    of the constraint. The `some sty` branch recurses with the same S. -/
theorem Constraint.unifyOne_keys_incl (c : Constraint) (S : SubstInfo)
    (relS : ValidSubstRelation [c] S)
    (h : Constraint.unifyOne c S = .ok relS) :
    ∀ k, k ∈ Maps.keys relS.newS.subst →
      k ∈ Maps.keys S.subst ∨ k ∈ Constraint.freeVars c ∨ k ∈ Subst.freeVars S.subst := by
  suffices ∀ relS, Constraint.unifyOne c S = .ok relS →
      ∀ k, k ∈ Maps.keys relS.newS.subst →
        k ∈ Maps.keys S.subst ∨ k ∈ Constraint.freeVars c ∨ k ∈ Subst.freeVars S.subst
    from this relS h
  apply Constraint.unifyOne.induct
    (motive1 := fun c S => ∀ relS, Constraint.unifyOne c S = .ok relS →
      ∀ k, k ∈ Maps.keys relS.newS.subst →
        k ∈ Maps.keys S.subst ∨ k ∈ Constraint.freeVars c ∨ k ∈ Subst.freeVars S.subst)
    (motive2 := fun cs S => ∀ relS, Constraints.unifyCore cs S = .ok relS →
      ∀ k, k ∈ Maps.keys relS.newS.subst →
        k ∈ Maps.keys S.subst ∨ k ∈ Constraints.freeVars cs ∨ k ∈ Subst.freeVars S.subst)
  -- Case 1: t1 == t2
  · intro S t1 t2 h_eq _ relS h k hk
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · simp only [Except.ok.injEq] at h; subst h; left; exact hk
    · exact absurd h_eq ‹_›
  -- Case 2: ftvar id, orig_lty; ftvar id == lty
  · intro S id orig_lty h_neq _lty _ _ h_eq_lty relS h k hk
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [Except.ok.injEq] at h; subst h; left; exact hk
  -- Case 3: ftvar id, orig_lty; occurs check
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_occurs relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 4: ftvar id, orig_lty; some sty — recursive
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_not_occurs sty h_some ih_rec relS h k hk
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty' h_some'
        rw [h_some] at h_some'; simp only [Option.some.injEq] at h_some'; subst h_some'
        simp only [bind, Except.bind] at h
        split at h
        · simp at h
        · rename_i relS' h_call
          simp only [Except.ok.injEq] at h; rw [← h] at hk
          -- ih_rec gives: k ∈ keys(S) ∨ k ∈ freeVars(sty, lty) ∨ k ∈ freeVars(S.values)
          rcases ih_rec relS' h_call k hk with h1 | h2 | h3
          · left; exact h1
          · -- k ∈ freeVars(sty, subst S orig_lty). Show it's in freeVars(c) ∨ freeVars(S.values)
            simp only [Constraint.freeVars, List.mem_append] at h2
            rcases h2 with h_sty | h_lty
            · -- k ∈ freeVars(sty): sty is a value of S
              right; right; exact Subst.freeVars_of_find_subset S.subst h_some h_sty
            · -- k ∈ freeVars(subst S orig_lty): by freeVars_of_subst_subset
              rcases List.mem_append.mp (LMonoTy.freeVars_of_subst_subset S.subst orig_lty h_lty) with
                h_orig | h_vals
              · right; left; simp [Constraint.freeVars]; right; exact h_orig
              · right; right; exact h_vals
          · right; right; exact h3
      · rename_i h_none; rw [h_some] at h_none; simp at h_none
  -- Case 5: ftvar id, orig_lty; none — insert+apply
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_not_occurs h_none _ _ _ns h' _nS _ _ relS h k hk
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty h_some; rw [h_none] at h_some; simp at h_some
      · simp only [Except.ok.injEq] at h; subst h
        have hk' := Maps.insert_keys_subset (ms := Subst.apply [(_,_)] S.subst) (key := _) (val := _) hk
        rw [Subst.keys_of_apply_eq] at hk'
        rcases List.mem_cons.mp hk' with rfl | h_old
        · right; left; simp [Constraint.freeVars, LMonoTy.freeVars]
        · left; exact h_old
  -- Case 6: orig_lty, ftvar id; ftvar id == lty
  · intro S orig_lty id h_neq _ _lty _ _ h_eq_lty relS h k hk
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [Except.ok.injEq] at h; subst h; left; exact hk
  -- Case 7: orig_lty, ftvar id; occurs check
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_occurs relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 8: orig_lty, ftvar id; some sty — recursive
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_not_occurs sty h_some ih_rec relS h k hk
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty' h_some'
        rw [h_some] at h_some'; simp only [Option.some.injEq] at h_some'; subst h_some'
        simp only [bind, Except.bind] at h
        split at h
        · simp at h
        · rename_i relS' h_call
          simp only [Except.ok.injEq] at h; rw [← h] at hk
          rcases ih_rec relS' h_call k hk with h1 | h2 | h3
          · left; exact h1
          · simp only [Constraint.freeVars, List.mem_append] at h2
            rcases h2 with h_sty | h_lty
            · right; right; exact Subst.freeVars_of_find_subset S.subst h_some h_sty
            · rcases List.mem_append.mp (LMonoTy.freeVars_of_subst_subset S.subst orig_lty h_lty) with
                h_orig | h_vals
              · right; left; simp [Constraint.freeVars]; left; exact h_orig
              · right; right; exact h_vals
          · right; right; exact h3
      · rename_i h_none; rw [h_some] at h_none; simp at h_none
  -- Case 9: orig_lty, ftvar id; none — insert+apply
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_not_occurs h_none _ _ _ns h' _nS _ _ relS h k hk
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty h_some; rw [h_none] at h_some; simp at h_some
      · simp only [Except.ok.injEq] at h; subst h
        have hk' := Maps.insert_keys_subset (ms := Subst.apply [(_,_)] S.subst) (key := _) (val := _) hk
        rw [Subst.keys_of_apply_eq] at hk'
        rcases List.mem_cons.mp hk' with rfl | h_old
        · right; left; simp [Constraint.freeVars, LMonoTy.freeVars]
        · left; exact h_old
  -- Case 10: bitvec n1 == n2 contradiction
  · intro S n1 n2 h_neq h_eq_n relS h
    exfalso; simp [beq_iff_eq] at h_eq_n; subst h_eq_n
    exact h_neq (beq_self_eq_true (LMonoTy.bitvec n1))
  -- Case 11: bitvec n1 ≠ n2 — error
  · intro S n1 n2 h_neq h_neq_n relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 12: tcons match — recursive unifyCore
  · intro S name1 args1 name2 args2 h_neq h_match _nc ih_core relS h k hk
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [bind, Except.bind] at h
      split at h
      · simp at h
      · rename_i relS' h_call
        simp only [Except.ok.injEq] at h; rw [← h] at hk
        rcases ih_core relS' h_call k hk with h1 | h2 | h3
        · left; exact h1
        · right; left; simp only [Constraint.freeVars, LMonoTy.freeVars, List.mem_append]
          exact List.mem_append.mp (Constraints.freeVars_of_zip_subset h2)
        · right; right; exact h3
  -- Case 13: tcons name/length mismatch — error
  · intro S name1 args1 name2 args2 h_neq h_mismatch relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 14: bitvec, tcons — error
  · intro S size name args h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 15: tcons, bitvec — error
  · intro S name args size h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 16: unifyCore []
  · intro S relS h k hk
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Except.ok.injEq] at h; subst h; left; exact hk
  -- Case 17: unifyCore c :: rest
  · intro S c c_rest ih1 ih2 relS h k hk
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Bind.bind, Except.bind, Except.mapError] at h
    split at h
    · simp at h
    · rename_i relS_one h_one_raw
      have h_one := Except.mapError_ok_h' h_one_raw
      split at h
      · simp at h
      · rename_i relS_rest h_rest
        simp only [Except.ok.injEq] at h
        have h_eq : relS_rest.newS = relS.newS := by cases h; rfl
        rw [← h_eq] at hk
        rcases ih2 relS_one relS_rest h_rest k hk with hk1 | hk2 | hk3
        · rcases ih1 relS_one h_one k hk1 with h1a | h1b | h1c
          · left; exact h1a
          · right; left; simp [Constraints.freeVars]; left; exact h1b
          · right; right; exact h1c
        · right; left; simp [Constraints.freeVars]; right; exact hk2
        · rcases List.mem_append.mp (relS_one.goodSubset hk3) with h_c | h_s
          · right; left; simp [Constraints.freeVars]; left
            simp [Subst.freeVars_subset_prop, Constraints.freeVars] at h_c; exact h_c
          · right; right; exact h_s

/-- Key inclusion for `unifyCore`: output keys come from input keys,
    constraint free vars, or input value free vars. -/
theorem Constraints.unifyCore_keys_incl :
    ∀ (cs : Constraints) (S : SubstInfo)
      (relS : ValidSubstRelation cs S),
      Constraints.unifyCore cs S = .ok relS →
      ∀ k, k ∈ Maps.keys relS.newS.subst →
        k ∈ Maps.keys S.subst ∨ k ∈ Constraints.freeVars cs ∨ k ∈ Subst.freeVars S.subst := by
  intro cs; induction cs with
  | nil =>
    intro S relS h k hk
    unfold Constraints.unifyCore at h; simp at h; subst h; left; exact hk
  | cons c rest ih =>
    intro S relS h k hk
    rw [Constraints.unifyCore.eq_2] at h
    simp only [Bind.bind, Except.bind, Except.mapError] at h
    split at h; · simp at h
    rename_i relS1 h_one; split at h; · simp at h
    rename_i relS2 h_core; simp at h; subst h
    have h_one' : Constraint.unifyOne c S = .ok relS1 := by
      revert h_one; cases Constraint.unifyOne c S <;> simp [Except.mapError]
    rcases ih relS1.newS relS2 h_core k hk with hk1 | hk2 | hk3
    · rcases Constraint.unifyOne_keys_incl c S relS1 h_one' k hk1 with h1a | h1b | h1c
      · left; exact h1a
      · right; left; simp [Constraints.freeVars]; left; exact h1b
      · right; right; exact h1c
    · right; left; simp [Constraints.freeVars]; right; exact hk2
    · rcases List.mem_append.mp (relS1.goodSubset hk3) with h_c | h_s
      · right; left; simp [Constraints.freeVars]; left
        simp [Subst.freeVars_subset_prop, Constraints.freeVars] at h_c; exact h_c
      · right; right; exact h_s

/-- Key-inclusion for `Constraints.unify`: output keys come from input keys,
    constraint free vars, or input value free vars. -/
theorem Constraints.unify_keys_incl
    {cs : Constraints} {S S' : SubstInfo}
    (h_unify : Constraints.unify cs S = .ok S') :
    ∀ k, k ∈ Maps.keys S'.subst →
      k ∈ Maps.keys S.subst ∨ k ∈ Constraints.freeVars cs ∨ k ∈ Subst.freeVars S.subst := by
  simp only [Constraints.unify, Bind.bind, Except.bind] at h_unify
  split at h_unify
  · simp at h_unify
  · rename_i relS h_core
    simp at h_unify; subst h_unify
    exact unifyCore_keys_incl cs S relS h_core

/-- Unification preserves freshness: if all keys of the input substitution and
    all free variables in the constraints are fresh in `Γ`, then all keys
    of the output substitution are also fresh in `Γ`.

    This follows from the structure of `unifyOne`: the only way a new key `id`
    enters the substitution is when `Maps.find? S.subst id = none` and `id`
    is a free type variable from the constraint types. -/
theorem Constraints.unify_allKeysFresh
    {cs : Constraints} {S S' : SubstInfo} {Γ : TContext T.IDMeta}
    (h_unify : Constraints.unify cs S = .ok S')
    (h_keys_fresh : Subst.allKeysFresh S.subst Γ)
    (h_cs_fresh : ∀ tv, tv ∈ Constraints.freeVars cs → TContext.isFresh (T := T) tv Γ)
    (h_vals_fresh : ∀ tv, tv ∈ Subst.freeVars S.subst → TContext.isFresh (T := T) tv Γ) :
    Subst.allKeysFresh S'.subst Γ := by
  intro k hk
  have h_incl := Constraints.unify_keys_incl h_unify k hk
  cases h_incl with
  | inl h => exact h_keys_fresh k h
  | inr h =>
    cases h with
    | inl h => exact h_cs_fresh k h
    | inr h => exact h_vals_fresh k h

/--
All keys in the substitution produced by `resolveAux` are fresh in the input
context. This is because `resolveAux` only adds bindings for type variables
generated by `genTyVar`, which are guaranteed fresh.

Note: the precondition `Subst.allKeysFresh Env.stateSubstInfo.subst Env.context`
is needed because `resolveAux` extends (not replaces) the input substitution.
For the top-level call via `LExpr.resolve`, the input substitution is empty
so the precondition is trivially satisfied.
-/
theorem resolveAux_keys_fresh :
    ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      Subst.allKeysFresh Env.stateSubstInfo.subst Env.context →
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

/-- If `x ∉ xs`, then `xs.removeAll [x] = xs`. -/
private theorem removeAll_not_mem {x : TyIdentifier} {xs : List TyIdentifier}
    (h : x ∉ xs) : xs.removeAll [x] = xs := by
  induction xs with
  | nil => simp [List.removeAll]
  | cons a rest ih =>
    have h_ne : x ≠ a := fun heq => h (heq ▸ List.mem_cons_self)
    have h_beq : (x == a) = false := beq_eq_false_iff_ne.mpr h_ne
    rw [List.cons_removeAll]
    -- [x].contains a = (x == a), and (x == a) = false since x ≠ a
    have h_contains : [x].contains a = false := by
      unfold List.contains List.elem
      rw [BEq.comm]
      simp [h_beq]
    rw [h_contains]
    simp
    exact ih (fun h_mem => h (List.mem_cons_of_mem a h_mem))

/-- Keys of a zipped map are a subset of the first list. -/
private theorem Map.keys_zip_subset {α β : Type} [DecidableEq α]
    (l1 : List α) (l2 : List β) {x : α} (h : x ∈ Map.keys (l1.zip l2)) : x ∈ l1 := by
  induction l1 generalizing l2 with
  | nil => simp [List.zip, Map.keys] at h
  | cons a rest ih =>
    cases l2 with
    | nil => simp [List.zip, Map.keys] at h
    | cons b rest2 =>
      simp [List.zip, Map.keys] at h
      cases h with
      | inl h => subst h; exact List.mem_cons_self
      | inr h => exact List.mem_cons_of_mem a (ih rest2 h)

/--
Helper: repeated `tinst` applications for each bound variable with the
corresponding type yield the same result as a parallel substitution.

If `e` has type `(.forAll vars body)`, then applying `tinst` for each
`(var_i, ty_i)` pair produces `HasType C Γ e (.forAll [] (subst [zip vars tys] body))`,
provided `vars` are distinct (Nodup) and the types `tys` have no free
variables among `vars` (so substitutions don't interfere).
-/
private theorem HasType_tinst_all
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono)
    : ∀ (vars : List TyIdentifier) (body : LMonoTy) (tys : List LMonoTy),
    tys.length = vars.length →
    vars.Nodup →
    (∀ v, v ∈ vars → ∀ t, t ∈ tys → v ∉ LMonoTy.freeVars t) →
    HasType C Γ e (.forAll vars body) →
    HasType C Γ e (.forAll [] (LMonoTy.subst [List.zip vars tys] body)) := by
  intro vars
  induction vars with
  | nil =>
    intro body tys h_len _ _ h_ty
    have h_tys_nil : tys = [] := by
      cases tys with
      | nil => rfl
      | cons _ _ => simp at h_len
    subst h_tys_nil
    -- [].zip [] = [], so subst [[].zip []] body = subst [[]] body = body
    have h_empty : Subst.hasEmptyScopes [List.zip ([] : List TyIdentifier) ([] : List LMonoTy)] = true := by
      simp [List.zip, Subst.hasEmptyScopes, Map.isEmpty]
    rw [LMonoTy.subst_emptyS h_empty]
    exact h_ty
  | cons v rest ih =>
    intro body tys h_len h_nodup h_no_clash h_ty
    -- tys must be t :: rest_tys
    cases tys with
    | nil => simp at h_len
    | cons t rest_tys =>
      simp at h_len
      -- Extract Nodup facts
      have h_v_notin_rest : v ∉ rest := (List.nodup_cons.mp h_nodup).1
      have h_rest_nodup : rest.Nodup := (List.nodup_cons.mp h_nodup).2
      -- Step 1: Apply tinst with v, t to get HasType for (.forAll rest (subst [[(v,t)]] body))
      -- LTy.open v t (.forAll (v :: rest) body) opens the first binder
      have h_inst := HasType.tinst Γ e (.forAll (v :: rest) body)
        (LTy.open v t (.forAll (v :: rest) body)) v t h_ty rfl
      -- Simplify: LTy.open v t (.forAll (v :: rest) body) =
      --   .forAll rest (subst [[(v,t)]] body)
      -- because v ∈ v :: rest and (v :: rest).removeAll [v] = rest (v ∉ rest by Nodup)
      have h_open_eq : LTy.open v t (.forAll (v :: rest) body) =
          .forAll rest (LMonoTy.subst [[(v, t)]] body) := by
        show (if v ∈ v :: rest then
            have S := [(v, t)]; LTy.forAll ((v :: rest).removeAll [v]) (LMonoTy.subst [S] body)
          else LTy.forAll (v :: rest) body) = _
        simp only [List.mem_cons_self, ↓reduceIte]
        congr 1
        -- Need: (v :: rest).removeAll [v] = rest
        rw [List.cons_removeAll]
        -- [v].contains v is true, so else branch: rest.removeAll [v]
        have h_contains_true : [v].contains v = true := by
          unfold List.contains List.elem
          simp [beq_self_eq_true]
        simp [h_contains_true]
        exact removeAll_not_mem h_v_notin_rest
      rw [h_open_eq] at h_inst
      -- h_inst : HasType C Γ e (.forAll rest (subst [[(v, t)]] body))
      -- Step 2: Apply IH
      have h_ih := ih (LMonoTy.subst [[(v, t)]] body) rest_tys h_len h_rest_nodup
        (fun w hw s hs => h_no_clash w (List.mem_cons_of_mem v hw) s (List.mem_cons_of_mem t hs))
        h_inst
      -- h_ih : HasType C Γ e (.forAll [] (subst [zip rest rest_tys] (subst [[(v, t)]] body)))
      -- Step 3: Use subst_cons_single to rewrite
      have h_t_stable : LMonoTy.subst [List.zip rest rest_tys] t = t := by
        apply LMonoTy.subst_no_relevant_keys
        intro x hx h_x_key
        have h_x_in_rest : x ∈ rest := by
          simp [Maps.keys] at h_x_key
          exact Map.keys_zip_subset rest rest_tys h_x_key
        exact h_no_clash x (List.mem_cons_of_mem v h_x_in_rest) t
          List.mem_cons_self hx
      have h_compose := LMonoTy.subst_cons_single v t (List.zip rest rest_tys) body h_t_stable
      rw [h_compose] at h_ih
      -- Now just need zip (v :: rest) (t :: rest_tys) = (v, t) :: zip rest rest_tys
      simp only [List.zip_cons_cons] at h_ih ⊢
      exact h_ih

/--
Helper: `LTy.instantiate` preserves HasType by repeated tinst.
If `e` has type `ty` and `instantiate ty` produces monotype `mty`,
then `e` has type `(.forAll [] mty)`.
For monomorphic types this is immediate; for polymorphic types this
follows from applying `tinst` for each bound variable.
-/
private theorem HasType_LTy_instantiate
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono) (ty : LTy)
    (mty : LMonoTy) (genEnv genEnv' : TGenEnv T.IDMeta)
    (h_ty : HasType C Γ e ty)
    (h_inst : LTy.instantiate ty genEnv = .ok (mty, genEnv'))
    (h_nodup : (LTy.boundVars ty).Nodup)
    (h_bv_known : ∀ v, v ∈ LTy.boundVars ty →
      v ∈ TContext.knownTypeVars genEnv.context) :
    HasType C Γ e (.forAll [] mty) := by
  -- Case analysis on ty
  cases ty with
  | forAll vars body =>
  -- Unfold LTy.instantiate for (.forAll vars body)
  cases vars with
  | nil =>
    -- Monomorphic: LTy.instantiate (.forAll [] body) = .ok (body, genEnv)
    simp [LTy.instantiate] at h_inst
    obtain ⟨h_eq, _⟩ := h_inst; rw [← h_eq]; exact h_ty
  | cons x xs =>
    -- Polymorphic: LTy.instantiate (.forAll (x :: xs) body) generates fresh vars
    simp only [LTy.instantiate, Bind.bind, Except.bind] at h_inst
    split at h_inst
    · simp at h_inst
    · rename_i v1 h_gen
      obtain ⟨freshtvs, genEnv1⟩ := v1
      simp at h_inst h_gen
      obtain ⟨h_eq, _⟩ := h_inst; rw [← h_eq]
      have h_len_gen := TGenEnv.genTyVars_length (x :: xs).length genEnv freshtvs genEnv1 h_gen
      have h_map_len : (List.map LMonoTy.ftvar freshtvs).length = (x :: xs).length := by
        simp [h_len_gen]
      apply HasType_tinst_all C Γ e (x :: xs) body (List.map LMonoTy.ftvar freshtvs)
        h_map_len
      · -- Nodup: from h_nodup, since boundVars (.forAll (x :: xs) body) = x :: xs
        have : LTy.boundVars (.forAll (x :: xs) body) = x :: xs := by simp [LTy.boundVars]
        rw [this] at h_nodup; exact h_nodup
      · -- No clash: bound variables don't appear in fresh type variables
        intro v hv t ht
        simp [List.mem_map] at ht
        obtain ⟨tv, htv_mem, h_tv⟩ := ht
        rw [← h_tv]; simp [LMonoTy.freeVars]
        -- v ∈ (x :: xs) = boundVars ty, so v ∈ knownTypeVars genEnv.context
        have h_v_known : v ∈ TContext.knownTypeVars genEnv.context := by
          apply h_bv_known
          show v ∈ LTy.boundVars (.forAll (x :: xs) body)
          simp [LTy.boundVars]; exact List.mem_cons.mp hv
        -- tv ∈ freshtvs, so tv ∉ knownTypeVars genEnv.context
        have h_tv_not : tv ∉ TContext.knownTypeVars genEnv.context :=
          TGenEnv.genTyVars_not_mem_knownTypeVars _ genEnv freshtvs genEnv1 h_gen tv htv_mem
        -- Therefore v ≠ tv
        exact fun h_eq => h_tv_not (h_eq ▸ h_v_known)
      · exact h_ty

/--
Helper: `LMonoTy.resolveAliases` preserves HasType under the output substitution.
If `e` has type `(.forAll [] mty_in)` and resolving aliases in `mty_in` produces
`(mty_out, Env')`, then `e` has type `(.forAll [] (subst Env'.subst mty_out))`.

The key insight is that alias resolution uses unification to expand type aliases,
and the resulting substitution ensures that the original and resolved types are
equal under `Env'.stateSubstInfo.subst`. For types without aliases (the common case
for types from the context), this is trivially true since resolveAliases is the
identity.
-/
private theorem HasType_resolveAliases
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono) (mty_in : LMonoTy)
    (mty_out : LMonoTy) (Env Env' : TEnv T.IDMeta)
    (h_ty : HasType C Γ e (.forAll [] mty_in))
    (h_ra : LMonoTy.resolveAliases mty_in Env = .ok (mty_out, Env'))
    (h_fresh : Subst.allKeysFresh Env'.stateSubstInfo.subst Γ) :
    HasType C Γ e (.forAll [] (LMonoTy.subst Env'.stateSubstInfo.subst mty_out)) := by
  -- Under the output substitution S = Env'.stateSubstInfo.subst,
  -- the pre-alias type and post-alias type satisfy:
  --   subst S mty_in = subst S mty_out
  -- This follows from the unification soundness within resolveAliases.
  -- Then HasType_subst_fresh_all applied to h_ty with S gives the result.
  sorry

theorem instantiateWithCheck_fvar_HasType
    (C : LContext T) (Γ : TContext T.IDMeta) (x : Identifier T.IDMeta)
    (ty : LTy) (mty : LMonoTy) (Env Env' : TEnv T.IDMeta)
    (m : T.mono.base.Metadata)
    (h_find : Γ.types.find? x = some ty)
    (h_ctx : Env.context = Γ)
    (h_inst : LTy.instantiateWithCheck ty C Env = .ok (mty, Env'))
    (h_nodup : (LTy.boundVars ty).Nodup)
    (h_bv_known : ∀ v, v ∈ LTy.boundVars ty →
      v ∈ TContext.knownTypeVars Env.genEnv.context) :
    HasType C Γ (.fvar m x none)
      (.forAll [] (LMonoTy.subst Env'.stateSubstInfo.subst mty)) := by
  -- Decompose instantiateWithCheck into resolveAliases + known type check
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h_inst
  split at h_inst
  · simp at h_inst  -- resolveAliases failed
  · rename_i v1 h_ra
    obtain ⟨mty_ra, Env_ra⟩ := v1
    split at h_inst
    · -- Known type check passed; extract equalities
      simp [Pure.pure, Except.pure] at h_inst
      obtain ⟨h_mty, h_env⟩ := h_inst
      subst h_mty; subst h_env
      -- Decompose resolveAliases = instantiate + LMonoTy.resolveAliases
      simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
      split at h_ra
      · simp at h_ra
      · rename_i v2 h_inst_inner
        obtain ⟨mty_inst, genEnv'⟩ := v2
        simp at h_ra h_inst_inner
        -- h_inst_inner : ty.instantiate Env.genEnv = .ok (mty_inst, genEnv')
        -- h_ra : LMonoTy.resolveAliases mty_inst {Env with genEnv := genEnv'}
        --          = .ok (mty, Env')
        -- Step 1: tvar gives HasType C Γ (.fvar m x none) ty
        have h_tvar := HasType.tvar (C := C) Γ m x ty h_find
        -- Step 2: tinst chain gives HasType for (.forAll [] mty_inst)
        have h_mono := HasType_LTy_instantiate C Γ (.fvar m x none) ty mty_inst
          Env.genEnv genEnv' h_tvar h_inst_inner h_nodup h_bv_known
        -- Step 3: All substitution keys are fresh in Γ (being proved elsewhere)
        have h_fresh : Subst.allKeysFresh Env_ra.stateSubstInfo.subst Γ := by
          sorry -- Needs: freshness property of genTyVar / resolveAliases
        -- Step 4: resolveAliases preserves HasType under the output substitution
        exact HasType_resolveAliases C Γ _ mty_inst mty_ra
          {Env with genEnv := genEnv'} Env_ra h_mono h_ra h_fresh
    · simp at h_inst  -- Known type check failed

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
    (h : inferFVar C Env x fty = .ok (ty_res, Env'))
    (h_wf : ∀ y ty, Env.context.types.find? y = some ty →
      (LTy.boundVars ty).Nodup ∧
      ∀ v, v ∈ LTy.boundVars ty → v ∈ TContext.knownTypeVars Env.genEnv.context) :
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
          have ⟨h_nd, h_bvk⟩ := h_wf x ty h_find
          exact instantiateWithCheck_fvar_HasType C Env.context x ty mty Env Env1 m
            h_find rfl h_inst h_nd h_bvk
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
private theorem transfer_wf
    {Env Env' : TEnv T.IDMeta}
    (h_wf : ∀ y ty, Env.context.types.find? y = some ty →
      (LTy.boundVars ty).Nodup ∧
      ∀ v, v ∈ LTy.boundVars ty → v ∈ TContext.knownTypeVars Env.genEnv.context)
    (h_ctx : Env'.context = Env.context) :
    ∀ y ty, Env'.context.types.find? y = some ty →
      (LTy.boundVars ty).Nodup ∧
      ∀ v, v ∈ LTy.boundVars ty → v ∈ TContext.knownTypeVars Env'.genEnv.context := by
  intro y ty h_f
  have h_f' : Env.context.types.find? y = some ty := by
    show Env.genEnv.context.types.find? y = some ty
    rw [← (show Env'.genEnv.context = Env.genEnv.context from h_ctx)]
    exact h_f
  obtain ⟨h1, h2⟩ := h_wf y ty h_f'
  exact ⟨h1, fun v hv => by rw [show Env'.genEnv.context = Env.genEnv.context from h_ctx]; exact h2 v hv⟩

theorem resolveAux_HasType :
    ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      (∀ y ty, Env.context.types.find? y = some ty →
        (LTy.boundVars ty).Nodup ∧
        ∀ v, v ∈ LTy.boundVars ty → v ∈ TContext.knownTypeVars Env.genEnv.context) →
      Subst.allKeysFresh Env.stateSubstInfo.subst Env.context →
      Env'.context = Env.context ∧
      HasType C (Env.context) e
        (.forAll [] (LMonoTy.subst Env'.stateSubstInfo.subst et.toLMonoTy)) := by
  intro e
  induction e with
  | const m c =>
    intro et C Env Env' h h_wf h_sf
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
    intro et C Env Env' h h_wf h_sf
    simp [resolveAux, Bind.bind, Except.bind] at h
  | fvar m x fty =>
    -- resolveAux calls inferFVar, which looks up x in context, instantiates
    -- bound type variables, and optionally unifies with the annotation.
    intro et C Env Env' h h_wf h_sf
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_infer
      obtain ⟨ty_res, Env_res⟩ := v1
      simp at h
      obtain ⟨h_et, h_env'⟩ := h
      rw [← h_et, ← h_env']
      simp [toLMonoTy]
      exact inferFVar_HasType C Env x fty ty_res Env_res m h_infer h_wf
  | op m o oty =>
    intro et C Env Env' h h_wf h_sf
    exact ⟨sorry, sorry⟩
  | app m e1 e2 ih1 ih2 =>
    /-
    Theorem: The .app case of resolveAux_HasType.

    Given: resolveAux C Env (.app m e1 e2) = .ok (et, Env')

    Proof:
      1. Decompose the hypothesis into:
         - resolveAux C Env e1 = .ok (e1t, Env1)
         - resolveAux C Env1 e2 = .ok (e2t, Env2)
         - genTyVar Env2 = .ok (fresh_name, Env3)
         - unify [(ty1, arrow [ty2, freshty])] Env3.subst = .ok S
         - et = .app ⟨m, mty⟩ e1t e2t, mty = subst S.subst (ftvar fresh_name)
         - Env' = updateSubst Env3 S' where S'.subst = remove S.subst fresh_name

      2. genTyVar preserves subst and context:
         Env3.subst = Env2.subst, Env3.context = Env2.context

      3. IHs give typing under Env1.subst and Env2.subst respectively.

      4. Context preservation: chain Env' → Env3 → Env2 → Env1 → Env.

      5. Absorption chain: S absorbs Env3.subst = Env2.subst (unify_absorbs),
         Env2 absorbs Env1 (resolveAux_absorbs), Env1 absorbs Env (resolveAux_absorbs).
         By transitivity, S absorbs Env1.subst.

      6. Freshness: allKeysFresh S.subst Env.context, obtained by extending
         allKeysFresh S'.subst Env.context (from resolveAux_keys_fresh) with
         the fact that fresh_name is fresh in Env.context.

      7. Upgrade IHs to S via HasType_subst_upgrade.

      8. From unification: subst S ty1 = tcons "arrow" [subst S ty2, mty].

      9. Apply HasType.tapp.

      10. Show subst S'.subst mty = mty: no key of S appears in freeVars(mty)
          (by subst_keys_not_in_substituted_type), and keys of S' ⊆ keys of S,
          so subst S' mty = mty (by subst_remove_eq_self).
    -/
    intro et C Env Env' h h_wf h_sf
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
        -- Decompose: TEnv.genTyVar Env2
        split at h
        · simp at h
        · rename_i v3 h_genTyVar
          obtain ⟨fresh_name, Env3⟩ := v3
          dsimp at h h_genTyVar
          -- Decompose: Constraints.unify (wrapped in mapError)
          split at h
          · simp at h
          · rename_i v4 h_mapError
            simp at h
            obtain ⟨h_et, h_env'⟩ := h
            -- Extract the underlying unify hypothesis from the mapError wrapper
            have h_unify : Constraints.unify
                [(e1t.toLMonoTy, LMonoTy.tcons "arrow" [e2t.toLMonoTy, .ftvar fresh_name])]
                Env3.stateSubstInfo = .ok v4 := by
              revert h_mapError
              generalize Constraints.unify
                [(toLMonoTy e1t, LMonoTy.tcons "arrow" [toLMonoTy e2t, LMonoTy.ftvar fresh_name])]
                Env3.stateSubstInfo = res
              intro h_me
              match res, h_me with
              | .ok val, h_me => simp at h_me; rw [h_me]
              | .error _, h_me => simp at h_me
            -- genTyVar preserves subst and context
            have h_gen_subst := TEnv.genTyVar_subst Env2 fresh_name Env3 h_genTyVar
            have h_gen_ctx := TEnv.genTyVar_context Env2 fresh_name Env3 h_genTyVar
            have h_gen_fresh := TEnv.genTyVar_isFresh Env2 fresh_name Env3 h_genTyVar
            -- IHs from recursive calls
            have ⟨h_ctx1, h_ty1⟩ := ih1 e1t C Env Env1 h_res1 h_wf h_sf
            have h_sf1 : Subst.allKeysFresh Env1.stateSubstInfo.subst Env1.context := by
              rw [h_ctx1]; exact resolveAux_keys_fresh e1 e1t C Env Env1 h_res1 h_sf
            have ⟨h_ctx2, h_ty2⟩ := ih2 e2t C Env1 Env2 h_res2 (transfer_wf h_wf h_ctx1) h_sf1
            -- Absorption chain: v4 absorbs Env3.subst = Env2.subst
            have h_abs_v4_Env3 := unify_absorbs
              [(e1t.toLMonoTy, LMonoTy.tcons "arrow" [e2t.toLMonoTy, .ftvar fresh_name])]
              Env3.stateSubstInfo v4 h_unify
            rw [h_gen_subst] at h_abs_v4_Env3
            -- Now h_abs_v4_Env3 : absorbs v4.subst Env2.subst
            have h_abs_Env2_Env1 := resolveAux_absorbs e2 e2t C Env1 Env2 h_res2
            have h_abs_Env1_Env := resolveAux_absorbs e1 e1t C Env Env1 h_res1
            have h_abs_v4_Env1 := Subst.absorbs_trans
              Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst v4.subst
              h_abs_Env2_Env1 h_abs_v4_Env3
            -- Freshness of v4.subst keys in Env.context
            -- First get allKeysFresh for S' (the remove'd version) via resolveAux_keys_fresh
            have h_fresh_S' : Subst.allKeysFresh
                (Maps.remove v4.subst fresh_name) Env.context := by
              have h_wf_remove : SubstWF (Maps.remove v4.subst fresh_name) :=
                SubstWF_of_remove fresh_name v4.isWF
              have := resolveAux_keys_fresh (.app m e1 e2)
                (.app ⟨m, LMonoTy.subst v4.subst (.ftvar fresh_name)⟩ e1t e2t) C Env
                (TEnv.updateSubst Env3
                  ⟨Maps.remove v4.subst fresh_name, h_wf_remove⟩) (by
                  simp [resolveAux, Bind.bind, Except.bind, Except.mapError,
                    h_res1, h_res2, h_genTyVar]
                  revert h_mapError
                  generalize Constraints.unify
                    [(toLMonoTy e1t,
                      LMonoTy.tcons "arrow" [toLMonoTy e2t, LMonoTy.ftvar fresh_name])]
                    Env3.stateSubstInfo = res
                  intro h_me
                  match res, h_me with
                  | .ok val, h_me =>
                    simp at h_me ⊢
                    subst h_me
                    exact ⟨rfl, rfl⟩
                  | .error _, h_me => simp at h_me)
                h_sf
              simp [TEnv.updateSubst] at this
              exact this
            -- Extend to allKeysFresh v4.subst Env.context
            have h_fresh_v4 : Subst.allKeysFresh v4.subst Env.context := by
              apply Subst.allKeysFresh_of_allKeysFresh_remove h_fresh_S'
              -- fresh_name is fresh in Env.context
              have : TContext.isFresh fresh_name Env2.context := h_gen_fresh
              rw [h_ctx2, h_ctx1] at this
              exact this
            constructor
            · -- Context preservation
              rw [← h_env']
              simp [TEnv.updateSubst, TEnv.context]
              change Env3.context = Env.context
              rw [h_gen_ctx, h_ctx2, h_ctx1]
            · -- Typing: apply HasType.tapp
              rw [← h_et]; simp [toLMonoTy]
              rw [← h_env']; simp [TEnv.updateSubst]
              -- The result type is mty = subst v4.subst (ftvar fresh_name).
              -- We need: subst (remove v4.subst fresh_name) mty = mty.
              -- This follows because no key of v4.subst is in freeVars(mty)
              -- (by subst_keys_not_in_substituted_type), and keys of remove ⊆ keys of v4.
              have h_no_keys_in_mty :=
                LMonoTy.subst_keys_not_in_substituted_type (S := v4.subst)
                  (ty := LMonoTy.ftvar fresh_name) v4.isWF
              rw [LMonoTy.subst_remove_eq_self v4.subst fresh_name
                (LMonoTy.subst v4.subst (LMonoTy.ftvar fresh_name)) h_no_keys_in_mty]
              -- Now goal: HasType C Env.context (.app m e1 e2)
              --   (.forAll [] (LMonoTy.subst v4.subst (.ftvar fresh_name)))
              -- Unification makes: subst v4 ty1 = tcons "arrow" [subst v4 ty2, subst v4 freshty]
              have h_eq := unify_makes_equal
                e1t.toLMonoTy
                (LMonoTy.tcons "arrow" [e2t.toLMonoTy, .ftvar fresh_name])
                Env3.stateSubstInfo v4 h_unify
              -- Upgrade IH1: from Env1.subst to v4.subst
              have h_ty1_up := HasType_subst_upgrade C Env.context e1
                e1t.toLMonoTy Env1.stateSubstInfo.subst v4.subst
                h_ty1 h_abs_v4_Env1 h_fresh_v4 v4.isWF
              -- Upgrade IH2: from Env2.subst to v4.subst
              rw [h_ctx1] at h_ty2
              have h_ty2_up := HasType_subst_upgrade C Env.context e2
                e2t.toLMonoTy Env2.stateSubstInfo.subst v4.subst
                h_ty2 h_abs_v4_Env3 h_fresh_v4 v4.isWF
              -- Rewrite h_ty1_up using unification equality
              -- First, distribute subst over tcons on the RHS of h_eq
              have h_eq_dist : LMonoTy.subst v4.subst e1t.toLMonoTy =
                  LMonoTy.tcons "arrow"
                    [LMonoTy.subst v4.subst e2t.toLMonoTy,
                     LMonoTy.subst v4.subst (.ftvar fresh_name)] := by
                rw [h_eq, LMonoTy.subst_tcons]
                congr 1
                rw [LMonoTys.subst_eq_substLogic]
                by_cases hS : Subst.hasEmptyScopes v4.subst
                · simp [LMonoTys.substLogic, hS, LMonoTy.subst_emptyS hS]
                · have hS' : v4.subst.hasEmptyScopes = false := by
                    cases h_dec : v4.subst.hasEmptyScopes <;> simp_all
                  simp only [LMonoTys.substLogic, hS', Bool.false_eq_true, ↓reduceIte]
              rw [h_eq_dist] at h_ty1_up
              -- Now h_ty1_up : HasType C Γ e1
              --   (.forAll [] (.tcons "arrow" [subst v4 ty2, subst v4 (ftvar fresh_name)]))
              -- Apply HasType.tapp
              exact HasType.tapp Env.context m e1 e2
                (.forAll [] (LMonoTy.subst v4.subst (.ftvar fresh_name)))
                (.forAll [] (LMonoTy.subst v4.subst e2t.toLMonoTy))
                (by simp [LTy.isMonoType, LTy.boundVars])
                (by simp [LTy.isMonoType, LTy.boundVars])
                (by simp [LTy.toMonoType]; exact h_ty1_up)
                h_ty2_up
  | abs m bty e ih =>
    intro et C Env Env' h h_wf h_sf
    exact ⟨sorry, sorry⟩
  | quant m qk bty tr e ih_tr ih_e =>
    intro et C Env Env' h h_wf h_sf
    exact ⟨sorry, sorry⟩
  | ite m c t e ih_c ih_t ih_e =>
    -- resolveAux recurses on c, t, e, then unifies [(cty, bool), (tty, ety)].
    -- Result type is tty (the then-branch type), and the HasType rule is `tif`.
    intro et C Env Env' h h_wf h_sf
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
            have ⟨h_ctx1, h_ty_c⟩ := ih_c ct C Env Env1 h_res_c h_wf h_sf
            have h_sf1 : Subst.allKeysFresh Env1.stateSubstInfo.subst Env1.context := by
              rw [h_ctx1]; exact resolveAux_keys_fresh c ct C Env Env1 h_res_c h_sf
            have ⟨h_ctx2, h_ty_t⟩ := ih_t tht C Env1 Env2 h_res_t (transfer_wf h_wf h_ctx1) h_sf1
            have h_sf2 : Subst.allKeysFresh Env2.stateSubstInfo.subst Env2.context := by
              rw [h_ctx2]; exact resolveAux_keys_fresh t tht C Env1 Env2 h_res_t h_sf1
            have ⟨h_ctx3, h_ty_e⟩ := ih_e elt C Env2 Env3 h_res_e
              (transfer_wf (transfer_wf h_wf h_ctx1) h_ctx2) h_sf2
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
                h_sf
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
    intro et C Env Env' h h_wf h_sf
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
          have ⟨h_ctx1, h_ty1⟩ := ih1 e1t C Env Env1 h_res1 h_wf h_sf
          have h_sf1 : Subst.allKeysFresh Env1.stateSubstInfo.subst Env1.context := by
            rw [h_ctx1]; exact resolveAux_keys_fresh e1 e1t C Env Env1 h_res1 h_sf
          have ⟨h_ctx2, h_ty2⟩ := ih2 e2t C Env1 Env2 h_res2 (transfer_wf h_wf h_ctx1) h_sf1
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
              h_sf
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
      (∀ y ty, Env.context.types.find? y = some ty →
        (LTy.boundVars ty).Nodup ∧
        ∀ v, v ∈ LTy.boundVars ty → v ∈ TContext.knownTypeVars Env.genEnv.context) →
      Subst.allKeysFresh Env.stateSubstInfo.subst Env.context →
      HasType C (Env.context) e (.forAll [] e_typed.toLMonoTy) := by
  intro e e_typed C Env _env h h_wf h_sf
  -- Decompose resolve into resolveAux + applySubstT
  simp only [LExpr.resolve, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i v h_aux
    obtain ⟨et, Env'⟩ := v
    simp at h
    obtain ⟨h_typed, h_env'⟩ := h
    have ⟨_h_ctx, h_hastype⟩ := resolveAux_HasType e et C Env Env' h_aux h_wf h_sf
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
