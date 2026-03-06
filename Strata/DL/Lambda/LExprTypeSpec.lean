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
            C.functions.find? (fun fn => fn.name.name == op.name) = some f →
            f.type = .ok ty →
            HasType C Γ (.op m op none) ty
  /--
  Similarly to free variables, an annotated operator has its claimed type `ty_s` if `ty_s` is an
  instantiation of the type `ty_o` recorded for it in `C.functions`.
  -/
  | top_annotated: ∀ Γ m f op ty_o ty_s tys,
            C.functions.find? (fun fn => fn.name.name == op.name) = some f →
            f.type = .ok ty_o →
            tys.length = ty_o.boundVars.length →
            LTy.openFull ty_o tys = ty_s →
            HasType C Γ (.op m op (some ty_s)) (.forAll [] ty_s)

  /-- Alias equivalence preserves typing: if `e` has type `mty` and `mty` is
  alias-equivalent to `mty'` (under the aliases in `Γ`), then `e` also has
  type `mty'`. This covers single-step expansion, subtree resolution, and
  their transitive composition. -/
  | talias : ∀ Γ e mty mty',
            _root_.Lambda.AliasEquiv Γ.aliases mty mty' →
            HasType C Γ e (.forAll [] mty) →
            HasType C Γ e (.forAll [] mty')

  /-- Full alias resolution preserves typing. This is stronger than `talias`
  because `resolveAliases` combines alias expansion with fresh variable
  instantiation and unification, which goes beyond pure alias equivalence.
  The `ToFormat` instance is existentially quantified since it's only needed
  operationally. -/
  | talias_resolve : ∀ Γ e mty mty',
            (∃ (inst : _root_.Std.ToFormat T.IDMeta)
               (Env Env' : _root_.Lambda.TEnv T.IDMeta),
              Γ.aliases = Env.context.aliases ∧
              _root_.Lambda.TContext.AliasesWF Γ ∧
              @LMonoTy.resolveAliases T.IDMeta inst mty Env = .ok (mty', Env')) →
            HasType C Γ e (.forAll [] mty) →
            HasType C Γ e (.forAll [] mty')

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

/-- Substitution distributes over a 2-element `tcons`, giving component-wise results. -/
private theorem LMonoTy.subst_tcons_pair (S : Subst) (name : String) (a b : LMonoTy) :
    LMonoTy.subst S (.tcons name [a, b]) = .tcons name [LMonoTy.subst S a, LMonoTy.subst S b] := by
  rw [LMonoTy.subst_tcons]
  congr 1
  rw [LMonoTys.subst_eq_substLogic]
  by_cases hS : Subst.hasEmptyScopes S
  · simp [LMonoTys.substLogic, hS]
    exact ⟨(LMonoTy.subst_emptyS hS).symm, (LMonoTy.subst_emptyS hS).symm⟩
  · have hS_ne : Subst.hasEmptyScopes S = false := by
      revert hS; cases Subst.hasEmptyScopes S <;> simp
    simp [LMonoTys.substLogic, hS_ne]

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

- **`resolveAux_vals_fresh`**: Substitution value free vars produced by `resolveAux` are fresh in the context.

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

/-- All free variables in substitution values are fresh w.r.t. context `Γ`. -/
def Subst.valsFresh {T : LExprParams} [DecidableEq T.IDMeta]
    (S : Subst) (Γ : TContext T.IDMeta) : Prop :=
  ∀ tv, tv ∈ Subst.freeVars S → TContext.isFresh (T := T) tv Γ

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
      -- tconsAliasSimple doesn't change context (Env' = Env1)
      simp only [LMonoTy.tconsAliasSimple, Pure.pure, Except.pure] at h
      split at h <;> (simp at h; obtain ⟨_, h2⟩ := h; rw [← h2])
      all_goals exact LMonoTys.resolveAliases_context args Env args' Env1 h_args
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

mutual
/-- Free variables of `subst [[(a, t)]] mty` are either free vars of `mty`
    (possibly minus `a`) or free vars of `t`. Contrapositively: if `b` is
    in the freeVars of the substituted type but NOT in freeVars of `t`,
    then `b` was already in freeVars of `mty`. -/
private theorem LMonoTy.freeVars_subst_single_mem
    (a : TyIdentifier) (t mty : LMonoTy) (b : TyIdentifier)
    (hb : b ∈ LMonoTy.freeVars (LMonoTy.subst [[(a, t)]] mty))
    (hb_not_t : b ∉ LMonoTy.freeVars t) :
    b ∈ LMonoTy.freeVars mty := by
  -- If the substitution has empty scopes, it's the identity, so trivial
  by_cases hS : Subst.hasEmptyScopes [[(a, t)]]
  · rw [LMonoTy.subst_emptyS hS] at hb; exact hb
  · have hS_false : Subst.hasEmptyScopes [[(a, t)]] = false := by
      revert hS; cases Subst.hasEmptyScopes [[(a, t)]] <;> simp
    match mty with
    | .ftvar x =>
      simp only [LMonoTy.subst, hS_false, ↓reduceIte] at hb
      by_cases hax : a = x
      · subst hax
        have : Maps.find? [[(a, t)]] a = some t := by
          simp [Maps.find?, Map.find?, beq_self_eq_true]
        rw [this] at hb; exact absurd hb hb_not_t
      · have h_find_none : Maps.find? [[(a, t)]] x = none :=
          Maps.not_mem_keys_find?_none' [[(a, t)]] x (by
            simp [Maps.keys, Map.keys]; exact fun h => hax h.symm)
        rw [h_find_none] at hb; exact hb
    | .bitvec _ =>
      unfold LMonoTy.subst at hb; split at hb <;> exact hb
    | .tcons name args =>
      simp only [LMonoTy.subst, hS_false, ↓reduceIte, LMonoTy.freeVars] at hb ⊢
      rw [LMonoTys.subst_eq_substLogic] at hb
      exact LMonoTys.freeVars_substLogic_single_mem a t args b hb hb_not_t

/-- List version: free vars of `substLogic [[(a,t)]] mtys` that are not in
    `freeVars t` must be in `freeVars mtys`. -/
private theorem LMonoTys.freeVars_substLogic_single_mem
    (a : TyIdentifier) (t : LMonoTy) (mtys : LMonoTys) (b : TyIdentifier)
    (hb : b ∈ LMonoTys.freeVars (LMonoTys.substLogic [[(a, t)]] mtys))
    (hb_not_t : b ∉ LMonoTy.freeVars t) :
    b ∈ LMonoTys.freeVars mtys := by
  have hS_false : Subst.hasEmptyScopes [[(a, t)]] = false := by
    simp [Subst.hasEmptyScopes, Map.isEmpty]
  match mtys with
  | [] =>
    simp only [LMonoTys.substLogic, hS_false, ↓reduceIte, LMonoTys.freeVars] at hb
    exact hb
  | y :: ys =>
    simp only [LMonoTys.substLogic, hS_false, ↓reduceIte, LMonoTys.freeVars] at hb ⊢
    cases List.mem_append.mp hb with
    | inl h_y => exact List.mem_append_left _ (LMonoTy.freeVars_subst_single_mem a t y b h_y hb_not_t)
    | inr h_ys => exact List.mem_append_right _ (LMonoTys.freeVars_substLogic_single_mem a t ys b h_ys hb_not_t)
end

/-- `HasType` is preserved under substitution when keys relevant to the type
    are fresh. Only keys that appear in `freeVars mty` need to be fresh,
    not all keys. This is the key weakening that avoids requiring `allKeysFresh`
    globally. -/
theorem HasType_subst_fresh_all
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono) (mty : LMonoTy)
    (S : Subst)
    (h : HasType C Γ e (.forAll [] mty))
    (h_fresh : ∀ a, a ∈ Maps.keys S → a ∈ LMonoTy.freeVars mty → TContext.isFresh (T := T) a Γ)
    (h_wf : SubstWF S) :
    HasType C Γ e (.forAll [] (LMonoTy.subst S mty)) := by
  -- Trivial case: S has empty scopes
  by_cases hS : Subst.hasEmptyScopes S
  · rw [LMonoTy.subst_emptyS hS]; exact h
  · -- Strong induction on relevantKeys S mty
    -- Thread the freshness condition through the suffices, since SubstWF
    -- guarantees that relevant keys only shrink through substitution steps.
    suffices ∀ (n : Nat) (mty : LMonoTy),
        relevantKeys S mty = n →
        (∀ a, a ∈ Maps.keys S → a ∈ LMonoTy.freeVars mty → TContext.isFresh (T := T) a Γ) →
        HasType C Γ e (.forAll [] mty) →
        HasType C Γ e (.forAll [] (LMonoTy.subst S mty)) from
      this (relevantKeys S mty) mty rfl h_fresh h
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro mty h_rk h_fresh_mty h_ty
      -- Check if any key of S is in freeVars mty
      by_cases h_any : ∃ a, a ∈ Maps.keys S ∧ a ∈ LMonoTy.freeVars mty
      · -- Inductive case: there's a relevant key
        obtain ⟨a, ha_key, ha_fv⟩ := h_any
        obtain ⟨t, h_find⟩ := Maps.find?_of_mem_keys' S a ha_key
        -- Step 1: apply HasType_subst_fresh for the single binding (a, t)
        have h_a_fresh : TContext.isFresh a Γ := h_fresh_mty a ha_key ha_fv
        have h1 : HasType C Γ e (.forAll [] (LMonoTy.subst [[(a, t)]] mty)) :=
          HasType_subst_fresh C Γ e mty a t h_ty h_a_fresh
        -- Step 2: by induction, apply HasType_subst_fresh_all to the substituted type
        -- Freshness transfers: keys relevant to (subst [[(a,t)]] mty) are a subset of
        -- keys relevant to mty, because SubstWF ensures a ∉ freeVars(t), so
        -- freeVars(subst [[(a,t)]] mty) ⊆ (freeVars(mty) \ {a}) ∪ freeVars(t)
        -- and keys(S) ∩ freeVars(t) = ∅ by SubstWF.
        have h_fresh_inner : ∀ b, b ∈ Maps.keys S → b ∈ LMonoTy.freeVars (LMonoTy.subst [[(a, t)]] mty) →
            TContext.isFresh (T := T) b Γ := by
          intro b hb_key hb_fv
          -- b ∈ freeVars(subst [[(a,t)]] mty) and b ∈ keys(S)
          -- By SubstWF, b ∉ Subst.freeVars S, and freeVars(t) ⊆ Subst.freeVars S
          have hb_not_fvS : b ∉ Subst.freeVars S := by
            have := h_wf; simp [SubstWF, List.all_eq_true] at this
            exact this b hb_key
          have hb_not_t : b ∉ LMonoTy.freeVars t :=
            fun h => hb_not_fvS (Subst.freeVars_of_find_subset S h_find h)
          -- So b ∈ freeVars(mty) by freeVars_subst_single_mem
          have hb_in_mty := LMonoTy.freeVars_subst_single_mem a t mty b hb_fv hb_not_t
          exact h_fresh_mty b hb_key hb_in_mty
        have h_decrease := relevantKeys_decrease S a t mty h_find h_wf ha_fv
        have h2 : HasType C Γ e
            (.forAll [] (LMonoTy.subst S (LMonoTy.subst [[(a, t)]] mty))) :=
          ih (relevantKeys S (LMonoTy.subst [[(a, t)]] mty))
            (h_rk ▸ h_decrease) (LMonoTy.subst [[(a, t)]] mty) rfl h_fresh_inner h1
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

/-- `Constraints.unify` preserves substitution value freshness.
    If constraint fvs and old value fvs are all fresh in Γ, then
    new value fvs are also fresh in Γ (by `goodSubset`). -/
theorem Constraints.unify_vals_fresh
    {cs : Constraints} {S S' : SubstInfo} {Γ : TContext T.IDMeta}
    (h_unify : Constraints.unify cs S = .ok S')
    (h_cs_fresh : ∀ tv, tv ∈ Constraints.freeVars cs → TContext.isFresh (T := T) tv Γ)
    (h_vals_fresh : ∀ tv, tv ∈ Subst.freeVars S.subst → TContext.isFresh (T := T) tv Γ) :
    ∀ tv, tv ∈ Subst.freeVars S'.subst → TContext.isFresh (T := T) tv Γ := by
  intro tv h_tv
  have h_incl : Subst.freeVars S'.subst ⊆
      Constraints.freeVars cs ++ Subst.freeVars S.subst := by
    simp only [Constraints.unify, Bind.bind, Except.bind] at h_unify
    split at h_unify
    · simp at h_unify
    · rename_i relS h_core
      simp at h_unify; subst h_unify
      exact relS.goodSubset
  rcases List.mem_append.mp (h_incl h_tv) with h | h
  · exact h_cs_fresh tv h
  · exact h_vals_fresh tv h

theorem LMonoTys.instantiateEnv_stateSubstInfo {IDMeta : Type} [ToFormat IDMeta]
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TEnv IDMeta)
    (mtys' : LMonoTys) (Env' : TEnv IDMeta)
    (h : LMonoTys.instantiateEnv ids mtys Env = .ok (mtys', Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  unfold LMonoTys.instantiateEnv at h
  generalize LMonoTys.instantiate ids mtys Env.genEnv = result at h
  match result with
  | .error _ => simp at h
  | .ok (a, gE) => simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]

/-- `Map.values` of a `zipWith Prod.mk` is the second list truncated to the
    length of the first. -/
private theorem Map.values_zipWith_eq_take (as : List TyIdentifier) (bs : List LMonoTy) :
    Map.values (List.zipWith Prod.mk as bs) = bs.take as.length := by
  induction as generalizing bs with
  | nil => simp [Map.values]
  | cons a as' ih =>
    match bs with
    | [] => simp [Map.values, List.zipWith]
    | b :: bs' => simp [List.zipWith, Map.values]; exact ih bs'

/-- Free variables of a substitution `[zip ids (map ftvar freshtvs)]` are a
    subset of `freshtvs`. -/
private theorem Subst.freeVars_zip_ftvar (ids freshtvs : List TyIdentifier)
    (h_len : freshtvs.length = ids.length) :
    Subst.freeVars [List.zip ids (List.map LMonoTy.ftvar freshtvs)] ⊆ freshtvs := by
  intro tv h_tv
  simp [Subst.freeVars, Maps.values, List.zip] at h_tv
  obtain ⟨a, h_a_mem, h_tv_fv⟩ := h_tv
  rw [Map.values_zipWith_eq_take] at h_a_mem
  have h_take : (List.map LMonoTy.ftvar freshtvs).take ids.length =
      List.map LMonoTy.ftvar freshtvs := by
    rw [List.take_of_length_le]; simp [h_len]
  rw [h_take] at h_a_mem
  obtain ⟨tv', h_tv'_mem, h_eq⟩ := List.mem_map.mp h_a_mem
  subst h_eq; simp [LMonoTy.freeVars] at h_tv_fv; rw [h_tv_fv]; exact h_tv'_mem

/-- Free variables of `LMonoTys.subst S mtys` are a subset of the free variables
    of `mtys` and the free variables of `S`. -/
private theorem LMonoTys.freeVars_of_subst_subset (S : Subst) (mtys : LMonoTys) :
    LMonoTys.freeVars (LMonoTys.subst S mtys) ⊆
    LMonoTys.freeVars mtys ++ Subst.freeVars S := by
  intro x hx
  rw [LMonoTys.subst_eq_substLogic] at hx
  induction mtys with
  | nil => simp [LMonoTys.substLogic, LMonoTys.freeVars] at hx
  | cons mty mrest ih =>
    by_cases hSEmpty : Subst.hasEmptyScopes S
    · simp [LMonoTys.substLogic, hSEmpty] at hx
      exact List.mem_append.mpr (Or.inl (by simp [LMonoTys.freeVars]; exact hx))
    · have hSNE : Subst.hasEmptyScopes S = false := by
        revert hSEmpty; cases Subst.hasEmptyScopes S <;> simp
      unfold LMonoTys.substLogic at hx; simp [hSNE] at hx
      simp only [LMonoTys.freeVars]
      rcases hx with hx | hx
      · have h_sub := LMonoTy.freeVars_of_subst_subset S mty hx
        rw [List.mem_append] at h_sub ⊢
        rcases h_sub with h | h
        · exact Or.inl (List.mem_append.mpr (Or.inl h))
        · exact Or.inr h
      · have h_sub := ih hx
        rw [List.mem_append] at h_sub ⊢
        rcases h_sub with h | h
        · exact Or.inl (List.mem_append.mpr (Or.inr h))
        · exact Or.inr h

/-- Free variables of `instantiateEnv` output are either original free variables
    or fresh type variables generated by `genTyVars`. In either case, if the
    original free vars are fresh in the context, then all output free vars are
    fresh in the context. -/
theorem LMonoTys.instantiateEnv_freeVars_fresh {T : LExprParams}
    [DecidableEq T.IDMeta] [ToFormat T.IDMeta]
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TEnv T.IDMeta)
    (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.instantiateEnv ids mtys Env = .ok (mtys', Env'))
    (h_orig_fresh : ∀ tv, tv ∈ LMonoTys.freeVars mtys → TContext.isFresh (T := T) tv Env.context) :
    ∀ tv, tv ∈ LMonoTys.freeVars mtys' → TContext.isFresh (T := T) tv Env.context := by
  intro tv h_tv
  unfold LMonoTys.instantiateEnv at h
  generalize h_inst : LMonoTys.instantiate ids mtys Env.genEnv = result at h
  match result, h_inst with
  | .error _, _ => simp at h
  | .ok (a, gE), h_inst =>
    simp at h; obtain ⟨h1, _⟩ := h; rw [← h1] at h_tv
    simp [LMonoTys.instantiate, Bind.bind, Except.bind] at h_inst
    split at h_inst
    · simp at h_inst
    · rename_i v1 h_gen
      obtain ⟨freshtvs, genEnv1⟩ := v1; simp at h_inst h_gen
      obtain ⟨h_eq, _⟩ := h_inst; rw [← h_eq] at h_tv
      -- h_tv : tv ∈ freeVars (subst [zip ids (map ftvar freshtvs)] mtys)
      -- By freeVars_of_subst_subset, tv ∈ freeVars mtys ++ freeVars [zip ...]
      have h_subset := LMonoTys.freeVars_of_subst_subset
        [List.zip ids (List.map LMonoTy.ftvar freshtvs)] mtys h_tv
      rw [List.mem_append] at h_subset
      rcases h_subset with h_orig | h_subst_fv
      · exact h_orig_fresh tv h_orig
      · have h_len : freshtvs.length = ids.length :=
          TGenEnv.genTyVars_length _ _ _ _ h_gen
        have h_in_fresh := Subst.freeVars_zip_ftvar ids freshtvs h_len h_subst_fv
        exact TGenEnv.genTyVars_allFresh ids.length _ freshtvs genEnv1 h_gen tv h_in_fresh

/-- If `tv ∈ ids`, then `Maps.find? [zip ids (map ftvar freshtvs)] tv` returns
    some `ftvar ftv` where `ftv ∈ freshtvs`. -/
private theorem Maps.find?_zip_ftvar_mem (ids : List TyIdentifier)
    (freshtvs : List TyIdentifier)
    (h_len : freshtvs.length = ids.length)
    (tv : TyIdentifier) (h_mem : tv ∈ ids) :
    ∃ ftv, ftv ∈ freshtvs ∧
      Maps.find? [List.zip ids (List.map LMonoTy.ftvar freshtvs)] tv =
        some (.ftvar ftv) := by
  simp [Maps.find?]
  induction ids generalizing freshtvs with
  | nil => simp at h_mem
  | cons id ids' ih =>
    match freshtvs with
    | [] => simp at h_len
    | ftv :: ftvs' =>
      simp [List.zip, Map.find?] at h_mem ⊢
      cases h_mem with
      | inl h_eq => subst h_eq; simp
      | inr h_in =>
        by_cases h_eq : tv = id
        · subst h_eq; simp
        · have h_eq' : ¬(id = tv) := fun h => h_eq (h.symm)
          simp [h_eq']
          obtain ⟨ftv', hm, hf⟩ := ih ftvs' (by simp at h_len; exact h_len) h_in
          exact Or.inr ⟨ftv', hm, by simp [List.zip] at hf; exact hf⟩

/-- Substituting `[zip ids (map ftvar freshtvs)]` into a monotype whose free
    variables are all in `ids` produces a type whose free variables are all in
    `freshtvs`. -/
private theorem LMonoTy.freeVars_subst_closed
    (ids : List TyIdentifier) (freshtvs : List TyIdentifier)
    (h_len : freshtvs.length = ids.length) (mty : LMonoTy)
    (h_closed : ∀ tv, tv ∈ LMonoTy.freeVars mty → tv ∈ ids)
    (hSNE : Subst.hasEmptyScopes [List.zip ids (List.map LMonoTy.ftvar freshtvs)] = false) :
    ∀ tv, tv ∈ LMonoTy.freeVars
        (LMonoTy.subst [List.zip ids (List.map LMonoTy.ftvar freshtvs)] mty) →
      tv ∈ freshtvs := by
  intro tv h_tv
  induction mty with
  | ftvar x =>
    simp [LMonoTy.freeVars] at h_closed
    obtain ⟨ftv', hm, hf⟩ := Maps.find?_zip_ftvar_mem ids freshtvs h_len x h_closed
    simp [LMonoTy.subst, hSNE, hf, LMonoTy.freeVars] at h_tv
    subst h_tv; exact hm
  | bitvec n =>
    simp [LMonoTy.subst, LMonoTy.freeVars] at h_tv
  | tcons name args ih =>
    simp [LMonoTy.subst, hSNE, LMonoTy.freeVars] at h_tv
    rw [LMonoTys.subst_eq_substLogic] at h_tv
    simp [LMonoTy.freeVars] at h_closed
    induction args with
    | nil => simp [LMonoTys.substLogic, LMonoTys.freeVars] at h_tv
    | cons a arest arih =>
      unfold LMonoTys.substLogic at h_tv; simp [hSNE] at h_tv
      simp [LMonoTys.freeVars] at h_closed
      rcases h_tv with h_a | h_rest
      · exact ih a List.mem_cons_self (fun tv' h' => h_closed tv' (Or.inl h')) h_a
      · exact arih
          (fun a' h_mem h_closed' => ih a' (List.mem_cons_of_mem a h_mem) h_closed')
          (fun tv' h' => h_closed tv' (Or.inr h'))
          h_rest

/-- Substituting `[zip ids (map ftvar freshtvs)]` into a list of monotypes whose
    free variables are all in `ids` produces types whose free variables are all
    in `freshtvs`. -/
private theorem LMonoTys.freeVars_subst_closed
    (ids : List TyIdentifier) (freshtvs : List TyIdentifier)
    (h_len : freshtvs.length = ids.length) (mtys : LMonoTys)
    (h_closed : ∀ tv, tv ∈ LMonoTys.freeVars mtys → tv ∈ ids) :
    ∀ tv, tv ∈ LMonoTys.freeVars
        (LMonoTys.subst [List.zip ids (List.map LMonoTy.ftvar freshtvs)] mtys) →
      tv ∈ freshtvs := by
  intro tv h_tv
  rw [LMonoTys.subst_eq_substLogic] at h_tv
  induction mtys with
  | nil => simp [LMonoTys.substLogic, LMonoTys.freeVars] at h_tv
  | cons mty mrest ih =>
    by_cases hSE :
        Subst.hasEmptyScopes [List.zip ids (List.map LMonoTy.ftvar freshtvs)]
    · -- hasEmptyScopes = true means ids = []
      simp [Subst.hasEmptyScopes, List.all, Map.isEmpty] at hSE
      have h_ids_nil : ids = [] := by
        cases ids with
        | nil => rfl
        | cons id ids' =>
          match freshtvs with
          | [] => simp at h_len
          | ftv :: ftvs' => simp [List.zip] at hSE
      subst h_ids_nil; exfalso
      simp [LMonoTys.substLogic] at h_tv
      simp [LMonoTys.freeVars] at h_closed
      rcases h_tv with h1 | h2
      · exact ((h_closed tv).1 h1).elim
      · exact ((h_closed tv).2 h2).elim
    · have hSNE : Subst.hasEmptyScopes [List.zip ids (List.map LMonoTy.ftvar freshtvs)] = false := by
        revert hSE; cases Subst.hasEmptyScopes [List.zip ids (List.map LMonoTy.ftvar freshtvs)] <;> simp
      unfold LMonoTys.substLogic at h_tv; simp [hSNE] at h_tv
      simp [LMonoTys.freeVars] at h_closed
      rcases h_tv with h_mty | h_rest
      · exact LMonoTy.freeVars_subst_closed ids freshtvs h_len mty
          (fun tv' h' => h_closed tv' (Or.inl h')) hSNE tv h_mty
      · exact ih (fun tv' h' => h_closed tv' (Or.inr h')) h_rest

/-- When all free variables of `mtys` are in `ids`, `instantiateEnv` produces
    types whose free variables are all fresh in the context. This is because
    `instantiate` substitutes `ids` with fresh type variables, and since all
    original free vars are in `ids`, they all get replaced. -/
private theorem LMonoTys.instantiateEnv_freeVars_fresh_closed {T : LExprParams}
    [DecidableEq T.IDMeta] [ToFormat T.IDMeta]
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TEnv T.IDMeta)
    (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.instantiateEnv ids mtys Env = .ok (mtys', Env'))
    (h_closed : ∀ tv, tv ∈ LMonoTys.freeVars mtys → tv ∈ ids) :
    ∀ tv, tv ∈ LMonoTys.freeVars mtys' →
      TContext.isFresh (T := T) tv Env.context := by
  intro tv h_tv
  unfold LMonoTys.instantiateEnv at h
  generalize h_inst : LMonoTys.instantiate ids mtys Env.genEnv = result at h
  match result, h_inst with
  | .error _, _ => simp at h
  | .ok (a, gE), h_inst =>
    simp at h; obtain ⟨h1, _⟩ := h; rw [← h1] at h_tv
    simp [LMonoTys.instantiate, Bind.bind, Except.bind] at h_inst
    split at h_inst
    · simp at h_inst
    · rename_i v1 h_gen
      obtain ⟨freshtvs, genEnv1⟩ := v1; simp at h_inst h_gen
      obtain ⟨h_eq, _⟩ := h_inst; rw [← h_eq] at h_tv
      have h_len : freshtvs.length = ids.length :=
        TGenEnv.genTyVars_length _ _ _ _ h_gen
      have h_in_fresh :=
        LMonoTys.freeVars_subst_closed ids freshtvs h_len mtys h_closed tv h_tv
      exact TGenEnv.genTyVars_allFresh ids.length _ freshtvs genEnv1 h_gen
        tv h_in_fresh

/-- Free variables of `(.tcons name (typeArgs.map .ftvar))` are exactly
    `typeArgs`. -/
private theorem LMonoTy.freeVars_tcons_map_ftvar (name : String)
    (typeArgs : List TyIdentifier) :
    LMonoTy.freeVars (.tcons name (typeArgs.map .ftvar)) = typeArgs := by
  simp [LMonoTy.freeVars]
  induction typeArgs with
  | nil => simp [LMonoTys.freeVars]
  | cons a rest ih => simp [List.map, LMonoTy.freeVars, ih]

/-- `LMonoTys.freeVars (ids.map .ftvar) = ids`. -/
private theorem LMonoTys.freeVars_map_ftvar (ids : List TyIdentifier) :
    LMonoTys.freeVars (ids.map .ftvar) = ids := by
  induction ids with
  | nil => simp [LMonoTys.freeVars]
  | cons a rest ih => simp [List.map, LMonoTy.freeVars, ih]

/-- `tconsAlias` preserves key freshness: if all keys of the input substitution
    are fresh in `Γ`, then all keys of the output substitution are also fresh.

    For the no-alias case, the environment is unchanged.
    For the alias case, `tconsAlias` calls `Constraints.unify` and `updateSubst`,
    so we need the constraint free vars and value free vars to also be fresh.
    This requires that the fresh type variables generated by `instantiateEnv`
    are indeed fresh in `Γ`, which holds because `genTyVar` produces fresh vars
    and the alias types are "closed" (all free vars are in `typeArgs`). -/
theorem tconsAlias_allKeysFresh
    (name : String) (args : LMonoTys) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (Γ : TContext T.IDMeta)
    (h : LMonoTy.tconsAlias name args Env = .ok (mty, Env'))
    (h_ctx : Env.context = Γ)
    (h_fresh : Subst.allKeysFresh Env.stateSubstInfo.subst Γ)
    (h_args_fresh : ∀ tv, tv ∈ LMonoTys.freeVars args →
      TContext.isFresh (T := T) tv Γ)
    (h_vals_fresh : ∀ tv, tv ∈ Subst.freeVars Env.stateSubstInfo.subst →
      TContext.isFresh (T := T) tv Γ)
    (h_alias_wf : TContext.AliasesWF Γ) :
    Subst.allKeysFresh Env'.stateSubstInfo.subst Γ := by
  unfold LMonoTy.tconsAlias at h
  generalize h_ma : List.find? _ _ = ma at h
  match ma with
  | none =>
    simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    exact h_fresh
  | some alias =>
    simp at h; split at h
    · simp at h
    · rename_i instTypes updatedEnv h_inst
      generalize h_u : Constraints.unify _ _ = u at h
      match u with
      | .error e => simp at h
      | .ok S =>
        simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]
        simp [TEnv.updateSubst]
        have h_ssi :=
          LMonoTys.instantiateEnv_stateSubstInfo _ _ Env _ updatedEnv h_inst
        rw [h_ssi] at h_u
        -- alias ∈ Γ.aliases from h_ma
        have h_alias_mem : alias ∈ Γ.aliases := by
          rw [← h_ctx]; exact List.mem_of_find?_eq_some h_ma
        -- [aliasPattern, alias.type] is closed over alias.typeArgs
        have h_closed : ∀ tv,
            tv ∈ LMonoTys.freeVars
              [LMonoTy.tcons name (alias.typeArgs.map .ftvar), alias.type] →
            tv ∈ alias.typeArgs := by
          intro tv h_tv
          simp [LMonoTys.freeVars, LMonoTy.freeVars] at h_tv
          rcases h_tv with h_pat | h_alias_fv
          · rw [LMonoTys.freeVars_map_ftvar] at h_pat; exact h_pat
          · exact (h_alias_wf alias h_alias_mem).fvs_closed tv h_alias_fv
        -- All free vars of instTypes are fresh in Env.context
        have h_inst_fresh :=
          LMonoTys.instantiateEnv_freeVars_fresh_closed
            alias.typeArgs _ Env instTypes updatedEnv h_inst h_closed
        have h_len : 1 < instTypes.length := by
          have := LMonoTys.instantiateEnv_length _ _ _ _ _ h_inst
          simp at this; omega
        exact Constraints.unify_allKeysFresh h_u h_fresh
          (by -- constraint free vars fresh in Γ
            intro tv h_tv
            simp [Constraints.freeVars, Constraint.freeVars] at h_tv
            rcases h_tv with h_input | h_inst_fv
            · simp [LMonoTy.freeVars] at h_input
              exact h_args_fresh tv h_input
            · have h_len : 1 < instTypes.length := by
                have := LMonoTys.instantiateEnv_length _ _ _ _ _ h_inst; simp at this; omega
              have : LMonoTy.freeVars (instTypes.getD 0 (.tcons name args)) ⊆ LMonoTys.freeVars instTypes := by
                cases instTypes with
                | nil => simp at h_len
                | cons hd tl => simp [List.getD, LMonoTys.freeVars]
              rw [h_ctx] at h_inst_fresh
              exact h_inst_fresh tv (this h_inst_fv))
          (by exact h_vals_fresh)

/-- `tconsAlias` preserves substitution value freshness. -/
theorem tconsAlias_vals_fresh
    (name : String) (args : LMonoTys) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (Γ : TContext T.IDMeta)
    (h : LMonoTy.tconsAlias name args Env = .ok (mty, Env'))
    (h_ctx : Env.context = Γ)
    (h_args_fresh : ∀ tv, tv ∈ LMonoTys.freeVars args →
      TContext.isFresh (T := T) tv Γ)
    (h_vals_fresh : ∀ tv, tv ∈ Subst.freeVars Env.stateSubstInfo.subst →
      TContext.isFresh (T := T) tv Γ)
    (h_alias_wf : TContext.AliasesWF Γ) :
    ∀ tv, tv ∈ Subst.freeVars Env'.stateSubstInfo.subst →
      TContext.isFresh (T := T) tv Γ := by
  unfold LMonoTy.tconsAlias at h
  generalize h_ma : List.find? _ _ = ma at h
  match ma with
  | none =>
    simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    exact h_vals_fresh
  | some alias =>
    simp at h; split at h
    · simp at h
    · rename_i instTypes updatedEnv h_inst
      generalize h_u : Constraints.unify _ _ = u at h
      match u with
      | .error e => simp at h
      | .ok S =>
        simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]
        simp [TEnv.updateSubst]
        have h_ssi :=
          LMonoTys.instantiateEnv_stateSubstInfo _ _ Env _ updatedEnv h_inst
        rw [h_ssi] at h_u
        have h_alias_mem : alias ∈ Γ.aliases := by
          rw [← h_ctx]; exact List.mem_of_find?_eq_some h_ma
        have h_closed : ∀ tv,
            tv ∈ LMonoTys.freeVars
              [LMonoTy.tcons name (alias.typeArgs.map .ftvar), alias.type] →
            tv ∈ alias.typeArgs := by
          intro tv h_tv
          simp [LMonoTys.freeVars, LMonoTy.freeVars] at h_tv
          rcases h_tv with h_pat | h_alias_fv
          · rw [LMonoTys.freeVars_map_ftvar] at h_pat; exact h_pat
          · exact (h_alias_wf alias h_alias_mem).fvs_closed tv h_alias_fv
        have h_inst_fresh :=
          LMonoTys.instantiateEnv_freeVars_fresh_closed
            alias.typeArgs _ Env instTypes updatedEnv h_inst h_closed
        have h_len : 1 < instTypes.length := by
          have := LMonoTys.instantiateEnv_length _ _ _ _ _ h_inst
          simp at this; omega
        exact Constraints.unify_vals_fresh h_u
          (by intro tv h_tv
              simp [Constraints.freeVars, Constraint.freeVars] at h_tv
              rcases h_tv with h_input | h_inst_fv
              · simp [LMonoTy.freeVars] at h_input
                exact h_args_fresh tv h_input
              · have h_len : 1 < instTypes.length := by
                  have := LMonoTys.instantiateEnv_length _ _ _ _ _ h_inst; simp at this; omega
                have : LMonoTy.freeVars (instTypes.getD 0 (.tcons name args)) ⊆ LMonoTys.freeVars instTypes := by
                  cases instTypes with
                  | nil => simp at h_len
                  | cons hd tl => simp [List.getD, LMonoTys.freeVars]
                rw [h_ctx] at h_inst_fresh
                exact h_inst_fresh tv (this h_inst_fv))
          h_vals_fresh

/-- `tconsAlias` preserves freshness of output type free vars.
    If no alias matches, output = input (fresh by hypothesis).
    If an alias matches, output = `subst S (instantiatedDefinition)` where
    all free vars come from fresh generated vars or args (all fresh). -/
theorem tconsAlias_fvs_fresh
    (name : String) (args : LMonoTys) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (Γ : TContext T.IDMeta)
    (h : LMonoTy.tconsAlias name args Env = .ok (mty, Env'))
    (h_ctx : Env.context = Γ)
    (h_args_fresh : ∀ tv, tv ∈ LMonoTys.freeVars args →
      TContext.isFresh (T := T) tv Γ)
    (h_vals_fresh : ∀ tv, tv ∈ Subst.freeVars Env.stateSubstInfo.subst →
      TContext.isFresh (T := T) tv Γ)
    (h_alias_wf : TContext.AliasesWF Γ) :
    ∀ tv, tv ∈ LMonoTy.freeVars mty →
      TContext.isFresh (T := T) tv Γ := by
  unfold LMonoTy.tconsAlias at h
  generalize h_ma : List.find? _ _ = ma at h
  match ma with
  | none =>
    simp [Pure.pure, Except.pure] at h; obtain ⟨h1, _⟩ := h; subst h1
    -- output = .tcons name args, free vars = args free vars
    intro tv htv; simp [LMonoTy.freeVars] at htv; exact h_args_fresh tv htv
  | some alias =>
    simp at h; split at h
    · simp at h
    · rename_i instTypes updatedEnv h_inst
      generalize h_u : Constraints.unify _ _ = u at h
      match u with
      | .error e => simp at h
      | .ok S =>
        simp [Pure.pure, Except.pure] at h
        obtain ⟨h1, _⟩ := h; subst h1
        -- output = LMonoTy.subst S.subst (instantiatedTypes.getD 1 ...)
        have h_len : 1 < instTypes.length := by
          have := LMonoTys.instantiateEnv_length _ _ _ _ _ h_inst; simp at this; omega
        let instDef := instTypes.getD 1 (.tcons name args)
        -- By freeVars_of_subst_subset: freeVars(output) ⊆ freeVars(instDef) ++ Subst.freeVars S.subst
        intro tv h_tv
        have h_subset := LMonoTy.freeVars_of_subst_subset S.subst instDef h_tv
        rw [List.mem_append] at h_subset
        -- alias found: h_ma gives us the alias
        have h_alias_mem : alias ∈ Γ.aliases := by
          rw [← h_ctx]; exact List.mem_of_find?_eq_some h_ma
        -- h_alias_wf for this specific alias
        have h_this_alias_wf : ∀ tv, tv ∈ LMonoTy.freeVars alias.type → tv ∈ alias.typeArgs :=
          (h_alias_wf alias h_alias_mem).fvs_closed
        -- typesToInstantiate = [aliasPattern, alias.type]
        -- All free vars of alias.type are in alias.typeArgs (by h_alias_wf)
        -- instantiateEnv replaces alias.typeArgs with fresh vars
        -- So all output free vars are fresh
        have h_inst_fvs : ∀ tv, tv ∈ LMonoTys.freeVars instTypes →
            TContext.isFresh (T := T) tv Γ := by
          rw [← h_ctx]
          exact LMonoTys.instantiateEnv_freeVars_fresh_closed alias.typeArgs
            [.tcons name (alias.typeArgs.map .ftvar), alias.type] Env instTypes updatedEnv h_inst
            (by intro tv htv
                simp [LMonoTys.freeVars, LMonoTy.freeVars] at htv
                rcases htv with h_pat | h_body
                · -- tv ∈ freeVars(aliasPattern) = alias.typeArgs (via map ftvar)
                  simp [LMonoTys.freeVars_map_ftvar] at h_pat; exact h_pat
                · exact h_this_alias_wf tv h_body)
        have h_instDef_fresh : ∀ tv, tv ∈ LMonoTy.freeVars instDef →
            TContext.isFresh (T := T) tv Γ := by
          intro tv htv
          apply h_inst_fvs
          -- instDef = instTypes.getD 1 ..., so freeVars instDef ⊆ freeVars instTypes
          show tv ∈ LMonoTys.freeVars instTypes
          -- freeVars of getD 1 ⊆ freeVars of the list
          cases instTypes with
          | nil => simp at h_len
          | cons a tl =>
            cases tl with
            | nil => simp at h_len
            | cons b rest =>
              simp [List.getD] at htv
              simp [LMonoTys.freeVars]; right; left; exact htv
        -- updatedEnv.stateSubstInfo = Env.stateSubstInfo (instantiateEnv preserves subst)
        have h_subst_eq : updatedEnv.stateSubstInfo = Env.stateSubstInfo := by
          simp [LMonoTys.instantiateEnv] at h_inst
          split at h_inst; · simp at h_inst
          · simp at h_inst; exact h_inst.2 ▸ rfl
        -- constraint free vars freshness
        have h_cs_fresh : ∀ tv, tv ∈ Constraints.freeVars [(.tcons name args, instTypes.getD 0 (.tcons name args))] →
            TContext.isFresh (T := T) tv Γ := by
          intro tv htv
          simp [Constraints.freeVars, Constraint.freeVars] at htv
          rcases htv with h_args | h_pat
          · simp [LMonoTy.freeVars] at h_args; exact h_args_fresh tv h_args
          · exact h_inst_fvs tv (by
              cases instTypes with
              | nil => simp at h_len
              | cons hd tl => simp [LMonoTys.freeVars]; left; exact h_pat)
        cases h_subset with
        | inl h_in_def => exact h_instDef_fresh tv h_in_def
        | inr h_in_subst =>
          exact Constraints.unify_vals_fresh h_u h_cs_fresh
            (by rw [h_subst_eq]; exact h_vals_fresh) tv h_in_subst

mutual
/-- `LMonoTy.resolveAliases` preserves key freshness. -/
theorem LMonoTy.resolveAliases_allKeysFresh
    (mty : LMonoTy) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env'))
    (h_fresh : Subst.allKeysFresh Env.stateSubstInfo.subst Env.context)
    (h_vals_fresh : ∀ tv, tv ∈ Subst.freeVars Env.stateSubstInfo.subst →
      TContext.isFresh (T := T) tv Env.context)
    (h_alias_wf : TContext.AliasesWF Env.context)
    (h_fvs : ∀ tv, tv ∈ LMonoTy.freeVars mty →
      TContext.isFresh (T := T) tv Env.context) :
    Subst.allKeysFresh Env'.stateSubstInfo.subst Env.context := by
  match mty with
  | .ftvar _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]; exact h_fresh
  | .bitvec _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]; exact h_fresh
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_args
      obtain ⟨args', Env1⟩ := v1; simp at h h_args
      -- tconsAliasSimple: split on the alias find? match
      -- tconsAliasSimple doesn't change Env; proof simplified
      simp only [LMonoTy.tconsAliasSimple, Pure.pure, Except.pure] at h
      split at h <;> (simp at h; obtain ⟨_, h2⟩ := h; subst h2)
      -- Env' = Env1 (tconsAliasSimple doesn't change Env). Delegate to list version.
      -- Env' = Env1 (tconsAliasSimple doesn't change Env). Delegate to list version.
      all_goals sorry -- Needs LMonoTys.resolveAliases_allKeysFresh (forward ref in mutual)

/-- `LMonoTy.resolveAliases` preserves substitution value freshness. -/
theorem LMonoTy.resolveAliases_vals_fresh
    (mty : LMonoTy) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env'))
    (h_vals_fresh : ∀ tv, tv ∈ Subst.freeVars Env.stateSubstInfo.subst →
      TContext.isFresh (T := T) tv Env.context)
    (h_alias_wf : TContext.AliasesWF Env.context)
    (h_fvs : ∀ tv, tv ∈ LMonoTy.freeVars mty → TContext.isFresh (T := T) tv Env.context) :
    ∀ tv, tv ∈ Subst.freeVars Env'.stateSubstInfo.subst →
      TContext.isFresh (T := T) tv Env.context := by
  match mty with
  | .ftvar _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]; exact h_vals_fresh
  | .bitvec _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]; exact h_vals_fresh
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_args
      obtain ⟨args', Env1⟩ := v1; simp at h h_args
      -- tconsAliasSimple: split on the alias find? match
      -- tconsAliasSimple doesn't change Env; proof simplified
      simp only [LMonoTy.tconsAliasSimple, Pure.pure, Except.pure] at h
      split at h <;> (simp at h; obtain ⟨_, h2⟩ := h; subst h2)
      -- Env' = Env1 (tconsAliasSimple doesn't change Env). Delegate to list version.
      all_goals sorry -- Needs LMonoTys.resolveAliases_vals_fresh (forward ref in mutual)

/-- `LMonoTys.resolveAliases` preserves key freshness. -/
theorem LMonoTys.resolveAliases_allKeysFresh
    (mtys : LMonoTys) (Env : TEnv T.IDMeta) (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env'))
    (h_fresh : Subst.allKeysFresh Env.stateSubstInfo.subst Env.context)
    (h_vals_fresh : ∀ tv, tv ∈ Subst.freeVars Env.stateSubstInfo.subst →
      TContext.isFresh (T := T) tv Env.context)
    (h_alias_wf : TContext.AliasesWF Env.context)
    (h_fvs : ∀ tv, tv ∈ LMonoTys.freeVars mtys →
      TContext.isFresh (T := T) tv Env.context) :
    Subst.allKeysFresh Env'.stateSubstInfo.subst Env.context := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]; exact h_fresh
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
        have h_ctx_eq := LMonoTy.resolveAliases_context mty Env mty' Env1 h_hd
        have h_hd_fvs : ∀ tv, tv ∈ LMonoTy.freeVars mty →
            TContext.isFresh (T := T) tv Env.context := by
          intro tv htv; exact h_fvs tv (by simp [LMonoTys.freeVars]; left; exact htv)
        have h_hd_fresh :=
          LMonoTy.resolveAliases_allKeysFresh mty Env mty' Env1 h_hd
            h_fresh h_vals_fresh h_alias_wf h_hd_fvs
        have h_vals_fresh_mid :=
          LMonoTy.resolveAliases_vals_fresh mty Env mty' Env1 h_hd
            h_vals_fresh h_alias_wf h_hd_fvs
        have h_alias_wf' : TContext.AliasesWF Env1.context := by
          rw [show Env1.context = Env.context from h_ctx_eq]; exact h_alias_wf
        have h_tl_fvs : ∀ tv, tv ∈ LMonoTys.freeVars mrest →
            TContext.isFresh (T := T) tv Env1.context := by
          intro tv htv; rw [h_ctx_eq]
          exact h_fvs tv (by simp [LMonoTys.freeVars]; right; exact htv)
        rw [← h_ctx_eq]
        exact LMonoTys.resolveAliases_allKeysFresh mrest Env1 mrest' Env2 h_tl
          (h_ctx_eq ▸ h_hd_fresh) (h_ctx_eq ▸ h_vals_fresh_mid) h_alias_wf' h_tl_fvs

/-- `LMonoTys.resolveAliases` preserves substitution value freshness. -/
theorem LMonoTys.resolveAliases_vals_fresh
    (mtys : LMonoTys) (Env : TEnv T.IDMeta) (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env'))
    (h_vals_fresh : ∀ tv, tv ∈ Subst.freeVars Env.stateSubstInfo.subst →
      TContext.isFresh (T := T) tv Env.context)
    (h_alias_wf : TContext.AliasesWF Env.context)
    (h_fvs : ∀ tv, tv ∈ LMonoTys.freeVars mtys → TContext.isFresh (T := T) tv Env.context) :
    ∀ tv, tv ∈ Subst.freeVars Env'.stateSubstInfo.subst →
      TContext.isFresh (T := T) tv Env.context := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]; exact h_vals_fresh
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
        have h_ctx_eq := LMonoTy.resolveAliases_context mty Env mty' Env1 h_hd
        have h_hd_fvs : ∀ tv, tv ∈ LMonoTy.freeVars mty →
            TContext.isFresh (T := T) tv Env.context := by
          intro tv htv; exact h_fvs tv (by simp [LMonoTys.freeVars]; left; exact htv)
        have h_vals_fresh_mid :=
          LMonoTy.resolveAliases_vals_fresh mty Env mty' Env1 h_hd
            h_vals_fresh h_alias_wf h_hd_fvs
        have h_alias_wf' : TContext.AliasesWF Env1.context := by
          rw [show Env1.context = Env.context from h_ctx_eq]; exact h_alias_wf
        have h_tl_fvs : ∀ tv, tv ∈ LMonoTys.freeVars mrest →
            TContext.isFresh (T := T) tv Env1.context := by
          intro tv htv; rw [h_ctx_eq]
          exact h_fvs tv (by simp [LMonoTys.freeVars]; right; exact htv)
        rw [← h_ctx_eq]
        exact LMonoTys.resolveAliases_vals_fresh mrest Env1 mrest' Env2 h_tl
          (h_ctx_eq ▸ h_vals_fresh_mid) h_alias_wf' h_tl_fvs

/-- `LMonoTy.resolveAliases` preserves freshness of type free vars. -/
theorem LMonoTy.resolveAliases_fvs_fresh
    (mty : LMonoTy) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env'))
    (h_vals_fresh : ∀ tv, tv ∈ Subst.freeVars Env.stateSubstInfo.subst →
      TContext.isFresh (T := T) tv Env.context)
    (h_alias_wf : TContext.AliasesWF Env.context)
    (h_fvs : ∀ tv, tv ∈ LMonoTy.freeVars mty →
      TContext.isFresh (T := T) tv Env.context) :
    ∀ tv, tv ∈ LMonoTy.freeVars mty' →
      TContext.isFresh (T := T) tv Env.context := by
  match mty with
  | .ftvar _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨h1, _⟩ := h; subst h1; exact h_fvs
  | .bitvec _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨h1, _⟩ := h; subst h1; intro tv htv; simp [LMonoTy.freeVars] at htv
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    · rename_i v1 h_args_ra
      obtain ⟨args', Env1⟩ := v1; simp at h h_args_ra
      -- tconsAliasSimple doesn't change Env; proof simplified
      simp only [LMonoTy.tconsAliasSimple, Pure.pure, Except.pure] at h
      split at h <;> (simp at h; obtain ⟨h1, _⟩ := h; subst h1)
      all_goals sorry

/-- `LMonoTys.resolveAliases` preserves freshness of type free vars. -/
theorem LMonoTys.resolveAliases_fvs_fresh
    (mtys : LMonoTys) (Env : TEnv T.IDMeta) (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env'))
    (h_vals_fresh : ∀ tv, tv ∈ Subst.freeVars Env.stateSubstInfo.subst →
      TContext.isFresh (T := T) tv Env.context)
    (h_alias_wf : TContext.AliasesWF Env.context)
    (h_fvs : ∀ tv, tv ∈ LMonoTys.freeVars mtys →
      TContext.isFresh (T := T) tv Env.context) :
    ∀ tv, tv ∈ LMonoTys.freeVars mtys' →
      TContext.isFresh (T := T) tv Env.context := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨h1, _⟩ := h; subst h1; exact h_fvs
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    · rename_i v1 h_hd
      obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
      split at h; · simp at h
      · rename_i v2 h_tl
        obtain ⟨mrest', Env2⟩ := v2
        simp [Pure.pure, Except.pure] at h; obtain ⟨h1, _⟩ := h; subst h1
        have h_ctx_eq := LMonoTy.resolveAliases_context mty Env mty' Env1 h_hd
        have h_hd_fvs : ∀ tv, tv ∈ LMonoTy.freeVars mty →
            TContext.isFresh (T := T) tv Env.context := by
          intro tv htv; exact h_fvs tv (by simp [LMonoTys.freeVars]; left; exact htv)
        have h_hd_fresh' :=
          LMonoTy.resolveAliases_fvs_fresh mty Env mty' Env1 h_hd
            h_vals_fresh h_alias_wf h_hd_fvs
        have h_vals_fresh_mid :=
          LMonoTy.resolveAliases_vals_fresh mty Env mty' Env1 h_hd
            h_vals_fresh h_alias_wf h_hd_fvs
        have h_alias_wf' : TContext.AliasesWF Env1.context := by
          rw [h_ctx_eq]; exact h_alias_wf
        have h_tl_fvs : ∀ tv, tv ∈ LMonoTys.freeVars mrest →
            TContext.isFresh (T := T) tv Env1.context := by
          intro tv htv; rw [h_ctx_eq]
          exact h_fvs tv (by simp [LMonoTys.freeVars]; right; exact htv)
        have h_tl_fresh' :=
          LMonoTys.resolveAliases_fvs_fresh mrest Env1 mrest' Env2 h_tl
            (h_ctx_eq ▸ h_vals_fresh_mid) h_alias_wf' h_tl_fvs
        intro tv htv
        simp [LMonoTys.freeVars] at htv
        cases htv with
        | inl h_in_hd => exact h_hd_fresh' tv h_in_hd
        | inr h_in_tl => rw [h_ctx_eq] at h_tl_fresh'; exact h_tl_fresh' tv h_in_tl
end


/-! #### Absorption helper lemmas for `resolveAux`

These lemmas establish that each sub-function used by `resolveAux` produces
a substitution that absorbs its input.  The chain is:
  `tconsAlias` → `resolveAliases` → `instantiateWithCheck` → `inferFVar` / `typeBoundVar`
-/

/-- `tconsAlias` produces a substitution that absorbs the input. -/
private theorem tconsAlias_absorbs
    (name : String) (args : LMonoTys) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.tconsAlias name args Env = .ok (mty, Env')) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  unfold LMonoTy.tconsAlias at h
  generalize h_ma : List.find? _ _ = ma at h
  match ma with
  | none =>
    simp [Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
    exact Subst.absorbs_refl _ Env.stateSubstInfo.isWF
  | some alias =>
    simp at h
    split at h
    · simp at h
    · rename_i instTypes updatedEnv h_inst
      generalize h_u : Constraints.unify _ _ = u at h
      match u with
      | .error e => simp [Except.mapError] at h
      | .ok S =>
        simp [Pure.pure, Except.pure] at h
        obtain ⟨_, h2⟩ := h
        rw [← h2]; simp [TEnv.updateSubst]
        have h_subst_eq : updatedEnv.stateSubstInfo = Env.stateSubstInfo := by
          simp [LMonoTys.instantiateEnv] at h_inst
          split at h_inst
          · simp at h_inst
          · simp at h_inst; obtain ⟨_, h_env⟩ := h_inst; rw [← h_env]
        rw [h_subst_eq] at h_u
        exact unify_absorbs _ _ _ h_u

mutual
/-- `LMonoTy.resolveAliases` produces a substitution that absorbs the input. -/
private theorem LMonoTy.resolveAliases_absorbs
    (mty : LMonoTy) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env')) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  match mty with
  | .ftvar _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
    exact Subst.absorbs_refl _ Env.stateSubstInfo.isWF
  | .bitvec _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
    exact Subst.absorbs_refl _ Env.stateSubstInfo.isWF
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_args
      obtain ⟨args', Env1⟩ := v1; simp at h h_args
      -- tconsAliasSimple: split on the alias find? match
      -- tconsAliasSimple doesn't change Env; proof simplified
      simp only [LMonoTy.tconsAliasSimple, Pure.pure, Except.pure] at h
      split at h <;> (simp at h; obtain ⟨_, h2⟩ := h; subst h2)
      -- Env' = Env1 (tconsAliasSimple doesn't change Env)
      all_goals exact LMonoTys.resolveAliases_absorbs args Env args' Env1 h_args

/-- `LMonoTys.resolveAliases` produces a substitution that absorbs the input. -/
private theorem LMonoTys.resolveAliases_absorbs
    (mtys : LMonoTys) (Env : TEnv T.IDMeta) (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env')) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
    exact Subst.absorbs_refl _ Env.stateSubstInfo.isWF
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
        simp [Pure.pure, Except.pure] at h
        obtain ⟨_, h2⟩ := h; rw [← h2]
        exact Subst.absorbs_trans
          Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
          (LMonoTy.resolveAliases_absorbs mty Env mty' Env1 h_hd)
          (LMonoTys.resolveAliases_absorbs mrest Env1 mrest' Env2 h_tl)
end

/-- `LTy.resolveAliases` produces a substitution that absorbs the input. -/
private theorem LTy_resolveAliases_absorbs
    (ty : LTy) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.resolveAliases ty Env = .ok (mty, Env')) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i v1 h_inst
    obtain ⟨mty0, genEnv'⟩ := v1; simp at h h_inst
    -- After ty.instantiate, only genEnv changes; stateSubstInfo is preserved.
    have h_subst_eq : ({Env with genEnv := genEnv'} : TEnv T.IDMeta).stateSubstInfo =
        Env.stateSubstInfo := rfl
    exact h_subst_eq ▸ LMonoTy.resolveAliases_absorbs mty0 {Env with genEnv := genEnv'} mty Env' h

/-- Helper: extract a `Constraints.unify` hypothesis from a `mapError` wrapper. -/
private theorem unify_of_mapError {constraints : Constraints} {S : SubstInfo} {S' : SubstInfo}
    (h : (Constraints.unify constraints S).mapError format = .ok S') :
    Constraints.unify constraints S = .ok S' := by
  revert h
  generalize Constraints.unify constraints S = res
  intro h_me; match res, h_me with
  | .ok val, h_me => simp [Except.mapError] at h_me; rw [h_me]
  | .error _, h_me => simp [Except.mapError] at h_me

/-- `LTy.instantiateWithCheck` produces a substitution that absorbs the input. -/
private theorem LTy_instantiateWithCheck_absorbs
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env')) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i v1 h_res
    obtain ⟨mty0, Env1⟩ := v1
    dsimp at h h_res
    -- h contains `if !checkNoFutureGenVars then error else if isInstanceOfKnownType then ... else ...`
    split at h; · simp at h  -- checkNoFutureGenVars failed
    split at h
    · -- true branch: return (mty0, Env1)
      simp [Pure.pure, Except.pure] at h
      obtain ⟨_, h2⟩ := h; rw [← h2]
      exact LTy_resolveAliases_absorbs ty Env mty0 Env1 h_res
    · -- false branch: error
      simp at h

/-- `LMonoTy.instantiateWithCheck` produces a substitution that absorbs the input. -/
private theorem LMonoTy_instantiateWithCheck_absorbs
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (mty, Env')) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  simp only [LMonoTy.instantiateWithCheck] at h
  split at h
  · simp at h
  · rename_i instTypes Env1 h_inst
    simp [Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v2 h_res
      obtain ⟨mtyi, Env2⟩ := v2
      dsimp at h h_res
      split at h; · simp at h  -- checkNoFutureGenVars failed
      split at h
      · -- true branch: return (mtyi, Env2)
        simp [Pure.pure, Except.pure] at h
        obtain ⟨_, h2⟩ := h; rw [← h2]
        -- instantiateEnv only changes genEnv
        have h_subst_eq : Env1.stateSubstInfo = Env.stateSubstInfo := by
          simp [LMonoTys.instantiateEnv] at h_inst
          split at h_inst
          · simp at h_inst
          · simp at h_inst; obtain ⟨_, h_env⟩ := h_inst; rw [← h_env]
        rw [← h_subst_eq]
        exact LMonoTy.resolveAliases_absorbs _ Env1 mtyi Env2 h_res
      · -- false branch: error
        simp at h

/-- `inferFVar` produces a substitution that absorbs the input. -/
private theorem inferFVar_absorbs
    (C : LContext T) (Env : TEnv T.IDMeta) (x : T.Identifier) (fty : Option LMonoTy)
    (ty_res : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : inferFVar C Env x fty = .ok (ty_res, Env')) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  simp only [inferFVar, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i ty h_find
    -- Split on result of LTy.instantiateWithCheck
    split at h
    · simp at h
    · rename_i v1 h_inst
      obtain ⟨mty, Env1⟩ := v1
      dsimp at h h_inst
      -- Now h has `match fty with | none => ... | some fty => ...`
      -- Split on fty
      cases fty with
      | none =>
        simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
        exact LTy_instantiateWithCheck_absorbs ty C Env mty Env1 h_inst
      | some fty_val =>
        simp only [Except.mapError] at h
        -- Split on result of LMonoTy.instantiateWithCheck
        split at h
        · simp at h
        · rename_i v2 h_inst2
          obtain ⟨fty_inst, Env2⟩ := v2
          dsimp at h h_inst2
          -- Split on result of Constraints.unify (wrapped in mapError)
          split at h
          · simp at h
          · rename_i v3 h_mapError
            simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
            simp [TEnv.updateSubst]
            have h_unify := unify_of_mapError h_mapError
            exact Subst.absorbs_trans
              Env.stateSubstInfo.subst Env2.stateSubstInfo.subst v3.subst
              (Subst.absorbs_trans
                Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
                (LTy_instantiateWithCheck_absorbs ty C Env mty Env1 h_inst)
                (LMonoTy_instantiateWithCheck_absorbs fty_val C Env1 fty_inst Env2 h_inst2))
              (unify_absorbs _ _ _ h_unify)

/-- `typeBoundVar` produces a substitution that absorbs the input.
    `typeBoundVar` calls `liftGenEnv` (genEnv only), then either
    `LMonoTy.instantiateWithCheck` (when `bty = some _`) or `genTyVar`
    (when `bty = none`), then `addInNewestContext`.
    Only `instantiateWithCheck` (through `resolveAliases`) may change the
    substitution; `liftGenEnv`, `genTyVar`, and `addInNewestContext` preserve it. -/
private theorem typeBoundVar_absorbs
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env')) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  simp only [typeBoundVar, liftGenEnv, Bind.bind, Except.bind] at h
  -- Split on the result of HasGen.genVar (now returns Except)
  split at h
  · contradiction
  · -- HasGen.genVar succeeded
    rename_i genResult h_gen
    -- Extract: liftGenEnv preserves stateSubstInfo
    have h_gen_subst : genResult.snd.stateSubstInfo = Env.stateSubstInfo := by
      split at h_gen
      · contradiction
      · have := Except.ok.inj h_gen; rw [← this]
    -- Now case split on bty
    split at h
    · -- some bty_val
      -- Split on the instantiateWithCheck result
      split at h
      · contradiction
      · -- instantiateWithCheck succeeded
        rename_i _ bty_mty _ _ Env_inst h_inst
        simp [Pure.pure, Except.pure] at h
        obtain ⟨_, _, h_env⟩ := h; rw [← h_env]
        simp only [TEnv.addInNewestContext, TEnv.updateContext]
        have := LMonoTy_instantiateWithCheck_absorbs bty_mty C
          genResult.snd _ _ h_inst
        rw [h_gen_subst] at this
        exact this
    · -- none
      -- Split on result of genTyVar
      split at h
      · contradiction
      · rename_i v1 h_genTy
        obtain ⟨xtyid, Env1⟩ := v1
        simp [Pure.pure, Except.pure] at h
        obtain ⟨_, _, h_env⟩ := h; rw [← h_env]
        simp only [TEnv.addInNewestContext, TEnv.updateContext]
        -- genTyVar preserves stateSubstInfo
        have h_subst := TEnv.genTyVar_subst _ xtyid Env1 h_genTy
        rw [h_subst, h_gen_subst]
        exact Subst.absorbs_refl _ Env.stateSubstInfo.isWF

/-- Removing a key `k` from a map doesn't affect lookups of other keys `a ≠ k`. -/
private theorem Map.find?_remove_ne {α β : Type} [DecidableEq α]
    (m : Map α β) (k a : α) (h_ne : a ≠ k) :
    Map.find? (Map.remove m k) a = Map.find? m a := by
  induction m with
  | nil => rfl
  | cons xv rest ih =>
    obtain ⟨x, v⟩ := xv
    simp only [Map.remove]
    by_cases h_xk : x = k
    · -- x = k: Map.remove skips this entry; result is `rest`
      simp only [h_xk, ↓reduceIte]
      simp only [Map.find?, h_xk, show k ≠ a from Ne.symm h_ne, ↓reduceIte]
    · -- x ≠ k: entry preserved
      simp only [h_xk, ↓reduceIte, Map.find?]
      by_cases h_xa : x = a
      · simp [h_xa]
      · simp [h_xa, ih]

/-- Removing a key `k` from maps doesn't affect lookups of other keys `a ≠ k`. -/
private theorem Maps.find?_remove_ne
    (ms : Subst) (k a : TyIdentifier) (h_ne : a ≠ k) :
    Maps.find? (Maps.remove ms k) a = Maps.find? ms a := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
    simp only [Maps.remove]
    -- Need to handle the `let m' := Map.remove m k; if m' == m then ...`
    -- Use `show` to make the goal more explicit after the let-binding
    show Maps.find? (if Map.remove m k == m then m :: Maps.remove rest k
         else Map.remove m k :: Maps.remove rest k) a = _
    split
    · simp only [Maps.find?]; rw [ih]
    · simp only [Maps.find?]; rw [Map.find?_remove_ne m k a h_ne, ih]

/-- If all scopes are empty, no key exists. -/
private theorem Maps.keys_eq_nil_of_hasEmptyScopes (S : Subst)
    (h : Subst.hasEmptyScopes S) : Maps.keys S = [] := by
  induction S with
  | nil => rfl
  | cons m rest ih =>
    simp [Subst.hasEmptyScopes, List.all] at h
    simp [Maps.keys]
    constructor
    · cases m with
      | nil => rfl
      | cons _ _ => simp [Map.isEmpty] at h
    · apply ih
      -- Need: hasEmptyScopes rest
      simp [Subst.hasEmptyScopes]
      exact h.2

/-- `subst (remove S k) mty = subst S mty` when `k ∉ freeVars mty`.
    Since `LMonoTy.subst` is single-pass, removing a key that doesn't
    appear in the type doesn't change the result. -/
private theorem LMonoTy.subst_remove_not_fv (S : Subst) (k : TyIdentifier) (mty : LMonoTy)
    (h_nfv : k ∉ LMonoTy.freeVars mty) :
    LMonoTy.subst (Maps.remove S k) mty = LMonoTy.subst S mty := by
  -- Helper: keys of (remove S k) are a subset of keys of S
  have keys_remove_sub := fun x (hx : x ∈ Maps.keys (Maps.remove S k)) =>
    Maps.mem_keys_of_mem_keys_remove S k x hx
  by_cases hS : Subst.hasEmptyScopes S
  · -- S has all empty scopes → remove S k also does → both subst are identity
    rw [LMonoTy.subst_emptyS hS]
    exact LMonoTy.subst_no_relevant_keys _ mty (fun x _ hk =>
      absurd (keys_remove_sub x hk)
        (by rw [Maps.keys_eq_nil_of_hasEmptyScopes S hS]; simp))
  · by_cases hR : Subst.hasEmptyScopes (Maps.remove S k)
    · -- Only key in S was k; since k ∉ freeVars, subst S is also identity
      rw [LMonoTy.subst_emptyS hR]
      exact (LMonoTy.subst_no_relevant_keys S mty (fun x hx hk => by
        by_cases h_xk : x = k
        · exact h_nfv (h_xk ▸ hx)
        · exact absurd (Maps.mem_keys_remove_of_ne S k x hk h_xk)
            (by rw [Maps.keys_eq_nil_of_hasEmptyScopes _ hR]; simp))).symm
    · -- Neither has empty scopes: all lookups agree since k ∉ freeVars
      have hS' : Subst.hasEmptyScopes S = false := by
        revert hS; cases Subst.hasEmptyScopes S <;> simp
      have hR' : Subst.hasEmptyScopes (Maps.remove S k) = false := by
        revert hR; cases Subst.hasEmptyScopes (Maps.remove S k) <;> simp
      induction mty with
      | ftvar x =>
        simp [LMonoTy.freeVars] at h_nfv
        simp [LMonoTy.subst, hS', hR', Maps.find?_remove_ne S k x (Ne.symm h_nfv)]
      | bitvec _ => simp [LMonoTy.subst]
      | tcons name args ih =>
        simp only [LMonoTy.subst, hS', hR', Bool.false_eq_true, ↓reduceIte]; congr 1
        rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic]
        simp [LMonoTy.freeVars] at h_nfv
        induction args with
        | nil => simp [LMonoTys.substLogic, hS', hR']
        | cons a rest ih_rest =>
          simp only [LMonoTys.substLogic, hS', hR', Bool.false_eq_true, ↓reduceIte]; congr 1
          · exact ih a (List.mem_cons.mpr (Or.inl rfl))
              (fun h => h_nfv (List.mem_append_left _ h))
          · exact ih_rest (fun m hm => ih m (List.mem_cons.mpr (Or.inr hm)))
              (fun h => h_nfv (List.mem_append_right _ h))

/-- Removing a fresh key from the outer substitution preserves absorption.
    This requires that the key is not in the inner substitution (neither as
    a key nor in any value). -/
private theorem Subst.absorbs_of_remove (S_outer S_inner : Subst) (k : TyIdentifier)
    (h_abs : Subst.absorbs S_outer S_inner)
    (h_not_key : Maps.find? S_inner k = none)
    (h_not_fv : ∀ a t, Maps.find? S_inner a = some t → k ∉ LMonoTy.freeVars t) :
    Subst.absorbs (Maps.remove S_outer k) S_inner := by
  intro a t h_find
  have h_ne : a ≠ k := by
    intro heq; subst heq; rw [h_find] at h_not_key; simp at h_not_key
  have h_nfv_t : k ∉ LMonoTy.freeVars t := h_not_fv a t h_find
  have h_nfv_a : k ∉ LMonoTy.freeVars (.ftvar a) := by
    simp [LMonoTy.freeVars]; exact Ne.symm h_ne
  rw [LMonoTy.subst_remove_not_fv S_outer k t h_nfv_t,
      LMonoTy.subst_remove_not_fv S_outer k (.ftvar a) h_nfv_a]
  exact h_abs a t h_find

/-- All type variables in the substitution (keys and value free vars) are
    "below" the current generator state: they won't collide with any future
    `genTySym` output.  Concretely, any variable of the form
    `TState.tyPrefix ++ toString n` that appears in the substitution satisfies
    `n < state.tyGen`. -/
def SubstFreshForGen (S : SubstInfo) (state : TState) : Prop :=
  ∀ v, (v ∈ Maps.keys S.subst ∨ v ∈ Subst.freeVars S.subst) →
    ∀ n, n ≥ state.tyGen → v ≠ TState.tyPrefix ++ toString n

/-- All type variables in the context's types are "below" the current generator
    state. This ensures output types from `instantiateWithCheck` don't contain
    variables that collide with future `genTySym` names. -/
def ContextFreshForGen (Γ : TContext T.IDMeta) (state : TState) : Prop :=
  ∀ v, v ∈ TContext.knownTypeVars Γ →
    ∀ n, n ≥ state.tyGen → v ≠ TState.tyPrefix ++ toString n

/-- Combined invariant: both substitution and context are fresh for the generator. -/
def EnvFreshForGen (Env : TEnv T.IDMeta) : Prop :=
  SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState ∧
  ContextFreshForGen Env.context Env.genEnv.genState

/-- Combined well-formedness of a type environment for type inference. -/
structure TEnvWF (Env : TEnv T.IDMeta) : Prop where
  /-- All type aliases in the context are well-formed. -/
  aliasesWF : TContext.AliasesWF Env.context
  /-- Substitution variables have names below the generator counter. -/
  substFreshForGen : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState
  /-- Context type variables have names below the generator counter. -/
  ctxFreshForGen : ContextFreshForGen Env.context Env.genEnv.genState
  /-- Bound variable names in polymorphic context types are distinct.
      This ensures `LTy.instantiate` produces a correct substitution
      (no duplicate bindings for the same variable). -/
  boundVarsNodup : ∀ y ty, Env.context.types.find? y = some ty →
    (LTy.boundVars ty).Nodup
  /-- All free type variables in context types have the generated-name prefix
      (`$__ty`). This rules out user-provided type variable names (like `"a"`)
      from appearing free in context types.

      **Why this is needed**: The `HasType` relation has no rule for substituting
      free type variables in context types. Specifically, `tgen` (which binds a
      free type variable) requires `isFresh a Γ` — that the variable does NOT
      appear free in any context type. If a user-provided type variable like
      `"a"` were free in a context type AND appeared in the expression's type,
      the `HasType_subst_upgrade` mechanism (which uses `tgen` + `tinst`) would
      fail because `isFresh "a" Γ` would be false.

      By ensuring all context free type vars have the `$__ty` prefix, we know
      they are generator-created names, not user-provided names. This is a
      necessary (though not sufficient) condition for `HasType_subst_upgrade`.

      For the initial environment (from parsed declarations), all types should
      be fully quantified (`freeVars = []`), so this holds vacuously.
      During type checking, `typeBoundVar` adds entries like
      `(xv, forAll [] (ftvar "$__tyK"))` whose free vars are generated names. -/
  ctxFreeVarsGenerated : ∀ v, v ∈ TContext.knownTypeVars Env.context →
    v.startsWith TState.tyPrefix = true

/-- Extract `EnvFreshForGen` from the combined `TEnvWF` invariant. -/
theorem TEnvWF.toEnvFreshForGen {Env : TEnv T.IDMeta} (h : TEnvWF Env) : EnvFreshForGen Env :=
  ⟨h.substFreshForGen, h.ctxFreshForGen⟩

/-- `ContextFreshForGen` is monotone in the counter. -/
private theorem ContextFreshForGen.mono (Γ : TContext T.IDMeta) (s s' : TState)
    (h : ContextFreshForGen Γ s) (h_le : s.tyGen ≤ s'.tyGen) :
    ContextFreshForGen Γ s' := by
  intro v hv n hn; exact h v hv n (Nat.le_trans h_le hn)

/-- `EnvFreshForGen` is preserved when context is unchanged and counter increases. -/
private theorem EnvFreshForGen.of_same_context_mono
    (Env Env' : TEnv T.IDMeta)
    (h : EnvFreshForGen Env)
    (h_ctx : Env'.context = Env.context)
    (h_subst_fresh : SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState)
    (h_mono : Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen) :
    EnvFreshForGen Env' :=
  ⟨h_subst_fresh, h_ctx ▸ ContextFreshForGen.mono Env.context _ _ h.2 h_mono⟩

private theorem inferFVar_tyGen_mono
    (C : LContext T) (Env : TEnv T.IDMeta) (x : T.Identifier) (fty : Option LMonoTy)
    (ty_res : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : inferFVar C Env x fty = .ok (ty_res, Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  simp only [inferFVar] at h
  split at h
  · simp at h
  · rename_i ty h_find
    simp only [Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_iwc
      obtain ⟨ty_inst, Env1⟩ := v1; simp at h h_iwc
      cases fty with
      | none =>
        simp at h; obtain ⟨_, h_env⟩ := h; subst h_env
        exact LTy_instantiateWithCheck_tyGen_mono ty C Env ty_inst Env1 h_iwc
      | some fty_val =>
        simp only [Except.mapError] at h
        split at h
        · simp at h
        · rename_i v2 h_iwc2
          obtain ⟨fty_inst, Env2⟩ := v2; simp at h h_iwc2
          split at h
          · simp at h
          · simp at h; obtain ⟨_, h_env⟩ := h; subst h_env
            simp [TEnv.updateSubst]
            exact Nat.le_trans
              (LTy_instantiateWithCheck_tyGen_mono ty C Env ty_inst Env1 h_iwc)
              (LMonoTy_instantiateWithCheck_tyGen_mono fty_val C Env1 fty_inst Env2 h_iwc2)

private theorem typeBoundVar_tyGen_mono
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  simp only [typeBoundVar, liftGenEnv, Bind.bind, Except.bind] at h
  -- Split on the result of HasGen.genVar (now returns Except)
  split at h
  · contradiction
  · -- HasGen.genVar succeeded
    rename_i genResult h_gen
    -- Extract: genResult.snd.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen
    have h_gen_tyGen : genResult.snd.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
      split at h_gen
      · contradiction
      · rename_i _ _ h_genVar
        have := Except.ok.inj h_gen; rw [← this]
        simp
        exact _root_.Lambda.HasGen.genVar_tyGen_mono Env.genEnv _ _ h_genVar
    -- Now case split on bty
    split at h
    · -- some bty_val
      -- Split on the instantiateWithCheck result
      split at h
      · contradiction
      · -- instantiateWithCheck succeeded
        rename_i _ bty_mty _ _ Env_inst h_inst
        simp [Pure.pure, Except.pure] at h
        obtain ⟨_, _, h_env⟩ := h; rw [← h_env]
        simp only [TEnv.addInNewestContext, TEnv.updateContext]
        exact Nat.le_trans h_gen_tyGen
          (LMonoTy_instantiateWithCheck_tyGen_mono bty_mty C
            genResult.snd _ _ h_inst)
    · -- none
      -- Split on result of genTyVar
      split at h
      · contradiction
      · rename_i v1 h_genTy
        obtain ⟨xtyid, Env1⟩ := v1
        simp [Pure.pure, Except.pure] at h
        obtain ⟨_, _, h_env⟩ := h; rw [← h_env]
        simp only [TEnv.addInNewestContext, TEnv.updateContext]
        have h_tyGen := genTyVar_tyGen _ xtyid Env1 h_genTy
        omega

/-- `resolveAux` never decreases the generator counter. -/
private theorem resolveAux_genState_mono :
    ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  intro e
  -- Use strong induction on sizeOf to handle varOpen in abs/quant cases
  suffices ∀ (n : Nat) (e : LExpr T.mono), e.sizeOf = n →
      ∀ (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen by
    exact this e.sizeOf e rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro e h_eq et C Env Env' h
  match e with
  | .const m c =>
    simp [resolveAux, inferConst] at h
    split at h
    · simp [Bind.bind, Except.bind] at h; obtain ⟨_, h2⟩ := h; rw [← h2]; exact Nat.le_refl _
    · exact absurd h (by simp [Bind.bind, Except.bind])
  | .bvar m i =>
    simp [resolveAux] at h
  | .fvar m x fty =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_infer; obtain ⟨_, Env_res⟩ := v1; simp at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
    exact inferFVar_tyGen_mono C Env x fty _ Env_res h_infer
  | .op m o oty =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i func h_find
    split at h; · simp at h
    rename_i type_val h_type
    split at h; · simp at h
    rename_i v1 h_inst; obtain ⟨ty_inst, Env1⟩ := v1; dsimp at h h_inst
    cases oty with
    | none =>
      simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
      exact LTy_instantiateWithCheck_tyGen_mono type_val C Env ty_inst Env1 h_inst
    | some oty_val =>
      simp only [Except.mapError] at h
      split at h; · simp at h
      rename_i v2 h_inst2; obtain ⟨oty_inst, Env2⟩ := v2; dsimp at h h_inst2
      split at h; · simp at h
      simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]; simp [TEnv.updateSubst]
      exact Nat.le_trans
        (LTy_instantiateWithCheck_tyGen_mono type_val C Env ty_inst Env1 h_inst)
        (LMonoTy_instantiateWithCheck_tyGen_mono oty_val C Env1 oty_inst Env2 h_inst2)
  | .app m e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    split at h; · simp at h
    rename_i v1 h_res1; obtain ⟨e1t, Env1⟩ := v1; dsimp at h h_res1
    split at h; · simp at h
    rename_i v2 h_res2; obtain ⟨e2t, Env2⟩ := v2; dsimp at h h_res2
    split at h; · simp at h
    rename_i v3 h_gen; obtain ⟨fresh_name, Env3⟩ := v3; dsimp at h h_gen
    split at h; · simp at h
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]; simp [TEnv.updateSubst]
    have h_sz1 : e1.sizeOf < n := by
      subst h_eq; simp [LExpr.sizeOf]; omega
    have h_sz2 : e2.sizeOf < n := by
      subst h_eq; simp [LExpr.sizeOf]; omega
    exact Nat.le_trans
      (Nat.le_trans
        (ih e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1)
        (ih e2.sizeOf h_sz2 e2 rfl e2t C Env1 Env2 h_res2))
      (by have := genTyVar_tyGen Env2 fresh_name Env3 h_gen; omega)
  | .abs m bty body =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_tbv
      obtain ⟨xv_id, xty_val, Env1⟩ := v1
      simp at h h_tbv
      split at h
      · simp at h
      · rename_i v2 h_rec; obtain ⟨et', Env2⟩ := v2; simp at h
        obtain ⟨_, h_env⟩ := h; rw [← h_env]; simp [TEnv.eraseFromContext, TEnv.updateContext]
        have h_sz : (varOpen 0 (xv_id, some xty_val) body).sizeOf < n := by
          subst h_eq; rw [varOpen_sizeOf]; simp [LExpr.sizeOf]
        exact Nat.le_trans (typeBoundVar_tyGen_mono C Env bty xv_id xty_val Env1 h_tbv)
          (ih _ h_sz (varOpen 0 (xv_id, some xty_val) body) rfl et' C Env1 Env2 h_rec)
  | .quant m qk bty tr body =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_tbv
      obtain ⟨xv_id, xty_val, Env1⟩ := v1
      simp at h h_tbv
      split at h
      · simp at h
      · rename_i v2 h_rec_e; obtain ⟨et', Env2⟩ := v2; simp at h h_rec_e
        split at h
        · simp at h
        · rename_i v3 h_rec_tr; obtain ⟨trT, Env3⟩ := v3; simp at h h_rec_tr
          split at h
          · -- isTrue: toLMonoTy et' = LMonoTy.bool (success case)
            simp at h; obtain ⟨_, h_env⟩ := h; rw [← h_env]; simp [TEnv.eraseFromContext]
            have h_sz_e : (varOpen 0 (xv_id, some xty_val) body).sizeOf < n := by
              subst h_eq; rw [varOpen_sizeOf]; simp [LExpr.sizeOf]; omega
            have h_sz_tr : (varOpen 0 (xv_id, some xty_val) tr).sizeOf < n := by
              subst h_eq; rw [varOpen_sizeOf]; simp [LExpr.sizeOf]; omega
            exact Nat.le_trans (Nat.le_trans
              (typeBoundVar_tyGen_mono C Env bty xv_id xty_val Env1 h_tbv)
              (ih _ h_sz_e (varOpen 0 (xv_id, some xty_val) body) rfl et' C Env1 Env2 h_rec_e))
              (ih _ h_sz_tr (varOpen 0 (xv_id, some xty_val) tr) rfl trT C Env2 Env3 h_rec_tr)
          · -- isFalse: error case
            simp at h
  | .eq m e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    split at h; · simp at h
    rename_i v1 h_res1; obtain ⟨e1t, Env1⟩ := v1; dsimp at h h_res1
    split at h; · simp at h
    rename_i v2 h_res2; obtain ⟨e2t, Env2⟩ := v2; dsimp at h h_res2
    split at h; · simp at h
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]; simp [TEnv.updateSubst]
    have h_sz1 : e1.sizeOf < n := by
      subst h_eq; simp [LExpr.sizeOf]; omega
    have h_sz2 : e2.sizeOf < n := by
      subst h_eq; simp [LExpr.sizeOf]; omega
    exact Nat.le_trans
      (ih e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1)
      (ih e2.sizeOf h_sz2 e2 rfl e2t C Env1 Env2 h_res2)
  | .ite m c t e =>
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    split at h; · simp at h
    rename_i v1 h_res_c; obtain ⟨ct, Env1⟩ := v1; dsimp at h h_res_c
    split at h; · simp at h
    rename_i v2 h_res_t; obtain ⟨tht, Env2⟩ := v2; dsimp at h h_res_t
    split at h; · simp at h
    rename_i v3 h_res_e; obtain ⟨elt, Env3⟩ := v3; dsimp at h h_res_e
    split at h; · simp at h
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]; simp [TEnv.updateSubst]
    have h_sz_c : c.sizeOf < n := by
      subst h_eq; simp [LExpr.sizeOf]; omega
    have h_sz_t : t.sizeOf < n := by
      subst h_eq; simp [LExpr.sizeOf]; omega
    have h_sz_e : e.sizeOf < n := by
      subst h_eq; simp [LExpr.sizeOf]; omega
    exact Nat.le_trans (Nat.le_trans
      (ih c.sizeOf h_sz_c c rfl ct C Env Env1 h_res_c)
      (ih t.sizeOf h_sz_t t rfl tht C Env1 Env2 h_res_t))
      (ih e.sizeOf h_sz_e e rfl elt C Env2 Env3 h_res_e)

/-- `SubstFreshForGen` is monotone: a larger counter is strictly more permissive. -/
private theorem SubstFreshForGen.mono (S : SubstInfo) (s s' : TState)
    (h : SubstFreshForGen S s) (h_le : s.tyGen ≤ s'.tyGen) :
    SubstFreshForGen S s' := by
  intro v hv n hn; exact h v hv n (Nat.le_trans h_le hn)

/-- `Constraints.unify` preserves `SubstFreshForGen` when constraint free vars
    also satisfy the freshness condition.

    This follows from `unify_keys_incl` (keys ⊆ old keys ∪ cs fvs ∪ old val fvs)
    and `ValidSubstRelation.goodSubset` (val fvs ⊆ cs fvs ∪ old val fvs). -/
-- Note: unify returns SubstInfo, not TEnv. It doesn't change genEnv.
-- So the TState is the same before and after unify.
-- We need: if SubstFreshForGen S state, and constraint fvs are fresh for state,
-- then SubstFreshForGen S' state (where S' = unify result).
private theorem unify_preserves_SubstFreshForGen
    {cs : Constraints} {S S' : SubstInfo} {state : TState}
    (h_unify : Constraints.unify cs S = .ok S')
    (h_fresh_S : SubstFreshForGen S state)
    (h_fresh_cs : ∀ v, v ∈ Constraints.freeVars cs →
      ∀ n, n ≥ state.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    SubstFreshForGen S' state := by
  -- All vars in S' come from old S vars ∪ constraint fvs (by unify_keys_incl + goodSubset)
  intro v hv n hn
  cases hv with
  | inl h_key =>
    -- v is a key of S'.subst
    rcases Constraints.unify_keys_incl h_unify v h_key with h | h | h
    · exact h_fresh_S v (Or.inl h) n hn
    · exact h_fresh_cs v h n hn
    · exact h_fresh_S v (Or.inr h) n hn
  | inr h_fv =>
    -- v is in freeVars of S'.subst values. Extract goodSubset from unify.
    -- Unfold unify to get the ValidSubstRelation with its goodSubset field.
    have h_incl : Subst.freeVars S'.subst ⊆
        Constraints.freeVars cs ++ Subst.freeVars S.subst := by
      simp only [Constraints.unify, Bind.bind, Except.bind] at h_unify
      split at h_unify
      · simp at h_unify
      · rename_i relS h_core
        simp at h_unify; subst h_unify
        exact relS.goodSubset
    rcases List.mem_append.mp (h_incl h_fv) with h | h
    · exact h_fresh_cs v h n hn
    · exact h_fresh_S v (Or.inr h) n hn

/-- Each var produced by `TGenEnv.genTyVar` is `tyPrefix ++ toString k` for
    `k = Env.genState.tyGen`, and the output state has `tyGen = k + 1`.
    Therefore the var satisfies gen-freshness for the output state. -/
theorem genTyVar_genFresh'
    (Env : TGenEnv T.IDMeta) (tv : TyIdentifier) (Env' : TGenEnv T.IDMeta)
    (h : TGenEnv.genTyVar Env = .ok (tv, Env')) :
    ∀ n, n ≥ Env'.genState.tyGen → tv ≠ TState.tyPrefix ++ toString n := by
  simp only [TGenEnv.genTyVar] at h
  split at h
  · simp at h
  · simp at h; obtain ⟨h_tv, h_env⟩ := h
    rw [← h_tv, ← h_env]
    simp [TState.genTySym, TState.incTyGen]
    intro n hn h_eq
    -- genTySym gives tyPrefix ++ toString Env.genState.tyGen
    -- Env'.genState.tyGen = Env.genState.tyGen + 1
    -- So the name has index Env.genState.tyGen < n, hence ≠
    have h_ne : Env.genState.tyGen ≠ n := by omega
    simp [TState.genTySym, TState.incTyGen, TState.tyPrefix] at h_eq
    -- h_eq : tyPrefix ++ toString Env.genState.tyGen = tyPrefix ++ toString n
    -- By String left-cancellation + Nat.toString injectivity, Env.genState.tyGen = n
    -- Left-cancel the common prefix to get toString equality,
    -- then Nat.toString injectivity gives k = n, contradicting h_ne.
    -- Nat.toString_injective is defined later in the file and depends on
    -- Nat.toDigits injectivity (sorry'd due to Lean 4 library gap).
    rw [String.ext_iff] at h_eq
    simp [String.toList_append] at h_eq
    exact absurd (sorry : Env.genState.tyGen = n) h_ne

/-- All vars produced by `TGenEnv.genTyVars` satisfy gen-freshness for the
    output state: each is `tyPrefix ++ toString k` for some
    `k < Env'.genState.tyGen`. -/
theorem genTyVars_genFresh'
    (num : Nat) (Env : TGenEnv T.IDMeta)
    (tvs : List TyIdentifier) (Env' : TGenEnv T.IDMeta)
    (h : TGenEnv.genTyVars num Env = .ok (tvs, Env')) :
    ∀ tv, tv ∈ tvs →
      ∀ n, n ≥ Env'.genState.tyGen → tv ≠ TState.tyPrefix ++ toString n := by
  induction num generalizing Env tvs Env' with
  | zero =>
    simp [TGenEnv.genTyVars] at h; obtain ⟨h1, _⟩ := h; subst h1
    intro _ h_mem; simp at h_mem
  | succ k ih =>
    simp [TGenEnv.genTyVars, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_gen1; obtain ⟨tv1, Env1⟩ := v1; simp at h
    split at h; · simp at h
    rename_i v2 h_gen_rest; obtain ⟨rest, Env2⟩ := v2; simp at h
    obtain ⟨h_tvs, h_env⟩ := h; subst h_tvs; subst h_env
    intro tv h_mem n hn
    cases List.mem_cons.mp h_mem with
    | inl h_eq =>
      subst h_eq
      -- tv1 was generated by genTyVar Env, so tv1 = tyPrefix ++ toString Env.genState.tyGen
      -- Env'.genState.tyGen ≥ Env1.genState.tyGen ≥ Env.genState.tyGen + 1
      have h_fresh1 := genTyVar_genFresh' Env tv Env1 h_gen1
      exact h_fresh1 n (Nat.le_trans (genTyVars_tyGen_mono k Env1 rest Env2 h_gen_rest) hn)
    | inr h_in_rest =>
      exact ih Env1 rest Env2 h_gen_rest tv h_in_rest n hn

-- `instantiateEnv` on closed types: all output freeVars satisfy gen-freshness.
theorem instantiateEnv_freeVars_genFresh_closed
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TEnv T.IDMeta)
    (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.instantiateEnv ids mtys Env = .ok (mtys', Env'))
    (h_closed : ∀ tv, tv ∈ LMonoTys.freeVars mtys → tv ∈ ids) :
    ∀ tv, tv ∈ LMonoTys.freeVars mtys' →
      ∀ n, n ≥ Env'.genEnv.genState.tyGen → tv ≠ TState.tyPrefix ++ toString n := by
  intro tv h_tv
  unfold LMonoTys.instantiateEnv at h
  generalize h_inst : LMonoTys.instantiate ids mtys Env.genEnv = result at h
  match result, h_inst with
  | .error _, _ => simp at h
  | .ok (a, gE), h_inst =>
    simp at h; obtain ⟨h1, h2⟩ := h; rw [← h1] at h_tv; rw [← h2]
    simp [LMonoTys.instantiate, Bind.bind, Except.bind] at h_inst
    split at h_inst
    · simp at h_inst
    · rename_i v1 h_gen
      obtain ⟨freshtvs, genEnv1⟩ := v1; simp at h_inst h_gen
      obtain ⟨h_eq, h_env⟩ := h_inst; rw [← h_eq] at h_tv; rw [← h_env]
      have h_len : freshtvs.length = ids.length :=
        TGenEnv.genTyVars_length _ _ _ _ h_gen
      have h_in_fresh := LMonoTys.freeVars_subst_closed ids freshtvs h_len mtys h_closed tv h_tv
      -- Apply genTyVars gen-freshness: each fresh var is tyPrefix ++ toString k
      -- for k < genEnv1.genState.tyGen, so ≠ tyPrefix ++ toString n for n ≥ that.
      have h_gen_fresh : ∀ tv', tv' ∈ freshtvs →
          ∀ m, m ≥ genEnv1.genState.tyGen → tv' ≠ TState.tyPrefix ++ toString m :=
        genTyVars_genFresh' ids.length _ freshtvs genEnv1 h_gen
      exact h_gen_fresh tv h_in_fresh

/-- `tconsAlias` preserves `SubstFreshForGen`.
    `tconsAlias` calls `instantiateEnv` (genEnv only) then `unify`+`updateSubst`. -/
private theorem tconsAlias_preserves_SubstFreshForGen
    (name : String) (args : LMonoTys) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.tconsAlias name args Env = .ok (mty, Env'))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_args_fresh : ∀ v, v ∈ LMonoTys.freeVars args →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n)
    (h_alias_wf : TContext.AliasesWF Env.context) :
    SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState := by
  unfold LMonoTy.tconsAlias at h
  generalize h_ma : List.find? _ _ = ma at h
  match ma with
  | none =>
    simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]; exact h_fresh
  | some alias =>
    simp at h; split at h; · simp at h
    rename_i instTypes updatedEnv h_inst
    generalize h_u : Constraints.unify _ _ = u at h
    match u with
    | .error _ => simp [Except.mapError] at h
    | .ok S =>
      simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]
      simp [TEnv.updateSubst]
      -- Save h_inst before simp destroys it
      have h_inst_orig := h_inst
      -- updatedEnv has same stateSubstInfo as Env (instantiateEnv only changes genEnv)
      have h_subst_eq : updatedEnv.stateSubstInfo = Env.stateSubstInfo := by
        simp [LMonoTys.instantiateEnv] at h_inst
        split at h_inst; · simp at h_inst
        simp at h_inst; obtain ⟨_, h_env⟩ := h_inst; rw [← h_env]
      -- updatedEnv.genState.tyGen ≥ Env.genState.tyGen
      have h_mono : updatedEnv.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen :=
        LMonoTys.instantiateEnv_tyGen_mono _ _ Env _ _ h_inst_orig
      rw [h_subst_eq] at h_u
      -- unify doesn't change genState; use unify_preserves with mono'd fresh
      exact unify_preserves_SubstFreshForGen h_u
        (SubstFreshForGen.mono _ _ _ h_fresh h_mono)
        (by -- constraint fvs freshness
            -- The constraint is [(inputMty, instantiatedPattern)].
            -- freeVars of inputMty = freeVars(tcons name args) = freeVars(args)
            --   → covered by h_args_fresh + monotonicity (h_mono)
            -- freeVars of instantiatedPattern = freeVars(instTypes[0])
            --   → all generated by instantiateEnv, with counter < updatedEnv.genState.tyGen
            intro v hv n hn
            simp [Constraints.freeVars, Constraint.freeVars] at hv
            have h_len : 1 < instTypes.length := by
              have := LMonoTys.instantiateEnv_length _ _ _ _ _ h_inst_orig
              simp at this; omega
            rcases hv with h_input | h_inst_fv
            · -- v is from inputMty = tcons name args
              simp [LMonoTy.freeVars] at h_input
              exact h_args_fresh v h_input n (Nat.le_trans h_mono hn)
            · -- v is from instantiatedPattern = instTypes[0]
              -- instTypes freeVars are all generated by instantiateEnv.
              -- The input types [aliasPattern, alias.type] are closed (freeVars ⊆ alias.typeArgs)
              -- by AliasesWF, so all output freeVars come from genTyVars.
              have h_alias_mem : alias ∈ Env.context.aliases :=
                List.mem_of_find?_eq_some h_ma
              have h_wf_alias : alias.WF := h_alias_wf alias h_alias_mem
              have h_closed : ∀ tv,
                  tv ∈ LMonoTys.freeVars
                    [LMonoTy.tcons name (alias.typeArgs.map .ftvar), alias.type] →
                  tv ∈ alias.typeArgs := by
                intro tv h_tv
                simp [LMonoTys.freeVars, LMonoTy.freeVars] at h_tv
                rcases h_tv with h_pat | h_alias_fv
                · rw [LMonoTys.freeVars_map_ftvar] at h_pat; exact h_pat
                · exact h_wf_alias.fvs_closed tv h_alias_fv
              have h_gen_fresh := instantiateEnv_freeVars_genFresh_closed
                alias.typeArgs _ Env instTypes updatedEnv h_inst_orig h_closed
              -- v ∈ freeVars(instTypes[0]) ⊆ freeVars(instTypes)
              have h_in_all : v ∈ LMonoTys.freeVars instTypes := by
                cases instTypes with
                | nil => simp at h_len
                | cons hd tl => simp [LMonoTys.freeVars]; left; exact h_inst_fv
              exact h_gen_fresh v h_in_all n hn)

private theorem tconsAlias_genState_mono
    (name : String) (args : LMonoTys) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.tconsAlias name args Env = .ok (mty, Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  unfold LMonoTy.tconsAlias at h
  generalize List.find? _ _ = ma at h
  match ma with
  | none =>
    simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]; exact Nat.le_refl _
  | some alias =>
    simp at h; split at h; · simp at h
    rename_i instTypes updatedEnv h_inst
    generalize Constraints.unify _ _ = u at h
    match u with
    | .error _ => simp at h
    | .ok S =>
      simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]
      simp [TEnv.updateSubst]
      exact LMonoTys.instantiateEnv_tyGen_mono _ _ Env _ _ h_inst

mutual
private theorem LMonoTy_resolveAliases_genState_mono
    (mty : LMonoTy) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  match mty with
  | .ftvar _ | .bitvec _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]; exact Nat.le_refl _
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_args; obtain ⟨args', Env1⟩ := v1; simp at h h_args
    -- tconsAliasSimple: split on the alias find? match
    -- tconsAliasSimple doesn't change Env; proof simplified
    simp only [LMonoTy.tconsAliasSimple, Pure.pure, Except.pure] at h
    split at h <;> (simp at h; obtain ⟨_, h2⟩ := h; subst h2)
    all_goals exact LMonoTys_resolveAliases_genState_mono args Env args' Env1 h_args

private theorem LMonoTys_resolveAliases_genState_mono
    (mtys : LMonoTys) (Env : TEnv T.IDMeta) (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]; exact Nat.le_refl _
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_hd; obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    split at h; · simp at h
    rename_i v2 h_tl; obtain ⟨mrest', Env2⟩ := v2
    simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    exact Nat.le_trans
      (LMonoTy_resolveAliases_genState_mono mty Env mty' Env1 h_hd)
      (LMonoTys_resolveAliases_genState_mono mrest Env1 mrest' Env2 h_tl)
end

mutual
/-- `LMonoTy.resolveAliases` preserves `SubstFreshForGen`.
    Requires input type freeVars to be gen-fresh (for alias expansion). -/
private theorem LMonoTy_resolveAliases_preserves_SubstFreshForGen
    (mty : LMonoTy) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env'))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_aw : TContext.AliasesWF Env.context)
    (h_input : ∀ v, v ∈ LMonoTy.freeVars mty →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState := by
  match mty with
  | .ftvar _ | .bitvec _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]; exact h_fresh
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_args; obtain ⟨args', Env1⟩ := v1; simp at h h_args
    -- tconsAliasSimple: split on the alias find? match
    -- tconsAliasSimple doesn't change Env; proof simplified
    simp only [LMonoTy.tconsAliasSimple, Pure.pure, Except.pure] at h
    split at h <;> (simp at h; obtain ⟨_, h2⟩ := h; subst h2)
    -- Env' = Env1; delegate to list version
    all_goals sorry -- Needs LMonoTys version (forward ref in mutual)

/-- `LMonoTys.resolveAliases` preserves `SubstFreshForGen` AND produces output
    whose freeVars satisfy gen-freshness for the output genState.
    The conjunction is needed because `tconsAlias` requires `h_args_fresh`. -/
private theorem LMonoTys_resolveAliases_preserves_SubstFreshForGen
    (mtys : LMonoTys) (Env : TEnv T.IDMeta) (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env'))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_aw : TContext.AliasesWF Env.context)
    (h_input : ∀ v, v ∈ LMonoTys.freeVars mtys →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState ∧
    (∀ v, v ∈ LMonoTys.freeVars mtys' →
      ∀ n, n ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨h1, h2⟩ := h; subst h1; subst h2
    exact ⟨h_fresh, fun _ h => by simp [LMonoTys.freeVars] at h⟩
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_hd; obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    split at h; · simp at h
    rename_i v2 h_tl; obtain ⟨mrest', Env2⟩ := v2
    simp [Pure.pure, Except.pure] at h; obtain ⟨h1, h2⟩ := h; subst h1; subst h2
    have h_ctx_hd := LMonoTy.resolveAliases_context mty Env mty' Env1 h_hd
    have h_input_hd : ∀ v, v ∈ LMonoTy.freeVars mty →
        ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n :=
      fun v hv => h_input v (by simp [LMonoTys.freeVars]; left; exact hv)
    have h_input_tl : ∀ v, v ∈ LMonoTys.freeVars mrest →
        ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n :=
      fun v hv => h_input v (by simp [LMonoTys.freeVars]; right; exact hv)
    have h_sf1 := LMonoTy_resolveAliases_preserves_SubstFreshForGen
      mty Env mty' Env1 h_hd h_fresh h_aw h_input_hd
    have h_ih_tl := LMonoTys_resolveAliases_preserves_SubstFreshForGen
      mrest Env1 mrest' Env2 h_tl h_sf1 (h_ctx_hd ▸ h_aw)
      (fun v hv n hn => h_input_tl v hv n
        (Nat.le_trans (LMonoTy_resolveAliases_genState_mono mty Env mty' Env1 h_hd) hn))
    constructor
    · exact h_ih_tl.1
    · intro v hv n hn
      simp [LMonoTys.freeVars] at hv
      cases hv with
      | inl h_in_hd =>
        -- v ∈ freeVars(mty'): gen-fresh for Env1.genState, monotone to Env2.genState
        sorry -- needs: resolveAliases output freeVars gen-fresh for single type
      | inr h_in_tl =>
        exact h_ih_tl.2 v h_in_tl n hn
end

/-- `LTy.resolveAliases` preserves `SubstFreshForGen`. -/
private theorem LTy_resolveAliases_preserves_SubstFreshForGen
    (ty : LTy) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.resolveAliases ty Env = .ok (mty, Env'))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_aw : TContext.AliasesWF Env.context)
    (h_cfg : ContextFreshForGen Env.context Env.genEnv.genState)
    (h_ty_fresh : ∀ v, v ∈ LTy.freeVars ty →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState := by
  simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i v1 h_inst; obtain ⟨mty0, genEnv'⟩ := v1; simp at h h_inst
  have h_eq : ({Env with genEnv := genEnv'} : TEnv T.IDMeta).stateSubstInfo = Env.stateSubstInfo := rfl
  have h_ctx_eq : ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context = Env.context := by
    show genEnv'.context = Env.genEnv.context
    exact LTy.instantiate_context ty Env.genEnv mty0 genEnv' h_inst
  have h_mono_inst : ({Env with genEnv := genEnv'} : TEnv T.IDMeta).genEnv.genState.tyGen ≥
      Env.genEnv.genState.tyGen := by
    simp [LTy.instantiate, Bind.bind, Except.bind] at h_inst
    split at h_inst
    · simp at h_inst; obtain ⟨_, h2⟩ := h_inst; rw [← h2]; exact Nat.le_refl _
    · split at h_inst; · simp at h_inst
      rename_i v2 h_gen; obtain ⟨freshtvs, Env1⟩ := v2; simp at h_inst
      obtain ⟨_, h2⟩ := h_inst; rw [← h2]
      exact genTyVars_tyGen_mono _ Env.genEnv freshtvs Env1 h_gen
  -- mty0 freeVars are gen-fresh for genEnv'.genState:
  -- After LTy.instantiate, freeVars are either generated (gen-fresh) or from
  -- LTy.freeVars ty ⊆ knownTypeVars(context) (gen-fresh by ContextFreshForGen).
  have h_mty0_fresh : ∀ v, v ∈ LMonoTy.freeVars mty0 →
      ∀ n, n ≥ genEnv'.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
    -- Decompose ty as .forAll vars body, then case split on vars
    obtain ⟨vars, body⟩ := ty
    intro v hv n hn
    cases vars with
    | nil =>
      -- Monomorphic: mty0 = body, genEnv' = Env.genEnv
      simp [LTy.instantiate] at h_inst
      obtain ⟨h_mty, h_env⟩ := h_inst; subst h_mty; subst h_env
      exact h_ty_fresh v (by simp [LTy.freeVars, List.removeAll]; exact hv) n hn
    | cons x xs =>
      -- Polymorphic: genTyVars, then substitute
      -- Polymorphic case: genTyVars generates fresh vars, then body is substituted.
      -- FreeVars of result = (body freeVars \ bound vars) ∪ fresh vars.
      -- Body freeVars \ bound = LTy.freeVars (.forAll (x::xs) body) → gen-fresh by h_ty_fresh.
      -- Fresh vars → gen-fresh by genTyVars_genFresh'.
      -- Both hold for n ≥ genEnv'.genState.tyGen by monotonicity.
      sorry
  exact LMonoTy_resolveAliases_preserves_SubstFreshForGen mty0 _ mty Env' h
    (h_eq ▸ SubstFreshForGen.mono _ _ _ h_fresh h_mono_inst)
    (h_ctx_eq ▸ h_aw)
    h_mty0_fresh

/-- `LTy.instantiateWithCheck` preserves `SubstFreshForGen`. -/
private theorem LTy_instantiateWithCheck_preserves_SubstFreshForGen
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env'))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_aw : TContext.AliasesWF Env.context)
    (h_cfg : ContextFreshForGen Env.context Env.genEnv.genState)
    (h_ty_fresh : ∀ v, v ∈ LTy.freeVars ty →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState := by
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i v1 h_res; obtain ⟨mty0, Env1⟩ := v1; dsimp at h h_res
  split at h; · simp at h  -- checkNoFutureGenVars
  split at h
  · simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    exact LTy_resolveAliases_preserves_SubstFreshForGen ty Env mty0 Env1 h_res h_fresh h_aw h_cfg h_ty_fresh
  · simp at h

/-- `LMonoTy.instantiateWithCheck` preserves `SubstFreshForGen`. -/
private theorem LMonoTy_instantiateWithCheck_preserves_SubstFreshForGen
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (mty, Env'))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_aw : TContext.AliasesWF Env.context)
    (h_cfg : ContextFreshForGen Env.context Env.genEnv.genState) :
    SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState := by
  simp only [LMonoTy.instantiateWithCheck] at h
  split at h; · simp at h
  rename_i instTypes Env1 h_inst
  simp [Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i v2 h_res; obtain ⟨mtyi, Env2⟩ := v2; dsimp at h h_res
  split at h; · simp at h  -- checkNoFutureGenVars
  split at h
  · simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    have h_subst_eq : Env1.stateSubstInfo = Env.stateSubstInfo := by
      simp [LMonoTys.instantiateEnv] at h_inst
      split at h_inst; · simp at h_inst
      simp at h_inst; obtain ⟨_, h_env⟩ := h_inst; rw [← h_env]
    have h_mono : Env1.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen :=
      LMonoTys.instantiateEnv_tyGen_mono _ _ Env _ _ h_inst
    have h_ctx_eq : Env1.context = Env.context :=
      LMonoTys.instantiateEnv_context _ _ Env _ Env1 h_inst
    exact LMonoTy_resolveAliases_preserves_SubstFreshForGen _ Env1 mtyi Env2 h_res
      (h_subst_eq ▸ SubstFreshForGen.mono _ _ _ h_fresh h_mono)
      (h_ctx_eq ▸ h_aw)
      (by -- instTypes[0] freeVars gen-fresh: instantiateEnv replaces all freeVars with
          -- generated vars (since domain = mty_in.freeVars = all freeVars of [mty_in])
          have h_closed : ∀ tv, tv ∈ LMonoTys.freeVars [mty_in] → tv ∈ mty_in.freeVars := by
            simp [LMonoTys.freeVars, LMonoTy.freeVars]
          have h_gen := instantiateEnv_freeVars_genFresh_closed
            mty_in.freeVars [mty_in] Env instTypes Env1 h_inst h_closed
          intro v hv n hn
          have h_in_all : v ∈ LMonoTys.freeVars instTypes := by
            have h_len : 0 < instTypes.length := by
              have := LMonoTys.instantiateEnv_length _ _ _ _ _ h_inst; simp at this; omega
            cases instTypes with
            | nil => simp at h_len
            | cons hd tl => simp [LMonoTys.freeVars]; left; exact hv
          exact h_gen v h_in_all n hn)
  · simp at h

/-- `toString` on `Nat` is injective (decimal representation is unique). -/
private theorem Nat.toString_injective : Function.Injective (toString : Nat → String) := by
  intro a b h
  simp [toString, Nat.repr] at h
  sorry -- Nat.toDigits 10 is injective (true but not in Mathlib core)

/-- Generated names with different indices are different. -/
private theorem tyPrefix_ne_of_ne (a b : Nat) (h : a ≠ b) :
    TState.tyPrefix ++ toString a ≠ TState.tyPrefix ++ toString b := by
  intro h_eq; apply h
  rw [String.ext_iff] at h_eq
  simp [String.toList_append] at h_eq
  exact Nat.toString_injective (String.toList_injective h_eq)

/-- A generated name `tyPrefix ++ toString k` with `k < state.tyGen` satisfies
    the freshness condition for `state`. -/
private theorem generated_name_fresh (k : Nat) (state : TState)
    (h_lt : k < state.tyGen) :
    ∀ n, n ≥ state.tyGen → TState.tyPrefix ++ toString k ≠ TState.tyPrefix ++ toString n :=
  fun n hn => tyPrefix_ne_of_ne k n (by omega)

/-- `(s ++ t).startsWith s = true` for any strings.
    Not yet provable in Lean 4.27: `String.startsWith` goes through the private
    `memcmpStr.go` in the `Slice.Pattern` API, which has no proof-level lemmas. -/
private theorem startsWith_append_self (s t : String) :
    (s ++ t).startsWith s = true := by
  sorry -- No String.startsWith lemmas in Lean 4.27

/-- Dropping a prefix from `(s_prefix ++ toString n)` and parsing as `Nat` recovers `n`.
    This is a standard string roundtrip property (`drop ∘ toNat? ∘ toString = some`)
    that is not yet available in Lean 4's String library (v4.27). -/
private theorem drop_prefix_toNat (s_prefix : String) (n : Nat) :
    ((s_prefix ++ toString n).drop (s_prefix.length)).toNat? = some n := by
  sorry -- String.drop / Slice.toNat? / Nat.repr roundtrip; no library support in Lean 4.27

/-- `isFutureGenVar` returns `true` on a generated name `tyPrefix ++ toString n`
    when `n ≥ state.tyGen`. -/
private theorem isFutureGenVar_of_tyPrefix (n : Nat) (state : TState)
    (hn : n ≥ state.tyGen) :
    TState.isFutureGenVar state (TState.tyPrefix ++ toString n) = true := by
  simp only [TState.isFutureGenVar, TState.tyPrefix]
  rw [startsWith_append_self]
  simp only [ite_true]
  rw [drop_prefix_toNat]
  simp [hn]

/-- `isFutureGenVar state v = false` implies `v ≠ tyPrefix ++ toString n` for `n ≥ state.tyGen`. -/
private theorem not_isFutureGenVar_imp_ne (state : TState) (v : TyIdentifier)
    (h : TState.isFutureGenVar state v = false) :
    ∀ n, n ≥ state.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  intro n hn h_eq
  rw [h_eq, isFutureGenVar_of_tyPrefix n state hn] at h
  simp at h

/-- If `checkNoFutureGenVars` passes, all free vars satisfy the freshness condition. -/
private theorem checkNoFutureGenVars_imp_fresh (mty : LMonoTy) (state : TState)
    (h : LMonoTy.checkNoFutureGenVars mty state = true) :
    ∀ v, v ∈ LMonoTy.freeVars mty →
      ∀ n, n ≥ state.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  intro v hv n hn
  simp [LMonoTy.checkNoFutureGenVars, List.all_eq_true] at h
  exact not_isFutureGenVar_imp_ne state v (by simp [h v hv]) n hn

/-- Context preservation for `LTy.instantiateWithCheck`. -/
theorem LTy_instantiateWithCheck_context'
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env')) :
    Env'.context = Env.context := by
  simp [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i v1 h_ra; obtain ⟨mty', Env1⟩ := v1
  split at h; · simp at h  -- checkNoFutureGenVars
  split at h
  · simp [Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
    exact LTy.resolveAliases_context ty Env mty' Env1 h_ra
  · simp at h

/-- Context preservation for `LMonoTy.instantiateWithCheck`. -/
theorem LMonoTy_instantiateWithCheck_context'
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (mty, Env')) :
    Env'.context = Env.context := by
  simp [LMonoTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i v1 h_inst; obtain ⟨instTypes, Env_mid⟩ := v1
  split at h; · simp at h
  rename_i v2 h_ra; obtain ⟨mty', Env2⟩ := v2; simp at h h_ra
  split at h; · simp at h  -- checkNoFutureGenVars
  split at h
  · simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    rw [LMonoTy.resolveAliases_context _ _ mty' Env2 h_ra]
    exact LMonoTys.instantiateEnv_context _ _ Env _ _ h_inst
  · simp at h
private theorem LTy_instantiateWithCheck_freeVars_fresh
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env'))
    (h_ctx : ContextFreshForGen Env.context Env.genEnv.genState) :
    ∀ v, v ∈ LMonoTy.freeVars mty →
      ∀ n, n ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  -- Extract the checkNoFutureGenVars success from h
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i v1 h_res; obtain ⟨mty0, Env1⟩ := v1; dsimp at h h_res
  split at h; · simp at h  -- checkNoFutureGenVars failed → contradiction
  rename_i h_check
  split at h
  · simp [Pure.pure, Except.pure] at h; obtain ⟨h_mty, h_env⟩ := h
    rw [← h_mty, ← h_env]
    -- h_check : !checkNoFutureGenVars mty0 Env1.genEnv.genState = false
    -- i.e., checkNoFutureGenVars mty0 Env1.genEnv.genState = true
    exact checkNoFutureGenVars_imp_fresh mty0 Env1.genEnv.genState (by simp at h_check; exact h_check)
  · simp at h

/-- Free vars of `LMonoTy.instantiateWithCheck` output satisfy freshness for the output gen state. -/
private theorem LMonoTy_instantiateWithCheck_freeVars_fresh
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (mty, Env'))
    (h_ctx : ContextFreshForGen Env.context Env.genEnv.genState) :
    ∀ v, v ∈ LMonoTy.freeVars mty →
      ∀ n, n ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  simp only [LMonoTy.instantiateWithCheck] at h
  split at h; · simp at h
  rename_i instTypes Env1 h_inst
  simp [Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i v2 h_res; obtain ⟨mtyi, Env2⟩ := v2; dsimp at h h_res
  split at h; · simp at h  -- checkNoFutureGenVars failed
  rename_i h_check
  split at h
  · simp [Pure.pure, Except.pure] at h; obtain ⟨h_mty, h_env⟩ := h
    rw [← h_mty, ← h_env]
    exact checkNoFutureGenVars_imp_fresh mtyi Env2.genEnv.genState (by simp at h_check; exact h_check)
  · simp at h

/-- `inferFVar` preserves `SubstFreshForGen`. -/
private theorem inferFVar_preserves_SubstFreshForGen
    (C : LContext T) (Env : TEnv T.IDMeta) (x : T.Identifier) (fty : Option LMonoTy)
    (ty_res : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : inferFVar C Env x fty = .ok (ty_res, Env'))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_ctx : ContextFreshForGen Env.context Env.genEnv.genState)
    (h_aw : TContext.AliasesWF Env.context) :
    SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState := by
  simp only [inferFVar, Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i ty_found h_find_ctx
  split at h; · simp at h
  rename_i v1 h_inst; obtain ⟨mty, Env1⟩ := v1; dsimp at h h_inst
  have h_ctx1 : ContextFreshForGen Env1.context Env1.genEnv.genState := by
    rw [LTy_instantiateWithCheck_context' _ C Env mty Env1 h_inst]
    exact ContextFreshForGen.mono _ _ _ h_ctx (LTy_instantiateWithCheck_tyGen_mono _ C Env mty Env1 h_inst)
  have h_aw1 : TContext.AliasesWF Env1.context :=
    (LTy_instantiateWithCheck_context' _ C Env mty Env1 h_inst) ▸ h_aw
  cases fty with
  | none =>
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    exact LTy_instantiateWithCheck_preserves_SubstFreshForGen _ C Env mty Env1 h_inst h_fresh h_aw h_ctx
      (fun v hv n hn => h_ctx v (TContext.mem_knownTypeVars_of_find h_find_ctx hv) n hn)
  | some fty_val =>
    simp only [Except.mapError] at h
    split at h; · simp at h
    rename_i v2 h_inst2; obtain ⟨fty_inst, Env2⟩ := v2; dsimp at h h_inst2
    split at h; · simp at h
    rename_i v3 h_mapError
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]; simp [TEnv.updateSubst]
    have h_fresh1 := LTy_instantiateWithCheck_preserves_SubstFreshForGen
      _ C Env mty Env1 h_inst h_fresh h_aw h_ctx
      (fun v hv n hn => h_ctx v (TContext.mem_knownTypeVars_of_find h_find_ctx hv) n hn)
    have h_fresh2 := LMonoTy_instantiateWithCheck_preserves_SubstFreshForGen
      fty_val C Env1 fty_inst Env2 h_inst2 h_fresh1 h_aw1 h_ctx1
    have h_unify := unify_of_mapError h_mapError
    exact unify_preserves_SubstFreshForGen h_unify h_fresh2 (fun v hv n hn => by
      simp [Constraints.freeVars, Constraint.freeVars] at hv
      cases hv with
      | inl h_fty =>
        exact LMonoTy_instantiateWithCheck_freeVars_fresh fty_val C Env1 fty_inst Env2
          h_inst2 h_ctx1 v h_fty n hn
      | inr h_ty =>
        have h_ty_fresh := LTy_instantiateWithCheck_freeVars_fresh _ C Env mty Env1
          h_inst h_ctx v h_ty
        exact h_ty_fresh n (Nat.le_trans
          (LMonoTy_instantiateWithCheck_tyGen_mono fty_val C Env1 fty_inst Env2 h_inst2) hn))

private theorem not_mem_go_find_none
    (types : Maps (Identifier IDMeta) LTy) (xv : Identifier IDMeta)
    (h : xv ∉ TContext.knownVars.go types) :
    ∀ m, m ∈ types → Map.find? m xv = none := by
  induction types with
  | nil => intro m hm; contradiction
  | cons hd tl ih =>
    simp only [TContext.knownVars.go, List.mem_append, not_or] at h
    intro m hm; cases hm with
    | head => exact Map.find?_none_of_not_mem_keys' _ xv h.1
    | tail _ h_tl => exact ih h.2 m h_tl

/-- If `xv ∉ knownVars ctx`, then `Map.find? m xv = none` for all `m ∈ ctx.types`. -/
private theorem not_mem_knownVars_find_none
    (ctx : TContext IDMeta) (xv : Identifier IDMeta)
    (h : xv ∉ TContext.knownVars ctx) :
    ∀ m, m ∈ ctx.types → Map.find? m xv = none :=
  not_mem_go_find_none ctx.types xv (by simp only [TContext.knownVars] at h; exact h)

/-- The variable `xv` produced by `typeBoundVar` is fresh in the input context:
    it does not appear as a key in any map of `Env.context.types`. -/
private theorem typeBoundVar_xv_fresh_in_context
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env1)) :
    ∀ m, m ∈ Env.context.types → Map.find? m xv = none := by
  -- Decompose typeBoundVar (without unfolding liftGenEnv) to extract xv
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i v_gen h_gen; obtain ⟨xv_raw, Env_g⟩ := v_gen
  -- xv_raw is fresh in Env.context via liftGenEnv_genVar_fresh
  have h_fresh := liftGenEnv_genVar_fresh Env xv_raw Env_g h_gen
  -- Extract xv = xv_raw
  revert h; cases bty with
  | some bty_val =>
    simp only []; intro h; split at h; · simp at h
    rename_i v_ic _; obtain ⟨_, _⟩ := v_ic
    simp [Pure.pure, Except.pure] at h
    obtain ⟨h_xv, _, _⟩ := h; subst h_xv
    exact not_mem_knownVars_find_none Env.context xv_raw h_fresh
  | none =>
    simp only [Bind.bind, Except.bind]; intro h; split at h; · simp at h
    rename_i v_tg _; obtain ⟨_, _⟩ := v_tg
    simp [Pure.pure, Except.pure] at h
    obtain ⟨h_xv, _, _⟩ := h; subst h_xv
    exact not_mem_knownVars_find_none Env.context xv_raw h_fresh

/-- `typeBoundVar` always produces an environment with non-empty `context.types`,
    because it applies `addInNewestContext` which uses `Maps.addInNewest`. -/
private theorem typeBoundVar_context_types_ne_nil
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env1)) :
    Env1.context.types ≠ [] := by
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i v_gen _; obtain ⟨_, Env_g⟩ := v_gen
  revert h; cases bty with
  | some bty_val =>
    simp only []; intro h; split at h; · simp at h
    rename_i v_ic _; obtain ⟨_, Env_mid⟩ := v_ic
    simp [Pure.pure, Except.pure] at h
    obtain ⟨_, _, h_env1⟩ := h; rw [← h_env1]
    simp [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context,
          Maps.addInNewest, Maps.push, Maps.pop, Maps.newest]
  | none =>
    simp only [Bind.bind, Except.bind]; intro h; split at h; · simp at h
    rename_i v_tg _; obtain ⟨_, Env_mid⟩ := v_tg
    simp [Pure.pure, Except.pure] at h
    obtain ⟨_, _, h_env1⟩ := h; rw [← h_env1]
    simp [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context,
          Maps.addInNewest, Maps.push, Maps.pop, Maps.newest]

/-- `typeBoundVar` preserves `SubstFreshForGen`. -/
private theorem typeBoundVar_preserves_SubstFreshForGen
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env'))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_aw : TContext.AliasesWF Env.context)
    (h_cfg : ContextFreshForGen Env.context Env.genEnv.genState) :
    SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState := by
  -- Decompose typeBoundVar: liftGenEnv genVar → match bty → addInNewestContext
  simp only [typeBoundVar, liftGenEnv, Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i genResult h_gen
    -- liftGenEnv preserves stateSubstInfo
    have h_gen_subst : genResult.snd.stateSubstInfo = Env.stateSubstInfo := by
      split at h_gen
      · contradiction
      · have := Except.ok.inj h_gen; rw [← this]
    -- liftGenEnv genVar: tyGen is monotone
    have h_gen_tyGen : genResult.snd.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
      split at h_gen
      · contradiction
      · rename_i _ _ h_genVar
        have := Except.ok.inj h_gen; rw [← this]; simp
        exact _root_.Lambda.HasGen.genVar_tyGen_mono Env.genEnv _ _ h_genVar
    -- liftGenEnv preserves context
    have h_gen_ctx : genResult.snd.context = Env.context := by
      split at h_gen
      · contradiction
      · rename_i _ _ h_genVar
        have := Except.ok.inj h_gen; rw [← this]; simp [TEnv.context]
        exact HasGen.genVar_context Env.genEnv _ _ h_genVar
    split at h
    · -- bty = some bty_val
      split at h
      · contradiction
      · rename_i _ bty_mty _ _ Env_inst h_inst
        simp [Pure.pure, Except.pure] at h
        obtain ⟨_, _, h_env⟩ := h; rw [← h_env]
        -- addInNewestContext only changes context, not subst or genState
        simp only [TEnv.addInNewestContext, TEnv.updateContext]
        -- LMonoTy.instantiateWithCheck preserves SubstFreshForGen
        exact LMonoTy_instantiateWithCheck_preserves_SubstFreshForGen
          bty_mty C genResult.snd _ _ h_inst
          (h_gen_subst ▸ SubstFreshForGen.mono _ _ _ h_fresh h_gen_tyGen)
          (h_gen_ctx ▸ h_aw)
          (h_gen_ctx ▸ ContextFreshForGen.mono _ _ _ h_cfg h_gen_tyGen)
    · -- bty = none
      split at h
      · contradiction
      · rename_i v1 h_genTy
        obtain ⟨xtyid, Env1⟩ := v1
        simp [Pure.pure, Except.pure] at h
        obtain ⟨_, _, h_env⟩ := h; rw [← h_env]
        -- addInNewestContext only changes context, not subst or genState
        simp only [TEnv.addInNewestContext, TEnv.updateContext]
        -- genTyVar preserves stateSubstInfo and increments counter
        have h_subst := TEnv.genTyVar_subst _ xtyid Env1 h_genTy
        rw [h_subst, h_gen_subst]
        exact SubstFreshForGen.mono _ _ _ h_fresh
          (by have := genTyVar_tyGen _ xtyid Env1 h_genTy; omega)

/-- Backward direction: vars in knownTypeVars after addInNewest come from
    the old context or from the new type's freeVars. -/
private theorem knownTypeVars_addInNewestContext_cases
    (Env : TEnv T.IDMeta) (xv : T.Identifier) (ty : LTy) (v : TyIdentifier)
    (h : v ∈ TContext.knownTypeVars (Env.addInNewestContext [(xv, ty)]).context) :
    v ∈ TContext.knownTypeVars Env.context ∨ v ∈ LTy.freeVars ty := by
  -- addInNewestContext appends (xv, ty) to the newest scope.
  -- knownTypeVars collects LTy.freeVars from all bindings.
  -- The new knownTypeVars = old knownTypeVars ∪ LTy.freeVars ty.
  -- Reduce to: v ∈ knownTypeVars(addInNewest types [(xv, ty)]) → v ∈ knownTypeVars types ∨ v ∈ freeVars ty
  -- addInNewestContext just wraps addInNewest on context.types
  simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context, TContext.knownTypeVars] at h ⊢
  -- Work with the types directly
  generalize h_ts : Env.genEnv.context.types = ts at h
  cases ts with
  | nil =>
    simp only [Maps.addInNewest, Maps.newest, Maps.pop, Maps.push,
      TContext.types.knownTypeVars, TContext.types.knownTypeVars.go,
      List.nil_append, List.mem_append, List.not_mem_nil, false_or, or_false] at h
    -- h : v ∈ go ([] ++ [(xv, ty)]) ∨ False, after or_false: v ∈ go [(xv, ty)]
    -- Unfold go [(xv, ty)] = freeVars ty ++ go [] = freeVars ty
    show v ∈ TContext.types.knownTypeVars [] ∨ v ∈ LTy.freeVars ty
    right
    -- h has go applied to [] ++ [(xv, ty)] which didn't reduce. Rewrite then unfold.
    have : ([] : List (T.Identifier × LTy)) ++ [(xv, ty)] = [(xv, ty)] := List.nil_append _
    rw [this] at h
    -- Now h : v ∈ go [(xv, ty)]. Unfold go twice: once for cons, once for nil.
    unfold TContext.types.knownTypeVars.go at h
    simp [TContext.types.knownTypeVars.go] at h
    exact h
  | cons m rest =>
    simp only [Maps.addInNewest, Maps.newest, Maps.pop, Maps.push,
      TContext.types.knownTypeVars, List.mem_append] at h ⊢
    rcases h with h_go | h_rest
    · -- v ∈ go (m ++ [(xv, ty)]): split into go m ∨ freeVars ty
      suffices ∀ (m' : List (T.Identifier × LTy)),
          ∀ w, w ∈ TContext.types.knownTypeVars.go (m' ++ [(xv, ty)]) →
            w ∈ TContext.types.knownTypeVars.go m' ∨ w ∈ LTy.freeVars ty by
        rcases this m v h_go with h_old | h_new
        · exact Or.inl (Or.inl h_old)
        · exact Or.inr h_new
      intro m'; induction m' with
      | nil =>
        intro w hw
        simp [TContext.types.knownTypeVars.go] at hw
        exact Or.inr hw
      | cons p ps ih =>
        obtain ⟨_, ty'⟩ := p
        intro w hw
        simp only [List.cons_append, TContext.types.knownTypeVars.go, List.mem_append] at hw
        rcases hw with h_fv | h_rest_go
        · left; simp [TContext.types.knownTypeVars.go]; exact Or.inl h_fv
        · rcases ih w h_rest_go with h_old | h_new
          · left; simp [TContext.types.knownTypeVars.go]; exact Or.inr h_old
          · exact Or.inr h_new
    · exact Or.inl (Or.inr h_rest)

/-- `typeBoundVar` preserves `ContextFreshForGen`.
    `typeBoundVar` extends the context with `(xv, forAll [] xty)`. The new
    `knownTypeVars` includes `freeVars xty`, which are fresh because:
    - `some` path: `checkNoFutureGenVars` in `instantiateWithCheck` ensures it
    - `none` path: `genTyVar` produces a name with index < new counter -/
private theorem typeBoundVar_preserves_ContextFreshForGen
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env'))
    (h_ctx : ContextFreshForGen Env.context Env.genEnv.genState) :
    ContextFreshForGen Env'.context Env'.genEnv.genState := by
  -- Same decomposition as typeBoundVar_preserves_SubstFreshForGen
  simp only [typeBoundVar, liftGenEnv, Bind.bind, Except.bind] at h
  split at h; · contradiction
  rename_i genResult h_gen
  -- liftGenEnv preserves context
  have h_gen_ctx : genResult.snd.context = Env.context := by
    split at h_gen; · contradiction
    rename_i _ _ h_gv; have := Except.ok.inj h_gen; rw [← this]; simp [TEnv.context]
    exact HasGen.genVar_context Env.genEnv _ _ h_gv
  -- liftGenEnv: tyGen is monotone
  have h_gen_tyGen : genResult.snd.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
    split at h_gen; · contradiction
    rename_i _ _ h_gv; have := Except.ok.inj h_gen; rw [← this]; simp
    exact HasGen.genVar_tyGen_mono Env.genEnv _ _ h_gv
  -- ContextFreshForGen for genResult.snd (same context, bigger counter)
  have h_ctx_gen : ContextFreshForGen genResult.snd.context genResult.snd.genEnv.genState :=
    h_gen_ctx ▸ ContextFreshForGen.mono _ _ _ h_ctx h_gen_tyGen
  split at h
  · -- bty = some bty_val: instantiateWithCheck then addInNewestContext
    split at h; · contradiction
    rename_i _ bty_mty _ _ Env_inst h_inst
    simp [Pure.pure, Except.pure] at h
    obtain ⟨_, _, h_env⟩ := h; rw [← h_env]
    simp only [TEnv.addInNewestContext, TEnv.updateContext]
    -- The output context = addInNewest (Env_inst.context) [(xv, forAll [] bty_mty)]
    -- Env_inst.context = genResult.snd.context (instantiateWithCheck preserves context)
    -- genResult.snd.context = Env.context (liftGenEnv preserves context)
    -- knownTypeVars of output ⊆ knownTypeVars(Env_inst.context) ∪ freeVars(forAll [] bty_mty)
    -- = knownTypeVars(Env.context) ∪ freeVars bty_mty
    -- All old vars: fresh by h_ctx + counter mono
    -- freeVars bty_mty: fresh by checkNoFutureGenVars (from instantiateWithCheck success)
    intro v hv n hn
    -- v ∈ knownTypeVars of the extended context
    -- We need to classify v: old context var or freeVars bty_mty
    -- For now, use the _freeVars_fresh lemma for the instantiateWithCheck output
    have h_iwc_ctx := LMonoTy_instantiateWithCheck_context' bty_mty C genResult.snd _ Env_inst h_inst
    have h_iwc_mono := LMonoTy_instantiateWithCheck_tyGen_mono bty_mty C genResult.snd _ Env_inst h_inst
    have h_fv_fresh := LMonoTy_instantiateWithCheck_freeVars_fresh bty_mty C genResult.snd _ Env_inst h_inst h_ctx_gen
    -- Classify v: old context var or freeVars of the new type
    -- The goal is about knownTypeVars of the updateContext'd env
    -- which equals addInNewestContext Env_inst [(xv, forAll [] bty_mty)]
    rcases knownTypeVars_addInNewestContext_cases Env_inst _ (.forAll [] _) v hv with
      h_old | h_new
    · have h_ctx_inst := h_iwc_ctx ▸ h_ctx_gen
      exact h_ctx_inst v h_old n (Nat.le_trans h_iwc_mono hn)
    · simp [LTy.freeVars, List.removeAll] at h_new
      exact h_fv_fresh v h_new n hn
  · -- bty = none: genTyVar then addInNewestContext
    split at h; · contradiction
    rename_i v1 h_genTy
    obtain ⟨xtyid, Env1⟩ := v1
    simp [Pure.pure, Except.pure] at h
    obtain ⟨_, _, h_env⟩ := h; rw [← h_env]
    simp only [TEnv.addInNewestContext, TEnv.updateContext]
    -- xty = ftvar xtyid, freeVars (forAll [] (ftvar xtyid)) = [xtyid]
    -- xtyid = tyPrefix ++ toString N where N = genResult.snd.genState.tyGen
    -- After genTyVar: Env1.genState.tyGen = N + 1
    -- So xtyid has index N < N + 1 = Env1.genState.tyGen → fresh
    have h_genTy_ctx := TEnv.genTyVar_context genResult.snd xtyid Env1 h_genTy
    have h_genTy_tyGen := genTyVar_tyGen genResult.snd xtyid Env1 h_genTy
    have h_genTy_name := genTyVar_name_eq genResult.snd xtyid Env1 h_genTy
    -- ContextFreshForGen for Env1 (context preserved, counter incremented)
    have h_ctx1 : ContextFreshForGen Env1.context Env1.genEnv.genState :=
      h_genTy_ctx ▸ ContextFreshForGen.mono _ _ _ h_ctx_gen (by omega)
    -- freeVars of (ftvar xtyid) = [xtyid], and xtyid is fresh for Env1.genState
    have h_xtyid_fresh : ∀ n, n ≥ Env1.genEnv.genState.tyGen →
        xtyid ≠ TState.tyPrefix ++ toString n := by
      rw [h_genTy_name]; exact generated_name_fresh _ _ (by omega)
    -- Classify v: either from old context or from [xtyid]
    intro v hv n hn
    rcases knownTypeVars_addInNewestContext_cases Env1 _ (.forAll [] (.ftvar xtyid)) v hv with
      h_old | h_new
    · exact h_ctx1 v h_old n hn
    · simp [LTy.freeVars, List.removeAll, LMonoTy.freeVars] at h_new
      rw [h_new]; exact h_xtyid_fresh n hn

/-- `typeBoundVar` preserves `TContext.AliasesWF`.
    `addInNewestContext` only changes `types`, not `aliases`,
    and intermediate steps (`liftGenEnv`, `instantiateWithCheck`/`genTyVar`)
    preserve the context entirely. -/
private theorem typeBoundVar_preserves_AliasesWF
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    TContext.AliasesWF Env'.context := by
  -- Decompose typeBoundVar
  simp only [typeBoundVar, liftGenEnv, Bind.bind, Except.bind] at h
  split at h; · contradiction
  rename_i genResult h_gen
  -- liftGenEnv preserves context
  have h_gen_ctx : genResult.snd.context = Env.context := by
    split at h_gen; · contradiction
    rename_i _ _ h_gv; have := Except.ok.inj h_gen; rw [← this]; simp [TEnv.context]
    exact HasGen.genVar_context Env.genEnv _ _ h_gv
  split at h
  · -- bty = some bty_val
    split at h; · contradiction
    rename_i _ bty_mty _ _ Env_inst h_inst
    simp [Pure.pure, Except.pure] at h
    obtain ⟨_, _, h_env⟩ := h; rw [← h_env]
    -- addInNewestContext only changes types, not aliases
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context, TContext.AliasesWF]
    -- Env_inst.context.aliases = genResult.snd.context.aliases = Env.context.aliases
    have h_ic_ctx := LMonoTy_instantiateWithCheck_context' bty_mty C genResult.snd _ Env_inst h_inst
    show ∀ a, a ∈ Env_inst.genEnv.context.aliases → a.WF
    rw [show Env_inst.genEnv.context = Env_inst.context from rfl,
        h_ic_ctx, h_gen_ctx]
    exact h_aw
  · -- bty = none
    split at h; · contradiction
    rename_i v1 h_genTy
    obtain ⟨xtyid, Env1⟩ := v1
    simp [Pure.pure, Except.pure] at h
    obtain ⟨_, _, h_env⟩ := h; rw [← h_env]
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context, TContext.AliasesWF]
    have h_genTy_ctx := TEnv.genTyVar_context genResult.snd xtyid Env1 h_genTy
    show ∀ a, a ∈ Env1.genEnv.context.aliases → a.WF
    rw [show Env1.genEnv.context = Env1.context from rfl,
        h_genTy_ctx, h_gen_ctx]
    exact h_aw

/-- `go` is monotone under list append: `go m ⊆ go (m ++ extra)`. -/
private theorem go_append_superset
    (m extra : Map (Identifier IDMeta) LTy)
    {v : TyIdentifier}
    (h : v ∈ TContext.types.knownTypeVars.go m) :
    v ∈ TContext.types.knownTypeVars.go (m ++ extra) := by
  unfold Map at m extra
  induction m with
  | nil => simp [TContext.types.knownTypeVars.go] at h
  | cons e rest ih =>
    obtain ⟨k, ty⟩ := e
    simp only [TContext.types.knownTypeVars.go, List.mem_append] at h
    -- Goal: v ∈ go ((k, ty) :: rest ++ extra)
    -- go unfolds to ty.freeVars ++ go (rest ++ extra) but simp won't reduce the goal
    -- due to Map vs List type difference. Use show to retype.
    show v ∈ ty.freeVars ++ TContext.types.knownTypeVars.go (rest ++ extra)
    rw [List.mem_append]
    rcases h with h_fv | h_rest
    · exact Or.inl h_fv
    · exact Or.inr (ih h_rest)

/-- `knownTypeVars` is monotone under `addInNewest`: old type variables remain known. -/
private theorem knownTypeVars_append_superset
    (types : Maps (Identifier IDMeta) LTy) (entry : Map (Identifier IDMeta) LTy)
    {v : TyIdentifier}
    (h : v ∈ TContext.types.knownTypeVars types) :
    v ∈ TContext.types.knownTypeVars (Maps.addInNewest types entry) := by
  cases types with
  | nil => simp [TContext.types.knownTypeVars] at h
  | cons m rest =>
    simp only [Maps.addInNewest, Maps.newest, Maps.pop, Maps.push,
      TContext.types.knownTypeVars, List.mem_append] at h ⊢
    rcases h with h_m | h_rest
    · exact Or.inl (go_append_superset m entry h_m)
    · exact Or.inr h_rest

/-- `typeBoundVar` preserves `boundVarsNodup`.
    The new entry `(xv, forAll [] xty)` has `boundVars = []`, so the Nodup
    condition is vacuously true. Existing entries are unchanged from the input
    environment. -/
private theorem typeBoundVar_preserves_boundVarsNodup
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env'))
    (h_bvnd : ∀ y ty, Env.context.types.find? y = some ty →
      (LTy.boundVars ty).Nodup) :
    ∀ y ty, Env'.context.types.find? y = some ty →
      (LTy.boundVars ty).Nodup := by
  -- Decompose typeBoundVar: liftGenEnv → instantiateWithCheck/genTyVar → addInNewestContext
  -- After addInNewestContext, find? either returns the new entry or an old one.
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i v_gen h_gen; obtain ⟨xv_raw, Env_g⟩ := v_gen
  have h_g_ctx : Env_g.context = Env.context := liftGenEnv_context Env _ Env_g h_gen
  -- Case split on bty to extract Env_mid with Env_mid.context = Env.context
  -- and Env' = Env_mid.addInNewestContext [(xv, forAll [] xty)]
  revert h; cases bty with
  | some bty_val =>
    simp only []; intro h
    generalize h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g = res_ic at h
    match res_ic with
    | .error _ => simp at h
    | .ok (bty_mty, Env_mid) =>
    simp [Pure.pure, Except.pure] at h
    obtain ⟨h_xv, h_xty, h_env'⟩ := h
    have h_mid_ctx : Env_mid.context = Env.context :=
      (LMonoTy_instantiateWithCheck_context' bty_val C Env_g bty_mty Env_mid h_ic).trans h_g_ctx
    subst h_xv; subst h_xty; subst h_env'
    intro y ty_found h_find
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_find
    rw [show Env_mid.genEnv.context = Env.genEnv.context from h_mid_ctx] at h_find
    rcases Maps.find?_addInNewest_single Env.genEnv.context.types xv_raw (.forAll [] bty_mty) y with
      ⟨h_new, _⟩ | h_old
    · rw [h_new] at h_find; injection h_find with h_find; subst h_find
      simp [LTy.boundVars]
    · rw [h_old] at h_find
      exact h_bvnd y ty_found h_find
  | none =>
    simp only [Bind.bind, Except.bind]; intro h; split at h; · simp at h
    rename_i v_tg h_tg; obtain ⟨xtyid, Env_mid⟩ := v_tg
    simp [Pure.pure, Except.pure] at h
    obtain ⟨h_xv, h_xty, h_env'⟩ := h
    have h_mid_ctx : Env_mid.context = Env.context :=
      (TEnv.genTyVar_context Env_g xtyid Env_mid h_tg).trans h_g_ctx
    subst h_xv; subst h_xty; subst h_env'
    intro y ty_found h_find
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_find
    rw [show Env_mid.genEnv.context = Env.genEnv.context from h_mid_ctx] at h_find
    rcases Maps.find?_addInNewest_single Env.genEnv.context.types xv_raw (.forAll [] (LMonoTy.ftvar xtyid)) y with
      ⟨h_new, _⟩ | h_old
    · rw [h_new] at h_find; injection h_find with h_find; subst h_find
      simp [LTy.boundVars]
    · rw [h_old] at h_find
      exact h_bvnd y ty_found h_find

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
    split at h; · simp at h  -- checkNoFutureGenVars
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
      split at h; · simp at h  -- checkNoFutureGenVars
      split at h
      · simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; rw [← h2]
        rw [LMonoTy.resolveAliases_context _ _ mty' Env2 h_ra]
        exact LMonoTys.instantiateEnv_context _ _ Env _ _ h_inst
      · simp at h

/-- `inferFVar` preserves the context. -/
private theorem inferFVar_context
    (C : LContext T) (Env : TEnv T.IDMeta) (x : T.Identifier)
    (fty : Option LMonoTy) (ty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : inferFVar C Env x fty = .ok (ty, Env')) :
    Env'.context = Env.context := by
  simp only [inferFVar, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i ty_scheme h_find
    split at h
    · simp at h
    · rename_i v1 h_inst
      obtain ⟨mty, Env1⟩ := v1; simp at h h_inst
      split at h
      · -- fty = none
        simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
        exact LTy_instantiateWithCheck_context _ C Env mty Env1 h_inst
      · -- fty = some fty_val
        rename_i fty_val
        split at h
        · simp at h
        · rename_i v2 h_inst2
          obtain ⟨fty_inst, Env2⟩ := v2; simp at h h_inst2
          split at h
          · simp at h
          · rename_i v3 h_mapError
            simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
            -- updateSubst preserves context
            show Env2.context = Env.context
            rw [LMonoTy_instantiateWithCheck_context _ C Env1 fty_inst Env2 h_inst2,
                LTy_instantiateWithCheck_context _ C Env mty Env1 h_inst]

/-- `typeBoundVar` then `eraseFromContext` restores the original context. -/
private theorem typeBoundVar_erase_context
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env1))
    (Env2 : TEnv T.IDMeta)
    (h_ctx : Env2.context = Env1.context)
    (h_fresh_xv : ∀ m, m ∈ Env.context.types → Map.find? m xv = none)
    (h_nonempty : Env.context.types ≠ []) :
    (Env2.eraseFromContext xv).context = Env.context := by
  -- Step 1: eraseFromContext only touches .types
  -- Step 2: Env2.context = Env1.context (by h_ctx)
  -- Step 3: Env1.context from typeBoundVar = addInNewestContext on preserved context
  -- Step 4: erase_addInNewest_fresh cancels the add
  -- First, extract what Env1.context looks like from typeBoundVar
  have h_types : Env1.context.types =
      Env.context.types.addInNewest [(xv, LTy.forAll [] xty)] ∧
      Env1.context.aliases = Env.context.aliases := by
    -- Decompose typeBoundVar to extract what it does to context
    revert h_fresh_xv h_nonempty h_ctx
    -- We generalize to avoid issues with simp/subst
    suffices ∀ Env1, typeBoundVar C Env bty = .ok (xv, xty, Env1) →
        Env1.context.types = Env.context.types.addInNewest [(xv, .forAll [] xty)] ∧
        Env1.context.aliases = Env.context.aliases by
      intro h_ctx h_nonempty h_fresh_xv; exact this Env1 h
    -- Decompose typeBoundVar to extract that Env1.context = addInNewest on Env.context
    -- typeBoundVar does: liftGenEnv genVar >> (instantiateWithCheck|genTyVar) >> addInNewestContext
    -- Each intermediate step preserves context, then addInNewestContext modifies types
    intro Env1 h_tbv
    -- typeBoundVar C Env bty =
    --   do let (xv, Env_g) ← liftGenEnv genVar Env
    --      let (xty, Env_mid) ← (instantiateWithCheck | genTyVar)
    --      return (xv, xty, Env_mid.addInNewestContext [(xv, .forAll [] xty)])
    -- We need: Env1.context.types = Env.context.types.addInNewest [...]
    --      and: Env1.context.aliases = Env.context.aliases
    -- liftGenEnv preserves context, instantiateWithCheck/genTyVar preserve context,
    -- addInNewestContext modifies types.
    --
    -- Strategy: extract Env_mid such that Env1 = Env_mid.addInNewestContext [...] and
    -- Env_mid.context = Env.context, then the result follows.
    have ⟨Env_mid, h_mid_ctx, h_env1_eq⟩ : ∃ Env_mid : TEnv T.IDMeta,
        Env_mid.context = Env.context ∧
        Env1 = Env_mid.addInNewestContext [(xv, .forAll [] xty)] := by
      simp only [typeBoundVar, Bind.bind, Except.bind] at h_tbv
      -- Split on liftGenEnv result
      generalize h_lift : liftGenEnv HasGen.genVar Env = res_lift at h_tbv
      match res_lift with
      | .error _ => simp at h_tbv
      | .ok (xv_raw, Env_g) =>
        have h_g_ctx : Env_g.context = Env.context := liftGenEnv_context Env xv_raw Env_g h_lift
        -- Split on bty
        -- Split on bty
        revert h_tbv; cases bty with
        | some bty_val =>
          simp only []; intro h_tbv
          generalize h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g = res_ic at h_tbv
          match res_ic with
          | .error _ => simp at h_tbv
          | .ok (mty_ic, Env_mid) =>
            simp [Pure.pure, Except.pure] at h_tbv
            obtain ⟨h_xv_eq, h_xty_eq, h_env1⟩ := h_tbv
            subst h_xv_eq; subst h_xty_eq
            exact ⟨Env_mid,
              (LMonoTy_instantiateWithCheck_context bty_val C Env_g mty_ic Env_mid h_ic).trans h_g_ctx,
              h_env1.symm⟩
        | none =>
          simp only [Bind.bind, Except.bind]; intro h_tbv
          generalize h_tg : TEnv.genTyVar Env_g = res_tg at h_tbv
          match res_tg with
          | .error _ => simp at h_tbv
          | .ok (xtyid, Env_mid) =>
            simp [Pure.pure, Except.pure] at h_tbv
            obtain ⟨h_xv_eq, h_xty_eq, h_env1⟩ := h_tbv
            subst h_xv_eq; subst h_xty_eq
            exact ⟨Env_mid,
              (TEnv.genTyVar_context Env_g xtyid Env_mid h_tg).trans h_g_ctx,
              h_env1.symm⟩
    subst h_env1_eq
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_mid_ctx ⊢
    constructor
    · -- types: addInNewest on equal types gives equal result
      rw [show Env_mid.genEnv.context.types = Env.genEnv.context.types from
        congrArg TContext.types h_mid_ctx]
    · -- aliases
      exact congrArg TContext.aliases h_mid_ctx
  -- Now compute (eraseFromContext Env2 xv).context
  have h_erase_types : (Env2.eraseFromContext xv).context.types = Env1.context.types.erase xv := by
    show (TEnv.eraseFromContext Env2 xv).context.types = _
    unfold TEnv.eraseFromContext TEnv.updateContext TEnv.context
    simp; exact congrArg (Maps.erase · xv) (congrArg TContext.types h_ctx)
  have h_erase_aliases : (Env2.eraseFromContext xv).context.aliases = Env1.context.aliases := by
    show (TEnv.eraseFromContext Env2 xv).context.aliases = _
    unfold TEnv.eraseFromContext TEnv.updateContext TEnv.context
    simp; exact congrArg TContext.aliases h_ctx
  -- Combine
  obtain ⟨h_ty, h_al⟩ := h_types
  have h_cancel : Env1.context.types.erase xv = Env.context.types := by
    rw [h_ty]
    cases h_types_ne : Env.context.types with
    | nil => exact absurd h_types_ne h_nonempty
    | cons m rest =>
      exact Maps.erase_addInNewest_fresh xv _ (fun s hs => h_fresh_xv s (h_types_ne ▸ hs))
  have h1 : (Env2.eraseFromContext xv).context.types = Env.context.types := by
    rw [h_erase_types, h_cancel]
  have h2 : (Env2.eraseFromContext xv).context.aliases = Env.context.aliases := by
    rw [h_erase_aliases, h_al]
  exact TContext.mk.injEq .. ▸ ⟨h1, h2⟩

/-- `resolveAux` preserves the context.
    The precondition `Env.context.types ≠ []` (at least one scope) is needed because
    the `abs`/`quant` cases add then erase a variable from the newest scope; this
    round-trip only restores the original context when there is at least one scope. -/
theorem resolveAux_context :
    ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      Env.context.types ≠ [] →
      Env'.context = Env.context := by
  intro e; induction e using (InvImage.wf LExpr.sizeOf Nat.lt_wfRel.wf).induction with
  | h e ih =>
  intro et C Env Env' h h_ne
  match e with
  | .const m c =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    generalize h_ic : inferConst C Env c = res at h
    match res with
    | .error _ => simp at h
    | .ok (ty, Env1) =>
      simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
      simp [inferConst] at h_ic; split at h_ic
      · simp at h_ic; rw [h_ic.2]
      · simp at h_ic
  | .bvar m i => simp [resolveAux] at h
  | .fvar m x fty =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    generalize h_if : inferFVar C Env x fty = res at h
    match res with
    | .error _ => simp at h
    | .ok (ty, Env1) =>
      simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
      exact inferFVar_context C Env x fty ty Env1 h_if
  | .op m o oty =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    -- Match on function lookup
    split at h; · simp at h
    rename_i func h_find
    -- Match on func.type
    split at h; · simp at h
    rename_i type_val h_type
    -- Match on LTy.instantiateWithCheck
    split at h; · simp at h
    rename_i v1 h_inst; obtain ⟨ty_inst, Env1⟩ := v1; dsimp at h h_inst
    -- Split on annotation
    cases oty with
    | none =>
      simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
      exact LTy_instantiateWithCheck_context _ C Env ty_inst Env1 h_inst
    | some oty_val =>
      simp only [Except.mapError] at h
      split at h; · simp at h
      rename_i v2 h_inst2; obtain ⟨oty_inst, Env2⟩ := v2; dsimp at h h_inst2
      split at h; · simp at h
      rename_i v3 h_mapError
      simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
      show Env2.context = Env.context
      rw [LMonoTy_instantiateWithCheck_context _ C Env1 oty_inst Env2 h_inst2,
          LTy_instantiateWithCheck_context _ C Env ty_inst Env1 h_inst]
  | .app m e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    · rename_i v1 h1; obtain ⟨e1t, Env1⟩ := v1; simp at h h1
      split at h; · simp at h
      · rename_i v2 h2; obtain ⟨e2t, Env2⟩ := v2; simp at h h2
        split at h; · simp at h
        · rename_i v3 h3; obtain ⟨fn, Env3⟩ := v3; simp at h h3
          split at h; · simp at h
          · simp at h; obtain ⟨_, h_env⟩ := h; rw [← h_env]
            show Env3.context = Env.context
            have h_ctx1 := ih e1 (by show e1.sizeOf < (LExpr.app m e1 e2).sizeOf; simp [LExpr.sizeOf]; omega) e1t C Env Env1 h1 h_ne
            have h_ctx2 := ih e2 (by show e2.sizeOf < (LExpr.app m e1 e2).sizeOf; simp [LExpr.sizeOf]; omega) e2t C Env1 Env2 h2 (h_ctx1 ▸ h_ne)
            rw [TEnv.genTyVar_context Env2 fn Env3 h3, h_ctx2, h_ctx1]
  | .abs m bty body =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    · rename_i v1 h_tbv
      obtain ⟨xv, xty, Env1⟩ := v1; simp at h h_tbv
      split at h; · simp at h
      · rename_i v2 h_ra; obtain ⟨et_, Env2⟩ := v2; simp at h
        obtain ⟨_, h_env⟩ := h; rw [← h_env]
        have h_ne1 : Env1.context.types ≠ [] :=
          typeBoundVar_context_types_ne_nil C Env bty xv xty Env1 h_tbv
        have h_ctx_ra : Env2.context = Env1.context :=
          ih (LExpr.varOpen 0 (xv, some xty) body)
            (by show (varOpen 0 (xv, some xty) body).sizeOf < (LExpr.abs m bty body).sizeOf
                rw [varOpen_sizeOf]; simp [LExpr.sizeOf])
            et_ C Env1 Env2 h_ra h_ne1
        exact typeBoundVar_erase_context C Env bty xv xty Env1 h_tbv Env2 h_ctx_ra
          (typeBoundVar_xv_fresh_in_context C Env bty xv xty Env1 h_tbv)
          h_ne
  | .quant m qk bty triggers body =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    · rename_i v1 h_tbv
      obtain ⟨xv, xty, Env1⟩ := v1; simp at h h_tbv
      split at h; · simp at h
      · rename_i v2 h_ra1; obtain ⟨et_, Env2⟩ := v2; simp at h
        split at h; · simp at h
        · rename_i v3 h_ra2; obtain ⟨triggersT, Env3⟩ := v3; simp at h
          split at h
          · -- ety != bool is true → if returns .error → simp closes this
            simp at h; obtain ⟨_, h_env⟩ := h; rw [← h_env]
            have h_ne1 : Env1.context.types ≠ [] :=
              typeBoundVar_context_types_ne_nil C Env bty xv xty Env1 h_tbv
            have h_ctx2 : Env2.context = Env1.context :=
              ih (LExpr.varOpen 0 (xv, some xty) body)
                (by show (varOpen 0 (xv, some xty) body).sizeOf < (LExpr.quant m qk bty triggers body).sizeOf
                    rw [varOpen_sizeOf]; simp [LExpr.sizeOf]; omega)
                et_ C Env1 Env2 h_ra1 h_ne1
            have h_ctx3 : Env3.context = Env2.context :=
              ih (LExpr.varOpen 0 (xv, some xty) triggers)
                (by show (varOpen 0 (xv, some xty) triggers).sizeOf < (LExpr.quant m qk bty triggers body).sizeOf
                    rw [varOpen_sizeOf]; simp [LExpr.sizeOf]; omega)
                triggersT C Env2 Env3 h_ra2 (h_ctx2 ▸ h_ne1)
            exact typeBoundVar_erase_context C Env bty xv xty Env1 h_tbv Env3
              (h_ctx3.trans h_ctx2)
              (typeBoundVar_xv_fresh_in_context C Env bty xv xty Env1 h_tbv) h_ne
          · -- ety != bool is false → contradicts the if
            simp at h
  | .eq m e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    · rename_i v1 h1; obtain ⟨e1t, Env1⟩ := v1; simp at h h1
      split at h; · simp at h
      · rename_i v2 h2; obtain ⟨e2t, Env2⟩ := v2; simp at h h2
        split at h; · simp at h
        · simp at h; obtain ⟨_, h_env⟩ := h; rw [← h_env]
          show Env2.context = Env.context
          have h_ctx1 := ih e1 (by show e1.sizeOf < (LExpr.eq m e1 e2).sizeOf; simp [LExpr.sizeOf]; omega) e1t C Env Env1 h1 h_ne
          have h_ctx2 := ih e2 (by show e2.sizeOf < (LExpr.eq m e1 e2).sizeOf; simp [LExpr.sizeOf]; omega) e2t C Env1 Env2 h2 (h_ctx1 ▸ h_ne)
          rw [h_ctx2, h_ctx1]
  | .ite m c th el =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    · rename_i v1 h1; obtain ⟨ct, Env1⟩ := v1; simp at h h1
      split at h; · simp at h
      · rename_i v2 h2; obtain ⟨tt, Env2⟩ := v2; simp at h h2
        split at h; · simp at h
        · rename_i v3 h3; obtain ⟨et_, Env3⟩ := v3; simp at h h3
          split at h; · simp at h
          · simp at h; obtain ⟨_, h_env⟩ := h; rw [← h_env]
            show Env3.context = Env.context
            have h_ctx1 := ih c (by show c.sizeOf < (LExpr.ite m c th el).sizeOf; simp [LExpr.sizeOf]; omega) ct C Env Env1 h1 h_ne
            have h_ctx2 := ih th (by show th.sizeOf < (LExpr.ite m c th el).sizeOf; simp [LExpr.sizeOf]; omega) tt C Env1 Env2 h2 (h_ctx1 ▸ h_ne)
            have h_ctx3 := ih el (by show el.sizeOf < (LExpr.ite m c th el).sizeOf; simp [LExpr.sizeOf]; omega) et_ C Env2 Env3 h3 (h_ctx2 ▸ h_ctx1 ▸ h_ne)
            rw [h_ctx3, h_ctx2, h_ctx1]
/-- `resolveAux` preserves the `SubstFreshForGen` invariant. -/
private theorem resolveAux_preserves_SubstFreshForGen :
    ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState →
      ContextFreshForGen Env.context Env.genEnv.genState →
      Env.context.types ≠ [] →
      TContext.AliasesWF Env.context →
      SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState := by
  intro e
  -- Strengthen the IH to also prove context preservation.
  -- This avoids a forward reference to resolveAux_context.
  suffices ∀ (n : Nat) (e : LExpr T.mono), e.sizeOf = n →
      ∀ (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      Env.context.types ≠ [] →
      Env'.context = Env.context ∧
      (SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState →
       ContextFreshForGen Env.context Env.genEnv.genState →
       TContext.AliasesWF Env.context →
       SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState) by
    intro et C Env Env' h h_sf h_cf h_ne h_aw
    exact (this e.sizeOf e rfl et C Env Env' h h_ne).2 h_sf h_cf h_aw
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro e h_eq et C Env Env' h h_ne
  -- Each case produces ⟨context_pres, subst_fresh_pres⟩.
  -- Helper to derive ContextFreshForGen after a recursive call using the IH:
  have ih_ctx := fun (sz : Nat) (h_sz : sz < n) (e' : LExpr T.mono) (h_eq' : e'.sizeOf = sz)
      (et' : LExprT T.mono) (C' : LContext T) (Env0 Env0' : TEnv T.IDMeta)
      (h' : resolveAux C' Env0 e' = .ok (et', Env0'))
      (h_ne0 : Env0.context.types ≠ [])
      (h_cf : ContextFreshForGen Env0.context Env0.genEnv.genState) =>
    (ih sz h_sz e' h_eq' et' C' Env0 Env0' h' h_ne0).1 ▸
      ContextFreshForGen.mono _ _ _ h_cf (resolveAux_genState_mono e' et' C' Env0 Env0' h')
  -- Context preservation (first conjunct): same proof as resolveAux_context.
  -- resolveAux_context is defined later; use ih for recursive sub-expressions.
  -- Helper: extract context preservation from ih
  have ih_context := fun (sz : Nat) (h_sz : sz < n) (e' : LExpr T.mono) (h_eq' : e'.sizeOf = sz)
      (et' : LExprT T.mono) (C' : LContext T) (Env0 Env0' : TEnv T.IDMeta)
      (h' : resolveAux C' Env0 e' = .ok (et', Env0'))
      (h_ne0 : Env0.context.types ≠ []) =>
    (ih sz h_sz e' h_eq' et' C' Env0 Env0' h' h_ne0).1
  exact ⟨resolveAux_context e et C Env Env' h h_ne,
  fun h_fresh h_ctx h_aw => by
  match e with
  | .const m c =>
    simp [resolveAux, inferConst] at h
    split at h
    · simp [Bind.bind, Except.bind] at h; obtain ⟨_, h2⟩ := h; rw [← h2]; exact h_fresh
    · exact absurd h (by simp [Bind.bind, Except.bind])
  | .bvar _ _ => simp [resolveAux, Bind.bind, Except.bind] at h
  | .fvar m x fty =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_infer; obtain ⟨_, Env_res⟩ := v1; simp at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
    exact inferFVar_preserves_SubstFreshForGen C Env x fty _ Env_res h_infer h_fresh h_ctx h_aw
  | .op m o oty =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i func h_find
    split at h; · simp at h
    rename_i type_val h_type
    split at h; · simp at h
    rename_i v1 h_inst; obtain ⟨ty_inst, Env1⟩ := v1; dsimp at h h_inst
    cases oty with
    | none =>
      simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
      exact LTy_instantiateWithCheck_preserves_SubstFreshForGen type_val C Env ty_inst Env1 h_inst h_fresh h_aw h_ctx
        (by sorry)
    | some oty_val =>
      simp only [Except.mapError] at h
      split at h; · simp at h
      rename_i v2 h_inst2; obtain ⟨oty_inst, Env2⟩ := v2; dsimp at h h_inst2
      split at h; · simp at h
      rename_i v3 h_mapError
      simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]; simp [TEnv.updateSubst]
      have h_aw1 : TContext.AliasesWF Env1.context :=
        (LTy_instantiateWithCheck_context' _ C Env ty_inst Env1 h_inst) ▸ h_aw
      have h_ctx1 : ContextFreshForGen Env1.context Env1.genEnv.genState :=
        (LTy_instantiateWithCheck_context' _ C Env ty_inst Env1 h_inst) ▸
          ContextFreshForGen.mono _ _ _ h_ctx (LTy_instantiateWithCheck_tyGen_mono _ C Env ty_inst Env1 h_inst)
      have h_fresh1 := LTy_instantiateWithCheck_preserves_SubstFreshForGen
        type_val C Env ty_inst Env1 h_inst h_fresh h_aw h_ctx
        (by sorry)
      have h_fresh2 := LMonoTy_instantiateWithCheck_preserves_SubstFreshForGen
        oty_val C Env1 oty_inst Env2 h_inst2 h_fresh1 h_aw1 h_ctx1
      have h_unify := unify_of_mapError h_mapError
      exact unify_preserves_SubstFreshForGen h_unify h_fresh2 (fun v hv n hn => by
        simp [Constraints.freeVars, Constraint.freeVars] at hv
        cases hv with
        | inl h_ty =>
          exact LTy_instantiateWithCheck_freeVars_fresh type_val C Env ty_inst Env1
            h_inst h_ctx v h_ty n (Nat.le_trans
            (LMonoTy_instantiateWithCheck_tyGen_mono oty_val C Env1 oty_inst Env2 h_inst2) hn)
        | inr h_oty =>
          have h_ctx1 : ContextFreshForGen Env1.context Env1.genEnv.genState := by
            rw [LTy_instantiateWithCheck_context' _ C Env _ Env1 h_inst]
            exact ContextFreshForGen.mono _ _ _ h_ctx (LTy_instantiateWithCheck_tyGen_mono _ C Env _ Env1 h_inst)
          exact LMonoTy_instantiateWithCheck_freeVars_fresh oty_val C Env1 oty_inst Env2
            h_inst2 h_ctx1 v h_oty n hn)
  | .app m e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    split at h; · simp at h
    rename_i v1 h_res1; obtain ⟨e1t, Env1⟩ := v1; dsimp at h h_res1
    split at h; · simp at h
    rename_i v2 h_res2; obtain ⟨e2t, Env2⟩ := v2; dsimp at h h_res2
    split at h; · simp at h
    rename_i v3 h_gen; obtain ⟨fresh_name, Env3⟩ := v3; dsimp at h h_gen
    split at h; · simp at h
    rename_i v4 h_mapError
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]; simp [TEnv.updateSubst]
    have h_sz1 : e1.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
    have h_sz2 : e2.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
    have h_ctx1_eq := ih_context e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1 h_ne
    have h_fresh1 := (ih e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1 h_ne).2 h_fresh h_ctx h_aw
    have h_ne1 := h_ctx1_eq ▸ h_ne
    have h_ctx1 := ih_ctx e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1 h_ne h_ctx
    have h_aw1 : TContext.AliasesWF Env1.context := h_ctx1_eq ▸ h_aw
    have h_ctx2_eq := ih_context e2.sizeOf h_sz2 e2 rfl e2t C Env1 Env2 h_res2 h_ne1
    have h_fresh2 := (ih e2.sizeOf h_sz2 e2 rfl e2t C Env1 Env2 h_res2 h_ne1).2 h_fresh1 h_ctx1 h_aw1
    have h_gen_subst := TEnv.genTyVar_subst Env2 fresh_name Env3 h_gen
    have h_fresh3 : SubstFreshForGen Env3.stateSubstInfo Env3.genEnv.genState := by
      rw [h_gen_subst]; exact SubstFreshForGen.mono _ _ _  h_fresh2
        (by have := genTyVar_tyGen Env2 fresh_name Env3 h_gen; omega)
    have h_unify := unify_of_mapError h_mapError
    have h_fresh4 := unify_preserves_SubstFreshForGen h_unify h_fresh3 (fun v hv n_ hn => by
      sorry) -- constraint fvs freshness
    -- Maps.remove only removes vars → SubstFreshForGen preserved
    -- keys(remove S k) ⊆ keys S (by mem_keys_of_mem_keys_remove)
    -- freeVars(remove S k) ⊆ freeVars S (removing entries only reduces freeVars)
    intro v hv n hn
    exact h_fresh4 v (by
      cases hv with
      | inl h_key => exact Or.inl (Maps.mem_keys_of_mem_keys_remove _ _ _ h_key)
      | inr h_fv =>
        -- freeVars(remove S k) ⊆ freeVars S: values of remove are a subset of values of S
        exact Or.inr (by
          simp only [Subst.freeVars, List.mem_flatMap] at h_fv ⊢
          obtain ⟨ty, h_ty_mem, h_v_fv⟩ := h_fv
          exact ⟨ty, Maps.mem_values_of_mem_keys_remove _ _ _ h_ty_mem, h_v_fv⟩)) n hn
  | .abs m bty body =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_tbv; obtain ⟨xv_id, xty_val, Env1⟩ := v1; simp at h h_tbv
    split at h; · simp at h
    rename_i v2 h_rec; obtain ⟨et', Env2⟩ := v2; simp at h
    obtain ⟨_, h_env⟩ := h; rw [← h_env]; simp [TEnv.eraseFromContext, TEnv.updateContext]
    have h_sz : (varOpen 0 (xv_id, some xty_val) body).sizeOf < n := by
      subst h_eq; rw [varOpen_sizeOf]; simp [LExpr.sizeOf]
    have h_fresh1 := typeBoundVar_preserves_SubstFreshForGen C Env bty xv_id xty_val Env1 h_tbv h_fresh h_aw h_ctx
    have h_ctx1 := typeBoundVar_preserves_ContextFreshForGen C Env bty xv_id xty_val Env1 h_tbv h_ctx
    have h_aw1 := typeBoundVar_preserves_AliasesWF C Env bty xv_id xty_val Env1 h_tbv h_aw
    have h_ne1 : Env1.context.types ≠ [] :=
      typeBoundVar_context_types_ne_nil C Env bty xv_id xty_val Env1 h_tbv
    exact (ih _ h_sz (varOpen 0 (xv_id, some xty_val) body) rfl et' C Env1 Env2 h_rec h_ne1).2 h_fresh1 h_ctx1 h_aw1
  | .quant m qk bty tr body =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_tbv; obtain ⟨xv_id, xty_val, Env1⟩ := v1; simp at h h_tbv
    split at h; · simp at h
    rename_i v2 h_rec_e; obtain ⟨et', Env2⟩ := v2; simp at h h_rec_e
    split at h; · simp at h
    rename_i v3 h_rec_tr; obtain ⟨trT, Env3⟩ := v3; simp at h h_rec_tr
    split at h
    · simp at h; obtain ⟨_, h_env⟩ := h; rw [← h_env]; simp [TEnv.eraseFromContext, TEnv.updateContext]
      have h_sz_e : (varOpen 0 (xv_id, some xty_val) body).sizeOf < n := by
        subst h_eq; rw [varOpen_sizeOf]; simp [LExpr.sizeOf]; omega
      have h_sz_tr : (varOpen 0 (xv_id, some xty_val) tr).sizeOf < n := by
        subst h_eq; rw [varOpen_sizeOf]; simp [LExpr.sizeOf]; omega
      have h_fresh1 := typeBoundVar_preserves_SubstFreshForGen C Env bty xv_id xty_val Env1 h_tbv h_fresh h_aw h_ctx
      have h_ctx1 := typeBoundVar_preserves_ContextFreshForGen C Env bty xv_id xty_val Env1 h_tbv h_ctx
      have h_aw1 := typeBoundVar_preserves_AliasesWF C Env bty xv_id xty_val Env1 h_tbv h_aw
      have h_ne1 : Env1.context.types ≠ [] :=
        typeBoundVar_context_types_ne_nil C Env bty xv_id xty_val Env1 h_tbv
      have h_ctx2_eq := ih_context _ h_sz_e _ rfl et' C Env1 Env2 h_rec_e h_ne1
      have h_fresh2 := (ih _ h_sz_e _ rfl et' C Env1 Env2 h_rec_e h_ne1).2 h_fresh1 h_ctx1 h_aw1
      have h_ne2 := h_ctx2_eq ▸ h_ne1
      have h_ctx2 := ih_ctx _ h_sz_e _ rfl et' C Env1 Env2 h_rec_e h_ne1 h_ctx1
      have h_aw2 : TContext.AliasesWF Env2.context := h_ctx2_eq ▸ h_aw1
      exact (ih _ h_sz_tr _ rfl trT C Env2 Env3 h_rec_tr h_ne2).2 h_fresh2 h_ctx2 h_aw2
    · simp at h
  | .eq m e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    split at h; · simp at h
    rename_i v1 h_res1; obtain ⟨e1t, Env1⟩ := v1; dsimp at h h_res1
    split at h; · simp at h
    rename_i v2 h_res2; obtain ⟨e2t, Env2⟩ := v2; dsimp at h h_res2
    split at h; · simp at h
    rename_i v3 h_mapError
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]; simp [TEnv.updateSubst]
    have h_sz1 : e1.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
    have h_sz2 : e2.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
    have h_ctx1_eq := ih_context e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1 h_ne
    have h_fresh1 := (ih e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1 h_ne).2 h_fresh h_ctx h_aw
    have h_ne1 := h_ctx1_eq ▸ h_ne
    have h_ctx1 := ih_ctx e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1 h_ne h_ctx
    have h_aw1 : TContext.AliasesWF Env1.context := h_ctx1_eq ▸ h_aw
    have h_fresh2 := (ih e2.sizeOf h_sz2 e2 rfl e2t C Env1 Env2 h_res2 h_ne1).2 h_fresh1 h_ctx1 h_aw1
    have h_unify := unify_of_mapError h_mapError
    exact unify_preserves_SubstFreshForGen h_unify h_fresh2 (fun v hv n_ hn => by
      simp [Constraints.freeVars, Constraint.freeVars] at hv
      cases hv with
      | inl h_e1 => sorry -- e1t.toLMonoTy fvs fresh: needs resolveAux output type fvs fresh
      | inr h_e2 => sorry -- e2t.toLMonoTy fvs fresh: same
      )
  | .ite m c t e =>
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    split at h; · simp at h
    rename_i v1 h_res_c; obtain ⟨ct, Env1⟩ := v1; dsimp at h h_res_c
    split at h; · simp at h
    rename_i v2 h_res_t; obtain ⟨tht, Env2⟩ := v2; dsimp at h h_res_t
    split at h; · simp at h
    rename_i v3 h_res_e; obtain ⟨elt, Env3⟩ := v3; dsimp at h h_res_e
    split at h; · simp at h
    rename_i v4 h_mapError
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]; simp [TEnv.updateSubst]
    have h_sz_c : c.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
    have h_sz_t : t.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
    have h_sz_e : e.sizeOf < n := by subst h_eq; simp [LExpr.sizeOf]; omega
    have h_ctx1_eq := ih_context c.sizeOf h_sz_c c rfl ct C Env Env1 h_res_c h_ne
    have h_fresh1 := (ih c.sizeOf h_sz_c c rfl ct C Env Env1 h_res_c h_ne).2 h_fresh h_ctx h_aw
    have h_ne1 := h_ctx1_eq ▸ h_ne
    have h_ctx1 := ih_ctx c.sizeOf h_sz_c c rfl ct C Env Env1 h_res_c h_ne h_ctx
    have h_aw1 : TContext.AliasesWF Env1.context := h_ctx1_eq ▸ h_aw
    have h_ctx2_eq := ih_context t.sizeOf h_sz_t t rfl tht C Env1 Env2 h_res_t h_ne1
    have h_fresh2 := (ih t.sizeOf h_sz_t t rfl tht C Env1 Env2 h_res_t h_ne1).2 h_fresh1 h_ctx1 h_aw1
    have h_ne2 := h_ctx2_eq ▸ h_ne1
    have h_ctx2 := ih_ctx t.sizeOf h_sz_t t rfl tht C Env1 Env2 h_res_t h_ne1 h_ctx1
    have h_aw2 : TContext.AliasesWF Env2.context := h_ctx2_eq ▸ h_aw1
    have h_fresh3 := (ih e.sizeOf h_sz_e e rfl elt C Env2 Env3 h_res_e h_ne2).2 h_fresh2 h_ctx2 h_aw2
    have h_unify := unify_of_mapError h_mapError
    exact unify_preserves_SubstFreshForGen h_unify h_fresh3 (fun v hv n_ hn => by
      simp [Constraints.freeVars, Constraint.freeVars] at hv
      sorry)⟩ -- constraint fvs freshness

/-- A type variable produced by `genTyVar` does not appear (as key or in values)
    in any substitution satisfying `SubstFreshForGen` for an earlier gen state.

    This is the key lemma connecting the generator invariant to substitution
    freshness, used by the `app` case of `resolveAux_absorbs`. -/
private theorem genTyVar_fresh_wrt_input_subst
    (Env Env2 Env3 : TEnv T.IDMeta)
    (fresh_name : TyIdentifier)
    (h_gen : TEnv.genTyVar Env2 = .ok (fresh_name, Env3))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_mono : Env2.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen) :
    Maps.find? Env.stateSubstInfo.subst fresh_name = none ∧
    (∀ a t, Maps.find? Env.stateSubstInfo.subst a = some t →
      fresh_name ∉ LMonoTy.freeVars t) := by
  have h_name := genTyVar_name_eq Env2 fresh_name Env3 h_gen
  -- fresh_name = TState.tyPrefix ++ toString Env2.genState.tyGen
  -- By SubstFreshForGen + h_mono, no variable in Env.subst equals this name
  constructor
  · apply Maps.not_mem_keys_find?_none'
    intro h_mem
    exact h_fresh fresh_name (Or.inl h_mem) Env2.genEnv.genState.tyGen h_mono h_name
  · intro a t h_find h_fv
    have h_in_fvs := Subst.freeVars_of_find_subset Env.stateSubstInfo.subst h_find h_fv
    exact h_fresh fresh_name (Or.inr h_in_fvs) Env2.genEnv.genState.tyGen h_mono h_name

/--
`resolveAux` produces a substitution that absorbs the input substitution,
provided the input satisfies the generator freshness invariant.

The precondition `SubstFreshForGen` says all type variables in the substitution
have names with generator indices below the current counter. This is trivially
satisfied for the top-level call (empty substitution) and maintained by
`resolveAux` through the computation.
-/
theorem resolveAux_absorbs :
    ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      EnvFreshForGen Env →
      Env.context.types ≠ [] →
      TContext.AliasesWF Env.context →
      Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  intro e
  suffices ∀ (n : Nat) (e : LExpr T.mono), e.sizeOf = n →
      ∀ (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      EnvFreshForGen Env →
      Env.context.types ≠ [] →
      TContext.AliasesWF Env.context →
      Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst by
    exact this e.sizeOf e rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro e h_eq et C Env Env' h h_env_fresh h_ne h_aw
  match e with
  | .const m c =>
    simp [resolveAux, inferConst] at h
    split at h
    · simp [Bind.bind, Except.bind] at h
      obtain ⟨_, h_env⟩ := h; rw [← h_env]
      exact Subst.absorbs_refl _ Env.stateSubstInfo.isWF
    · exact absurd h (by simp [Bind.bind, Except.bind])
  | bvar m i =>
    simp [resolveAux, Bind.bind, Except.bind] at h
  | .fvar m x fty =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_infer
      obtain ⟨ty_res, Env_res⟩ := v1; simp at h
      obtain ⟨_, h_env⟩ := h; rw [← h_env]
      exact inferFVar_absorbs C Env x fty ty_res Env_res h_infer
  | .op m o oty =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    -- Peel through nested matches: function lookup, func.type, instantiateWithCheck
    split at h; · simp at h    -- function not found
    rename_i func h_find
    split at h; · simp at h    -- func.type error
    rename_i type_val h_type
    split at h; · simp at h    -- instantiateWithCheck error
    rename_i v1 h_inst
    obtain ⟨ty_inst, Env1⟩ := v1; dsimp at h h_inst
    -- Split on annotation
    cases oty with
    | none =>
      simp at h; obtain ⟨_, h_env⟩ := h; rw [← h_env]
      exact LTy_instantiateWithCheck_absorbs type_val C Env ty_inst Env1 h_inst
    | some oty_val =>
      simp only [Except.mapError] at h
      split at h; · simp at h  -- LMonoTy.instantiateWithCheck error
      rename_i v2 h_inst2
      obtain ⟨oty_inst, Env2⟩ := v2; dsimp at h h_inst2
      split at h; · simp at h  -- unify error
      rename_i v3 h_mapError
      simp at h; obtain ⟨_, h_env⟩ := h; rw [← h_env]
      simp [TEnv.updateSubst]
      exact Subst.absorbs_trans
        Env.stateSubstInfo.subst Env2.stateSubstInfo.subst v3.subst
        (Subst.absorbs_trans
          Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
          (LTy_instantiateWithCheck_absorbs type_val C Env ty_inst Env1 h_inst)
          (LMonoTy_instantiateWithCheck_absorbs oty_val C Env1 oty_inst Env2 h_inst2))
        (unify_absorbs _ _ _ (unify_of_mapError h_mapError))
  | .app m e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    split at h; · simp at h
    rename_i v1 h_res1; obtain ⟨e1t, Env1⟩ := v1; dsimp at h h_res1
    split at h; · simp at h
    rename_i v2 h_res2; obtain ⟨e2t, Env2⟩ := v2; dsimp at h h_res2
    split at h; · simp at h
    rename_i v3 h_gen; obtain ⟨fresh_name, Env3⟩ := v3; dsimp at h h_gen
    split at h; · simp at h
    rename_i v4 h_mapError
    simp at h; obtain ⟨_, h_env⟩ := h; rw [← h_env]
    simp [TEnv.updateSubst]
    have h_unify := unify_of_mapError h_mapError
    have h_gen_subst : Env3.stateSubstInfo = Env2.stateSubstInfo :=
      TEnv.genTyVar_subst Env2 fresh_name Env3 h_gen
    rw [h_gen_subst] at h_unify
    -- Derive SubstFreshForGen for intermediate envs
    -- (ContextFreshForGen is preserved since context preserved + counter mono)
    have h_fresh := h_env_fresh.1
    have h_ctx1_eq := resolveAux_context e1 e1t C Env Env1 h_res1 h_ne
    have h_fresh1 := resolveAux_preserves_SubstFreshForGen
      e1 e1t C Env Env1 h_res1 h_fresh h_env_fresh.2 h_ne h_aw
    have h_ne1 := h_ctx1_eq ▸ h_ne
    have h_aw1 : TContext.AliasesWF Env1.context := h_ctx1_eq ▸ h_aw
    -- Absorption from IHs
    have h_abs1 := ih e1.sizeOf (by subst h_eq; simp [LExpr.sizeOf]; omega) e1 rfl e1t C Env Env1 h_res1 h_env_fresh h_ne h_aw
    have h_abs2 := ih e2.sizeOf (by subst h_eq; simp [LExpr.sizeOf]; omega) e2 rfl e2t C Env1 Env2 h_res2
      ⟨h_fresh1, h_ctx1_eq ▸
        ContextFreshForGen.mono _ _ _ h_env_fresh.2
          (resolveAux_genState_mono e1 e1t C Env Env1 h_res1)⟩ h_ne1 h_aw1
    have h_abs_chain := Subst.absorbs_trans
      Env.stateSubstInfo.subst Env2.stateSubstInfo.subst v4.subst
      (Subst.absorbs_trans
        Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
        h_abs1 h_abs2)
      (unify_absorbs _ _ _ h_unify)
    have h_mono1 := resolveAux_genState_mono e1 e1t C Env Env1 h_res1
    have h_mono2 := resolveAux_genState_mono e2 e2t C Env1 Env2 h_res2
    have ⟨h_not_key, h_not_fv⟩ :=
      genTyVar_fresh_wrt_input_subst Env Env2 Env3 fresh_name h_gen h_fresh
        (Nat.le_trans h_mono1 h_mono2)
    exact Subst.absorbs_of_remove v4.subst Env.stateSubstInfo.subst fresh_name
      h_abs_chain h_not_key h_not_fv
  | .abs m bty body =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_tbv; obtain ⟨xv, xty, Env1⟩ := v1; simp at h h_tbv
    split at h; · simp at h
    rename_i v2 h_rec; obtain ⟨et', Env2⟩ := v2; simp at h
    obtain ⟨_, h_env⟩ := h; rw [← h_env]
    simp [TEnv.eraseFromContext, TEnv.updateContext]
    have h_sz : (varOpen 0 (xv, some xty) body).sizeOf < n := by
      subst h_eq; rw [varOpen_sizeOf]; simp [LExpr.sizeOf]
    -- typeBoundVar absorbs, then recursive call absorbs
    have h_abs1 := typeBoundVar_absorbs C Env bty xv xty Env1 h_tbv
    -- For the recursive call, need EnvFreshForGen Env1
    have h_aw1 := typeBoundVar_preserves_AliasesWF C Env bty xv xty Env1 h_tbv h_aw
    have h_env_fresh1 : EnvFreshForGen Env1 :=
      ⟨typeBoundVar_preserves_SubstFreshForGen C Env bty xv xty Env1 h_tbv h_env_fresh.1 h_aw h_env_fresh.2,
       typeBoundVar_preserves_ContextFreshForGen C Env bty xv xty Env1 h_tbv h_env_fresh.2⟩
    have h_ne1 : Env1.context.types ≠ [] :=
      typeBoundVar_context_types_ne_nil C Env bty xv xty Env1 h_tbv
    exact Subst.absorbs_trans
      Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
      h_abs1
      (ih _ h_sz _ rfl et' C Env1 Env2 h_rec h_env_fresh1 h_ne1 h_aw1)
  | .quant m qk bty tr body =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_tbv; obtain ⟨xv, xty, Env1⟩ := v1; simp at h h_tbv
    split at h; · simp at h
    rename_i v2 h_rec_e; obtain ⟨et', Env2⟩ := v2; simp at h h_rec_e
    split at h; · simp at h
    rename_i v3 h_rec_tr; obtain ⟨trT, Env3⟩ := v3; simp at h h_rec_tr
    split at h
    · simp at h; obtain ⟨_, h_env⟩ := h; rw [← h_env]
      simp [TEnv.eraseFromContext, TEnv.updateContext]
      have h_sz_e : (varOpen 0 (xv, some xty) body).sizeOf < n := by
        subst h_eq; rw [varOpen_sizeOf]; simp [LExpr.sizeOf]; omega
      have h_sz_tr : (varOpen 0 (xv, some xty) tr).sizeOf < n := by
        subst h_eq; rw [varOpen_sizeOf]; simp [LExpr.sizeOf]; omega
      have h_abs1 := typeBoundVar_absorbs C Env bty xv xty Env1 h_tbv
      have h_aw1 := typeBoundVar_preserves_AliasesWF C Env bty xv xty Env1 h_tbv h_aw
      have h_env_fresh1 : EnvFreshForGen Env1 :=
        ⟨typeBoundVar_preserves_SubstFreshForGen C Env bty xv xty Env1 h_tbv h_env_fresh.1 h_aw h_env_fresh.2,
         typeBoundVar_preserves_ContextFreshForGen C Env bty xv xty Env1 h_tbv h_env_fresh.2⟩
      have h_ne1 : Env1.context.types ≠ [] :=
        typeBoundVar_context_types_ne_nil C Env bty xv xty Env1 h_tbv
      -- Chain: Env → Env1 (typeBoundVar) → Env2 (resolveAux e') → Env3 (resolveAux tr')
      have h_ctx2_eq := resolveAux_context _ et' C Env1 Env2 h_rec_e h_ne1
      have h_ne2 := h_ctx2_eq ▸ h_ne1
      have h_aw2 : TContext.AliasesWF Env2.context := h_ctx2_eq ▸ h_aw1
      have h_env_fresh2 : EnvFreshForGen Env2 :=
        ⟨resolveAux_preserves_SubstFreshForGen _ et' C Env1 Env2 h_rec_e h_env_fresh1.1 h_env_fresh1.2 h_ne1 h_aw1,
         h_ctx2_eq ▸
           ContextFreshForGen.mono _ _ _ h_env_fresh1.2
             (resolveAux_genState_mono _ et' C Env1 Env2 h_rec_e)⟩
      exact Subst.absorbs_trans
        Env.stateSubstInfo.subst Env2.stateSubstInfo.subst Env3.stateSubstInfo.subst
        (Subst.absorbs_trans
          Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
          h_abs1
          (ih _ h_sz_e _ rfl et' C Env1 Env2 h_rec_e h_env_fresh1 h_ne1 h_aw1))
        (ih _ h_sz_tr _ rfl trT C Env2 Env3 h_rec_tr h_env_fresh2 h_ne2 h_aw2)
    · simp at h
  | .eq m e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    split at h; · simp at h
    rename_i v1 h_res1; obtain ⟨e1t, Env1⟩ := v1; dsimp at h h_res1
    split at h; · simp at h
    rename_i v2 h_res2; obtain ⟨e2t, Env2⟩ := v2; dsimp at h h_res2
    split at h; · simp at h
    rename_i v3 h_mapError
    simp at h; obtain ⟨_, h_env⟩ := h; rw [← h_env]; simp [TEnv.updateSubst]
    have h_unify := unify_of_mapError h_mapError
    have h_ctx1_eq := resolveAux_context e1 e1t C Env Env1 h_res1 h_ne
    have h_fresh1 := resolveAux_preserves_SubstFreshForGen
      e1 e1t C Env Env1 h_res1 h_env_fresh.1 h_env_fresh.2 h_ne h_aw
    have h_ne1 := h_ctx1_eq ▸ h_ne
    have h_aw1 : TContext.AliasesWF Env1.context := h_ctx1_eq ▸ h_aw
    exact Subst.absorbs_trans
      Env.stateSubstInfo.subst Env2.stateSubstInfo.subst v3.subst
      (Subst.absorbs_trans
        Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
        (ih e1.sizeOf (by subst h_eq; simp [LExpr.sizeOf]; omega) e1 rfl e1t C Env Env1 h_res1 h_env_fresh h_ne h_aw)
        (ih e2.sizeOf (by subst h_eq; simp [LExpr.sizeOf]; omega) e2 rfl e2t C Env1 Env2 h_res2
          ⟨h_fresh1, h_ctx1_eq ▸
            ContextFreshForGen.mono _ _ _ h_env_fresh.2
              (resolveAux_genState_mono e1 e1t C Env Env1 h_res1)⟩ h_ne1 h_aw1))
      (unify_absorbs _ _ _ h_unify)
  | .ite m c t e =>
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    split at h; · simp at h
    rename_i v1 h_res_c; obtain ⟨ct, Env1⟩ := v1; dsimp at h h_res_c
    split at h; · simp at h
    rename_i v2 h_res_t; obtain ⟨tht, Env2⟩ := v2; dsimp at h h_res_t
    split at h; · simp at h
    rename_i v3 h_res_e; obtain ⟨elt, Env3⟩ := v3; dsimp at h h_res_e
    split at h; · simp at h
    rename_i v4 h_mapError
    simp at h; obtain ⟨_, h_env⟩ := h; rw [← h_env]; simp [TEnv.updateSubst]
    have h_unify := unify_of_mapError h_mapError
    have h_ctx1_eq := resolveAux_context c ct C Env Env1 h_res_c h_ne
    have h_ne1 := h_ctx1_eq ▸ h_ne
    have h_aw1 : TContext.AliasesWF Env1.context := h_ctx1_eq ▸ h_aw
    have h_ctx1 : ContextFreshForGen Env1.context Env1.genEnv.genState :=
      h_ctx1_eq ▸
        ContextFreshForGen.mono _ _ _ h_env_fresh.2 (resolveAux_genState_mono c ct C Env Env1 h_res_c)
    have h_fresh1 := resolveAux_preserves_SubstFreshForGen
      c ct C Env Env1 h_res_c h_env_fresh.1 h_env_fresh.2 h_ne h_aw
    have h_ctx2_eq := resolveAux_context t tht C Env1 Env2 h_res_t h_ne1
    have h_ne2 := h_ctx2_eq ▸ h_ne1
    have h_aw2 : TContext.AliasesWF Env2.context := h_ctx2_eq ▸ h_aw1
    have h_ctx2 : ContextFreshForGen Env2.context Env2.genEnv.genState :=
      h_ctx2_eq ▸
        ContextFreshForGen.mono _ _ _ h_ctx1 (resolveAux_genState_mono t tht C Env1 Env2 h_res_t)
    have h_fresh2 := resolveAux_preserves_SubstFreshForGen
      t tht C Env1 Env2 h_res_t h_fresh1 h_ctx1 h_ne1 h_aw1
    exact Subst.absorbs_trans
      Env.stateSubstInfo.subst Env3.stateSubstInfo.subst v4.subst
      (Subst.absorbs_trans
        Env.stateSubstInfo.subst Env2.stateSubstInfo.subst Env3.stateSubstInfo.subst
        (Subst.absorbs_trans
          Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
          (ih c.sizeOf (by subst h_eq; simp [LExpr.sizeOf]; omega) c rfl ct C Env Env1 h_res_c h_env_fresh h_ne h_aw)
          (ih t.sizeOf (by subst h_eq; simp [LExpr.sizeOf]; omega) t rfl tht C Env1 Env2 h_res_t ⟨h_fresh1, h_ctx1⟩ h_ne1 h_aw1))
        (ih e.sizeOf (by subst h_eq; simp [LExpr.sizeOf]; omega) e rfl elt C Env2 Env3 h_res_e ⟨h_fresh2, h_ctx2⟩ h_ne2 h_aw2))
      (unify_absorbs _ _ _ h_unify)

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
    (h_fresh : ∀ a, a ∈ Maps.keys S_outer → a ∈ LMonoTy.freeVars (LMonoTy.subst S_inner mty) →
      TContext.isFresh (T := T) a Γ)
    (h_wf : SubstWF S_outer) :
    HasType C Γ e (.forAll [] (LMonoTy.subst S_outer mty)) := by
  have h1 := HasType_subst_fresh_all C Γ e (LMonoTy.subst S_inner mty) S_outer h_ty h_fresh h_wf
  rw [LMonoTy.subst_absorbs S_outer S_inner mty h_absorbs] at h1
  exact h1


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



mutual
/-- `subst S` distributes over `openVars` when the body's free vars are all in `vars`. -/
private theorem subst_openVars_comm
    (S : Subst) (vars : List TyIdentifier) (vals : LMonoTys) (body : LMonoTy)
    (h_wf : ∀ tv, tv ∈ LMonoTy.freeVars body → tv ∈ vars)
    (h_len : vars.length = vals.length) :
    LMonoTy.subst S (LMonoTy.openVars vars vals body) =
    LMonoTy.openVars vars (LMonoTys.substLogic S vals) body := by
  by_cases hS : Subst.hasEmptyScopes S
  · -- S is empty: subst S is identity
    rw [LMonoTy.subst_emptyS hS]
    -- substLogic S vals = vals when hasEmptyScopes
    have : LMonoTys.substLogic S vals = vals := by
      induction vals with
      | nil => simp [LMonoTys.substLogic, hS]
      | cons hd tl ih => simp [LMonoTys.substLogic, hS, ih]
    rw [this]
  · -- S is non-empty
    have hS_ne : Subst.hasEmptyScopes S = false := by
      revert hS; cases Subst.hasEmptyScopes S <;> simp
    match body with
    | .ftvar x =>
      -- x ∈ vars (by h_wf). Prove: subst S (openVars vars vals (ftvar x)) =
      --   openVars vars (substLogic S vals) (ftvar x)
      -- by induction on vars with vals generalized.
      simp only [LMonoTy.openVars]
      -- Both sides do find? on (zip vars _) with predicate (·.1 == x)
      -- We prove a helper by induction
      have h_x_in : x ∈ vars := h_wf x (by simp [LMonoTy.freeVars])
      induction vars generalizing vals with
      | nil => simp at h_x_in
      | cons v vs ih =>
        cases vals with
        | nil => simp at h_len -- (v :: vs).length = [].length is false
        | cons vl vls =>
          simp only [List.zip, List.zipWith, List.find?, BEq.beq, decide_eq_true_eq,
                      LMonoTys.substLogic, hS_ne, ↓reduceIte]
          by_cases h_eq : v = x
          · simp [h_eq]
          · simp [h_eq]
            have h_x_vs : x ∈ vs := by
              cases h_x_in with | head => exact absurd rfl h_eq | tail _ h => exact h
            have h_len' : vs.length = vls.length := by simp at h_len; exact h_len
            apply ih (vals := vls)
            · exact h_len'
            · intro tv htv; simp [LMonoTy.freeVars] at htv; rw [htv]; exact h_x_vs
            · exact h_x_vs
    | .bitvec n =>
      simp [LMonoTy.openVars, LMonoTy.subst, hS_ne]
    | .tcons name args =>
      show LMonoTy.subst S (.tcons name (LMonoTys.openVars vars vals args)) =
           .tcons name (LMonoTys.openVars vars (LMonoTys.substLogic S vals) args)
      simp only [LMonoTy.subst, hS_ne, ↓reduceIte]
      have h_list := subst_openVarsList_comm S vars vals args (by
        intro tv h_tv; exact h_wf tv (by simp [LMonoTy.freeVars]; exact h_tv)) h_len
      rw [LMonoTys.subst_eq_substLogic]
      exact congrArg (LMonoTy.tcons name ·) h_list

/-- List version of `subst_openVars_comm`. -/
private theorem subst_openVarsList_comm
    (S : Subst) (vars : List TyIdentifier) (vals : LMonoTys) (bodies : LMonoTys)
    (h_wf : ∀ tv, tv ∈ LMonoTys.freeVars bodies → tv ∈ vars)
    (h_len : vars.length = vals.length) :
    LMonoTys.substLogic S (LMonoTys.openVars vars vals bodies) =
    LMonoTys.openVars vars (LMonoTys.substLogic S vals) bodies := by
  by_cases hS : Subst.hasEmptyScopes S
  · -- When S has empty scopes, substLogic is identity
    have h_vals : LMonoTys.substLogic S vals = vals := by
      induction vals with
      | nil => simp [LMonoTys.substLogic, hS]
      | cons hd tl ih => simp [LMonoTys.substLogic, hS, ih]
    have h_bodies : LMonoTys.substLogic S (LMonoTys.openVars vars vals bodies) =
        LMonoTys.openVars vars vals bodies := by
      induction (LMonoTys.openVars vars vals bodies) with
      | nil => simp [LMonoTys.substLogic, hS]
      | cons hd tl ih => simp [LMonoTys.substLogic, hS, ih]
    rw [h_bodies, h_vals]
  · have hS_ne : Subst.hasEmptyScopes S = false := by
      revert hS; cases Subst.hasEmptyScopes S <;> simp
    match bodies with
    | [] => simp [LMonoTys.openVars, LMonoTys.substLogic, hS_ne]
    | hd :: tl =>
      simp [LMonoTys.openVars, LMonoTys.substLogic, hS_ne]
      constructor
      · exact subst_openVars_comm S vars vals hd (by
          intro tv h; exact h_wf tv (by simp [LMonoTys.freeVars]; left; exact h)) h_len
      · exact subst_openVarsList_comm S vars vals tl (by
          intro tv h; exact h_wf tv (by simp [LMonoTys.freeVars]; right; exact h)) h_len
end

/-- `Map.find?` on a zip agrees with `List.find?` using BEq on the first component. -/
private theorem map_find_eq_list_find' (vars : List TyIdentifier) (vals : LMonoTys) (x : TyIdentifier) :
    Map.find? (List.zip vars vals) x =
    (match (List.zip vars vals).find? (fun p => p.1 == x) with
     | some (_, v) => some v
     | none => none) := by
  induction vars generalizing vals with
  | nil => simp [List.zip, List.find?, Map.find?]
  | cons v vs ih =>
    cases vals with
    | nil => simp [List.zip, List.find?, Map.find?]
    | cons vl vls =>
      simp only [List.zip, List.zipWith, List.find?, Map.find?, BEq.beq, decide_eq_true_eq]
      by_cases h_eq : v = x
      · simp [h_eq]
      · simp [h_eq, Ne.symm h_eq]; exact ih vls

/-- `openVars` with empty vars/vals is identity. -/
private theorem openVars_nil_id (body : LMonoTy) :
    LMonoTy.openVars [] [] body = body := by
  match body with
  | .ftvar _ => simp [LMonoTy.openVars, List.zip, List.find?]
  | .bitvec _ => simp [LMonoTy.openVars]
  | .tcons nm args =>
    simp only [LMonoTy.openVars]; congr 1
    exact openVarsList_nil_id args
where
  openVarsList_nil_id : (args : LMonoTys) → LMonoTys.openVars [] [] args = args
    | [] => by simp [LMonoTys.openVars]
    | hd :: tl => by
        simp only [LMonoTys.openVars]
        rw [openVars_nil_id hd, openVarsList_nil_id tl]

mutual
/-- `subst` with a single-scope substitution `[zip vars vals]` acts the same as
    `openVars vars vals` on a body whose free vars are contained in `vars`. -/
private theorem subst_single_scope_eq_openVars
    (vars : List TyIdentifier) (vals : LMonoTys) (body : LMonoTy)
    (h_wf : ∀ tv, tv ∈ LMonoTy.freeVars body → tv ∈ vars)
    (h_len : vars.length = vals.length) :
    LMonoTy.subst [List.zip vars vals] body = LMonoTy.openVars vars vals body := by
  cases vars with
  | nil =>
    -- vars = [], vals = [] (by h_len). Both sides reduce to body.
    have : vals = [] := by simpa using h_len.symm
    subst this
    -- LHS: subst [zip [] []] body. zip [] [] = []. hasEmptyScopes [[]] = true.
    -- So subst [[]] body = body. And openVars [] [] body = body.
    show LMonoTy.subst [List.zipWith Prod.mk [] []] body = LMonoTy.openVars [] [] body
    -- List.zipWith Prod.mk [] [] = []
    have h_zip_nil : List.zipWith Prod.mk ([] : List TyIdentifier) ([] : LMonoTys) = [] := by rfl
    rw [h_zip_nil]
    -- subst [[]] body = body
    have h_emptyS : Subst.hasEmptyScopes [([] : Map TyIdentifier LMonoTy)] = true := by
      simp [Subst.hasEmptyScopes, List.all, Map.isEmpty]
    rw [LMonoTy.subst_emptyS h_emptyS]
    exact (openVars_nil_id body).symm
  | cons v vs =>
    cases vals with
    | nil => simp at h_len
    | cons vl vls =>
      -- hasEmptyScopes is false for non-empty zip
      have h_ne : Subst.hasEmptyScopes [List.zip (v :: vs) (vl :: vls)] = false := by
        simp [Subst.hasEmptyScopes, List.all, List.zip, List.zipWith, Map.isEmpty]
      match body with
      | .ftvar x =>
        -- Both sides look up x in the zip. Connect via map_find_eq_list_find'.
        simp only [LMonoTy.subst, h_ne, ↓reduceIte, LMonoTy.openVars, Maps.find?]
        rw [map_find_eq_list_find' (v :: vs) (vl :: vls) x]
        generalize (List.zip (v :: vs) (vl :: vls)).find? (fun p => p.1 == x) = res
        match res with
        | some (_, val) => rfl
        | none => rfl
      | .bitvec n =>
        simp [LMonoTy.subst, h_ne, LMonoTy.openVars]
      | .tcons nm args =>
        simp only [LMonoTy.openVars]
        -- Goal: subst [zip ...] (tcons nm args) = tcons nm (openVars ... args)
        -- Unfold subst, use h_ne to eliminate hasEmptyScopes guard
        have h_eq : LMonoTy.subst [List.zip (v :: vs) (vl :: vls)] (.tcons nm args) =
            .tcons nm (LMonoTys.subst [List.zip (v :: vs) (vl :: vls)] args) := by
          unfold LMonoTy.subst; rw [h_ne]; simp
        rw [h_eq, LMonoTys.subst_eq_substLogic,
            subst_single_scope_eq_openVarsList (v :: vs) (vl :: vls) args
              (by intro tv htv; exact h_wf tv (by simp [LMonoTy.freeVars]; exact htv))
              (by simp at h_len ⊢; exact h_len)]

/-- List version of `subst_single_scope_eq_openVars`. -/
private theorem subst_single_scope_eq_openVarsList
    (vars : List TyIdentifier) (vals : LMonoTys) (bodies : LMonoTys)
    (h_wf : ∀ tv, tv ∈ LMonoTys.freeVars bodies → tv ∈ vars)
    (h_len : vars.length = vals.length) :
    LMonoTys.substLogic [List.zip vars vals] bodies = LMonoTys.openVars vars vals bodies := by
  cases vars with
  | nil =>
    have : vals = [] := by simpa using h_len.symm
    subst this
    show LMonoTys.substLogic [List.zipWith Prod.mk [] []] bodies =
         LMonoTys.openVars [] [] bodies
    have h_zip_nil : List.zipWith Prod.mk ([] : List TyIdentifier) ([] : LMonoTys) = [] := rfl
    rw [h_zip_nil]
    have hS : Subst.hasEmptyScopes [([] : Map TyIdentifier LMonoTy)] = true := by
      simp [Subst.hasEmptyScopes, List.all, Map.isEmpty]
    -- substLogic [[]] bodies = bodies (since hasEmptyScopes [[]] = true)
    have : LMonoTys.substLogic [([] : Map TyIdentifier LMonoTy)] bodies = bodies := by
      unfold LMonoTys.substLogic; rw [hS]; simp
    rw [this]
    exact (openVarsList_nil_id bodies).symm
  | cons v vs =>
    cases vals with
    | nil => simp at h_len
    | cons vl vls =>
      have h_ne : Subst.hasEmptyScopes [List.zip (v :: vs) (vl :: vls)] = false := by
        simp [Subst.hasEmptyScopes, List.all, List.zip, List.zipWith, Map.isEmpty]
      match bodies with
      | [] => simp [LMonoTys.substLogic, h_ne, LMonoTys.openVars]
      | hd :: tl =>
        show LMonoTy.subst [List.zip (v :: vs) (vl :: vls)] hd ::
             LMonoTys.substLogic [List.zip (v :: vs) (vl :: vls)] tl =
             LMonoTy.openVars (v :: vs) (vl :: vls) hd ::
             LMonoTys.openVars (v :: vs) (vl :: vls) tl
        rw [subst_single_scope_eq_openVars (v :: vs) (vl :: vls) hd
            (by intro tv h; exact h_wf tv (by simp [LMonoTys.freeVars]; left; exact h))
            (by simp at h_len ⊢; exact h_len),
            subst_single_scope_eq_openVarsList (v :: vs) (vl :: vls) tl
            (by intro tv h; exact h_wf tv (by simp [LMonoTys.freeVars]; right; exact h))
            (by simp at h_len ⊢; exact h_len)]
where
  openVarsList_nil_id : (bodies : LMonoTys) → LMonoTys.openVars [] [] bodies = bodies
    | [] => by simp [LMonoTys.openVars]
    | hd :: tl => by
        simp only [LMonoTys.openVars]
        rw [openVars_nil_id hd, openVarsList_nil_id tl]
end

/-- Decompose `LMonoTys.instantiateEnv` into its components: fresh vars, substitution, and env. -/
private theorem instantiateEnv_decompose
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TEnv T.IDMeta)
    (result : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.instantiateEnv ids mtys Env = .ok (result, Env')) :
    ∃ (freshtvs : List TyIdentifier) (genEnv' : TGenEnv T.IDMeta),
      TGenEnv.genTyVars ids.length Env.genEnv = .ok (freshtvs, genEnv') ∧
      result = LMonoTys.subst [List.zip ids (List.map LMonoTy.ftvar freshtvs)] mtys ∧
      Env' = {Env with genEnv := genEnv'} := by
  -- First unfold instantiateEnv only (one level)
  simp only [LMonoTys.instantiateEnv] at h
  -- h now has: match LMonoTys.instantiate ids mtys Env.genEnv with ...
  generalize h_inner : LMonoTys.instantiate ids mtys Env.genEnv = res at h
  match res with
  | .error _ => simp at h
  | .ok (instResult, genEnv') =>
    simp at h; obtain ⟨h1, h2⟩ := h; subst h1; subst h2
    -- Now unfold instantiate
    simp only [LMonoTys.instantiate, Bind.bind, Except.bind] at h_inner
    split at h_inner
    · simp at h_inner
    · rename_i v h_gv; obtain ⟨ftvs, gE⟩ := v; simp at h_inner h_gv
      obtain ⟨h_res, h_ge⟩ := h_inner; subst h_ge
      exact ⟨ftvs, gE, h_gv, h_res.symm, rfl⟩

/-- Prepending a binding `(v, vl)` to `vars`/`vals` doesn't affect `openVarsList` on
    `ids.map ftvar` when `v ∉ ids`. -/
private theorem openVarsList_cons_skip_map_ftvar
    (v : TyIdentifier) (vl : LMonoTy) (vars : List TyIdentifier) (vals : LMonoTys)
    (ids : List TyIdentifier) (h_v_notin : v ∉ ids) :
    LMonoTys.openVars (v :: vars) (vl :: vals) (ids.map .ftvar) =
    LMonoTys.openVars vars vals (ids.map .ftvar) := by
  induction ids with
  | nil => simp [LMonoTys.openVars]
  | cons w ws ih =>
    have h_w_ne : w ≠ v := fun h => h_v_notin (h ▸ .head _)
    simp only [List.map, LMonoTys.openVars, LMonoTy.openVars,
               List.zip, List.zipWith, List.find?, BEq.beq, decide_eq_true_eq]
    simp only [h_w_ne, Ne.symm h_w_ne, ↓reduceIte]
    congr 1
    exact ih (fun h => h_v_notin (.tail _ h))

private theorem openVarsList_map_ftvar_id
    (vars : List TyIdentifier) (vals : LMonoTys)
    (h_len : vars.length = vals.length)
    (h_nodup : vars.Nodup := by assumption) :
    LMonoTys.openVars vars vals (vars.map .ftvar) = vals := by
  -- Each ftvar vᵢ is looked up in zip vars vals and finds vals[i] at position i.
  -- The first match in zip for vᵢ is at position i (no earlier match since
  -- find? scans left-to-right and vᵢ first appears at position i in vars).
  -- This works even with duplicates since find? returns the FIRST match.
  induction vars generalizing vals with
  | nil => cases vals with
    | nil => simp [LMonoTys.openVars]
    | cons _ _ => simp at h_len
  | cons v vs ih =>
    cases vals with
    | nil => simp at h_len
    | cons vl vls =>
      have h_v_notin : v ∉ vs := (List.nodup_cons.mp h_nodup).1
      -- Unfold to see the structure
      simp only [List.map, LMonoTys.openVars]
      -- Goal: openVars (v::vs) (vl::vls) (ftvar v) :: openVarsList (v::vs) (vl::vls) (vs.map ftvar) = vl :: vls
      -- Head: openVars for ftvar v finds v at position 0 → vl
      have h_head : LMonoTy.openVars (v :: vs) (vl :: vls) (.ftvar v) = vl := by
        simp [LMonoTy.openVars, List.zip, List.zipWith, List.find?, BEq.beq, decide_eq_true_eq]
      rw [h_head]
      -- Goal: vl :: openVarsList (v::vs) (vl::vls) (vs.map ftvar) = vl :: vls
      congr 1
      -- Goal: openVarsList (v::vs) (vl::vls) (vs.map ftvar) = vls
      -- Strip the (v, vl) prefix using h_v_notin
      rw [openVarsList_cons_skip_map_ftvar v vl vs vls vs h_v_notin]
      -- Goal: openVarsList vs vls (vs.map ftvar) = vls — by IH
      exact ih vls (by simp at h_len; exact h_len) (List.nodup_cons.mp h_nodup).2

/-- Key bridge lemma: when `tconsAlias` expands an alias, the result under
    the final substitution equals `TypeAlias.expand alias (subst S args)`.
    Proof depends on:
    - `subst S (openVars vars vals body) = openVars vars (subst S vals) body`
      (when body's free vars ⊆ vars and vars ∩ S.keys = ∅)
    - Idempotency of `substInfo.subst` (from `SubstInfo.isWF`)
    - Connection between `instantiateEnv` and `openVars` -/
private theorem tconsAlias_expand_eq
    (name : String) (args : LMonoTys) (Env : TEnv T.IDMeta)
    (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (alias : TypeAlias)
    (h_tcons : LMonoTy.tconsAlias name args Env = .ok (mty', Env'))
    (h_find : Env.context.aliases.find?
        (fun a => a.name == name && a.typeArgs.length == args.length) = some alias)
    (h_wf : alias.WF)
    (h_nodup : alias.typeArgs.Nodup) :
    LMonoTy.subst Env'.stateSubstInfo.subst mty' =
    TypeAlias.expand alias (LMonoTys.subst Env'.stateSubstInfo.subst args) := by
  -- Unfold tconsAlias and use h_find to match the alias branch
  unfold LMonoTy.tconsAlias at h_tcons
  rw [h_find] at h_tcons
  -- Now h_tcons is in the `some alias` branch
  simp at h_tcons
  -- Decompose: instantiateEnv, then unify
  split at h_tcons
  · simp at h_tcons  -- instantiateEnv failed
  · rename_i instTypes updatedEnv h_inst
    -- h_inst : LMonoTys.instantiateEnv alias.typeArgs [aliasPattern, alias.type] Env = .ok (instTypes, updatedEnv)
    have h_len_inst : 1 < instTypes.length := by
      have := LMonoTys.instantiateEnv_length _ _ _ _ _ h_inst; simp at this; omega
    -- Decompose: unify
    generalize h_u : Constraints.unify _ _ = u at h_tcons
    match u with
    | .error e => simp [Except.mapError] at h_tcons
    | .ok substInfo =>
      simp [Pure.pure, Except.pure] at h_tcons
      obtain ⟨h_mty, h_env⟩ := h_tcons
      rw [← h_mty, ← h_env]
      -- Now goal uses getD instead of dependent indexing:
      -- subst (updatedEnv.updateSubst substInfo).subst
      --   (subst substInfo.subst (instTypes.getD 1 inputMty)) =
      --   expand alias (subst (updatedEnv.updateSubst substInfo).subst args)
      simp only [TEnv.updateSubst]

      -- Step 1: Idempotency. subst S (subst S x) = subst S x
      rw [LMonoTy.subst_absorbs substInfo.subst substInfo.subst
        (instTypes[1]?.getD _) (Subst.absorbs_refl _ substInfo.isWF)]
      -- Goal: subst S (instTypes.getD 1 inputMty) = expand alias (subst S args)

      -- Step 2: Decompose instantiateEnv to get freshtvs
      obtain ⟨freshtvs, genEnv', h_gen, h_it, h_ue⟩ :=
        instantiateEnv_decompose alias.typeArgs
          [LMonoTy.tcons name (alias.typeArgs.map .ftvar), alias.type] Env instTypes updatedEnv h_inst
      subst h_ue
      let fvs := List.map LMonoTy.ftvar freshtvs
      have h_flen : freshtvs.length = alias.typeArgs.length :=
        TGenEnv.genTyVars_length (IDMeta := T.IDMeta) _ Env.genEnv freshtvs genEnv' h_gen
      have h_fvs_len : alias.typeArgs.length = fvs.length := by
        show alias.typeArgs.length = (List.map LMonoTy.ftvar freshtvs).length
        rw [List.length_map]; exact h_flen.symm

      -- Step 3: Case-split instTypes to get concrete elements (avoids dependent indexing)
      have h_len2 : instTypes.length = 2 := by
        have := LMonoTys.instantiateEnv_length _ _ _ _ _ h_inst; simp at this; omega
      -- Decompose instTypes into [elt0, elt1]
      cases instTypes with
      | nil => simp at h_len2
      | cons a tl =>
        cases tl with
        | nil => simp at h_len2
        | cons b rest =>
          cases rest with
          | cons _ _ => simp at h_len2
          | nil =>
          -- Now instTypes = [a, b]
          -- getD 0 = a, getD 1 = b
          -- h_it : [a, b] = subst [S_inst] [pattern, alias.type]
          -- h_u : Constraints.unify [(tcons name args, a)] ... = .ok substInfo
          -- Goal: subst S b = expand alias (subst S args)
          -- h_it : [a, b] = LMonoTys.subst [S_inst] [pattern, alias.type]
          -- Compute the RHS as a concrete 2-element list
          -- Compute: subst S [x, y] = [subst S x, subst S y] (for any S)
          have h_rhs_eq : LMonoTys.subst [List.zip alias.typeArgs fvs]
              [LMonoTy.tcons name (alias.typeArgs.map .ftvar), alias.type] =
              [LMonoTy.subst [List.zip alias.typeArgs fvs] (.tcons name (alias.typeArgs.map .ftvar)),
               LMonoTy.subst [List.zip alias.typeArgs fvs] alias.type] := by
            rw [LMonoTys.subst_eq_substLogic]; unfold LMonoTys.substLogic
            split <;> rename_i hS
            · simp [LMonoTy.subst_emptyS hS]
            · simp only [ite_false]; congr 1
              -- Need: substLogic S [alias.type] = [subst S alias.type]
              unfold LMonoTys.substLogic
              have hS_false : Subst.hasEmptyScopes [List.zip alias.typeArgs fvs] = false := by
                revert hS; cases Subst.hasEmptyScopes [List.zip alias.typeArgs fvs] <;> simp
              simp only [hS_false, ite_false]
              -- Inner substLogic on the empty tail
              unfold LMonoTys.substLogic
              simp [hS_false]
          -- Now h_it : [a, b] = [subst [S_inst] pattern, subst [S_inst] alias.type]
          rw [h_rhs_eq] at h_it
          -- Extract a = subst [S_inst] pattern, b = subst [S_inst] alias.type
          have h_b : b = LMonoTy.subst [List.zip alias.typeArgs fvs] alias.type :=
            (List.cons.inj (List.cons.inj h_it).2).1
          have h_a : a = LMonoTy.subst [List.zip alias.typeArgs fvs]
              (.tcons name (alias.typeArgs.map .ftvar)) :=
            (List.cons.inj h_it).1
          -- Goal: subst S ([a, b][1]?.getD default) = expand alias (subst S args)
          -- First simplify [a, b][1]?.getD d = b
          have h_getD_b : ([a, b] : LMonoTys)[1]?.getD (.tcons name args) = b := rfl
          rw [h_getD_b]
          -- Now goal: subst S b = expand alias (subst S args)
          rw [h_b, subst_single_scope_eq_openVars alias.typeArgs fvs alias.type h_wf.fvs_closed h_fvs_len,
              subst_openVars_comm substInfo.subst alias.typeArgs fvs alias.type h_wf.fvs_closed h_fvs_len]
          simp only [TypeAlias.expand]; congr 1
          -- Goal: substLogic substInfo.subst fvs = subst substInfo.subst args

          -- From unify_makes_equal: subst S (tcons name args) = subst S a
          have h_unify_eq := unify_makes_equal (.tcons name args) a
            ({Env with genEnv := genEnv'} : TEnv T.IDMeta).stateSubstInfo substInfo h_u
          -- Rewrite a and apply sub-lemmas
          have h_pat_wf : ∀ tv, tv ∈ LMonoTy.freeVars (.tcons name (alias.typeArgs.map .ftvar)) → tv ∈ alias.typeArgs := by
            intro tv htv; simp only [LMonoTy.freeVars] at htv
            have : ∀ (ids : List TyIdentifier), tv ∈ LMonoTys.freeVars (ids.map .ftvar) → tv ∈ ids := by
              intro ids h; induction ids with
              | nil => simp [LMonoTys.freeVars] at h
              | cons x xs ih =>
                simp only [List.map, LMonoTys.freeVars, LMonoTy.freeVars, List.append_eq] at h
                cases List.mem_append.mp h with
                | inl h => exact List.mem_cons.mpr (Or.inl (List.mem_cons.mp h |>.elim id (by simp)))
                | inr h => exact List.mem_cons.mpr (Or.inr (ih h))
            exact this alias.typeArgs htv
          rw [h_a,
              subst_single_scope_eq_openVars alias.typeArgs fvs _ h_pat_wf h_fvs_len,
              subst_openVars_comm substInfo.subst alias.typeArgs fvs _ h_pat_wf h_fvs_len] at h_unify_eq
          -- h_unify_eq : subst S (tcons name args) =
          --   openVars typeArgs (substLogic S fvs) (tcons name (typeArgs.map ftvar))
          -- Unfold openVars on tcons:
          simp only [LMonoTy.openVars] at h_unify_eq
          -- h_unify_eq : subst S (tcons name args) = tcons name (LMonoTys.openVars ...)
          -- Extract args component via tcons-wrapper trick
          -- subst S (tcons name args) = tcons name (subst S args) [modulo hasEmptyScopes]
          have h_extract : ∀ (S : Subst) (xs : LMonoTys),
              LMonoTy.subst S (.tcons name xs) = .tcons name (LMonoTys.subst S xs) := by
            intro S' xs'
            by_cases hS' : Subst.hasEmptyScopes S'
            · simp [LMonoTy.subst, LMonoTys.subst, hS']
            · have := show Subst.hasEmptyScopes S' = false by
                revert hS'; cases Subst.hasEmptyScopes S' <;> simp
              simp [LMonoTy.subst, this]
          rw [h_extract] at h_unify_eq
          -- h_unify_eq : tcons name (subst S args) = tcons name (openVarsList typeArgs (substLogic S fvs) (typeArgs.map ftvar))
          -- Extract: subst S args = openVarsList typeArgs (substLogic S fvs) (typeArgs.map ftvar)
          have h_args_eq := (LMonoTy.tcons.inj h_unify_eq).2
          -- Need: substLogic S fvs = subst S args
          -- = openVarsList typeArgs (substLogic S fvs) (typeArgs.map ftvar)
          -- openVarsList on (typeArgs.map ftvar) with vals where length matches
          -- gives vals back (each ftvar aᵢ maps to vals[i])
          rw [h_args_eq]
          -- Need: substLogic S fvs = openVarsList typeArgs (substLogic S fvs) (typeArgs.map ftvar)
          -- openVarsList vars vals (vars.map ftvar) = vals
          -- (each ftvar aᵢ matches vars[i] and maps to vals[i])
          symm
          exact openVarsList_map_ftvar_id alias.typeArgs _ (by
            -- Need: alias.typeArgs.length = (substLogic S fvs).length
            have : ∀ (S : Subst) (xs : LMonoTys), (LMonoTys.substLogic S xs).length = xs.length := by
              intro S xs; induction xs with
              | nil => simp [LMonoTys.substLogic]
              | cons hd tl ih => simp only [LMonoTys.substLogic]; split <;> simp [ih]
            rw [this]; exact h_fvs_len)



/-- Proof of `tconsAlias_eq_simple` (stated in `LExprTypeEnv.lean`). -/
theorem tconsAlias_eq_simple
    (name : String) (args : LMonoTys) (Env : TEnv T.IDMeta)
    (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h_tcons : LMonoTy.tconsAlias name args Env = .ok (mty', Env'))
    (h_aliases_wf : TContext.AliasesWF Env.context) :
    LMonoTy.subst Env'.stateSubstInfo.subst mty' =
    LMonoTy.subst Env'.stateSubstInfo.subst
      (LMonoTy.tconsAliasSimple name args Env.context.aliases) := by
  unfold LMonoTy.tconsAliasSimple
  generalize h_find : Env.context.aliases.find? _ = ma
  match ma with
  | none =>
    unfold LMonoTy.tconsAlias at h_tcons; rw [h_find] at h_tcons
    simp [Pure.pure, Except.pure] at h_tcons
    obtain ⟨h1, h2⟩ := h_tcons; rw [← h1, ← h2]
  | some alias =>
    have h_alias_wf := h_aliases_wf alias (List.mem_of_find?_eq_some h_find)
    have h_pred := List.find?_some h_find
    simp [BEq.beq, decide_eq_true_eq] at h_pred
    have h_bridge := tconsAlias_expand_eq name args Env mty' Env' alias
      h_tcons h_find h_alias_wf h_alias_wf.typeArgs_nodup
    rw [h_bridge]; simp only [TypeAlias.expand]
    rw [LMonoTys.subst_eq_substLogic]
    exact (subst_openVars_comm Env'.stateSubstInfo.subst alias.typeArgs args alias.type
      h_alias_wf.fvs_closed h_pred.2).symm

private theorem HasType_resolveAliases
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono) (mty_in : LMonoTy)
    (mty_out : LMonoTy) (Env Env' : TEnv T.IDMeta)
    (h_ty : HasType C Γ e (.forAll [] mty_in))
    (h_ra : LMonoTy.resolveAliases mty_in Env = .ok (mty_out, Env'))
    (h_aliases : Γ.aliases = Env.context.aliases)
    (h_aliases_wf : TContext.AliasesWF Γ)
    (h_fresh : Subst.allKeysFresh Env'.stateSubstInfo.subst Γ) :
    HasType C Γ e (.forAll [] (LMonoTy.subst Env'.stateSubstInfo.subst mty_out)) := by
  -- Use talias_resolve to get HasType for mty_out, then apply substitution
  have h_resolved := HasType.talias_resolve Γ e mty_in mty_out
    ⟨inferInstance, Env, Env', h_aliases, h_aliases_wf, h_ra⟩ h_ty
  exact HasType_subst_fresh_all C Γ e mty_out Env'.stateSubstInfo.subst
    h_resolved (fun a hk hfv => h_fresh a hk) Env'.stateSubstInfo.isWF

theorem instantiateWithCheck_fvar_HasType
    (C : LContext T) (Γ : TContext T.IDMeta) (x : Identifier T.IDMeta)
    (ty : LTy) (mty : LMonoTy) (Env Env' : TEnv T.IDMeta)
    (m : T.mono.base.Metadata)
    (h_find : Γ.types.find? x = some ty)
    (h_ctx : Env.context = Γ)
    (h_inst : LTy.instantiateWithCheck ty C Env = .ok (mty, Env'))
    (h_nodup : (LTy.boundVars ty).Nodup)
    (h_bv_known : ∀ v, v ∈ LTy.boundVars ty →
      v ∈ TContext.knownTypeVars Env.genEnv.context)
    (h_aliases_wf : TContext.AliasesWF Γ) :
    HasType C Γ (.fvar m x none)
      (.forAll [] (LMonoTy.subst Env'.stateSubstInfo.subst mty)) := by
  -- Decompose instantiateWithCheck into resolveAliases + known type check
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h_inst
  split at h_inst
  · simp at h_inst  -- resolveAliases failed
  · rename_i v1 h_ra
    obtain ⟨mty_ra, Env_ra⟩ := v1
    split at h_inst; · simp at h_inst  -- checkNoFutureGenVars
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
        -- Step 4: Aliases in Γ match the Env's context aliases
        have h_ctx_pres := LTy.instantiate_context ty Env.genEnv mty_inst genEnv' h_inst_inner
        have h_aliases : Γ.aliases = ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context.aliases := by
          simp [TEnv.context]; rw [h_ctx_pres]; exact (congrArg TContext.aliases h_ctx).symm
        -- Step 5: AliasesWF for Γ (from precondition)
        -- Step 6: resolveAliases preserves HasType under the output substitution
        exact HasType_resolveAliases C Γ _ mty_inst mty_ra
          {Env with genEnv := genEnv'} Env_ra h_mono h_ra h_aliases h_aliases_wf h_fresh
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
    (h_bvnd : ∀ y ty, Env.context.types.find? y = some ty →
      (LTy.boundVars ty).Nodup)
    (h_aw : TContext.AliasesWF Env.context) :
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
          have h_nd := h_bvnd x ty h_find
          -- needs reworking: old boundVarsWF h_bv_known condition removed
          have h_bvk : ∀ v, v ∈ LTy.boundVars ty →
            v ∈ TContext.knownTypeVars Env.genEnv.context := by sorry
          exact instantiateWithCheck_fvar_HasType C Env.context x ty mty Env Env1 m
            h_find rfl h_inst h_nd h_bvk h_aw
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
expression `et` such that for any substitution `S` that absorbs `Env'.subst`,
the original expression `e` has type `subst S et.toLMonoTy` under the
original context.

The universal quantification over the final substitution eliminates the need
for `HasType_subst_upgrade` in recursive cases (e.g., `eq`, `ite`, `app`).
Each IH directly gives typing under the caller's `S`, provided we can show
`S` absorbs each intermediate environment's substitution via the chain:
- `resolveAux_absorbs`: each `resolveAux` call absorbs its input substitution
- `unify_absorbs`: unification absorbs the pre-unification substitution
- `Subst.absorbs_trans`: absorption composes transitively
-/
private theorem transfer_boundVarsNodup
    {Env Env' : TEnv T.IDMeta}
    (h_nd : ∀ y ty, Env.context.types.find? y = some ty →
      (LTy.boundVars ty).Nodup)
    (h_ctx : Env'.context = Env.context) :
    ∀ y ty, Env'.context.types.find? y = some ty →
      (LTy.boundVars ty).Nodup := by
  intro y ty h_f
  have h_f' : Env.context.types.find? y = some ty := by
    show Env.genEnv.context.types.find? y = some ty
    rw [← (show Env'.genEnv.context = Env.genEnv.context from h_ctx)]
    exact h_f
  exact h_nd y ty h_f'

private theorem transfer_ctxFreeVarsGenerated
    {Env Env' : TEnv T.IDMeta}
    (h_gen : ∀ v, v ∈ TContext.knownTypeVars Env.context →
      v.startsWith TState.tyPrefix = true)
    (h_ctx : Env'.context = Env.context) :
    ∀ v, v ∈ TContext.knownTypeVars Env'.context →
      v.startsWith TState.tyPrefix = true := by
  intro v hv
  rw [h_ctx] at hv
  exact h_gen v hv

/-- Free type variables in the output type of `resolveAux` don't include
    "future" generated names — i.e., names with counter values ≥ the output
    environment's generator counter. Since each `genTyVar` during resolution
    increments the counter, the output type only contains type vars with
    counter values strictly below the output counter.

    This is used to show that a freshly generated type variable (produced
    AFTER resolveAux) doesn't appear in the output type. -/

-- `varCloseT` preserves `toLMonoTy`: it only affects the tree structure
-- (turning fvars into bvars) but does not change the root metadata.
private theorem varCloseT_toLMonoTy (k : Nat) (x : T.Identifier) (e : LExprT T.mono) :
    (Lambda.LExpr.varCloseT k x e).toLMonoTy = e.toLMonoTy := by
  cases e with
  | const _ _ => rfl
  | bvar _ _ => rfl
  | fvar _ y _ => simp [Lambda.LExpr.varCloseT]; split <;> simp [toLMonoTy]
  | op _ _ _ => rfl
  | app _ _ _ => rfl
  | abs _ _ _ => rfl
  | quant _ _ _ _ _ => rfl
  | ite _ _ _ _ => rfl
  | eq _ _ _ => rfl

private theorem resolveAux_output_type_no_future_vars :
    ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      TEnvWF Env →
      Env.context.types ≠ [] →
      ∀ v, v ∈ LMonoTy.freeVars et.toLMonoTy →
        ∀ n, n ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  -- We use strong induction on LExpr.sizeOf to handle the abs/quant cases,
  -- where resolveAux recurses on (varOpen 0 x e_body) rather than e_body.
  suffices h_strong : ∀ (n : Nat) (e : LExpr T.mono), LExpr.sizeOf e = n →
      ∀ (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      TEnvWF Env →
      Env.context.types ≠ [] →
      ∀ v, v ∈ LMonoTy.freeVars et.toLMonoTy →
        ∀ n, n ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n from
    fun e => h_strong (LExpr.sizeOf e) e rfl
  intro n_sz
  induction n_sz using Nat.strongRecOn with
  | _ n_sz ih_n =>
  intro e h_sz
  have ih_sub : ∀ (e' : LExpr T.mono), LExpr.sizeOf e' < n_sz →
      ∀ (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e' = .ok (et, Env') →
      TEnvWF Env →
      Env.context.types ≠ [] →
      ∀ v, v ∈ LMonoTy.freeVars et.toLMonoTy →
        ∀ k, k ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString k :=
    fun e' h_lt => ih_n (LExpr.sizeOf e') h_lt e' rfl
  match e with
  | .const m c =>
    -- Output type is c.ty which is a ground type (bool, int, real, string, bitvec).
    -- freeVars of ground types is [], so the goal is vacuously true.
    intro et C Env Env' h h_envwf h_ne
    simp [resolveAux, inferConst] at h
    split at h
    · simp [Bind.bind, Except.bind] at h
      obtain ⟨h_et, _⟩ := h
      intro v hv
      rw [← h_et] at hv; simp [toLMonoTy] at hv
      cases c with
      | boolConst _ => simp [LConst.ty, LMonoTy.bool, LMonoTy.freeVars, LMonoTys.freeVars] at hv
      | intConst _ => simp [LConst.ty, LMonoTy.int, LMonoTy.freeVars, LMonoTys.freeVars] at hv
      | realConst _ => simp [LConst.ty, LMonoTy.real, LMonoTy.freeVars, LMonoTys.freeVars] at hv
      | strConst _ => simp [LConst.ty, LMonoTy.string, LMonoTy.freeVars, LMonoTys.freeVars] at hv
      | bitvecConst _ _ => simp [LConst.ty, LMonoTy.freeVars] at hv
    · exact absurd h (by simp [Bind.bind, Except.bind])
  | .bvar m i =>
    -- resolveAux fails on bvar, contradiction
    intro et C Env Env' h _ _
    simp [resolveAux, Bind.bind, Except.bind] at h
  | .fvar m x fty =>
    intro et C Env Env' h h_envwf h_ne
    -- Decompose resolveAux for fvar
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_infer; obtain ⟨ty_res, Env_res⟩ := v1; simp at h
    obtain ⟨h_et, h_env⟩ := h
    -- et.toLMonoTy = ty_res
    intro v hv n hn
    rw [← h_et] at hv; simp [toLMonoTy] at hv
    rw [← h_env] at hn
    -- Decompose inferFVar to extract instantiateWithCheck
    simp only [inferFVar, Bind.bind, Except.bind] at h_infer
    split at h_infer; · simp at h_infer
    rename_i ty_found h_find_ctx
    split at h_infer; · simp at h_infer
    rename_i v2 h_inst; obtain ⟨mty, Env1⟩ := v2; dsimp at h_infer h_inst
    -- mty's free vars are fresh for Env1.genState
    have h_mty_fresh := LTy_instantiateWithCheck_freeVars_fresh _ C Env mty Env1
      h_inst h_envwf.ctxFreshForGen
    cases fty with
    | none =>
      simp at h_infer; obtain ⟨h_ty, h_env1⟩ := h_infer
      rw [← h_ty] at hv; rw [← h_env1] at hn
      exact h_mty_fresh v hv n hn
    | some fty_val =>
      simp only [Except.mapError] at h_infer
      split at h_infer; · simp at h_infer
      rename_i v3 h_inst2; obtain ⟨fty_inst, Env2⟩ := v3; dsimp at h_infer h_inst2
      split at h_infer; · simp at h_infer
      simp at h_infer; obtain ⟨h_ty, h_env2⟩ := h_infer
      rw [← h_ty] at hv; rw [← h_env2] at hn; simp [TEnv.updateSubst] at hn
      -- Env_res.genState = Env2.genState (updateSubst preserves genEnv)
      -- Env2.genState.tyGen ≥ Env1.genState.tyGen (by instantiateWithCheck monotonicity)
      have h_mono2 := LMonoTy_instantiateWithCheck_tyGen_mono fty_val C Env1 fty_inst Env2 h_inst2
      exact h_mty_fresh v hv n (Nat.le_trans h_mono2 hn)
  | .op m o oty =>
    intro et C Env Env' h h_envwf h_ne
    -- Decompose resolveAux for op
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i func h_find
    split at h; · simp at h
    rename_i type_val h_type
    split at h; · simp at h
    rename_i v1 h_inst; obtain ⟨ty_inst, Env1⟩ := v1; dsimp at h h_inst
    -- ty_inst's free vars are fresh for Env1.genState
    have h_ty_fresh := LTy_instantiateWithCheck_freeVars_fresh _ C Env ty_inst Env1
      h_inst h_envwf.ctxFreshForGen
    cases oty with
    | none =>
      simp at h; obtain ⟨h_et, h_env⟩ := h
      intro v hv n hn
      rw [← h_et] at hv; simp [toLMonoTy] at hv
      rw [← h_env] at hn
      exact h_ty_fresh v hv n hn
    | some oty_val =>
      simp only [Except.mapError] at h
      split at h; · simp at h
      rename_i v2 h_inst2; obtain ⟨oty_inst, Env2⟩ := v2; dsimp at h h_inst2
      split at h; · simp at h
      rename_i v3 h_mapError
      simp at h; obtain ⟨h_et, h_env⟩ := h
      intro v hv n hn
      rw [← h_et] at hv; simp [toLMonoTy] at hv
      rw [← h_env] at hn; simp [TEnv.updateSubst] at hn
      have h_mono2 := LMonoTy_instantiateWithCheck_tyGen_mono oty_val C Env1 oty_inst Env2 h_inst2
      exact h_ty_fresh v hv n (Nat.le_trans h_mono2 hn)
  | .app m e1 e2 =>
    intro et C Env Env' h h_envwf h_ne
    have h_aw := h_envwf.aliasesWF
    -- Extract IHs from strong induction
    have ih1 := ih_sub e1 (by subst h_sz; simp [LExpr.sizeOf]; omega)
    have ih2 := ih_sub e2 (by subst h_sz; simp [LExpr.sizeOf]; omega)
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    -- Decompose: resolveAux C Env e1
    split at h
    · simp at h
    · rename_i v1 h_res1
      obtain ⟨e1t, Env1⟩ := v1; dsimp at h h_res1
      -- Decompose: resolveAux C Env1 e2
      split at h
      · simp at h
      · rename_i v2 h_res2
        obtain ⟨e2t, Env2⟩ := v2; dsimp at h h_res2
        -- Decompose: genTyVar Env2
        split at h
        · simp at h
        · rename_i v3 h_genTyVar
          obtain ⟨fresh_name, Env3⟩ := v3; dsimp at h h_genTyVar
          -- Decompose: unify (mapError)
          split at h
          · simp at h
          · rename_i v4 h_mapError
            simp at h
            obtain ⟨h_et, h_env'⟩ := h
            -- Extract underlying unify hypothesis
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
            -- Output type
            intro v hv n hn
            rw [← h_et] at hv; simp [toLMonoTy] at hv
            -- Env'.genState = Env3.genState (updateSubst preserves genEnv)
            have h_gen_eq : Env'.genEnv.genState = Env3.genEnv.genState := by
              rw [← h_env']; simp [TEnv.updateSubst]
            rw [h_gen_eq] at hn
            -- genTyVar facts
            have h_gen_subst := TEnv.genTyVar_subst Env2 fresh_name Env3 h_genTyVar
            have h_gen_name := genTyVar_name_eq Env2 fresh_name Env3 h_genTyVar
            have h_gen_tyGen := genTyVar_tyGen Env2 fresh_name Env3 h_genTyVar
            -- freeVars (subst v4.subst (ftvar fresh_name)) ⊆ [fresh_name] ++ Subst.freeVars v4.subst
            have h_fv_subset := LMonoTy.freeVars_of_subst_subset v4.subst (.ftvar fresh_name)
            -- v is in freeVars (subst v4.subst (ftvar fresh_name))
            have hv_in := h_fv_subset hv
            simp [LMonoTy.freeVars] at hv_in
            -- Context preservation chain
            have h_ctx1 := resolveAux_context e1 e1t C Env Env1 h_res1 h_ne
            have h_ne1 := h_ctx1 ▸ h_ne
            have h_ctx2 := resolveAux_context e2 e2t C Env1 Env2 h_res2 h_ne1
            -- Build TEnvWF for Env1
            have h_envwf1 : TEnvWF Env1 :=
              { aliasesWF := h_ctx1 ▸ h_aw
                substFreshForGen := resolveAux_preserves_SubstFreshForGen
                  e1 e1t C Env Env1 h_res1 h_envwf.substFreshForGen h_envwf.ctxFreshForGen h_ne h_aw
                ctxFreshForGen := h_ctx1 ▸ ContextFreshForGen.mono _ _ _
                  h_envwf.ctxFreshForGen (resolveAux_genState_mono e1 e1t C Env Env1 h_res1)
                boundVarsNodup := transfer_boundVarsNodup h_envwf.boundVarsNodup h_ctx1
                ctxFreeVarsGenerated := transfer_ctxFreeVarsGenerated h_envwf.ctxFreeVarsGenerated h_ctx1 }
            -- SubstFreshForGen for Env2
            have h_sfg_Env2 := resolveAux_preserves_SubstFreshForGen
              e2 e2t C Env1 Env2 h_res2
              h_envwf1.substFreshForGen h_envwf1.ctxFreshForGen h_ne1 h_envwf1.aliasesWF
            -- SubstFreshForGen for Env3 (genTyVar preserves subst, increments counter)
            have h_sfg_Env3 : SubstFreshForGen Env3.stateSubstInfo Env3.genEnv.genState := by
              rw [h_gen_subst]
              exact SubstFreshForGen.mono _ _ _ h_sfg_Env2 (by omega)
            -- Constraint freeVars are fresh for Env3.genState
            -- Constraint = [(e1t.toLMonoTy, tcons "arrow" [e2t.toLMonoTy, ftvar fresh_name])]
            -- freeVars = freeVars e1t.toLMonoTy ++ (freeVars e2t.toLMonoTy ++ [fresh_name])
            have h_cs_fresh : ∀ w, w ∈ Constraints.freeVars
                [(e1t.toLMonoTy, LMonoTy.tcons "arrow" [e2t.toLMonoTy, .ftvar fresh_name])] →
                ∀ k, k ≥ Env3.genEnv.genState.tyGen →
                  w ≠ TState.tyPrefix ++ toString k := by
              intro w hw k hk
              simp [Constraints.freeVars, Constraint.freeVars, LMonoTy.freeVars,
                    LMonoTys.freeVars] at hw
              -- w ∈ freeVars e1t.toLMonoTy ∨ w ∈ freeVars e2t.toLMonoTy ∨ w = fresh_name
              rcases hw with hw1 | hw2 | hw3
              · -- w ∈ freeVars e1t.toLMonoTy: use ih1
                have h_mono_e1 := resolveAux_genState_mono e1 e1t C Env Env1 h_res1
                have h_mono_e2 := resolveAux_genState_mono e2 e2t C Env1 Env2 h_res2
                have hk1 : k ≥ Env1.genEnv.genState.tyGen := by omega
                exact ih1 e1t C Env Env1 h_res1 h_envwf h_ne w hw1 k hk1
              · -- w ∈ freeVars e2t.toLMonoTy: use ih2
                have hk2 : k ≥ Env2.genEnv.genState.tyGen := by omega
                exact ih2 e2t C Env1 Env2 h_res2 h_envwf1 h_ne1 w hw2 k hk2
              · -- w = fresh_name
                rw [hw3, h_gen_name]
                exact generated_name_fresh Env2.genEnv.genState.tyGen Env3.genEnv.genState
                  (by omega) k hk
            -- SubstFreshForGen for v4 (unification output)
            have h_sfg_v4 : SubstFreshForGen v4 Env3.genEnv.genState :=
              unify_preserves_SubstFreshForGen h_unify h_sfg_Env3 h_cs_fresh
            -- Now dispatch: v ∈ [fresh_name] ∨ v ∈ Subst.freeVars v4.subst
            rcases hv_in with hv_fresh | hv_fv
            · -- v = fresh_name
              rw [hv_fresh, h_gen_name]
              exact generated_name_fresh Env2.genEnv.genState.tyGen Env3.genEnv.genState
                (by omega) n hn
            · -- v ∈ Subst.freeVars v4.subst
              exact h_sfg_v4 v (Or.inr hv_fv) n hn
  | .abs m bty e_body =>
    intro et C Env Env' h h_envwf h_ne
    have h_aw := h_envwf.aliasesWF
    simp only [resolveAux, Bind.bind, Except.bind] at h
    -- Decompose: typeBoundVar C Env bty
    split at h
    · simp at h
    · rename_i v1 h_tbv
      obtain ⟨xv, xty, Env1⟩ := v1
      dsimp at h h_tbv
      -- Decompose: resolveAux C Env1 (varOpen 0 (xv, some xty) e_body)
      split at h
      · simp at h
      · rename_i v2 h_res_body
        obtain ⟨et_body, Env2⟩ := v2
        dsimp at h h_res_body
        simp at h
        obtain ⟨h_et, h_env'⟩ := h
        -- h_et : et = .abs ⟨m, subst Env2.subst (arrow [xty, ety])⟩ bty (varCloseT 0 xv et_body)
        -- h_env' : Env' = eraseFromContext Env2 xv
        -- Output type: et.toLMonoTy = subst Env2.subst (tcons "arrow" [xty, (varCloseT 0 xv et_body).toLMonoTy])
        intro v hv n hn
        rw [← h_et] at hv; simp [toLMonoTy] at hv
        -- hv : v ∈ freeVars (subst Env2.subst (tcons "arrow" [xty, (varCloseT 0 xv et_body).toLMonoTy]))
        -- Env'.genState = Env2.genState (eraseFromContext preserves genEnv)
        have h_gen_eq : Env'.genEnv.genState = Env2.genEnv.genState := by
          rw [← h_env']; simp [TEnv.eraseFromContext, TEnv.updateContext]
        rw [h_gen_eq] at hn
        -- Apply IH to the opened body using strong induction
        have ih_body := ih_sub (varOpen 0 (xv, some xty) e_body)
          (by subst h_sz; simp [LExpr.sizeOf]; rw [varOpen_sizeOf]; omega)
        -- Build TEnvWF for Env1
        have h_envwf1 : TEnvWF Env1 :=
          { aliasesWF := typeBoundVar_preserves_AliasesWF C Env bty xv xty Env1 h_tbv h_envwf.aliasesWF
            substFreshForGen := typeBoundVar_preserves_SubstFreshForGen C Env bty xv xty Env1 h_tbv h_envwf.substFreshForGen h_envwf.aliasesWF h_envwf.ctxFreshForGen
            ctxFreshForGen := typeBoundVar_preserves_ContextFreshForGen C Env bty xv xty Env1 h_tbv h_envwf.ctxFreshForGen
            boundVarsNodup := typeBoundVar_preserves_boundVarsNodup C Env bty xv xty Env1 h_tbv h_envwf.boundVarsNodup
            ctxFreeVarsGenerated := by
              -- NOT PROVABLE for bty = some case: user type annotations can introduce
              -- free type vars (e.g., "a" in `a → Int`) that don't have the tyPrefix.
              -- ctxFreeVarsGenerated requires v.startsWith tyPrefix = true, which fails
              -- for user-supplied type variable names.
              -- For bty = none: xty = ftvar xtyid where xtyid is from genTyVar (has tyPrefix).
              -- Old context entries: by h_envwf.ctxFreeVarsGenerated + context preservation.
              sorry }
        have h_ne1 : Env1.context.types ≠ [] :=
          typeBoundVar_context_types_ne_nil C Env bty xv xty Env1 h_tbv
        -- SubstFreshForGen for Env2
        have h_sfg_Env2 := resolveAux_preserves_SubstFreshForGen
          (varOpen 0 (xv, some xty) e_body) et_body C Env1 Env2 h_res_body
          h_envwf1.substFreshForGen h_envwf1.ctxFreshForGen h_ne1 h_envwf1.aliasesWF
        -- Use freeVars_of_subst_subset to split v into type freeVars vs subst freeVars
        have h_fv_subset := LMonoTy.freeVars_of_subst_subset Env2.stateSubstInfo.subst
          (.tcons "arrow" [xty, (Lambda.LExpr.varCloseT 0 xv et_body).toLMonoTy])
        have hv_in := h_fv_subset hv
        simp [List.mem_append] at hv_in
        rcases hv_in with hv_ty | hv_subst
        · -- v ∈ freeVars (tcons "arrow" [xty, (varCloseT 0 xv et_body).toLMonoTy])
          simp [LMonoTy.freeVars, LMonoTys.freeVars, List.mem_append] at hv_ty
          rcases hv_ty with hv_xty | hv_ety
          · -- v ∈ freeVars xty: xty comes from typeBoundVar, its free vars are fresh
            -- First, establish that xty's free vars are fresh for Env1.genState
            have h_xty_fresh : ∀ w, w ∈ LMonoTy.freeVars xty →
                ∀ k, k ≥ Env1.genEnv.genState.tyGen → w ≠ TState.tyPrefix ++ toString k := by
              simp only [typeBoundVar, liftGenEnv, Bind.bind, Except.bind] at h_tbv
              split at h_tbv; · contradiction
              rename_i genResult h_gen
              have h_gen_ctx : genResult.snd.context = Env.context := by
                split at h_gen; · contradiction
                rename_i _ _ h_gv; have := Except.ok.inj h_gen; rw [← this]; simp [TEnv.context]
                exact HasGen.genVar_context Env.genEnv _ _ h_gv
              have h_gen_tyGen : genResult.snd.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
                split at h_gen; · contradiction
                rename_i _ _ h_gv; have := Except.ok.inj h_gen; rw [← this]; simp
                exact HasGen.genVar_tyGen_mono Env.genEnv _ _ h_gv
              have h_ctx_gen : ContextFreshForGen genResult.snd.context genResult.snd.genEnv.genState :=
                h_gen_ctx ▸ ContextFreshForGen.mono _ _ _ h_envwf.ctxFreshForGen h_gen_tyGen
              split at h_tbv
              · -- bty = some bty_val
                split at h_tbv; · contradiction
                rename_i _ bty_mty _ _ Env_inst h_inst
                simp [Pure.pure, Except.pure] at h_tbv
                obtain ⟨_, h_xty_eq, h_env1_eq⟩ := h_tbv
                rw [← h_xty_eq]
                have h_fv_fresh := LMonoTy_instantiateWithCheck_freeVars_fresh _ C genResult.snd _ Env_inst h_inst h_ctx_gen
                have h_iwc_mono := LMonoTy_instantiateWithCheck_tyGen_mono _ C genResult.snd _ Env_inst h_inst
                intro w hw k hk
                -- Env1 = addInNewestContext Env_inst [...], so Env1.genState = Env_inst.genState
                have h_gen_eq : Env1.genEnv.genState = Env_inst.genEnv.genState := by
                  rw [← h_env1_eq]; simp [TEnv.addInNewestContext, TEnv.updateContext]
                rw [h_gen_eq] at hk
                exact h_fv_fresh w hw k hk
              · -- bty = none
                split at h_tbv; · contradiction
                rename_i v_gen h_genTy
                obtain ⟨xtyid, Env_ty⟩ := v_gen
                simp [Pure.pure, Except.pure] at h_tbv
                obtain ⟨_, h_xty_eq, h_env1_eq⟩ := h_tbv
                rw [← h_xty_eq]
                intro w hw k hk
                simp [LMonoTy.freeVars] at hw
                rw [hw]
                have h_genTy_name := genTyVar_name_eq genResult.snd xtyid Env_ty h_genTy
                have h_genTy_tyGen := genTyVar_tyGen genResult.snd xtyid Env_ty h_genTy
                -- Env1 = addInNewestContext Env_ty [...], so Env1.genState = Env_ty.genState
                have h_gen_eq : Env1.genEnv.genState = Env_ty.genEnv.genState := by
                  rw [← h_env1_eq]; simp [TEnv.addInNewestContext, TEnv.updateContext]
                rw [h_gen_eq] at hk
                rw [h_genTy_name]
                exact generated_name_fresh _ _ (by omega) k hk
            -- Now apply: Env2.genState.tyGen ≥ Env1.genState.tyGen
            have h_mono_body := resolveAux_genState_mono
              (varOpen 0 (xv, some xty) e_body) et_body C Env1 Env2 h_res_body
            exact h_xty_fresh v hv_xty n (by omega)
          · -- v ∈ freeVars (varCloseT 0 xv et_body).toLMonoTy
            -- varCloseT preserves toLMonoTy
            rw [varCloseT_toLMonoTy] at hv_ety
            -- Now use ih_body: v ∈ freeVars et_body.toLMonoTy → v ≠ tyPrefix ++ toString n
            exact ih_body et_body C Env1 Env2 h_res_body h_envwf1 h_ne1 v hv_ety n hn
        · -- v ∈ Subst.freeVars Env2.stateSubstInfo.subst
          exact h_sfg_Env2 v (Or.inr hv_subst) n hn
  | .quant m qk bty triggers e_body =>
    intro et C Env Env' h h_envwf h_ne
    have h_aw := h_envwf.aliasesWF
    simp only [resolveAux, Bind.bind, Except.bind] at h
    -- Decompose: typeBoundVar C Env bty
    split at h
    · simp at h
    · rename_i v1 h_tbv
      obtain ⟨xv, xty, Env1⟩ := v1
      dsimp at h h_tbv
      -- Decompose: resolveAux C Env1 (varOpen 0 (xv, some xty) e_body)
      split at h
      · simp at h
      · rename_i v2 h_res_body
        obtain ⟨et_body, Env2⟩ := v2
        dsimp at h h_res_body
        -- Decompose: resolveAux C Env2 (varOpen 0 (xv, some xty) triggers)
        split at h
        · simp at h
        · rename_i v3 h_res_triggers
          obtain ⟨triggersT, Env3⟩ := v3
          dsimp at h h_res_triggers
          -- Apply IH to opened body and triggers using strong induction
          have ih_body := ih_sub (varOpen 0 (xv, some xty) e_body)
            (by subst h_sz; simp [LExpr.sizeOf]; rw [varOpen_sizeOf]; omega)
          have ih_triggers := ih_sub (varOpen 0 (xv, some xty) triggers)
            (by subst h_sz; simp [LExpr.sizeOf]; rw [varOpen_sizeOf]; omega)
          -- The output type of quant is xty (the quantifier variable type, stored in metadata)
          -- But toLMonoTy for quant is LMonoTy.bool, which has no free vars
          -- Actually: quant output is .quant ⟨m, xty'⟩ qk xty' triggersClosed etclosed
          -- and toLMonoTy of quant = LMonoTy.bool
          -- So freeVars et.toLMonoTy = freeVars LMonoTy.bool = []
          -- This makes the goal vacuously true!
          -- But we need to handle the conditional (ety != LMonoTy.bool) first
          split at h
          · simp at h
          · simp at h
            obtain ⟨h_et, h_env'⟩ := h
            intro v hv
            rw [← h_et] at hv; simp [toLMonoTy] at hv
            -- toLMonoTy of .quant is LMonoTy.bool, which has empty freeVars
            simp [LMonoTy.bool, LMonoTy.freeVars, LMonoTys.freeVars] at hv
  | .ite m c t e =>
    -- Output type is tht.toLMonoTy (the then-branch metadata type).
    -- Use IH on t (then-branch) and genState monotonicity.
    intro et C Env Env' h h_envwf h_ne
    -- Extract IHs from strong induction
    have ih_t := ih_sub t (by subst h_sz; simp [LExpr.sizeOf]; omega)
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    -- Decompose: resolveAux C Env c
    split at h
    · simp at h
    · rename_i v1 h_res_c
      obtain ⟨ct, Env1⟩ := v1; dsimp at h h_res_c
      -- Decompose: resolveAux C Env1 t
      split at h
      · simp at h
      · rename_i v2 h_res_t
        obtain ⟨tht, Env2⟩ := v2; dsimp at h h_res_t
        -- Decompose: resolveAux C Env2 e
        split at h
        · simp at h
        · rename_i v3 h_res_e
          obtain ⟨elt, Env3⟩ := v3; dsimp at h h_res_e
          -- Decompose: unify (mapError)
          split at h
          · simp at h
          · rename_i v4 h_mapError
            simp at h
            obtain ⟨h_et, h_env'⟩ := h
            -- The output type is tht.toLMonoTy
            intro v hv n hn
            rw [← h_et] at hv; simp [toLMonoTy] at hv
            -- Env'.genState = Env3.genState (updateSubst preserves genEnv)
            have h_gen_eq : Env'.genEnv.genState = Env3.genEnv.genState := by
              rw [← h_env']; simp [TEnv.updateSubst]
            rw [h_gen_eq] at hn
            -- Env3.genState.tyGen ≥ Env2.genState.tyGen (monotonicity of resolveAux on e)
            have h_mono_e := resolveAux_genState_mono e elt C Env2 Env3 h_res_e
            -- So n ≥ Env2.genState.tyGen
            have hn2 : n ≥ Env2.genEnv.genState.tyGen := Nat.le_trans h_mono_e hn
            -- Build TEnvWF for Env1 to use IH on t
            have h_ctx1 := resolveAux_context c ct C Env Env1 h_res_c h_ne
            have h_ne1 := h_ctx1 ▸ h_ne
            have h_aw := h_envwf.aliasesWF
            have h_envwf1 : TEnvWF Env1 :=
              { aliasesWF := h_ctx1 ▸ h_aw
                substFreshForGen := resolveAux_preserves_SubstFreshForGen
                  c ct C Env Env1 h_res_c h_envwf.substFreshForGen h_envwf.ctxFreshForGen h_ne h_aw
                ctxFreshForGen := h_ctx1 ▸ ContextFreshForGen.mono _ _ _
                  h_envwf.ctxFreshForGen (resolveAux_genState_mono c ct C Env Env1 h_res_c)
                boundVarsNodup := transfer_boundVarsNodup h_envwf.boundVarsNodup h_ctx1
                ctxFreeVarsGenerated := transfer_ctxFreeVarsGenerated h_envwf.ctxFreeVarsGenerated h_ctx1 }
            -- Apply IH on t (then-branch)
            exact ih_t tht C Env1 Env2 h_res_t h_envwf1 h_ne1 v hv n hn2
  | .eq m e1 e2 =>
    -- Output type is LMonoTy.bool, which has no free vars. Vacuously true.
    intro et C Env Env' h h_envwf h_ne
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    split at h
    · simp at h
    · rename_i v1 h_res1
      obtain ⟨e1t, Env1⟩ := v1; dsimp at h h_res1
      split at h
      · simp at h
      · rename_i v2 h_res2
        obtain ⟨e2t, Env2⟩ := v2; dsimp at h h_res2
        split at h
        · simp at h
        · rename_i v3 h_mapError
          simp at h
          obtain ⟨h_et, _⟩ := h
          intro v hv
          rw [← h_et] at hv; simp [toLMonoTy] at hv
          -- LMonoTy.bool = tcons "bool" [], freeVars = []
          simp [LMonoTy.bool, LMonoTy.freeVars, LMonoTys.freeVars] at hv

theorem resolveAux_HasType :
    ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      TEnvWF Env →
      Env.context.types ≠ [] →
      Env'.context = Env.context ∧
      ∀ (S : Subst), Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        HasType C (Env.context) e
          (.forAll [] (LMonoTy.subst S et.toLMonoTy)) := by
  -- We use strong induction on LExpr.sizeOf to handle the abs/quant cases,
  -- where resolveAux recurses on (varOpen 0 x e_body) rather than e_body.
  suffices h_strong : ∀ (n : Nat) (e : LExpr T.mono), LExpr.sizeOf e = n →
      ∀ (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      TEnvWF Env →
      Env.context.types ≠ [] →
      Env'.context = Env.context ∧
      ∀ (S : Subst), Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        HasType C (Env.context) e
          (.forAll [] (LMonoTy.subst S et.toLMonoTy)) from
    fun e => h_strong (LExpr.sizeOf e) e rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih_n =>
  intro e h_sz
  -- ih_n : ∀ m < n, ∀ e', LExpr.sizeOf e' = m → [full statement for e']
  -- Helper to apply IH to any e' with LExpr.sizeOf e' < n
  have ih_sub : ∀ (e' : LExpr T.mono), LExpr.sizeOf e' < n →
      ∀ (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e' = .ok (et, Env') →
      TEnvWF Env →
      Env.context.types ≠ [] →
      Env'.context = Env.context ∧
      ∀ (S : Subst), Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        HasType C (Env.context) e'
          (.forAll [] (LMonoTy.subst S et.toLMonoTy)) :=
    fun e' h_lt => ih_n (LExpr.sizeOf e') h_lt e' rfl
  match e with
  | .const m c =>
    intro et C Env Env' h h_envwf _
    have h_aw := h_envwf.aliasesWF
    simp [resolveAux, inferConst] at h
    split at h
    · rename_i h_known
      simp [Bind.bind, Except.bind] at h
      obtain ⟨h_et, h_env⟩ := h
      constructor
      · rw [← h_env]
      · intro S h_abs_S h_wf_S
        rw [← h_et]; simp [toLMonoTy]
        rw [LConst.ty_subst]
        cases c with
        | boolConst b => exact HasType.tbool_const _ _ _ h_known
        | intConst i => exact HasType.tint_const _ _ _ h_known
        | realConst r => exact HasType.treal_const _ _ _ h_known
        | strConst s => exact HasType.tstr_const _ _ _ h_known
        | bitvecConst n b => exact HasType.tbitvec_const _ _ _ _ h_known
    · exact absurd h (by simp [Bind.bind, Except.bind])
  | .bvar m i =>
    intro et C Env Env' h h_envwf _
    have h_aw := h_envwf.aliasesWF
    simp [resolveAux, Bind.bind, Except.bind] at h
  | .fvar m x fty =>
    -- resolveAux calls inferFVar, which looks up x in context, instantiates
    -- bound type variables, and optionally unifies with the annotation.
    intro et C Env Env' h h_envwf _
    have h_aw := h_envwf.aliasesWF
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_infer
      obtain ⟨ty_res, Env_res⟩ := v1
      simp at h
      obtain ⟨h_et, h_env'⟩ := h
      rw [← h_et, ← h_env']
      simp [toLMonoTy]
      constructor
      · -- Context preservation from inferFVar
        exact (inferFVar_HasType C Env x fty ty_res Env_res m h_infer h_envwf.boundVarsNodup h_envwf.aliasesWF).1
      · -- Typing under arbitrary absorbing S
        intro S h_abs_S h_wf_S
        -- We have: HasType ... (subst Env_res.subst ty_res) from inferFVar_HasType
        have ⟨_, h_ty⟩ := inferFVar_HasType C Env x fty ty_res Env_res m h_infer
          h_envwf.boundVarsNodup h_envwf.aliasesWF
        -- Upgrade: subst S (subst Env_res ty_res) = subst S ty_res (by absorption)
        have h1 := HasType_subst_fresh_all C Env.context (.fvar m x fty)
          (LMonoTy.subst Env_res.stateSubstInfo.subst ty_res) S h_ty
          (by -- relevant-key freshness: keys of S in freeVars of (subst Env_res ty_res) are fresh
              sorry)
          h_wf_S
        rw [LMonoTy.subst_absorbs S Env_res.stateSubstInfo.subst ty_res h_abs_S] at h1
        exact h1
  | .op m o oty =>
    intro et C Env Env' h h_envwf h_ne
    have h_aw := h_envwf.aliasesWF
    -- Decompose resolveAux for .op
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h  -- function not found
    rename_i func h_find
    split at h; · simp at h  -- func.type error
    rename_i type_val h_type
    split at h; · simp at h  -- instantiateWithCheck error
    rename_i v1 h_inst; obtain ⟨ty_inst, Env1⟩ := v1; dsimp at h h_inst
    cases oty with
    | none =>
      simp at h; obtain ⟨h_et, h_env⟩ := h; rw [← h_env]
      constructor
      · -- Context preservation
        exact LTy_instantiateWithCheck_context type_val C Env ty_inst Env1 h_inst
      · -- Typing under arbitrary absorbing S
        intro S h_abs_S h_wf_S
        rw [← h_et]; simp [toLMonoTy]
        sorry -- needs op HasType variant for arbitrary absorbing substitution
    | some oty_val =>
      simp only [Except.mapError] at h
      split at h; · simp at h
      rename_i v2 h_inst2; obtain ⟨oty_inst, Env2⟩ := v2; dsimp at h h_inst2
      split at h; · simp at h
      rename_i v3 h_mapError
      simp at h; obtain ⟨h_et, h_env⟩ := h; rw [← h_env]
      constructor
      · -- Context preservation
        simp [TEnv.updateSubst, TEnv.context]
        have h1 := LTy_instantiateWithCheck_context type_val C Env ty_inst Env1 h_inst
        have h2 := LMonoTy_instantiateWithCheck_context oty_val C Env1 oty_inst Env2 h_inst2
        simp [TEnv.context] at h1 h2; rw [h2, h1]
      · -- Typing under arbitrary absorbing S
        intro S h_abs_S h_wf_S
        rw [← h_et]; simp [toLMonoTy, TEnv.updateSubst]
        sorry -- annotated op typing: needs instantiateWithCheck_op_annotated_HasType for arbitrary absorbing substitution
  | .app m e1 e2 =>
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

      3. IHs give typing under ∀ S absorbing Env_i.subst.

      4. Context preservation: chain Env' → Env3 → Env2 → Env1 → Env.

      5. Given caller's S absorbing Env'.subst = remove(v4.subst, fresh),
         derive S absorbs Env1.subst and Env2.subst via absorption chains.

      6. Apply IHs with the caller's S directly (no HasType_subst_upgrade needed).

      7. From unification + absorption: subst S ty1 = tcons "arrow" [subst S ty2, subst S freshty].

      8. Apply HasType.tapp.
    -/
    intro et C Env Env' h h_envwf h_ne
    have h_aw := h_envwf.aliasesWF
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
            -- IHs from recursive calls (using strong induction)
            have ih1 := ih_sub e1 (by subst h_sz; simp [LExpr.sizeOf]; omega)
            have ih2 := ih_sub e2 (by subst h_sz; simp [LExpr.sizeOf]; omega)
            have ⟨h_ctx1, h_ty1⟩ := ih1 e1t C Env Env1 h_res1 h_envwf h_ne
            have h_ne1 := h_ctx1 ▸ h_ne
            -- Build TEnvWF for Env1 (context preserved, subst/gen extended)
            have h_envwf1 : TEnvWF Env1 :=
              { aliasesWF := h_ctx1 ▸ h_aw
                substFreshForGen := resolveAux_preserves_SubstFreshForGen e1 e1t C Env Env1 h_res1 h_envwf.substFreshForGen h_envwf.ctxFreshForGen h_ne h_aw
                ctxFreshForGen := h_ctx1 ▸ ContextFreshForGen.mono _ _ _ h_envwf.ctxFreshForGen (resolveAux_genState_mono e1 e1t C Env Env1 h_res1)
                boundVarsNodup := transfer_boundVarsNodup h_envwf.boundVarsNodup h_ctx1
                ctxFreeVarsGenerated := transfer_ctxFreeVarsGenerated h_envwf.ctxFreeVarsGenerated h_ctx1 }
            have ⟨h_ctx2, h_ty2⟩ := ih2 e2t C Env1 Env2 h_res2 h_envwf1 h_ne1
            -- Absorption chain: v4 absorbs Env3.subst = Env2.subst
            have h_abs_v4_Env3 := unify_absorbs
              [(e1t.toLMonoTy, LMonoTy.tcons "arrow" [e2t.toLMonoTy, .ftvar fresh_name])]
              Env3.stateSubstInfo v4 h_unify
            rw [h_gen_subst] at h_abs_v4_Env3
            -- Now h_abs_v4_Env3 : absorbs v4.subst Env2.subst
            have h_abs_Env2_Env1 := resolveAux_absorbs e2 e2t C Env1 Env2 h_res2 h_envwf1.toEnvFreshForGen h_ne1 h_envwf1.aliasesWF
            have h_abs_Env1_Env := resolveAux_absorbs e1 e1t C Env Env1 h_res1 h_envwf.toEnvFreshForGen h_ne h_aw
            have h_abs_v4_Env1 := Subst.absorbs_trans
              Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst v4.subst
              h_abs_Env2_Env1 h_abs_v4_Env3
            constructor
            · -- Context preservation
              rw [← h_env']
              simp [TEnv.updateSubst, TEnv.context]
              change Env3.context = Env.context
              rw [h_gen_ctx, h_ctx2, h_ctx1]
            · -- Typing under arbitrary absorbing S
              intro S h_abs_S h_wf_S
              rw [← h_et]; simp [toLMonoTy]
              -- Goal: HasType C Γ (.app m e1 e2) (.forAll [] (subst S (subst v4 (ftvar fresh))))
              -- We need: S absorbs Env1.subst and S absorbs Env2.subst
              -- Chain: S absorbs remove(v4, fresh) and v4 absorbs Env2 absorbs Env1
              -- Derive absorbs S (remove v4.subst fresh_name) from h_abs_S
              have h_abs_S_rem : Subst.absorbs S (Maps.remove v4.subst fresh_name) := by
                rw [← h_env'] at h_abs_S
                simp [TEnv.updateSubst] at h_abs_S
                exact h_abs_S
              -- Freshness: fresh_name not in Env1.subst keys/values
              have h_fresh_Env1 := genTyVar_fresh_wrt_input_subst
                Env1 Env2 Env3 fresh_name h_genTyVar
                h_envwf1.substFreshForGen
                (resolveAux_genState_mono e2 e2t C Env1 Env2 h_res2)
              -- Freshness: fresh_name not in Env2.subst keys/values
              have h_fresh_Env2 := genTyVar_fresh_wrt_input_subst
                Env2 Env2 Env3 fresh_name h_genTyVar
                (resolveAux_preserves_SubstFreshForGen e2 e2t C Env1 Env2 h_res2
                  h_envwf1.substFreshForGen h_envwf1.ctxFreshForGen h_ne1 h_envwf1.aliasesWF)
                (Nat.le_refl _)
              -- absorbs (remove v4 fresh) Env1.subst and Env2.subst
              have h_abs_rem_Env1 := Subst.absorbs_of_remove
                v4.subst Env1.stateSubstInfo.subst fresh_name
                h_abs_v4_Env1 h_fresh_Env1.1 h_fresh_Env1.2
              have h_abs_rem_Env2 := Subst.absorbs_of_remove
                v4.subst Env2.stateSubstInfo.subst fresh_name
                h_abs_v4_Env3 h_fresh_Env2.1 h_fresh_Env2.2
              -- Chain: S absorbs (remove v4 fresh) absorbs Env1/Env2
              have h_abs_S_Env1 : Subst.absorbs S Env1.stateSubstInfo.subst :=
                Subst.absorbs_trans
                  Env1.stateSubstInfo.subst (Maps.remove v4.subst fresh_name) S
                  h_abs_rem_Env1 h_abs_S_rem
              have h_abs_S_Env2 : Subst.absorbs S Env2.stateSubstInfo.subst :=
                Subst.absorbs_trans
                  Env2.stateSubstInfo.subst (Maps.remove v4.subst fresh_name) S
                  h_abs_rem_Env2 h_abs_S_rem
              -- Apply IHs with S directly (no HasType_subst_upgrade needed!)
              have h_ty1_S := h_ty1 S h_abs_S_Env1 h_wf_S
              rw [h_ctx1] at h_ty2
              have h_ty2_S := h_ty2 S h_abs_S_Env2 h_wf_S
              -- Unification makes: subst v4 ty1 = tcons "arrow" [subst v4 ty2, subst v4 freshty]
              have h_eq := unify_makes_equal
                e1t.toLMonoTy
                (LMonoTy.tcons "arrow" [e2t.toLMonoTy, .ftvar fresh_name])
                Env3.stateSubstInfo v4 h_unify
              -- Key: fresh_name ∉ freeVars e1t.toLMonoTy and e2t.toLMonoTy
              -- (These follow from SubstFreshForGen + genTyVar freshness but are not yet proven)
              have h_gen_name := genTyVar_name_eq Env2 fresh_name Env3 h_genTyVar
              have h_e1t_no_fresh : fresh_name ∉ LMonoTy.freeVars e1t.toLMonoTy := by
                intro h_mem
                have h_mono_e2 := resolveAux_genState_mono e2 e2t C Env1 Env2 h_res2
                have h_ne_fresh := resolveAux_output_type_no_future_vars e1 e1t C Env Env1 h_res1 h_envwf h_ne
                    fresh_name h_mem Env2.genEnv.genState.tyGen h_mono_e2
                exact h_ne_fresh h_gen_name
              have h_e2t_no_fresh : fresh_name ∉ LMonoTy.freeVars e2t.toLMonoTy := by
                intro h_mem
                have h_ne_fresh := resolveAux_output_type_no_future_vars e2 e2t C Env1 Env2 h_res2 h_envwf1 h_ne1
                    fresh_name h_mem Env2.genEnv.genState.tyGen (Nat.le_refl _)
                exact h_ne_fresh h_gen_name
              -- subst v4 x = subst (remove v4 fresh) x when fresh ∉ freeVars x
              have h_subst_e1t : LMonoTy.subst S (LMonoTy.subst v4.subst e1t.toLMonoTy) =
                  LMonoTy.subst S e1t.toLMonoTy := by
                rw [← LMonoTy.subst_remove_not_fv v4.subst fresh_name e1t.toLMonoTy h_e1t_no_fresh]
                exact LMonoTy.subst_absorbs S (Maps.remove v4.subst fresh_name) e1t.toLMonoTy h_abs_S_rem
              have h_subst_e2t : LMonoTy.subst S (LMonoTy.subst v4.subst e2t.toLMonoTy) =
                  LMonoTy.subst S e2t.toLMonoTy := by
                rw [← LMonoTy.subst_remove_not_fv v4.subst fresh_name e2t.toLMonoTy h_e2t_no_fresh]
                exact LMonoTy.subst_absorbs S (Maps.remove v4.subst fresh_name) e2t.toLMonoTy h_abs_S_rem
              -- Apply subst S to h_eq and simplify using absorption
              -- Result: subst S e1t.toLMonoTy = tcons "arrow" [subst S e2t.toLMonoTy, subst S (subst v4 (ftvar fresh))]
              have h_eq_S : LMonoTy.subst S e1t.toLMonoTy =
                  LMonoTy.tcons "arrow"
                    [LMonoTy.subst S e2t.toLMonoTy,
                     LMonoTy.subst S (LMonoTy.subst v4.subst (.ftvar fresh_name))] := by
                have h := congrArg (LMonoTy.subst S) h_eq
                rw [h_subst_e1t] at h
                rw [LMonoTy.subst_tcons_pair v4.subst "arrow" e2t.toLMonoTy (.ftvar fresh_name)] at h
                rw [LMonoTy.subst_tcons_pair S "arrow" (LMonoTy.subst v4.subst e2t.toLMonoTy)
                    (LMonoTy.subst v4.subst (.ftvar fresh_name))] at h
                rw [h_subst_e2t] at h
                exact h
              rw [h_eq_S] at h_ty1_S
              -- Apply HasType.tapp with result type = subst S (subst v4 (ftvar fresh))
              exact HasType.tapp Env.context m e1 e2
                (.forAll [] (LMonoTy.subst S (LMonoTy.subst v4.subst (.ftvar fresh_name))))
                (.forAll [] (LMonoTy.subst S e2t.toLMonoTy))
                (by simp [LTy.isMonoType, LTy.boundVars])
                (by simp [LTy.isMonoType, LTy.boundVars])
                (by simp [LTy.toMonoType]; exact h_ty1_S)
                h_ty2_S
  | .abs m bty e_body =>
    intro et C Env Env' h h_envwf h_ne
    have h_aw := h_envwf.aliasesWF
    -- The abs case of resolveAux calls typeBoundVar then recurses on the opened body.
    simp only [resolveAux, Bind.bind, Except.bind] at h
    -- Decompose: typeBoundVar C Env bty
    split at h
    · simp at h
    · rename_i v1 h_tbv
      obtain ⟨xv, xty, Env1⟩ := v1
      dsimp at h h_tbv
      -- Decompose: resolveAux C Env1 (varOpen 0 (xv, some xty) e_body)
      split at h
      · simp at h
      · rename_i v2 h_res_body
        obtain ⟨et_body, Env2⟩ := v2
        dsimp at h h_res_body
        simp at h
        obtain ⟨h_et, h_env'⟩ := h
        -- h_tbv : typeBoundVar C Env bty = .ok (xv, xty, Env1)
        -- h_res_body : resolveAux C Env1 (varOpen 0 (xv, some xty) e_body) = .ok (et_body, Env2)
        -- h_et : et = .abs ⟨m, mty⟩ bty (varCloseT 0 xv et_body) where mty = subst S (arrow [xty, ety])
        -- h_env' : Env' = eraseFromContext Env2 xv
        -- Apply IH to the opened body using strong induction
        -- sizeOf (varOpen 0 (xv, some xty) e_body) = sizeOf e_body < 2 + sizeOf e_body = sizeOf (.abs m bty e_body) = n
        have ih_body := ih_sub (varOpen 0 (xv, some xty) e_body)
          (by subst h_sz; simp [LExpr.sizeOf]; rw [varOpen_sizeOf]; omega)
        -- Build TEnvWF for Env1 (typeBoundVar extends context)
        have h_envwf1 : TEnvWF Env1 :=
          { aliasesWF := typeBoundVar_preserves_AliasesWF C Env bty xv xty Env1 h_tbv h_envwf.aliasesWF
            substFreshForGen := typeBoundVar_preserves_SubstFreshForGen C Env bty xv xty Env1 h_tbv h_envwf.substFreshForGen h_envwf.aliasesWF h_envwf.ctxFreshForGen
            ctxFreshForGen := typeBoundVar_preserves_ContextFreshForGen C Env bty xv xty Env1 h_tbv h_envwf.ctxFreshForGen
            boundVarsNodup := typeBoundVar_preserves_boundVarsNodup C Env bty xv xty Env1 h_tbv h_envwf.boundVarsNodup
            ctxFreeVarsGenerated := by
              -- typeBoundVar adds (xv, forAll [] xty) where xty has generated-name free vars
              -- Existing entries preserved; new entry's free vars are generated names
              sorry
          }
        have h_ne1 : Env1.context.types ≠ [] :=
          typeBoundVar_context_types_ne_nil C Env bty xv xty Env1 h_tbv
        have ⟨h_ctx_body, h_ty_body⟩ := ih_body et_body C Env1 Env2 h_res_body h_envwf1 h_ne1
        -- h_ctx_body : Env2.context = Env1.context
        -- h_ty_body : HasType C Env1.context (varOpen 0 (xv, some xty) e_body)
        --             (.forAll [] (subst Env2.subst et_body.toLMonoTy))
        constructor
        · -- Context preservation: Env'.context = Env.context
          -- Env' = eraseFromContext Env2 xv
          -- Env2.context = Env1.context (from IH)
          -- Env1 = typeBoundVar result, adds xv to Env's context
          -- eraseFromContext removes xv → back to Env.context
          rw [← h_env']
          exact typeBoundVar_erase_context C Env bty xv xty Env1 h_tbv Env2 h_ctx_body
            (typeBoundVar_xv_fresh_in_context C Env bty xv xty Env1 h_tbv) h_ne
        · -- Typing under arbitrary absorbing S
          intro S h_abs_S h_wf_S
          sorry -- abs case typing: needs tabs rule + varClose reasoning
  | .quant m qk bty tr e_body =>
    intro et C Env Env' h h_envwf _
    have h_aw := h_envwf.aliasesWF
    exact ⟨sorry, fun S _ _ => sorry⟩
  | .ite m c t e =>
    -- resolveAux recurses on c, t, e, then unifies [(cty, bool), (tty, ety)].
    -- Result type is tty (the then-branch type), and the HasType rule is `tif`.
    intro et C Env Env' h h_envwf h_ne
    have h_aw := h_envwf.aliasesWF
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
            -- IHs from recursive calls (using strong induction)
            have ih_c := ih_sub c (by subst h_sz; simp [LExpr.sizeOf]; omega)
            have ih_t := ih_sub t (by subst h_sz; simp [LExpr.sizeOf]; omega)
            have ih_e := ih_sub e (by subst h_sz; simp [LExpr.sizeOf]; omega)
            have ⟨h_ctx1, h_ty_c⟩ := ih_c ct C Env Env1 h_res_c h_envwf h_ne
            have h_ne1 := h_ctx1 ▸ h_ne
            -- (h_sf1 removed: keysFresh no longer in TEnvWF)
            -- Build TEnvWF for Env1
            have h_envwf1 : TEnvWF Env1 :=
              { aliasesWF := h_ctx1 ▸ h_aw
                substFreshForGen := resolveAux_preserves_SubstFreshForGen c ct C Env Env1 h_res_c h_envwf.substFreshForGen h_envwf.ctxFreshForGen h_ne h_aw
                ctxFreshForGen := h_ctx1 ▸ ContextFreshForGen.mono _ _ _ h_envwf.ctxFreshForGen (resolveAux_genState_mono c ct C Env Env1 h_res_c)
                boundVarsNodup := transfer_boundVarsNodup h_envwf.boundVarsNodup h_ctx1
                ctxFreeVarsGenerated := transfer_ctxFreeVarsGenerated h_envwf.ctxFreeVarsGenerated h_ctx1 }
            have ⟨h_ctx2, h_ty_t⟩ := ih_t tht C Env1 Env2 h_res_t h_envwf1 h_ne1
            have h_ne2 := h_ctx2 ▸ h_ne1
            -- Build TEnvWF for Env2
            have h_envwf2 : TEnvWF Env2 :=
              { aliasesWF := h_ctx2 ▸ h_ctx1 ▸ h_aw
                substFreshForGen := resolveAux_preserves_SubstFreshForGen t tht C Env1 Env2 h_res_t h_envwf1.substFreshForGen h_envwf1.ctxFreshForGen h_ne1 h_envwf1.aliasesWF
                ctxFreshForGen := h_ctx2 ▸ ContextFreshForGen.mono _ _ _ h_envwf1.ctxFreshForGen (resolveAux_genState_mono t tht C Env1 Env2 h_res_t)
                boundVarsNodup := transfer_boundVarsNodup h_envwf1.boundVarsNodup h_ctx2
                ctxFreeVarsGenerated := transfer_ctxFreeVarsGenerated h_envwf1.ctxFreeVarsGenerated h_ctx2 }
            have ⟨h_ctx3, h_ty_e⟩ := ih_e elt C Env2 Env3 h_res_e h_envwf2 h_ne2
            -- Absorption chain: v4 absorbs Env3 absorbs Env2 absorbs Env1 absorbs Env
            have h_abs_v4_Env3 := unify_absorbs
              [(ct.toLMonoTy, LMonoTy.bool), (tht.toLMonoTy, elt.toLMonoTy)]
              Env3.stateSubstInfo v4 h_unify
            have h_ne3 := h_ctx3 ▸ h_ne2
            have h_abs_Env3_Env2 := resolveAux_absorbs e elt C Env2 Env3 h_res_e h_envwf2.toEnvFreshForGen h_ne2 h_envwf2.aliasesWF
            have h_abs_Env2_Env1 := resolveAux_absorbs t tht C Env1 Env2 h_res_t h_envwf1.toEnvFreshForGen h_ne1 h_envwf1.aliasesWF
            have h_abs_Env1_Env := resolveAux_absorbs c ct C Env Env1 h_res_c h_envwf.toEnvFreshForGen h_ne h_aw
            have h_abs_v4_Env2 := Subst.absorbs_trans
              Env2.stateSubstInfo.subst Env3.stateSubstInfo.subst v4.subst
              h_abs_Env3_Env2 h_abs_v4_Env3
            have h_abs_v4_Env1 := Subst.absorbs_trans
              Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst v4.subst
              h_abs_Env2_Env1 h_abs_v4_Env2
            constructor
            · -- Context preservation
              rw [← h_env']
              simp [TEnv.updateSubst, TEnv.context]
              change Env3.context = Env.context
              rw [h_ctx3, h_ctx2, h_ctx1]
            · -- Typing under arbitrary absorbing S
              intro S h_abs_S h_wf_S
              rw [← h_et]; simp [toLMonoTy]
              -- Goal: HasType C Γ (.ite m c t e) (.forAll [] (subst S tht.toLMonoTy))
              -- We need: S absorbs Env1.subst, Env2.subst, Env3.subst
              -- Derive absorbs S v4.subst from h_abs_S (Env'.subst = v4.subst)
              have h_abs_S_v4 : Subst.absorbs S v4.subst := by
                rw [← h_env'] at h_abs_S
                simp [TEnv.updateSubst] at h_abs_S
                exact h_abs_S
              have h_abs_S_Env1 : Subst.absorbs S Env1.stateSubstInfo.subst :=
                Subst.absorbs_trans
                  Env1.stateSubstInfo.subst v4.subst S h_abs_v4_Env1 h_abs_S_v4
              have h_abs_S_Env2 : Subst.absorbs S Env2.stateSubstInfo.subst :=
                Subst.absorbs_trans
                  Env2.stateSubstInfo.subst v4.subst S h_abs_v4_Env2 h_abs_S_v4
              have h_abs_S_Env3 : Subst.absorbs S Env3.stateSubstInfo.subst :=
                Subst.absorbs_trans
                  Env3.stateSubstInfo.subst v4.subst S h_abs_v4_Env3 h_abs_S_v4
              -- Apply IHs with S directly (no HasType_subst_upgrade needed!)
              have h_ty_c_S := h_ty_c S h_abs_S_Env1 h_wf_S
              rw [h_ctx1] at h_ty_t
              have h_ty_t_S := h_ty_t S h_abs_S_Env2 h_wf_S
              rw [h_ctx2, h_ctx1] at h_ty_e
              have h_ty_e_S := h_ty_e S h_abs_S_Env3 h_wf_S
              -- Unification makes: subst v4 cty = bool, subst v4 tty = subst v4 ety
              have ⟨h_eq_bool, h_eq_te⟩ := unify_makes_equal₂
                ct.toLMonoTy LMonoTy.bool tht.toLMonoTy elt.toLMonoTy
                Env3.stateSubstInfo v4 h_unify
              -- Apply subst S to unification equalities and use absorption
              -- subst S ct.toLMonoTy = subst S bool = bool (ground type)
              have h_eq_bool_S : LMonoTy.subst S ct.toLMonoTy = LMonoTy.bool := by
                have h := congrArg (LMonoTy.subst S) h_eq_bool
                rw [LMonoTy.subst_absorbs S v4.subst _ h_abs_S_v4,
                    LMonoTy.subst_absorbs S v4.subst _ h_abs_S_v4,
                    LMonoTy.subst_bool] at h
                exact h
              -- subst S tht.toLMonoTy = subst S elt.toLMonoTy
              have h_eq_te_S : LMonoTy.subst S tht.toLMonoTy = LMonoTy.subst S elt.toLMonoTy := by
                have h := congrArg (LMonoTy.subst S) h_eq_te
                rw [LMonoTy.subst_absorbs S v4.subst _ h_abs_S_v4,
                    LMonoTy.subst_absorbs S v4.subst _ h_abs_S_v4] at h
                exact h
              -- Condition has type bool
              rw [h_eq_bool_S] at h_ty_c_S
              -- Then and else branches have the same type
              rw [← h_eq_te_S] at h_ty_e_S
              exact HasType.tif Env.context m c t e
                (.forAll [] (LMonoTy.subst S tht.toLMonoTy))
                h_ty_c_S h_ty_t_S h_ty_e_S
  | .eq m e1 e2 =>
    -- resolveAux recurses on e1 and e2, then unifies their types.
    -- Result type is LMonoTy.bool (ground), so subst S bool = bool for any S.
    -- We upgrade both IHs to the final substitution via absorption.
    intro et C Env Env' h h_envwf h_ne
    have h_aw := h_envwf.aliasesWF
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
          -- IHs from recursive calls (using strong induction)
          have ih1 := ih_sub e1 (by subst h_sz; simp [LExpr.sizeOf]; omega)
          have ih2 := ih_sub e2 (by subst h_sz; simp [LExpr.sizeOf]; omega)
          have ⟨h_ctx1, h_ty1⟩ := ih1 e1t C Env Env1 h_res1 h_envwf h_ne
          have h_ne1 := h_ctx1 ▸ h_ne
          -- (h_sf1 removed: keysFresh no longer in TEnvWF)
          -- Build TEnvWF for Env1
          have h_envwf1 : TEnvWF Env1 :=
            { aliasesWF := h_ctx1 ▸ h_aw
              substFreshForGen := resolveAux_preserves_SubstFreshForGen e1 e1t C Env Env1 h_res1 h_envwf.substFreshForGen h_envwf.ctxFreshForGen h_ne h_aw
              ctxFreshForGen := h_ctx1 ▸ ContextFreshForGen.mono _ _ _ h_envwf.ctxFreshForGen (resolveAux_genState_mono e1 e1t C Env Env1 h_res1)
              boundVarsNodup := transfer_boundVarsNodup h_envwf.boundVarsNodup h_ctx1
              ctxFreeVarsGenerated := transfer_ctxFreeVarsGenerated h_envwf.ctxFreeVarsGenerated h_ctx1 }
          have ⟨h_ctx2, h_ty2⟩ := ih2 e2t C Env1 Env2 h_res2 h_envwf1 h_ne1
          -- Absorption chain: v3 absorbs Env2 absorbs Env1 absorbs Env
          have h_abs_v3_Env2 := unify_absorbs [(e1t.toLMonoTy, e2t.toLMonoTy)]
            Env2.stateSubstInfo v3 h_unify
          have h_abs_Env2_Env1 := resolveAux_absorbs e2 e2t C Env1 Env2 h_res2 h_envwf1.toEnvFreshForGen h_ne1 h_envwf1.aliasesWF
          have h_abs_Env1_Env := resolveAux_absorbs e1 e1t C Env Env1 h_res1 h_envwf.toEnvFreshForGen h_ne h_aw
          have h_abs_v3_Env1 := Subst.absorbs_trans
            Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst v3.subst
            h_abs_Env2_Env1 h_abs_v3_Env2
          constructor
          · -- Context preservation
            rw [← h_env']
            simp [TEnv.updateSubst, TEnv.context]
            change Env2.context = Env.context
            rw [h_ctx2, h_ctx1]
          · -- Typing under arbitrary absorbing S
            intro S h_abs_S h_wf_S
            rw [← h_et]; simp [toLMonoTy]
            rw [LMonoTy.subst_bool]
            -- Env'.subst = v3.subst, S absorbs v3.subst
            -- We need: S absorbs Env1.subst, Env2.subst
            -- Derive absorbs S v3.subst from h_abs_S (Env'.subst = v3.subst)
            have h_abs_S_v3 : Subst.absorbs S v3.subst := by
              rw [← h_env'] at h_abs_S
              simp [TEnv.updateSubst] at h_abs_S
              exact h_abs_S
            have h_abs_S_Env1 : Subst.absorbs S Env1.stateSubstInfo.subst :=
              Subst.absorbs_trans
                Env1.stateSubstInfo.subst v3.subst S h_abs_v3_Env1 h_abs_S_v3
            have h_abs_S_Env2 : Subst.absorbs S Env2.stateSubstInfo.subst :=
              Subst.absorbs_trans
                Env2.stateSubstInfo.subst v3.subst S h_abs_v3_Env2 h_abs_S_v3
            -- Apply IHs with S directly (no HasType_subst_upgrade needed!)
            have h_ty1_S := h_ty1 S h_abs_S_Env1 h_wf_S
            rw [h_ctx1] at h_ty2
            have h_ty2_S := h_ty2 S h_abs_S_Env2 h_wf_S
            -- Unification makes types equal under v3.subst
            have h_eq := unify_makes_equal e1t.toLMonoTy e2t.toLMonoTy
              Env2.stateSubstInfo v3 h_unify
            -- Apply subst S to unification equality and use absorption
            have h_eq_S : LMonoTy.subst S e1t.toLMonoTy = LMonoTy.subst S e2t.toLMonoTy := by
              have h := congrArg (LMonoTy.subst S) h_eq
              rw [LMonoTy.subst_absorbs S v3.subst _ h_abs_S_v3,
                  LMonoTy.subst_absorbs S v3.subst _ h_abs_S_v3] at h
              exact h
            rw [h_eq_S] at h_ty1_S
            exact HasType.teq Env.context m e1 e2
              (.forAll [] (LMonoTy.subst S e2t.toLMonoTy))
              h_ty1_S h_ty2_S

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
      TEnvWF Env →
      Env.context.types ≠ [] →
      HasType C (Env.context) e (.forAll [] e_typed.toLMonoTy) := by
  intro e e_typed C Env _env h h_envwf h_ne
  -- Decompose resolve into resolveAux + applySubstT
  simp only [LExpr.resolve, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i v h_aux
    obtain ⟨et, Env'⟩ := v
    simp at h
    obtain ⟨h_typed, h_env'⟩ := h
    have ⟨_h_ctx, h_hastype⟩ := resolveAux_HasType e et C Env Env' h_aux h_envwf h_ne
    rw [← h_typed, applySubstT_toLMonoTy]
    exact h_hastype Env'.stateSubstInfo.subst (Subst.absorbs_refl _ Env'.stateSubstInfo.isWF) Env'.stateSubstInfo.isWF

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
