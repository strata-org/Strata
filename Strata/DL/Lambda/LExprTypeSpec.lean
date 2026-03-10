/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.LTyUnify
import all Strata.DL.Util.Map
import all Strata.DL.Util.Maps
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.Identifiers
import all Strata.DL.Util.Func
import all Strata.DL.Util.ListMap
import all Strata.DL.Util.List
public import Strata.DL.Lambda.LExprT
import all Strata.DL.Lambda.LExprT
public import Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.FactoryWF
/-! ## Typing Relation for Lambda Expressions

Specification of Lambda's type inference. See `Strata.DL.Lambda.LExprT` for the
implementation.

The inductive relation `HasType` characterizes well-typed `LExpr`s. We
specify a Hindley-Milner type system here, but note that at this time, we
do not have `let`s in `LExpr`, so we do not tackle let-polymorphism yet.

The theorem `resolve_HasType` shows that the implementation conforms to the specification.
-/

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)

public section

namespace LExpr
open LTy

variable {IDMeta : Type} [DecidableEq IDMeta]

/-!
### Lean 4 Standard Library Gaps

The `String.startsWith` and `String.drop` APIs in Lean 4.27 go through the
`Slice`/`Pattern` infrastructure with private internal definitions that have
no proof-level lemmas. To avoid this, `TState.isFutureGenVar` uses
`List.isPrefixOf` on `Char` lists, making the prefix-detection and
suffix-parsing properties trivially provable with standard `List` lemmas.

`Nat.toString_injective`, `isPrefixOf_append_self`, `listCharToNat?_roundtrip`,
and related helpers are in `Strata.DL.Util.String` (imported transitively
via `LExprTypeEnv`).
-/


/-- An annotation `ann` is compatible with a type `xty` under `aliases`:
    there exists a substitution of `ann`'s free type variables that makes it
    alias-equivalent to `xty`. This captures the relationship between a user's
    type annotation and the processed bound-variable type produced by
    `instantiateWithCheck` (which renames free vars and resolves aliases). -/
def AnnotCompat (aliases : List TypeAlias) (ann xty : LMonoTy) : Prop :=
  ∃ (σ : Map TyIdentifier LMonoTy),
    AliasEquiv aliases (LMonoTy.subst [σ] ann) xty

theorem AnnotCompat.of_eq {aliases : List TypeAlias} {ann : LMonoTy} :
    AnnotCompat aliases ann ann :=
  ⟨[], by unfold LMonoTy.subst; simp [Subst.hasEmptyScopes, Map.isEmpty]; exact .refl⟩

-- `AnnotCompat_subst` is defined later (after `AliasEquiv_subst` which it depends on).
-- See the actual definition below the `AliasEquiv_subst` theorem.

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
  instantiation of the type `ty_o` recorded for it in `Γ`, and the annotation
  `ann` is compatible with `ty_s` (via substitution + alias equivalence).
  -/
  | tvar_annotated : ∀ Γ m x ty_o ty_s tys ann,
            Γ.types.find? x = some ty_o →
            tys.length = ty_o.boundVars.length →
            LTy.openFull ty_o tys = ty_s →
            AnnotCompat Γ.aliases ann ty_s →
            HasType C Γ (.fvar m x (some ann)) (.forAll [] ty_s)

  /--
  An abstraction `λ x.e` has type `x_ty → e_ty` if the claimed type of `x` is
  `x_ty` or None and if `e` has type `e_ty` when `Γ` is extended with the
  binding `(x → x_ty)`.
  -/
  | tabs : ∀ Γ m name x x_ty e e_ty o,
            LExpr.fresh x e →
            (hx : LTy.isMonoType x_ty) →
            (he : LTy.isMonoType e_ty) →
            HasType C { Γ with types := Γ.types.insert x.fst x_ty} (LExpr.varOpen 0 x e) e_ty →
            (o = none ∨ ∃ t, o = some t ∧ AnnotCompat Γ.aliases t (x_ty.toMonoType hx)) →
            HasType C Γ (.abs m name o e)
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
  | tquant: ∀ Γ m k name tr tr_ty x x_ty e o,
            LExpr.fresh x e →
            (hx : LTy.isMonoType x_ty) →
            HasType C { Γ with types := Γ.types.insert x.fst x_ty} (LExpr.varOpen 0 x e) (.forAll [] .bool) →
            HasType C {Γ with types := Γ.types.insert x.fst x_ty} (LExpr.varOpen 0 x tr) tr_ty →
            (o = none ∨ ∃ t, o = some t ∧ AnnotCompat Γ.aliases t (x_ty.toMonoType hx)) →
            HasType C Γ (.quant m k name o tr e) (.forAll [] .bool)

  /--
  An un-annotated operator has the type recorded for it in `C.functions`, if any.
  -/
  | top: ∀ Γ m f op ty,
            C.functions.find? (fun fn => fn.name == op) = some f →
            f.type = .ok ty →
            HasType C Γ (.op m op none) ty
  /--
  Similarly to free variables, an annotated operator has its claimed type `ty_s` if `ty_s` is an
  instantiation of the type `ty_o` recorded for it in `C.functions`, and the annotation
  `ann` is compatible with `ty_s`.
  -/
  | top_annotated: ∀ Γ m f op ty_o ty_s tys ann,
            C.functions.find? (fun fn => fn.name == op) = some f →
            f.type = .ok ty_o →
            tys.length = ty_o.boundVars.length →
            LTy.openFull ty_o tys = ty_s →
            AnnotCompat Γ.aliases ann ty_s →
            HasType C Γ (.op m op (some ann)) (.forAll [] ty_s)

  /-- Alias equivalence preserves typing: if `e` has type `mty` and `mty` is
  alias-equivalent to `mty'` (under the aliases in `Γ`), then `e` also has
  type `mty'`. This covers single-step expansion, subtree resolution, and
  their transitive composition. -/
  | talias : ∀ Γ e mty mty',
            _root_.Lambda.AliasEquiv Γ.aliases mty mty' →
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
  case tabs m name x x_ty e e_ty hx h_x_mono h_e_mono ht ih =>
    simp_all [WF]
    exact lcAt_varOpen_abs ih (by simp)
  case tquant m k name tr tr_ty x x_ty e o h_x_mono hx htr ih ihtr =>
    simp_all [WF]
    exact lcAt_varOpen_quant ih (by omega) ihtr
  done


section Proofs
attribute [local simp] Pure.pure Except.pure

/-!
### Helper lemmas for `resolve_HasType`
-/

/--
Ground types (from constants) are unaffected by type substitution.
-/
theorem LConst.ty_freeVars (c : LConst) : LMonoTy.freeVars c.ty = [] := by
  cases c <;> simp [LConst.ty, LMonoTy.int, LMonoTy.bool, LMonoTy.real, LMonoTy.string,
    LMonoTy.freeVars, LMonoTys.freeVars]

theorem LConst.ty_subst (c : LConst) (S : Subst) :
    LMonoTy.subst S c.ty = c.ty := by
  cases c <;> simp [LConst.ty, LMonoTy.int, LMonoTy.bool, LMonoTy.real, LMonoTy.string,
    LMonoTy.subst, LMonoTys.subst, LMonoTys.subst.substAux]

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
  | abs m _ ty e => simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.toLMonoTy]
  | ite m c t e => simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.toLMonoTy]
  | eq m e1 e2 => simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.toLMonoTy]
  | quant m k _ ty tr e =>
    simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.toLMonoTy, LMonoTy.bool]
    unfold LMonoTy.subst
    split <;> simp [LMonoTys.subst, LMonoTys.subst.substAux]

/-!
### Proof architecture for `resolve_HasType`

The proof is structured in two layers:

1. **`resolveAux_HasType`**: The core theorem, proved by induction on `e`.
   States that if `resolveAux C Env e = .ok (et, Env')`, then:
   - `Env'.context = Env.context` (context is preserved), and
   - for any substitution `S` that absorbs `Env'.stateSubstInfo.subst`,
     `HasType C (TContext.subst Env.context S) e (.forAll [] (LMonoTy.subst S et.toLMonoTy))`.

   The conclusion is universally quantified over `S` so that the caller
   (including recursive cases) can instantiate it with the final substitution.
   This eliminates the need for `HasType_subst_upgrade` in recursive cases
   (e.g., `eq`, `ite`, `app`): each IH directly gives typing under the
   caller's `S`, provided we can show `S` absorbs each intermediate
   environment's substitution via the absorption chain built from
   `resolveAux_absorbs`, `unify_absorbs`, and `Subst.absorbs_trans`.

2. **`resolve_HasType`**: The top-level theorem. Since `resolve` is just
   `resolveAux` followed by `applySubstT`, we decompose the hypothesis,
   apply `resolveAux_HasType` (instantiating `S` with the final substitution),
   and use `applySubstT_toLMonoTy`.

#### Key supporting lemmas:

- **`Subst.absorbs`**: `S_outer` absorbs `S_inner` when every binding in
  `S_inner` is "already known" to `S_outer`.

- **`LMonoTy.subst_absorbs`**: Absorption implies `subst S_outer (subst S_inner mty) = subst S_outer mty`.

- **`HasType_subst_upgrade`**: Upgrade typing from `S_inner` to `S_outer` via
  absorption + `HasType_subst_fresh_all`.

- **`resolveAux_absorbs`**: Each `resolveAux` call absorbs its input substitution.

- **`unify_absorbs`**: Unification absorbs the pre-unification substitution.

- **`unify_makes_equal`**: Unification makes constrained types equal.

- **`resolveAux_preserves_SubstFreshForGen`**: Substitution keys and values produced by `resolveAux` stay fresh w.r.t. the generator counter.

- **`HasType_subst_fresh_all`**: Typing is preserved under substitution of fresh variables.
-/

/-!
#### Substitution lemmas for `HasType_subst_fresh_all`
-/

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
  grind

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
    grind

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
    simp [SubstWF] at h_wf
    have h_t_sub := Subst.freeVars_of_find_subset S h_find
    grind
  -- Key fact 5: freeVars after subst ⊆ freeVars mty ++ freeVars t
  have h_fv_subset := LMonoTy.freeVars_of_subst_subset [[(a, t)]] mty
  -- Now prove the filter length decreases
  apply List.filter_length_lt_of_imp_witness
    (a := a)
  · -- Implication: k ∈ freeVars(subst) → k ∈ freeVars(mty) for k ∈ keys S
    intro k hk hk_in_subst
    rw [decide_eq_true_eq] at hk_in_subst ⊢
    have hk_in_union := h_fv_subset hk_in_subst
    have : Subst.freeVars [[(a, t)]] = LMonoTy.freeVars t := by
      simp [Subst.freeVars, Maps.values, Map.values]
    grind
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

/-- Weaker variant of `allKeysFresh`: keys of `S` are fresh only with respect to
    **polymorphic** entries in the context (those with non-empty bound variables).
    This condition is preserved through `typeBoundVar` (which adds monomorphic entries)
    and suffices for the polymorphic `fvar` case of `inferFVar_HasType`. -/
def Subst.polyKeysFresh {T : LExprParams} [DecidableEq T.IDMeta]
    (S : Subst) (Γ : TContext T.IDMeta) : Prop :=
  ∀ a, a ∈ Maps.keys S → ∀ (x : T.Identifier) (ty : LTy),
    Γ.types.find? x = some ty → LTy.boundVars ty ≠ [] → a ∉ LTy.freeVars ty

theorem Subst.allKeysFresh_implies_polyKeysFresh {T : LExprParams} [DecidableEq T.IDMeta]
    (S : Subst) (Γ : TContext T.IDMeta)
    (h : Subst.allKeysFresh S Γ) : Subst.polyKeysFresh (T := T) S Γ := by
  intro a ha x ty hf _
  exact h a ha x ty hf

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
      | cons _ _ => simp at hYs
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
    grind

-- Helper: applyLogic preserves none bindings.
private theorem Map.find?_applyLogic_none_h' {new old : SubstOne} {a : TyIdentifier}
    (h : Map.find? old a = none) :
    Map.find? (SubstOne.applyLogic new old) a = none := by
  induction old with
  | nil => simp [SubstOne.applyLogic, Map.find?]
  | cons hd rest ih =>
    simp [SubstOne.applyLogic, Map.find?]
    simp [Map.find?] at h
    grind

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
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
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
  · grind
  -- Case 11: bitvec n1 ≠ n2 — error
  · intro S n1 n2 h_neq h_neq_n relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
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
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  -- Case 14: bitvec, tcons — error
  · intro S size name args h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  -- Case 15: tcons, bitvec — error
  · intro S name args size h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
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


mutual
/-- `LMonoTy.resolveAliases` preserves the context. -/
theorem LMonoTy.resolveAliases_context {IDMeta : Type} [ToFormat IDMeta]
    (mty : LMonoTy) (Env : TEnv IDMeta) (mty' : LMonoTy) (Env' : TEnv IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env')) :
    Env'.context = Env.context := by
  match mty with
  | .ftvar _ =>
    simp [LMonoTy.resolveAliases] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
  | .bitvec _ =>
    simp [LMonoTy.resolveAliases] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_args
      obtain ⟨args', Env1⟩ := v1; simp at h h_args
      -- tconsAliasSimple doesn't change context (Env' = Env1)
      simp only [LMonoTy.tconsAliasSimple] at h
      split at h <;> (obtain ⟨_, h2⟩ := h; rw [← h2])
      all_goals exact LMonoTys.resolveAliases_context args Env args' Env1 h_args
theorem LMonoTys.resolveAliases_context {IDMeta : Type} [ToFormat IDMeta]
    (mtys : LMonoTys) (Env : TEnv IDMeta) (mtys' : LMonoTys) (Env' : TEnv IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env')) :
    Env'.context = Env.context := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases] at h; grind
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
        simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
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
  [Std.ToFormat T.Metadata]

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
      simp only [LMonoTy.subst, hS_false] at hb
      by_cases hax : a = x
      · subst hax
        have : Maps.find? [[(a, t)]] a = some t := by
          simp [Maps.find?, Map.find?]
        rw [this] at hb; exact absurd hb hb_not_t
      · have h_find_none : Maps.find? [[(a, t)]] x = none :=
          Maps.not_mem_keys_find?_none' [[(a, t)]] x (by
            simp [Maps.keys, Map.keys]; exact fun h => hax h.symm)
        rw [h_find_none] at hb; exact hb
    | .bitvec _ =>
      unfold LMonoTy.subst at hb; split at hb <;> exact hb
    | .tcons name args =>
      simp only [LMonoTy.subst, hS_false, LMonoTy.freeVars] at hb ⊢
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
    simp only [LMonoTys.substLogic, hS_false] at hb
    exact hb
  | y :: ys =>
    simp only [LMonoTys.substLogic, hS_false, LMonoTys.freeVars] at hb ⊢
    cases List.mem_append.mp hb with
    | inl h_y => exact List.mem_append_left _ (LMonoTy.freeVars_subst_single_mem a t y b h_y hb_not_t)
    | inr h_ys => exact List.mem_append_right _ (LMonoTys.freeVars_substLogic_single_mem a t ys b h_ys hb_not_t)
end

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    rw [Constraint.unifyOne.eq_def] at h; grind
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
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; grind
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
  · intro S n1 n2 h_neq h_eq_n relS h; grind
  -- Case 11: bitvec n1 ≠ n2 — error
  · intro S n1 n2 h_neq h_neq_n relS h
    rw [Constraint.unifyOne.eq_def] at h; grind
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
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- Case 14: bitvec, tcons — error
  · intro S size name args h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- Case 15: tcons, bitvec — error
  · intro S name args size h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- Case 16: unifyCore []
  · intro S relS h p hp
    rw [Constraints.unifyCore.eq_def] at h; grind
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
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- Case 2: ftvar id, orig_lty; ftvar id == lty
  · intro S id orig_lty h_neq _lty _ _ h_eq_lty relS h k hk
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- Case 3: ftvar id, orig_lty; occurs check
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_occurs relS h
    rw [Constraint.unifyOne.eq_def] at h; grind
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
  · intro S n1 n2 h_neq h_eq_n relS h; grind
  -- Case 11: bitvec n1 ≠ n2 — error
  · intro S n1 n2 h_neq h_neq_n relS h
    rw [Constraint.unifyOne.eq_def] at h; grind
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
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- Case 14: bitvec, tcons — error
  · intro S size name args h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- Case 15: tcons, bitvec — error
  · intro S name args size h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- Case 16: unifyCore []
  · intro S relS h k hk
    rw [Constraints.unifyCore.eq_def] at h; grind
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
            simp [Constraints.freeVars] at h_c; exact h_c
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
    intro S relS h k hk;
    unfold Constraints.unifyCore at h; grind
  | cons c rest ih =>
    intro S relS h k hk
    rw [Constraints.unifyCore.eq_2] at h
    simp only [Bind.bind, Except.bind, Except.mapError] at h
    split at h; · simp at h
    rename_i relS1 h_one; split at h; · simp at h
    rename_i relS2 h_core; simp at h; subst h
    have h_one' : Constraint.unifyOne c S = .ok relS1 := by
      revert h_one; cases Constraint.unifyOne c S <;> simp
    rcases ih relS1.newS relS2 h_core k hk with hk1 | hk2 | hk3
    · rcases Constraint.unifyOne_keys_incl c S relS1 h_one' k hk1 with h1a | h1b | h1c <;> simp [Constraints.freeVars] <;> grind
    · right; left; simp [Constraints.freeVars]; right; exact hk2
    · rcases List.mem_append.mp (relS1.goodSubset hk3) with h_c | h_s
      · right; left; simp [Constraints.freeVars]; left
        simp [Constraints.freeVars] at h_c; exact h_c
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
        grind
      · grind

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

mutual
/-- Free vars of `openVars vars vals body` are contained in `freeVarsList vals`
    when `body`'s free vars are all in `vars` and lengths match. -/
theorem openVars_freeVars_subset
    (vars : List TyIdentifier) (vals : LMonoTys) (body : LMonoTy)
    (h_wf : ∀ tv, tv ∈ LMonoTy.freeVars body → tv ∈ vars)
    (h_len : vars.length = vals.length) :
    ∀ tv, tv ∈ LMonoTy.freeVars (LMonoTy.openVars vars vals body) →
      tv ∈ LMonoTys.freeVars vals := by
  match body with
  | .ftvar x =>
    have h_x_in : x ∈ vars := h_wf x (by simp [LMonoTy.freeVars])
    intro tv htv
    simp only [LMonoTy.openVars] at htv
    -- find? for x in zip vars vals gives some val. tv ∈ freeVars(val) ⊆ freeVars(vals)
    induction vars generalizing vals with
    | nil => simp at h_x_in
    | cons v vs ih =>
      cases vals with
      | nil => simp at h_len
      | cons vl vls =>
        simp only [List.zip, List.zipWith, List.find?, BEq.beq] at htv
        by_cases h_eq : v = x
        · simp [h_eq] at htv; simp [LMonoTys.freeVars]; left; exact htv
        · have h_x_vs : x ∈ vs := by
            cases h_x_in with | head => exact absurd rfl h_eq | tail _ h => exact h
          simp [LMonoTys.freeVars]; right
          -- htv is about openVars (v::vs) (vl::vls) (ftvar x) with x ≠ v
          -- After simp, the find? skips (v,vl) and searches (vs,vls)
          -- So openVars (v::vs) (vl::vls) (ftvar x) = openVars vs vls (ftvar x)
          -- and htv's type matches what ih expects
          simp [h_eq] at htv
          exact ih vls (by simp at h_len; exact h_len)
            (fun tv' htv' => by simp [LMonoTy.freeVars] at htv'; rw [htv']; exact h_x_vs)
            h_x_vs htv
  | .bitvec _ =>
    intro tv htv; simp [LMonoTy.openVars, LMonoTy.freeVars] at htv
  | .tcons nm args =>
    intro tv htv; simp only [LMonoTy.openVars, LMonoTy.freeVars] at htv
    exact openVarsList_freeVars_subset vars vals args
      (fun tv' h => h_wf tv' (by simp [LMonoTy.freeVars]; exact h)) h_len tv htv

/-- List version of `openVars_freeVars_subset`. -/
theorem openVarsList_freeVars_subset
    (vars : List TyIdentifier) (vals bodies : LMonoTys)
    (h_wf : ∀ tv, tv ∈ LMonoTys.freeVars bodies → tv ∈ vars)
    (h_len : vars.length = vals.length) :
    ∀ tv, tv ∈ LMonoTys.freeVars (LMonoTys.openVars vars vals bodies) →
      tv ∈ LMonoTys.freeVars vals := by
  match bodies with
  | [] => intro tv htv; simp [LMonoTys.openVars, LMonoTys.freeVars] at htv
  | hd :: tl =>
    intro tv htv
    simp only [LMonoTys.openVars, LMonoTys.freeVars] at htv
    rw [List.mem_append] at htv
    cases htv with
    | inl h =>
      exact openVars_freeVars_subset vars vals hd
        (fun tv' h' => h_wf tv' (by simp [LMonoTys.freeVars]; left; exact h')) h_len tv h
    | inr h =>
      exact openVarsList_freeVars_subset vars vals tl
        (fun tv' h' => h_wf tv' (by simp [LMonoTys.freeVars]; right; exact h')) h_len tv h
end
omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    simp [LMonoTy.resolveAliases] at h; grind
  | .bitvec _ =>
    simp [LMonoTy.resolveAliases] at h; grind
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_args
      obtain ⟨args', Env1⟩ := v1; simp at h h_args
      -- tconsAliasSimple: split on the alias find? match
      -- tconsAliasSimple doesn't change Env; proof simplified
      simp only [LMonoTy.tconsAliasSimple] at h
      split at h <;> (obtain ⟨_, h2⟩ := h; subst h2)
      -- Env' = Env1 (tconsAliasSimple doesn't change Env). Delegate to list version.
      <;> exact LMonoTys.resolveAliases_allKeysFresh args Env args' Env1 h_args
          h_fresh h_vals_fresh h_alias_wf
          (fun tv htv => h_fvs tv (by simp [LMonoTy.freeVars]; exact htv))

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
    simp [LMonoTy.resolveAliases] at h; grind
  | .bitvec _ =>
    simp [LMonoTy.resolveAliases] at h; grind
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_args
      obtain ⟨args', Env1⟩ := v1; simp at h h_args
      -- tconsAliasSimple: split on the alias find? match
      -- tconsAliasSimple doesn't change Env; proof simplified
      simp only [LMonoTy.tconsAliasSimple] at h
      split at h <;> (obtain ⟨_, h2⟩ := h; subst h2)
      -- Env' = Env1 (tconsAliasSimple doesn't change Env). Delegate to list version.
      <;> exact LMonoTys.resolveAliases_vals_fresh args Env args' Env1 h_args
          h_vals_fresh h_alias_wf
          (fun tv htv => h_fvs tv (by simp [LMonoTy.freeVars]; exact htv))

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
    simp [LMonoTys.resolveAliases] at h; grind
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
        simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
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
    simp [LMonoTys.resolveAliases] at h; grind
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
        simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
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
    simp [LMonoTy.resolveAliases] at h; grind
  | .bitvec _ =>
    simp [LMonoTy.resolveAliases] at h; grind
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    · rename_i v1 h_args_ra
      obtain ⟨args', Env1⟩ := v1; simp at h h_args_ra
      -- tconsAliasSimple doesn't change Env; proof simplified
      simp only [LMonoTy.tconsAliasSimple] at h
      have h_args_fvs : ∀ tv, tv ∈ LMonoTys.freeVars args →
          TContext.isFresh (T := T) tv Env.context := by
        intro tv htv; exact h_fvs tv (by simp [LMonoTy.freeVars]; exact htv)
      have h_args'_fresh :=
        LMonoTys.resolveAliases_fvs_fresh args Env args' Env1 h_args_ra
          h_vals_fresh h_alias_wf h_args_fvs
      have h_ctx_eq := LMonoTys.resolveAliases_context args Env args' Env1 h_args_ra
      split at h
      · -- No alias: output = tcons name args', fvs ⊆ args' fvs
        obtain ⟨h1, _⟩ := h; subst h1
        intro tv htv; simp [LMonoTy.freeVars] at htv
        exact h_args'_fresh tv htv
      · -- Alias: output = expand alias args', fvs ⊆ args' fvs (by alias WF)
        rename_i alias h_find
        obtain ⟨h1, _⟩ := h; subst h1
        intro tv htv
        -- fvs of (expand alias args') = fvs of (openVars typeArgs args' alias.type) ⊆ fvs of args'
        -- since alias.WF: all fvs of alias.type are in typeArgs, and openVars maps
        -- each typeArg to the corresponding element of args'.
        -- So fvs of the result come from args' elements only.
        have h_alias_mem : alias ∈ Env1.context.aliases :=
          List.mem_of_find?_eq_some h_find
        have h_alias_wf := (h_alias_wf alias (by rw [← h_ctx_eq]; exact h_alias_mem))
        have h_pred := List.find?_some h_find
        simp [BEq.beq, decide_eq_true_eq] at h_pred
        simp only [TypeAlias.expand] at htv
        exact h_args'_fresh tv (openVars_freeVars_subset alias.typeArgs args' alias.type
          h_alias_wf.fvs_closed h_pred.2 tv htv)

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
    simp [LMonoTys.resolveAliases] at h; grind
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    · rename_i v1 h_hd
      obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
      split at h; · simp at h
      · rename_i v2 h_tl
        obtain ⟨mrest', Env2⟩ := v2
        simp at h; obtain ⟨h1, _⟩ := h; subst h1
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


omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
mutual
/-- `LMonoTy.resolveAliases` produces a substitution that absorbs the input. -/
private theorem LMonoTy.resolveAliases_absorbs
    (mty : LMonoTy) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env')) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  match mty with
  | .ftvar _ =>
    simp [LMonoTy.resolveAliases] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
    exact Subst.absorbs_refl _ Env.stateSubstInfo.isWF
  | .bitvec _ =>
    simp [LMonoTy.resolveAliases] at h
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
      simp only [LMonoTy.tconsAliasSimple] at h
      split at h <;> (obtain ⟨_, h2⟩ := h; subst h2)
      -- Env' = Env1 (tconsAliasSimple doesn't change Env)
      all_goals exact LMonoTys.resolveAliases_absorbs args Env args' Env1 h_args

/-- `LMonoTys.resolveAliases` produces a substitution that absorbs the input. -/
private theorem LMonoTys.resolveAliases_absorbs
    (mtys : LMonoTys) (Env : TEnv T.IDMeta) (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env')) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases] at h
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
        simp at h
        obtain ⟨_, h2⟩ := h; rw [← h2]
        exact Subst.absorbs_trans
          Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
          (LMonoTy.resolveAliases_absorbs mty Env mty' Env1 h_hd)
          (LMonoTys.resolveAliases_absorbs mrest Env1 mrest' Env2 h_tl)
end

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
      simp at h
      obtain ⟨_, h2⟩ := h; rw [← h2]
      exact LTy_resolveAliases_absorbs ty Env mty0 Env1 h_res
    · -- false branch: error
      simp at h

omit [ToString
  T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
        simp at h
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

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
        simp at h
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
        simp at h
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
      simp only [Map.find?, show k ≠ a from Ne.symm h_ne, ↓reduceIte]
    · -- x ≠ k: entry preserved
      simp only [h_xk, ↓reduceIte, Map.find?]
      grind

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
  /-- Bound variable names in polymorphic context types are gen-fresh:
      they don't collide with generated type variable names. This holds
      because user-defined bound vars (like `a`, `b`) don't start with
      `$__ty`, and `resolveAux` preserves context. -/
  boundVarsFresh : ∀ y ty, Env.context.types.find? y = some ty →
    ∀ v, v ∈ LTy.boundVars ty →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Extract `EnvFreshForGen` from the combined `TEnvWF` invariant. -/
theorem TEnvWF.toEnvFreshForGen {Env : TEnv T.IDMeta} (h : TEnvWF Env) : EnvFreshForGen Env :=
  ⟨h.substFreshForGen, h.ctxFreshForGen⟩

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `ContextFreshForGen` is monotone in the counter. -/
private theorem ContextFreshForGen.mono (Γ : TContext T.IDMeta) (s s' : TState)
    (h : ContextFreshForGen Γ s) (h_le : s.tyGen ≤ s'.tyGen) :
    ContextFreshForGen Γ s' := by
  intro v hv n hn; exact h v hv n (Nat.le_trans h_le hn)


omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] [DecidableEq T.IDMeta] in
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
        simp at h
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
        simp at h
        obtain ⟨_, _, h_env⟩ := h; rw [← h_env]
        simp only [TEnv.addInNewestContext, TEnv.updateContext]
        have h_tyGen := genTyVar_tyGen _ xtyid Env1 h_genTy
        omega

/-- Prove `e_i.sizeOf < n` (or `≤`) from a hypothesis `h : LExpr.sizeOf e = n`. -/
macro "expr_size" h:ident : tactic =>
  `(tactic| (subst $h; first | (rw [varOpen_sizeOf]; simp [LExpr.sizeOf]; omega)
                              | (rw [varOpen_sizeOf]; simp [LExpr.sizeOf])
                              | (simp [LExpr.sizeOf]; omega)))

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
      expr_size h_eq
    have h_sz2 : e2.sizeOf < n := by
      expr_size h_eq
    exact Nat.le_trans
      (Nat.le_trans
        (ih e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1)
        (ih e2.sizeOf h_sz2 e2 rfl e2t C Env1 Env2 h_res2))
      (by have := genTyVar_tyGen Env2 fresh_name Env3 h_gen; omega)
  | .abs m _ bty body =>
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
          expr_size h_eq
        exact Nat.le_trans (typeBoundVar_tyGen_mono C Env bty xv_id xty_val Env1 h_tbv)
          (ih _ h_sz (varOpen 0 (xv_id, some xty_val) body) rfl et' C Env1 Env2 h_rec)
  | .quant m qk _ bty tr body =>
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
              expr_size h_eq
            have h_sz_tr : (varOpen 0 (xv_id, some xty_val) tr).sizeOf < n := by
              expr_size h_eq
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
      expr_size h_eq
    have h_sz2 : e2.sizeOf < n := by
      expr_size h_eq
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
      expr_size h_eq
    have h_sz_t : t.sizeOf < n := by
      expr_size h_eq
    have h_sz_e : e.sizeOf < n := by
      expr_size h_eq
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

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    simp [TState.tyPrefix] at h_eq
    -- h_eq : tyPrefix ++ toString Env.genState.tyGen = tyPrefix ++ toString n
    -- By String left-cancellation + Nat.toString injectivity, Env.genState.tyGen = n
    -- Left-cancel the common prefix to get toString equality,
    -- then Nat.toString injectivity gives k = n, contradicting h_ne.
    rw [String.ext_iff] at h_eq
    simp [String.toList_append] at h_eq
    exact absurd (Nat.toString_injective (String.toList_injective h_eq)) h_ne

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    simp [TGenEnv.genTyVars] at h; grind
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

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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



omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
mutual
private theorem LMonoTy_resolveAliases_genState_mono
    (mty : LMonoTy) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  match mty with
  | .ftvar _ | .bitvec _ =>
    simp [LMonoTy.resolveAliases] at h; grind
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_args; obtain ⟨args', Env1⟩ := v1; simp at h h_args
    -- tconsAliasSimple: split on the alias find? match
    -- tconsAliasSimple doesn't change Env; proof simplified
    simp only [LMonoTy.tconsAliasSimple] at h
    split at h <;> (obtain ⟨_, h2⟩ := h; subst h2)
    all_goals exact LMonoTys_resolveAliases_genState_mono args Env args' Env1 h_args

private theorem LMonoTys_resolveAliases_genState_mono
    (mtys : LMonoTys) (Env : TEnv T.IDMeta) (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases] at h; grind
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_hd; obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    split at h; · simp at h
    rename_i v2 h_tl; obtain ⟨mrest', Env2⟩ := v2
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    exact Nat.le_trans
      (LMonoTy_resolveAliases_genState_mono mty Env mty' Env1 h_hd)
      (LMonoTys_resolveAliases_genState_mono mrest Env1 mrest' Env2 h_tl)
end

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState ∧
    (∀ v, v ∈ LMonoTy.freeVars mty' →
      ∀ n, n ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) := by
  match mty with
  | .ftvar _ | .bitvec _ =>
    simp [LMonoTy.resolveAliases] at h; grind
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_args; obtain ⟨args', Env1⟩ := v1; simp at h h_args
    have h_args_result := LMonoTys_resolveAliases_preserves_SubstFreshForGen args Env args' Env1 h_args
          h_fresh h_aw (fun v hv => h_input v (by simp [LMonoTy.freeVars]; exact hv))
    -- tconsAliasSimple: split on the alias find? match
    simp only [LMonoTy.tconsAliasSimple] at h
    split at h <;> (obtain ⟨h1, h2⟩ := h; subst h1; subst h2)
    · -- No alias: mty' = tcons name args', freeVars = LMonoTys.freeVars args'
      exact ⟨h_args_result.1, h_args_result.2⟩
    · -- Alias found: mty' = expand alias args'. freeVars ⊆ freeVars args' (by openVars_freeVars_subset)
      rename_i alias h_find
      have h_ctx_eq := LMonoTys.resolveAliases_context args Env args' Env1 h_args
      have h_alias_wf := h_aw alias (by rw [← h_ctx_eq]; exact List.mem_of_find?_eq_some h_find)
      have h_pred := List.find?_some h_find
      simp [BEq.beq, decide_eq_true_eq] at h_pred
      exact ⟨h_args_result.1, fun v hv n hn =>
        h_args_result.2 v (openVars_freeVars_subset alias.typeArgs args' alias.type
          h_alias_wf.fvs_closed h_pred.2 v hv) n hn⟩

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
    simp [LMonoTys.resolveAliases] at h; grind
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_hd; obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    split at h; · simp at h
    rename_i v2 h_tl; obtain ⟨mrest', Env2⟩ := v2
    simp at h; obtain ⟨h1, h2⟩ := h; subst h1; subst h2
    have h_ctx_hd := LMonoTy.resolveAliases_context mty Env mty' Env1 h_hd
    have h_input_hd : ∀ v, v ∈ LMonoTy.freeVars mty →
        ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n :=
      fun v hv => h_input v (by simp [LMonoTys.freeVars]; left; exact hv)
    have h_input_tl : ∀ v, v ∈ LMonoTys.freeVars mrest →
        ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n :=
      fun v hv => h_input v (by simp [LMonoTys.freeVars]; right; exact hv)
    have ⟨h_sf1, h_fv1⟩ := LMonoTy_resolveAliases_preserves_SubstFreshForGen
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
        exact h_fv1 v h_in_hd n
          (Nat.le_trans (LMonoTys_resolveAliases_genState_mono mrest Env1 mrest' Env2 h_tl) hn)
      | inr h_in_tl =>
        exact h_ih_tl.2 v h_in_tl n hn
end

omit [ToString
  T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `LTy.resolveAliases` preserves `SubstFreshForGen`. -/
private theorem LTy_resolveAliases_preserves_SubstFreshForGen
    (ty : LTy) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.resolveAliases ty Env = .ok (mty, Env'))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_aw : TContext.AliasesWF Env.context)
    (h_ty_fresh : ∀ v, v ∈ LTy.freeVars ty →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n)
    (h_bv_fresh : ∀ v, v ∈ LTy.boundVars ty →
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
    · grind
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
      -- Polymorphic: genTyVars generates fresh vars, then body is substituted.
      -- Decompose h_inst to extract freshtvs
      simp [LTy.instantiate, Bind.bind, Except.bind] at h_inst
      split at h_inst; · simp at h_inst
      rename_i v_gen h_gen; obtain ⟨freshtvs, Env1⟩ := v_gen; simp at h_inst h_gen
      obtain ⟨h_mty, h_env⟩ := h_inst; subst h_mty; subst h_env
      -- mty0 = subst [zip (x::xs) (map ftvar freshtvs)] body
      -- freeVars ⊆ freeVars(body) ++ Subst.freeVars [zip ...]
      have h_subset := LMonoTy.freeVars_of_subst_subset
        [List.zip (x :: xs) (List.map LMonoTy.ftvar freshtvs)] body hv
      rw [List.mem_append] at h_subset
      cases h_subset with
      | inl h_body =>
        -- v ∈ freeVars body: if v ∉ (x::xs), then v ∈ LTy.freeVars ty, gen-fresh by h_ty_fresh + mono
        -- if v ∈ (x::xs), the substitution would have replaced it (overapprox)
        -- In either case, v is either a known type var (gen-fresh) or was substituted away
        -- For the overapprox case: v ∈ freeVars body and v ∈ (x::xs) means v is a bound var.
        -- Context's knownTypeVars include bound vars, so v is gen-fresh by ContextFreshForGen.
        -- Use h_ty_fresh which covers LTy.freeVars = freeVars(body) \ bound vars
        -- But freeVars_of_subst_subset includes ALL body fvs, not just unbound ones.
        -- For bound vars: they are in context's knownTypeVars, hence gen-fresh by h_cfg.
        -- Since h_cfg : ContextFreshForGen Env.context Env.genState, and
        -- n ≥ genEnv'.genState.tyGen ≥ Env.genState.tyGen:
        -- v ∈ freeVars body where ty = forAll (x::xs) body
        -- Split: v ∈ (x::xs) (bound var) or v ∉ (x::xs) (free var)
        by_cases h_bound : v ∈ (x :: xs)
        · -- Bound var: gen-fresh by h_bv_fresh + monotonicity
          exact h_bv_fresh v (by simp [LTy.boundVars]; exact List.mem_cons.mp h_bound) n
            (Nat.le_trans h_mono_inst hn)
        · -- Free var: v ∈ LTy.freeVars ty, gen-fresh by h_ty_fresh + monotonicity
          have h_in_fvs : v ∈ LTy.freeVars (.forAll (x :: xs) body) := by
            simp only [LTy.freeVars]
            show v ∈ List.filter (fun a => !List.elem a (x :: xs)) body.freeVars
            grind
          exact h_ty_fresh v h_in_fvs n (Nat.le_trans h_mono_inst hn)
      | inr h_subst_fvs =>
        -- v ∈ Subst.freeVars [zip (x::xs) (map ftvar freshtvs)]
        -- The values are (map ftvar freshtvs), so v ∈ freshtvs
        -- Subst.freeVars [m] = m.values.flatMap freeVars
        -- m = zip (x::xs) (map ftvar freshtvs), values = map snd (zip ...) ⊆ map ftvar freshtvs
        -- freeVars (ftvar tv) = [tv], so flatMap gives freshtvs
        -- Then by genTyVars_genFresh': v ≠ tyPrefix ++ toString n
        have h_fresh_gen := genTyVars_genFresh' (x :: xs).length Env.genEnv freshtvs Env1 h_gen
        -- Need: v ∈ freshtvs
        -- h_subst_fvs : v ∈ Subst.freeVars [zip (x::xs) (map ftvar freshtvs)]
        -- Subst.freeVars = Maps.values.flatMap freeVars
        -- For single scope [m], Maps.values [m] = Map.values m
        -- Map.values (zip vars vals) ⊆ vals
        -- freeVars(ftvar tv) = [tv]
        -- So v ∈ freshtvs
        have h_v_in_freshtvs : v ∈ freshtvs := by
          -- v ∈ Subst.freeVars [zip (x::xs) (map ftvar freshtvs)]
          -- Unfold: Subst.freeVars = Maps.values.flatMap freeVars
          -- Maps.values [m] = Map.values m
          -- Map.values (zip vars vals): the second components of the zip
          -- freeVars (ftvar tv) = [tv]
          -- So v ∈ flatMap freeVars (Map.values (zip vars (map ftvar freshtvs)))
          -- ⊆ flatMap freeVars (map ftvar freshtvs) = freshtvs
          -- Prove by showing: for any vars vals,
          --   v ∈ (Map.values (zip vars (map ftvar tvs))).flatMap freeVars → v ∈ tvs
          -- Prove: v ∈ Subst.freeVars [zip vars (map ftvar freshtvs)] → v ∈ freshtvs
          -- by induction on vars/freshtvs
          simp only [Subst.freeVars, Maps.values] at h_subst_fvs
          rw [List.mem_flatMap] at h_subst_fvs
          obtain ⟨mty_val, h_in_vals, h_fv⟩ := h_subst_fvs
          -- mty_val ∈ Map.values (zip (x::xs) (map ftvar freshtvs))
          -- Map.values of zip = second components ⊆ map ftvar freshtvs
          suffices ∀ (vars : List TyIdentifier) (tvs : List TyIdentifier),
              mty_val ∈ Map.values (List.zip vars (tvs.map LMonoTy.ftvar)) →
              ∃ t ∈ tvs, mty_val = .ftvar t by
            simp at h_in_vals
            obtain ⟨t, h_t_mem, h_eq⟩ := this (x :: xs) freshtvs h_in_vals
            rw [h_eq] at h_fv; simp [LMonoTy.freeVars] at h_fv
            rw [h_fv]; exact h_t_mem
          intro vars tvs h_val
          induction vars generalizing tvs with
          | nil => simp [List.zip, Map.values] at h_val
          | cons a as ih =>
            cases tvs with
            | nil => simp [List.zip, List.map, Map.values] at h_val
            | cons t ts =>
              simp only [List.map, List.zip, List.zipWith, Map.values] at h_val
              cases h_val with
              | head => exact ⟨t, .head _, rfl⟩
              | tail _ h => obtain ⟨t', h_mem, h_eq⟩ := ih ts h
                            exact ⟨t', .tail _ h_mem, h_eq⟩
        exact h_fresh_gen v h_v_in_freshtvs n hn
  exact (LMonoTy_resolveAliases_preserves_SubstFreshForGen mty0 _ mty Env' h
    (h_eq ▸ SubstFreshForGen.mono _ _ _ h_fresh h_mono_inst)
    (h_ctx_eq ▸ h_aw)
    h_mty0_fresh).1

omit [ToString
  T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `LTy.instantiateWithCheck` preserves `SubstFreshForGen`. -/
private theorem LTy_instantiateWithCheck_preserves_SubstFreshForGen
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env'))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_aw : TContext.AliasesWF Env.context)
    (h_ty_fresh : ∀ v, v ∈ LTy.freeVars ty →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n)
    (h_bv_fresh : ∀ v, v ∈ LTy.boundVars ty →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState := by
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i v1 h_res; obtain ⟨mty0, Env1⟩ := v1; dsimp at h h_res
  split at h; · simp at h  -- checkNoFutureGenVars
  split at h
  · simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    exact LTy_resolveAliases_preserves_SubstFreshForGen ty Env mty0 Env1 h_res h_fresh h_aw h_ty_fresh h_bv_fresh
  · simp at h

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `LMonoTy.instantiateWithCheck` preserves `SubstFreshForGen`. -/
private theorem LMonoTy_instantiateWithCheck_preserves_SubstFreshForGen
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (mty, Env'))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_aw : TContext.AliasesWF Env.context) :
    SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState := by
  simp only [LMonoTy.instantiateWithCheck] at h
  split at h; · simp at h
  rename_i instTypes Env1 h_inst
  simp [Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i v2 h_res; obtain ⟨mtyi, Env2⟩ := v2; dsimp at h h_res
  split at h; · simp at h  -- checkNoFutureGenVars
  split at h
  · simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    have h_subst_eq : Env1.stateSubstInfo = Env.stateSubstInfo := by
      simp [LMonoTys.instantiateEnv] at h_inst
      split at h_inst; · simp at h_inst
      simp at h_inst; obtain ⟨_, h_env⟩ := h_inst; rw [← h_env]
    have h_mono : Env1.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen :=
      LMonoTys.instantiateEnv_tyGen_mono _ _ Env _ _ h_inst
    have h_ctx_eq : Env1.context = Env.context :=
      LMonoTys.instantiateEnv_context _ _ Env _ Env1 h_inst
    exact (LMonoTy_resolveAliases_preserves_SubstFreshForGen _ Env1 mtyi Env2 h_res
      (h_subst_eq ▸ SubstFreshForGen.mono _ _ _ h_fresh h_mono)
      (h_ctx_eq ▸ h_aw)
      (by -- instTypes[0] freeVars gen-fresh: instantiateEnv replaces all freeVars with
          -- generated vars (since domain = mty_in.freeVars = all freeVars of [mty_in])
          have h_closed : ∀ tv, tv ∈ LMonoTys.freeVars [mty_in] → tv ∈ mty_in.freeVars := by
            simp [LMonoTys.freeVars]
          have h_gen := instantiateEnv_freeVars_genFresh_closed
            mty_in.freeVars [mty_in] Env instTypes Env1 h_inst h_closed
          intro v hv n hn
          have h_in_all : v ∈ LMonoTys.freeVars instTypes := by
            have h_len : 0 < instTypes.length := by
              have := LMonoTys.instantiateEnv_length _ _ _ _ _ h_inst; simp at this; omega
            cases instTypes with
            | nil => simp at h_len
            | cons hd tl => simp [LMonoTys.freeVars]; left; exact hv
          exact h_gen v h_in_all n hn)).1
  · simp at h

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

/-- `isFutureGenVar` returns `true` on a generated name `tyPrefix ++ toString n`
    when `n ≥ state.tyGen`. -/
private theorem isFutureGenVar_of_tyPrefix (n : Nat) (state : TState)
    (hn : n ≥ state.tyGen) :
    TState.isFutureGenVar state (TState.tyPrefix ++ toString n) = true := by
  simp only [TState.isFutureGenVar, TState.tyPrefix]
  rw [String.toList_append, isPrefixOf_append_self]
  simp only [ite_true]
  rw [List.drop_left, listCharToNat?_roundtrip]
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

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
  · simp at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
    exact LTy.resolveAliases_context ty Env mty' Env1 h_ra
  · simp at h

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
  · simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    rw [LMonoTy.resolveAliases_context _ _ mty' Env2 h_ra]
    exact LMonoTys.instantiateEnv_context _ _ Env _ _ h_inst
  · simp at h
omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
private theorem LTy_instantiateWithCheck_freeVars_fresh
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env')) :
    ∀ v, v ∈ LMonoTy.freeVars mty →
      ∀ n, n ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  -- Extract the checkNoFutureGenVars success from h
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i v1 h_res; obtain ⟨mty0, Env1⟩ := v1; dsimp at h h_res
  split at h; · simp at h  -- checkNoFutureGenVars failed → contradiction
  rename_i h_check
  split at h
  · simp at h; obtain ⟨h_mty, h_env⟩ := h
    rw [← h_mty, ← h_env]
    -- h_check : !checkNoFutureGenVars mty0 Env1.genEnv.genState = false
    -- i.e., checkNoFutureGenVars mty0 Env1.genEnv.genState = true
    exact checkNoFutureGenVars_imp_fresh mty0 Env1.genEnv.genState (by simp at h_check; exact h_check)
  · simp at h

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Free vars of `LMonoTy.instantiateWithCheck` output satisfy freshness for the output gen state. -/
private theorem LMonoTy_instantiateWithCheck_freeVars_fresh
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (mty, Env')) :
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
  · simp at h; obtain ⟨h_mty, h_env⟩ := h
    rw [← h_mty, ← h_env]
    exact checkNoFutureGenVars_imp_fresh mtyi Env2.genEnv.genState (by simp at h_check; exact h_check)
  · simp at h

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `inferFVar` preserves `SubstFreshForGen`. -/
private theorem inferFVar_preserves_SubstFreshForGen
    (C : LContext T) (Env : TEnv T.IDMeta) (x : T.Identifier) (fty : Option LMonoTy)
    (ty_res : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : inferFVar C Env x fty = .ok (ty_res, Env'))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_ctx : ContextFreshForGen Env.context Env.genEnv.genState)
    (h_aw : TContext.AliasesWF Env.context)
    (h_bvf : ∀ y ty, Env.context.types.find? y = some ty →
      ∀ v, v ∈ LTy.boundVars ty →
        ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) :
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
    exact LTy_instantiateWithCheck_preserves_SubstFreshForGen _ C Env mty Env1 h_inst h_fresh h_aw
      (fun v hv n hn => h_ctx v (TContext.mem_knownTypeVars_of_find h_find_ctx hv) n hn)
      (h_bvf _ _ h_find_ctx)
  | some fty_val =>
    simp only [Except.mapError] at h
    split at h; · simp at h
    rename_i v2 h_inst2; obtain ⟨fty_inst, Env2⟩ := v2; dsimp at h h_inst2
    split at h; · simp at h
    rename_i v3 h_mapError
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]; simp [TEnv.updateSubst]
    have h_fresh1 := LTy_instantiateWithCheck_preserves_SubstFreshForGen
      _ C Env mty Env1 h_inst h_fresh h_aw
      (fun v hv n hn => h_ctx v (TContext.mem_knownTypeVars_of_find h_find_ctx hv) n hn)
      (h_bvf _ _ h_find_ctx)
    have h_fresh2 := LMonoTy_instantiateWithCheck_preserves_SubstFreshForGen
      fty_val C Env1 fty_inst Env2 h_inst2 h_fresh1 h_aw1
    have h_unify := unify_of_mapError h_mapError
    exact unify_preserves_SubstFreshForGen h_unify h_fresh2 (fun v hv n hn => by
      simp [Constraints.freeVars, Constraint.freeVars] at hv
      cases hv with
      | inl h_fty =>
        exact LMonoTy_instantiateWithCheck_freeVars_fresh fty_val C Env1 fty_inst Env2
          h_inst2 v h_fty n hn
      | inr h_ty =>
        have h_ty_fresh := LTy_instantiateWithCheck_freeVars_fresh _ C Env mty Env1
          h_inst v h_ty
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

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    simp at h
    obtain ⟨h_xv, _, _⟩ := h; subst h_xv
    exact not_mem_knownVars_find_none Env.context xv_raw h_fresh
  | none =>
    simp; intro h; split at h; · simp at h
    rename_i v_tg _; obtain ⟨_, _⟩ := v_tg
    simp at h
    obtain ⟨h_xv, _, _⟩ := h; subst h_xv
    exact not_mem_knownVars_find_none Env.context xv_raw h_fresh

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    simp at h
    obtain ⟨_, _, h_env1⟩ := h; rw [← h_env1]
    simp [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context,
          Maps.addInNewest, Maps.push, Maps.pop, Maps.newest]
  | none =>
    simp; intro h; split at h; · simp at h
    rename_i v_tg _; obtain ⟨_, Env_mid⟩ := v_tg
    simp at h
    obtain ⟨_, _, h_env1⟩ := h; rw [← h_env1]
    simp [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context,
          Maps.addInNewest, Maps.push, Maps.pop, Maps.newest]

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `typeBoundVar` preserves `SubstFreshForGen`. -/
private theorem typeBoundVar_preserves_SubstFreshForGen
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env'))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_aw : TContext.AliasesWF Env.context) :
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
        simp at h
        obtain ⟨_, _, h_env⟩ := h; rw [← h_env]
        -- addInNewestContext only changes context, not subst or genState
        simp only [TEnv.addInNewestContext, TEnv.updateContext]
        -- LMonoTy.instantiateWithCheck preserves SubstFreshForGen
        exact LMonoTy_instantiateWithCheck_preserves_SubstFreshForGen
          bty_mty C genResult.snd _ _ h_inst
          (h_gen_subst ▸ SubstFreshForGen.mono _ _ _ h_fresh h_gen_tyGen)
          (h_gen_ctx ▸ h_aw)
    · -- bty = none
      split at h
      · contradiction
      · rename_i v1 h_genTy
        obtain ⟨xtyid, Env1⟩ := v1
        simp at h
        obtain ⟨_, _, h_env⟩ := h; rw [← h_env]
        -- addInNewestContext only changes context, not subst or genState
        simp only [TEnv.addInNewestContext, TEnv.updateContext]
        -- genTyVar preserves stateSubstInfo and increments counter
        have h_subst := TEnv.genTyVar_subst _ xtyid Env1 h_genTy
        rw [h_subst, h_gen_subst]
        exact SubstFreshForGen.mono _ _ _ h_fresh
          (by have := genTyVar_tyGen _ xtyid Env1 h_genTy; omega)

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
      TContext.types.knownTypeVars,
      List.mem_append, List.not_mem_nil, or_false] at h
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

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    simp at h
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
    have h_fv_fresh := LMonoTy_instantiateWithCheck_freeVars_fresh bty_mty C genResult.snd _ Env_inst h_inst
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
    simp at h
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

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    simp at h
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
    simp at h
    obtain ⟨_, _, h_env⟩ := h; rw [← h_env]
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context, TContext.AliasesWF]
    have h_genTy_ctx := TEnv.genTyVar_context genResult.snd xtyid Env1 h_genTy
    show ∀ a, a ∈ Env1.genEnv.context.aliases → a.WF
    rw [show Env1.genEnv.context = Env1.context from rfl,
        h_genTy_ctx, h_gen_ctx]
    exact h_aw

omit [DecidableEq IDMeta] in
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
    grind


omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    simp at h
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
    simp; intro h; split at h; · simp at h
    rename_i v_tg h_tg; obtain ⟨xtyid, Env_mid⟩ := v_tg
    simp at h
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

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `typeBoundVar` preserves `boundVarsFresh`.
    The new entry `(xv, forAll [] xty)` has `boundVars = []` (vacuously fresh).
    Existing entries are unchanged; gen counter is monotone. -/
private theorem typeBoundVar_preserves_boundVarsFresh
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env'))
    (h_bf : ∀ y ty, Env.context.types.find? y = some ty →
      ∀ v, v ∈ LTy.boundVars ty →
        ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    ∀ y ty, Env'.context.types.find? y = some ty →
      ∀ v, v ∈ LTy.boundVars ty →
        ∀ n, n ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  have h_mono := typeBoundVar_tyGen_mono C Env bty xv xty Env' h
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i v_gen h_gen; obtain ⟨xv_raw, Env_g⟩ := v_gen
  have h_g_ctx : Env_g.context = Env.context := liftGenEnv_context Env _ Env_g h_gen
  revert h; cases bty with
  | some bty_val =>
    simp only []; intro h
    generalize h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g = res_ic at h
    match res_ic with
    | .error _ => simp at h
    | .ok (bty_mty, Env_mid) =>
    simp at h
    obtain ⟨h_xv, h_xty, h_env'⟩ := h
    have h_mid_ctx : Env_mid.context = Env.context :=
      (LMonoTy_instantiateWithCheck_context' bty_val C Env_g bty_mty Env_mid h_ic).trans h_g_ctx
    subst h_xv; subst h_xty; subst h_env'
    intro y ty_found h_find v hv n hn
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_find
    rw [show Env_mid.genEnv.context = Env.genEnv.context from h_mid_ctx] at h_find
    rcases Maps.find?_addInNewest_single Env.genEnv.context.types xv_raw (.forAll [] bty_mty) y with
      ⟨h_new, _⟩ | h_old
    · rw [h_new] at h_find; injection h_find with h_find; subst h_find
      simp [LTy.boundVars] at hv
    · rw [h_old] at h_find
      exact h_bf y ty_found h_find v hv n (Nat.le_trans h_mono hn)
  | none =>
    simp; intro h; split at h; · simp at h
    rename_i v_tg h_tg; obtain ⟨xtyid, Env_mid⟩ := v_tg
    simp at h
    obtain ⟨h_xv, h_xty, h_env'⟩ := h
    have h_mid_ctx : Env_mid.context = Env.context :=
      (TEnv.genTyVar_context Env_g xtyid Env_mid h_tg).trans h_g_ctx
    subst h_xv; subst h_xty; subst h_env'
    intro y ty_found h_find v hv n hn
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_find
    rw [show Env_mid.genEnv.context = Env.genEnv.context from h_mid_ctx] at h_find
    rcases Maps.find?_addInNewest_single Env.genEnv.context.types xv_raw (.forAll [] (LMonoTy.ftvar xtyid)) y with
      ⟨h_new, _⟩ | h_old
    · rw [h_new] at h_find; injection h_find with h_find; subst h_find
      simp [LTy.boundVars] at hv
    · rw [h_old] at h_find
      exact h_bf y ty_found h_find v hv n (Nat.le_trans h_mono hn)

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    · simp at h
      obtain ⟨_, h2⟩ := h; rw [← h2]
      exact LTy.resolveAliases_context ty Env mty' Env1 h_ra
    · simp at h

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
      · simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
        rw [LMonoTy.resolveAliases_context _ _ mty' Env2 h_ra]
        exact LMonoTys.instantiateEnv_context _ _ Env _ _ h_inst
      · simp at h

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
            simp at h_tbv
            obtain ⟨h_xv_eq, h_xty_eq, h_env1⟩ := h_tbv
            subst h_xv_eq; subst h_xty_eq
            exact ⟨Env_mid,
              (LMonoTy_instantiateWithCheck_context bty_val C Env_g mty_ic Env_mid h_ic).trans h_g_ctx,
              h_env1.symm⟩
        | none =>
          simp; intro h_tbv
          generalize h_tg : TEnv.genTyVar Env_g = res_tg at h_tbv
          match res_tg with
          | .error _ => simp at h_tbv
          | .ok (xtyid, Env_mid) =>
            simp at h_tbv
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

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
      simp [inferConst] at h_ic; grind
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
  | .abs m _ bty body =>
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
            (by show (varOpen 0 (xv, some xty) body).sizeOf < (LExpr.abs m _ bty body).sizeOf
                rw [varOpen_sizeOf]; simp [LExpr.sizeOf])
            et_ C Env1 Env2 h_ra h_ne1
        exact typeBoundVar_erase_context C Env bty xv xty Env1 h_tbv Env2 h_ctx_ra
          (typeBoundVar_xv_fresh_in_context C Env bty xv xty Env1 h_tbv)
          h_ne
  | .quant m qk _ bty triggers body =>
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
                (by show (varOpen 0 (xv, some xty) body).sizeOf < (LExpr.quant m qk _ bty triggers body).sizeOf
                    rw [varOpen_sizeOf]; simp [LExpr.sizeOf]; omega)
                et_ C Env1 Env2 h_ra1 h_ne1
            have h_ctx3 : Env3.context = Env2.context :=
              ih (LExpr.varOpen 0 (xv, some xty) triggers)
                (by show (varOpen 0 (xv, some xty) triggers).sizeOf < (LExpr.quant m qk _ bty triggers body).sizeOf
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
/-- `removeAll` produces `[]` when every element of the source is in the filter list. -/
private theorem List.removeAll_eq_nil_of_forall_mem [BEq α] [LawfulBEq α]
    {xs ys : List α} (h : ∀ x, x ∈ xs → x ∈ ys) :
    xs.removeAll ys = [] := by
  simp only [List.removeAll]
  rw [List.filter_eq_nil_iff]
  grind

/-- `freeVars (mkArrow mty mtys)` is `freeVars mty ++ LMonoTys.freeVars mtys`. -/
private theorem LMonoTy.freeVars_mkArrow (mty : LMonoTy) :
    ∀ (mtys : LMonoTys),
    LMonoTy.freeVars (LMonoTy.mkArrow mty mtys) =
    LMonoTy.freeVars mty ++ LMonoTys.freeVars mtys := by
  intro mtys
  induction mtys generalizing mty with
  | nil => simp [LMonoTy.mkArrow, LMonoTys.freeVars]
  | cons m mrest ih =>
    simp only [LMonoTy.mkArrow, LMonoTy.arrow, LMonoTy.freeVars, LMonoTys.freeVars]
    rw [ih m]; simp

/-- `LMonoTys.freeVars (xs ++ ys) = freeVars xs ++ freeVars ys`. -/
private theorem LMonoTys.freeVars_append (xs ys : LMonoTys) :
    LMonoTys.freeVars (xs ++ ys) = LMonoTys.freeVars xs ++ LMonoTys.freeVars ys := by
  induction xs with
  | nil => simp [LMonoTys.freeVars]
  | cons x xrest ih => simp [LMonoTys.freeVars, ih, List.append_assoc]

-- Combined proof by well-founded induction on sizeOf, proving both single-type
-- and list versions together.
mutual
private def mtySize (mty : LMonoTy) : Nat :=
  match mty with
  | .ftvar _ => 1
  | .bitvec _ => 1
  | .tcons _ args => 1 + mtysSize args
private def mtysSize (mtys : LMonoTys) : Nat :=
  match mtys with
  | [] => 0
  | mty :: rest => 1 + mtySize mty + mtysSize rest
end

private theorem freeVars_destructArrow_subset_combined (n : Nat) :
    (∀ (mty : LMonoTy), mtySize mty ≤ n →
      LMonoTys.freeVars (LMonoTy.destructArrow mty) ⊆ LMonoTy.freeVars mty) ∧
    (∀ (mtys : LMonoTys), mtysSize mtys ≤ n →
      LMonoTys.freeVars (LMonoTys.destructArrow mtys) ⊆ LMonoTys.freeVars mtys) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  refine ⟨?_, ?_⟩
  · -- Single type case
    intro mty h_sz
    unfold LMonoTy.destructArrow
    split
    · -- arrow case: tcons "arrow" (t1 :: trest) => t1 :: LMonoTys.destructArrow trest
      rename_i t1 trest
      simp only [LMonoTys.freeVars, LMonoTy.freeVars]
      intro x hx
      cases List.mem_append.mp hx with
      | inl h1 => exact List.mem_append_left _ h1
      | inr h2 =>
        -- Need: LMonoTys.freeVars (LMonoTys.destructArrow trest) ⊆ LMonoTys.freeVars trest
        have h_trest_sz : mtysSize trest < n := by
          simp only [mtySize, mtysSize] at h_sz ⊢
          omega
        have := (ih (mtysSize trest) h_trest_sz).2 trest (Nat.le_refl _)
        exact List.mem_append_right _ (this h2)
    · -- non-arrow case: returns [mty]
      simp [LMonoTys.freeVars]
  · -- List case
    intro mtys h_sz
    match mtys with
    | [] => simp [LMonoTys.destructArrow, LMonoTys.freeVars]
    | mty :: mrest =>
      simp only [LMonoTys.destructArrow, LMonoTys.freeVars]
      rw [LMonoTys.freeVars_append]
      intro x hx
      cases List.mem_append.mp hx with
      | inl h1 =>
        -- Use IH on mty (mtySize mty < mtysSize (mty :: mrest))
        have h_mty_sz : mtySize mty < n := by
          simp only [mtysSize] at h_sz
          omega
        exact List.mem_append_left _ ((ih (mtySize mty) h_mty_sz).1 mty (Nat.le_refl _) h1)
      | inr h2 =>
        -- Use IH on mrest (mtysSize mrest < mtysSize (mty :: mrest))
        have h_mrest_sz : mtysSize mrest < n := by
          simp only [mtysSize] at h_sz
          omega
        exact List.mem_append_right _ ((ih (mtysSize mrest) h_mrest_sz).2 mrest (Nat.le_refl _) h2)

private theorem LMonoTy.freeVars_destructArrow_subset (mty : LMonoTy) :
    LMonoTys.freeVars (LMonoTy.destructArrow mty) ⊆ LMonoTy.freeVars mty :=
  (freeVars_destructArrow_subset_combined (mtySize mty)).1 mty (Nat.le_refl _)

private theorem LMonoTys.freeVars_destructArrow_subset (mtys : LMonoTys) :
    LMonoTys.freeVars (LMonoTys.destructArrow mtys) ⊆ LMonoTys.freeVars mtys :=
  (freeVars_destructArrow_subset_combined (mtysSize mtys)).2 mtys (Nat.le_refl _)

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Factory function types produced by `LFunc.type` have empty `freeVars`
    when the function satisfies `LFuncWF`. -/
private theorem LFunc.type_freeVars_eq_nil [DecidableEq T.IDMeta]
    (func : LFunc T) (ty : LTy) (h_type : func.type = .ok ty)
    (h_wf : LFuncWF func) :
    LTy.freeVars ty = [] := by
  cases ty with
  | forAll vars body =>
  simp [LTy.freeVars]
  apply List.removeAll_eq_nil_of_forall_mem
  unfold LFunc.type at h_type; simp only [Bind.bind, Except.bind] at h_type
  split at h_type; · simp at h_type
  split at h_type; · simp at h_type
  generalize h_vals : func.inputs.values = vals at h_type
  cases vals with
  | nil =>
    injection h_type with h1; injection h1 with h1a h1b; subst h1a; subst h1b
    exact h_wf.output_typevars_in_typeArgs
  | cons ity irest =>
    injection h_type with h1; injection h1 with h1a h1b; subst h1a; subst h1b
    rw [LMonoTy.freeVars_mkArrow]
    intro x hx
    simp [LMonoTys.freeVars_append, List.mem_append] at hx
    rcases hx with hx_ity | hx_irest | hx_destr
    · exact h_wf.inputs_typevars_in_typeArgs ity (h_vals ▸ List.mem_cons_self) hx_ity
    · have h_irest_sub : ∀ ty, ty ∈ irest → ty ∈ func.inputs.values :=
        fun ty ht => h_vals ▸ List.mem_cons_of_mem _ ht
      have : ∀ (xs : LMonoTys), (∀ ty, ty ∈ xs → ty ∈ func.inputs.values) →
          ∀ v, v ∈ LMonoTys.freeVars xs → v ∈ func.typeArgs := by
        intro xs h_sub v hv
        induction xs with
        | nil => simp [LMonoTys.freeVars] at hv
        | cons t ts ih =>
          simp [LMonoTys.freeVars, List.mem_append] at hv
          rcases hv with hv_t | hv_ts
          · exact h_wf.inputs_typevars_in_typeArgs t (h_sub t List.mem_cons_self) hv_t
          · exact ih (fun ty ht => h_sub ty (List.mem_cons_of_mem _ ht)) hv_ts
      exact this irest h_irest_sub x hx_irest
    · exact h_wf.output_typevars_in_typeArgs (LMonoTy.freeVars_destructArrow_subset func.output hx_destr)

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Factory function types produced by `LFunc.type` have `boundVars = func.typeArgs`. -/
private theorem LFunc.type_boundVars_eq_typeArgs [DecidableEq T.IDMeta]
    (func : LFunc T) (ty : LTy) (h_type : func.type = .ok ty) :
    LTy.boundVars ty = func.typeArgs := by
  unfold LFunc.type at h_type; simp only [Bind.bind, Except.bind] at h_type
  split at h_type; · simp at h_type
  split at h_type; · simp at h_type
  generalize h_vals : func.inputs.values = vals at h_type
  cases vals with
  | nil =>
    simp at h_type; subst h_type; simp [LTy.boundVars]
  | cons _ _ =>
    simp at h_type; subst h_type; simp [LTy.boundVars]

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
mutual
/-- `LMonoTy.resolveAliases` does not grow free variables when aliases are WF. -/
private theorem LMonoTy_resolveAliases_freeVars_subset
    (mty : LMonoTy) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    ∀ v, v ∈ LMonoTy.freeVars mty' → v ∈ LMonoTy.freeVars mty := by
  match mty with
  | .ftvar _ | .bitvec _ =>
    simp [LMonoTy.resolveAliases] at h; grind
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_args; obtain ⟨args', Env1⟩ := v1; simp at h h_args
    simp only [LMonoTy.tconsAliasSimple] at h
    generalize h_alias_find : List.find? _ Env1.context.aliases = alias_opt at h
    cases alias_opt with
    | none =>
      simp at h; obtain ⟨h1, _⟩ := h; subst h1
      intro v hv; simp [LMonoTy.freeVars] at hv ⊢
      exact LMonoTys_resolveAliases_freeVars_subset args Env args' Env1 h_args h_aw v hv
    | some alias =>
      simp at h; obtain ⟨h1, _⟩ := h; subst h1
      have h_ctx_eq := LMonoTys.resolveAliases_context args Env args' Env1 h_args
      have h_aw1 : TContext.AliasesWF Env1.context := h_ctx_eq ▸ h_aw
      have h_alias_wf := h_aw1 alias (List.mem_of_find?_eq_some h_alias_find)
      have h_pred := List.find?_some h_alias_find
      simp [BEq.beq, decide_eq_true_eq] at h_pred
      intro v hv; simp [LMonoTy.freeVars]
      exact LMonoTys_resolveAliases_freeVars_subset args Env args' Env1 h_args h_aw v
        (openVars_freeVars_subset alias.typeArgs args' alias.type
          h_alias_wf.fvs_closed h_pred.2 v hv)

/-- `LMonoTys.resolveAliases` does not grow free variables when aliases are WF. -/
private theorem LMonoTys_resolveAliases_freeVars_subset
    (mtys : LMonoTys) (Env : TEnv T.IDMeta) (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    ∀ v, v ∈ LMonoTys.freeVars mtys' → v ∈ LMonoTys.freeVars mtys := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases] at h; grind
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_hd; obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    split at h; · simp at h
    rename_i v2 h_tl; obtain ⟨mrest', Env2⟩ := v2
    simp at h; obtain ⟨h1, _⟩ := h; subst h1
    have h_ctx_eq := LMonoTy.resolveAliases_context mty Env mty' Env1 h_hd
    intro v hv; simp [LMonoTys.freeVars, List.mem_append] at hv ⊢
    rcases hv with hv_hd | hv_tl
    · left; exact LMonoTy_resolveAliases_freeVars_subset mty Env mty' Env1 h_hd h_aw v hv_hd
    · right; exact LMonoTys_resolveAliases_freeVars_subset mrest Env1 mrest' Env2 h_tl
        (h_ctx_eq ▸ h_aw) v hv_tl
end


omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Combined result: context preservation, SubstFreshForGen preservation, and output type freshness.
    These are proved together by strong induction to avoid circular dependencies. -/
private theorem transfer_boundVarsFresh
    {Env Env' : TEnv T.IDMeta}
    (h_bf : ∀ y ty, Env.context.types.find? y = some ty →
      ∀ v, v ∈ LTy.boundVars ty →
        ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n)
    (h_ctx : Env'.context = Env.context)
    (h_mono : Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen) :
    ∀ y ty, Env'.context.types.find? y = some ty →
      ∀ v, v ∈ LTy.boundVars ty →
        ∀ n, n ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  intro y ty h_f v hv n hn
  exact h_bf y ty (by rwa [h_ctx] at h_f) v hv n (Nat.le_trans h_mono hn)

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
private theorem resolveAux_preserves_combined :
    ∀ (n : Nat) (e : LExpr T.mono), e.sizeOf = n →
      ∀ (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      Env.context.types ≠ [] →
      Env'.context = Env.context ∧
      (SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState →
       ContextFreshForGen Env.context Env.genEnv.genState →
       TContext.AliasesWF Env.context →
       FactoryWF C.functions →
       (∀ y ty, Env.context.types.find? y = some ty →
         ∀ v, v ∈ LTy.boundVars ty →
           ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) →
       SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState ∧
       (∀ v, v ∈ LMonoTy.freeVars et.toLMonoTy →
         ∀ k, k ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString k)) := by
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
  -- Helper: extract output type freshness from ih
  have ih_output_fresh := fun (sz : Nat) (h_sz : sz < n) (e' : LExpr T.mono) (h_eq' : e'.sizeOf = sz)
      (et' : LExprT T.mono) (C' : LContext T) (Env0 Env0' : TEnv T.IDMeta)
      (h' : resolveAux C' Env0 e' = .ok (et', Env0'))
      (h_ne0 : Env0.context.types ≠ [])
      (h_sf0 : SubstFreshForGen Env0.stateSubstInfo Env0.genEnv.genState)
      (h_cf0 : ContextFreshForGen Env0.context Env0.genEnv.genState)
      (h_aw0 : TContext.AliasesWF Env0.context)
      (h_fwf0 : FactoryWF C'.functions)
      (h_bvf0 : ∀ y ty, Env0.context.types.find? y = some ty →
        ∀ v, v ∈ LTy.boundVars ty →
          ∀ n, n ≥ Env0.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) =>
    ((ih sz h_sz e' h_eq' et' C' Env0 Env0' h' h_ne0).2 h_sf0 h_cf0 h_aw0 h_fwf0 h_bvf0).2
  exact ⟨resolveAux_context e et C Env Env' h h_ne,
  fun h_fresh h_ctx h_aw h_fwf h_bvf => by
  match e with
  | .const m c =>
    simp [resolveAux, inferConst] at h
    split at h
    · simp [Bind.bind, Except.bind] at h; obtain ⟨h_et, h2⟩ := h; rw [← h2]
      exact ⟨h_fresh, fun v hv => by
        rw [← h_et] at hv; simp [toLMonoTy] at hv
        simp [LConst.ty_freeVars] at hv⟩
    · exact absurd h (by simp [Bind.bind, Except.bind])
  | .bvar _ _ => simp [resolveAux] at h
  | .fvar m x fty =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_infer; obtain ⟨ty_res, Env_res⟩ := v1; simp at h
    obtain ⟨h_et, h2⟩ := h; rw [← h2]
    constructor
    · exact inferFVar_preserves_SubstFreshForGen C Env x fty _ Env_res h_infer h_fresh h_ctx h_aw h_bvf
    · -- Output type freshness for fvar
      subst h_et h2
      intro v hv k hk
      simp [toLMonoTy] at hv
      -- Decompose inferFVar to extract instantiateWithCheck
      simp only [inferFVar, Bind.bind, Except.bind] at h_infer
      split at h_infer; · simp at h_infer
      rename_i ty_found h_find_ctx
      split at h_infer; · simp at h_infer
      rename_i v2 h_inst; obtain ⟨mty, Env1⟩ := v2; dsimp at h_infer h_inst
      have h_mty_fresh := LTy_instantiateWithCheck_freeVars_fresh _ C Env mty Env1
        h_inst
      cases fty with
      | none => grind
      | some fty_val =>
        simp only [Except.mapError] at h_infer
        split at h_infer; · simp at h_infer
        rename_i v3 h_inst2; obtain ⟨fty_inst, Env2⟩ := v3; dsimp at h_infer h_inst2
        split at h_infer; · simp at h_infer
        simp at h_infer; obtain ⟨h_ty, h_env2⟩ := h_infer
        rw [← h_ty] at hv; rw [← h_env2] at hk; simp [TEnv.updateSubst] at hk
        have h_mono2 := LMonoTy_instantiateWithCheck_tyGen_mono fty_val C Env1 fty_inst Env2 h_inst2
        exact h_mty_fresh v hv k (Nat.le_trans h_mono2 hk)
  | .op m o oty =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i func h_find
    split at h; · simp at h
    rename_i type_val h_type
    split at h; · simp at h
    rename_i v1 h_inst; obtain ⟨ty_inst, Env1⟩ := v1; dsimp at h h_inst
    -- Derive that type_val has empty freeVars from FactoryWF
    have h_func_mem : func ∈ C.functions := Array.mem_of_find?_eq_some h_find
    have h_func_wf : LFuncWF func := h_fwf.lfuncs_wf func h_func_mem
    have h_ty_closed : LTy.freeVars type_val = [] :=
      LFunc.type_freeVars_eq_nil func type_val h_type h_func_wf
    have h_ty_fresh_vacuous : ∀ v, v ∈ LTy.freeVars type_val →
        ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
      intro v hv; simp [h_ty_closed] at hv
    have h_bv_fresh : ∀ v, v ∈ LTy.boundVars type_val →
        ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
      rw [LFunc.type_boundVars_eq_typeArgs func type_val h_type]
      intro v hv _ _ h_eq
      have := h_func_wf.typeArgs_no_gen_prefix v hv
      exact this (h_eq ▸ (by rw [String.toList_append]; exact isPrefixOf_append_self _ _))
    cases oty with
    | none =>
      simp at h; obtain ⟨h_et, h2⟩ := h; subst h_et h2
      constructor
      · exact LTy_instantiateWithCheck_preserves_SubstFreshForGen type_val C Env ty_inst Env1 h_inst h_fresh h_aw
          h_ty_fresh_vacuous
          h_bv_fresh
      · intro v hv k hk
        simp [toLMonoTy] at hv
        exact LTy_instantiateWithCheck_freeVars_fresh type_val C Env ty_inst Env1 h_inst v hv k hk
    | some oty_val =>
      simp only [Except.mapError] at h
      split at h; · simp at h
      rename_i v2 h_inst2; obtain ⟨oty_inst, Env2⟩ := v2; dsimp at h h_inst2
      split at h; · simp at h
      rename_i v3 h_mapError
      simp at h; obtain ⟨h_et, h2⟩ := h; subst h_et h2
      simp [TEnv.updateSubst]
      have h_aw1 : TContext.AliasesWF Env1.context :=
        (LTy_instantiateWithCheck_context' _ C Env ty_inst Env1 h_inst) ▸ h_aw
      have h_ctx1 : ContextFreshForGen Env1.context Env1.genEnv.genState :=
        (LTy_instantiateWithCheck_context' _ C Env ty_inst Env1 h_inst) ▸
          ContextFreshForGen.mono _ _ _ h_ctx (LTy_instantiateWithCheck_tyGen_mono _ C Env ty_inst Env1 h_inst)
      have h_fresh1 := LTy_instantiateWithCheck_preserves_SubstFreshForGen
        type_val C Env ty_inst Env1 h_inst h_fresh h_aw
        h_ty_fresh_vacuous
        h_bv_fresh
      have h_fresh2 := LMonoTy_instantiateWithCheck_preserves_SubstFreshForGen
        oty_val C Env1 oty_inst Env2 h_inst2 h_fresh1 h_aw1
      have h_unify := unify_of_mapError h_mapError
      constructor
      · exact unify_preserves_SubstFreshForGen h_unify h_fresh2 (fun v hv n hn => by
          simp [Constraints.freeVars, Constraint.freeVars] at hv
          cases hv with
          | inl h_ty =>
            exact LTy_instantiateWithCheck_freeVars_fresh type_val C Env ty_inst Env1
              h_inst v h_ty n (Nat.le_trans
              (LMonoTy_instantiateWithCheck_tyGen_mono oty_val C Env1 oty_inst Env2 h_inst2) hn)
          | inr h_oty =>
            have h_ctx1 : ContextFreshForGen Env1.context Env1.genEnv.genState := by
              rw [LTy_instantiateWithCheck_context' _ C Env _ Env1 h_inst]
              exact ContextFreshForGen.mono _ _ _ h_ctx (LTy_instantiateWithCheck_tyGen_mono _ C Env _ Env1 h_inst)
            exact LMonoTy_instantiateWithCheck_freeVars_fresh oty_val C Env1 oty_inst Env2
              h_inst2 v h_oty n hn)
      · -- Output type freshness for op (some oty_val case)
        intro v hv k hk
        simp [toLMonoTy] at hv
        have h_mono2 := LMonoTy_instantiateWithCheck_tyGen_mono oty_val C Env1 oty_inst Env2 h_inst2
        exact LTy_instantiateWithCheck_freeVars_fresh type_val C Env ty_inst Env1 h_inst v hv k (Nat.le_trans h_mono2 hk)
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
    simp at h; obtain ⟨h_et, h2⟩ := h; subst h_et h2; simp [TEnv.updateSubst]
    have h_sz1 : e1.sizeOf < n := by expr_size h_eq
    have h_sz2 : e2.sizeOf < n := by expr_size h_eq
    have h_ctx1_eq := ih_context e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1 h_ne
    have h_fresh1 := ((ih e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1 h_ne).2 h_fresh h_ctx h_aw h_fwf h_bvf).1
    have h_e1t_type_fresh := ih_output_fresh e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1 h_ne h_fresh h_ctx h_aw h_fwf h_bvf
    have h_ne1 := h_ctx1_eq ▸ h_ne
    have h_ctx1 := ih_ctx e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1 h_ne h_ctx
    have h_aw1 : TContext.AliasesWF Env1.context := h_ctx1_eq ▸ h_aw
    have h_ctx2_eq := ih_context e2.sizeOf h_sz2 e2 rfl e2t C Env1 Env2 h_res2 h_ne1
    have h_bvf1 := transfer_boundVarsFresh h_bvf h_ctx1_eq (resolveAux_genState_mono e1 e1t C Env Env1 h_res1)
    have h_fresh2 := ((ih e2.sizeOf h_sz2 e2 rfl e2t C Env1 Env2 h_res2 h_ne1).2 h_fresh1 h_ctx1 h_aw1 h_fwf h_bvf1).1
    have h_e2t_type_fresh := ih_output_fresh e2.sizeOf h_sz2 e2 rfl e2t C Env1 Env2 h_res2 h_ne1 h_fresh1 h_ctx1 h_aw1 h_fwf h_bvf1

    have h_gen_subst := TEnv.genTyVar_subst Env2 fresh_name Env3 h_gen
    have h_gen_name := genTyVar_name_eq Env2 fresh_name Env3 h_gen
    have h_gen_tyGen := genTyVar_tyGen Env2 fresh_name Env3 h_gen
    have h_fresh3 : SubstFreshForGen Env3.stateSubstInfo Env3.genEnv.genState := by
      rw [h_gen_subst]; exact SubstFreshForGen.mono _ _ _  h_fresh2
        (by omega)
    have h_unify := unify_of_mapError h_mapError
    have h_cs_fresh : ∀ v, v ∈ Constraints.freeVars
        [(e1t.toLMonoTy, LMonoTy.tcons "arrow" [e2t.toLMonoTy, .ftvar fresh_name])] →
        ∀ k, k ≥ Env3.genEnv.genState.tyGen →
          v ≠ TState.tyPrefix ++ toString k := by
      intro w hw k hk
      simp [Constraints.freeVars, Constraint.freeVars, LMonoTy.freeVars,
            LMonoTys.freeVars] at hw
      rcases hw with hw1 | hw2 | hw3
      · -- w ∈ freeVars e1t.toLMonoTy
        have h_mono_e1 := resolveAux_genState_mono e1 e1t C Env Env1 h_res1
        have h_mono_e2 := resolveAux_genState_mono e2 e2t C Env1 Env2 h_res2
        have hk1 : k ≥ Env1.genEnv.genState.tyGen := by omega
        exact h_e1t_type_fresh w hw1 k hk1
      · -- w ∈ freeVars e2t.toLMonoTy
        have hk2 : k ≥ Env2.genEnv.genState.tyGen := by omega
        exact h_e2t_type_fresh w hw2 k hk2
      · -- w = fresh_name
        rw [hw3, h_gen_name]
        exact generated_name_fresh Env2.genEnv.genState.tyGen Env3.genEnv.genState
          (by omega) k hk
    have h_fresh4 := unify_preserves_SubstFreshForGen h_unify h_fresh3 h_cs_fresh
    constructor
    · -- SubstFreshForGen preserved through Maps.remove
      -- Maps.remove only removes vars → SubstFreshForGen preserved
      -- keys(remove S k) ⊆ keys S (by mem_keys_of_mem_keys_remove)
      -- freeVars(remove S k) ⊆ freeVars S (removing entries only reduces freeVars)
      intro v hv n_ hn
      exact h_fresh4 v (by
        cases hv with
        | inl h_key => exact Or.inl (Maps.mem_keys_of_mem_keys_remove _ _ _ h_key)
        | inr h_fv =>
          -- freeVars(remove S k) ⊆ freeVars S: values of remove are a subset of values of S
          exact Or.inr (by
            simp only [Subst.freeVars, List.mem_flatMap] at h_fv ⊢
            obtain ⟨ty, h_ty_mem, h_v_fv⟩ := h_fv
            exact ⟨ty, Maps.mem_values_of_mem_keys_remove _ _ _ h_ty_mem, h_v_fv⟩)) n_ hn
    · -- Output type freshness for app
      -- et = .app ⟨m, subst v4.subst (ftvar fresh_name)⟩ e1t e2t
      -- toLMonoTy = subst v4.subst (ftvar fresh_name)
      intro v hv k hk
      simp [toLMonoTy] at hv
      -- hv : v ∈ freeVars (subst v4.subst (ftvar fresh_name))
      have h_fv_subset := LMonoTy.freeVars_of_subst_subset v4.subst (.ftvar fresh_name)
      have hv_in := h_fv_subset hv
      simp [LMonoTy.freeVars] at hv_in
      -- SubstFreshForGen for v4
      have h_sfg_v4 : SubstFreshForGen v4 Env3.genEnv.genState :=
        unify_preserves_SubstFreshForGen h_unify h_fresh3 h_cs_fresh
      rcases hv_in with hv_fresh | hv_fv
      · -- v = fresh_name
        rw [hv_fresh, h_gen_name]
        exact generated_name_fresh Env2.genEnv.genState.tyGen Env3.genEnv.genState
          (by omega) k hk
      · -- v ∈ Subst.freeVars v4.subst
        exact h_sfg_v4 v (Or.inr hv_fv) k hk
  | .abs m _ bty body =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_tbv; obtain ⟨xv_id, xty_val, Env1⟩ := v1; simp at h h_tbv
    split at h; · simp at h
    rename_i v2 h_rec; obtain ⟨et', Env2⟩ := v2; simp at h
    obtain ⟨h_et, h_env⟩ := h; rw [← h_env]; simp [TEnv.eraseFromContext, TEnv.updateContext]
    have h_sz : (varOpen 0 (xv_id, some xty_val) body).sizeOf < n := by
      expr_size h_eq
    have h_fresh1 := typeBoundVar_preserves_SubstFreshForGen C Env bty xv_id xty_val Env1 h_tbv h_fresh h_aw
    have h_ctx1 := typeBoundVar_preserves_ContextFreshForGen C Env bty xv_id xty_val Env1 h_tbv h_ctx
    have h_aw1 := typeBoundVar_preserves_AliasesWF C Env bty xv_id xty_val Env1 h_tbv h_aw
    have h_ne1 : Env1.context.types ≠ [] :=
      typeBoundVar_context_types_ne_nil C Env bty xv_id xty_val Env1 h_tbv
    have h_bvf1 := typeBoundVar_preserves_boundVarsFresh C Env bty xv_id xty_val Env1 h_tbv h_bvf
    have h_ih_result := (ih _ h_sz (varOpen 0 (xv_id, some xty_val) body) rfl et' C Env1 Env2 h_rec h_ne1).2 h_fresh1 h_ctx1 h_aw1 h_fwf h_bvf1

    constructor
    · exact h_ih_result.1
    · -- Output type freshness for abs: et.toLMonoTy = subst Env2.subst (arrow [xty, ety])
      -- freeVars come from Env2.subst values (gen-fresh by SubstFreshForGen)
      -- or from xty/ety (gen-fresh from typeBoundVar and IH).
      intro v hv k hk
      rw [← h_et] at hv; simp [toLMonoTy] at hv
      have h_fv_subset := LMonoTy.freeVars_of_subst_subset Env2.stateSubstInfo.subst
        (.tcons "arrow" [xty_val, (Lambda.LExpr.varCloseT 0 xv_id et').toLMonoTy])
      have hv_in := h_fv_subset hv
      simp [List.mem_append] at hv_in
      rcases hv_in with hv_ty | hv_subst
      · -- v from freeVars of (arrow [xty_val, varCloseT_toLMonoTy])
        simp [LMonoTy.freeVars, LMonoTys.freeVars, List.mem_append] at hv_ty
        rcases hv_ty with hv_xty | hv_ety
        · -- v from xty_val: gen-fresh from typeBoundVar
          -- xty_val comes from typeBoundVar which either:
          -- (a) calls LMonoTy.instantiateWithCheck (annotation) → gen-fresh by freeVars_fresh
          -- (b) calls genTyVar (no annotation) → single fresh var, gen-fresh
          -- In both cases, xty_val freeVars are gen-fresh for Env1.genState.
          -- Env2.genState ≥ Env1.genState by resolveAux genState monotonicity.
          have h_mono_body := resolveAux_genState_mono
            (LExpr.varOpen 0 (xv_id, some xty_val) body) et' C Env1 Env2 h_rec
          -- xty_val freeVars are gen-fresh for Env1.genState
          -- Decompose typeBoundVar to extract xty_val's origin
          simp only [typeBoundVar, liftGenEnv, Bind.bind, Except.bind] at h_tbv
          split at h_tbv; · contradiction
          rename_i genResult h_gen
          have h_gen_tyGen : genResult.snd.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
            split at h_gen; · contradiction
            rename_i _ _ h_gv; have := Except.ok.inj h_gen; rw [← this]; simp
            exact HasGen.genVar_tyGen_mono Env.genEnv _ _ h_gv
          have h_gen_ctx : genResult.snd.context = Env.context := by
            split at h_gen; · contradiction
            rename_i _ _ h_gv; have := Except.ok.inj h_gen; rw [← this]; simp [TEnv.context]
            exact HasGen.genVar_context Env.genEnv _ _ h_gv
          have h_ctx_gen : ContextFreshForGen genResult.snd.context genResult.snd.genEnv.genState :=
            h_gen_ctx ▸ ContextFreshForGen.mono _ _ _ h_ctx h_gen_tyGen
          split at h_tbv
          · -- bty = some: xty_val from LMonoTy.instantiateWithCheck
            split at h_tbv; · contradiction
            rename_i _ bty_mty _ _ Env_inst h_inst
            simp at h_tbv
            obtain ⟨_, rfl, h_env1_eq⟩ := h_tbv
            have h_fv_fresh := LMonoTy_instantiateWithCheck_freeVars_fresh _ C genResult.snd _ Env_inst h_inst
            have h_iwc_mono := LMonoTy_instantiateWithCheck_tyGen_mono _ C genResult.snd _ Env_inst h_inst
            have h_gen_eq : Env1.genEnv.genState = Env_inst.genEnv.genState := by
              rw [← h_env1_eq]; simp [TEnv.addInNewestContext, TEnv.updateContext]
            exact h_fv_fresh v hv_xty k (by rw [h_gen_eq] at h_mono_body; omega)
          · -- bty = none: xty_val = ftvar xtyid from genTyVar
            split at h_tbv; · contradiction
            rename_i v_gen h_genTy
            obtain ⟨xtyid, Env_ty⟩ := v_gen
            simp at h_tbv
            obtain ⟨_, rfl, h_env1_eq⟩ := h_tbv
            simp [LMonoTy.freeVars] at hv_xty; rw [hv_xty]
            have h_genTy_name := genTyVar_name_eq genResult.snd xtyid Env_ty h_genTy
            have h_genTy_tyGen := genTyVar_tyGen genResult.snd xtyid Env_ty h_genTy
            have h_gen_eq : Env1.genEnv.genState = Env_ty.genEnv.genState := by
              rw [← h_env1_eq]; simp [TEnv.addInNewestContext, TEnv.updateContext]
            rw [h_genTy_name]
            exact generated_name_fresh _ _ (by rw [h_gen_eq] at h_mono_body; omega) k hk
        · -- v from varCloseT et': varCloseT preserves toLMonoTy
          -- (varCloseT 0 xv et').toLMonoTy = et'.toLMonoTy
          -- So v ∈ freeVars et'.toLMonoTy, gen-fresh by IH (h_ih_result.2)
          -- varCloseT_toLMonoTy is defined later, but the equality is simple:
          -- varCloseT only changes fvar/bvar structure, not metadata types
          have : (Lambda.LExpr.varCloseT 0 xv_id et').toLMonoTy = et'.toLMonoTy := by
            match et' with
            | .const _ _ | .op _ _ _ | .bvar _ _ | .abs _ _ _ _ | .app _ _ _
            | .ite _ _ _ _ | .eq _ _ _ | .quant _ _ _ _ _ _ => rfl
            | .fvar _ y _ =>
              -- toLMonoTy gives m.type for both bvar and fvar
              simp only [Lambda.LExpr.varCloseT]; split <;> rfl
          rw [this] at hv_ety
          exact h_ih_result.2 v hv_ety k hk
      · -- v from Subst.freeVars Env2.subst: gen-fresh by SubstFreshForGen
        exact h_ih_result.1 v (Or.inr hv_subst) k hk
  | .quant m qk _ bty tr body =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_tbv; obtain ⟨xv_id, xty_val, Env1⟩ := v1; simp at h h_tbv
    split at h; · simp at h
    rename_i v2 h_rec_e; obtain ⟨et', Env2⟩ := v2; simp at h h_rec_e
    split at h; · simp at h
    rename_i v3 h_rec_tr; obtain ⟨trT, Env3⟩ := v3; simp at h h_rec_tr
    split at h
    · simp at h; obtain ⟨h_et, h_env⟩ := h; rw [← h_env]; simp [TEnv.eraseFromContext, TEnv.updateContext]
      have h_sz_e : (varOpen 0 (xv_id, some xty_val) body).sizeOf < n := by
        expr_size h_eq
      have h_sz_tr : (varOpen 0 (xv_id, some xty_val) tr).sizeOf < n := by
        expr_size h_eq
      have h_fresh1 := typeBoundVar_preserves_SubstFreshForGen C Env bty xv_id xty_val Env1 h_tbv h_fresh h_aw
      have h_ctx1 := typeBoundVar_preserves_ContextFreshForGen C Env bty xv_id xty_val Env1 h_tbv h_ctx
      have h_aw1 := typeBoundVar_preserves_AliasesWF C Env bty xv_id xty_val Env1 h_tbv h_aw
      have h_ne1 : Env1.context.types ≠ [] :=
        typeBoundVar_context_types_ne_nil C Env bty xv_id xty_val Env1 h_tbv
      have h_ctx2_eq := ih_context _ h_sz_e _ rfl et' C Env1 Env2 h_rec_e h_ne1
      have h_bvf1 := typeBoundVar_preserves_boundVarsFresh C Env bty xv_id xty_val Env1 h_tbv h_bvf
      have h_fresh2 := ((ih _ h_sz_e _ rfl et' C Env1 Env2 h_rec_e h_ne1).2 h_fresh1 h_ctx1 h_aw1 h_fwf h_bvf1).1
      have h_ne2 := h_ctx2_eq ▸ h_ne1
      have h_ctx2 := ih_ctx _ h_sz_e _ rfl et' C Env1 Env2 h_rec_e h_ne1 h_ctx1
      have h_aw2 : TContext.AliasesWF Env2.context := h_ctx2_eq ▸ h_aw1
      have h_bvf2 := transfer_boundVarsFresh h_bvf1 h_ctx2_eq (resolveAux_genState_mono _ et' C Env1 Env2 h_rec_e)
      have h_ih_tr := (ih _ h_sz_tr _ rfl trT C Env2 Env3 h_rec_tr h_ne2).2 h_fresh2 h_ctx2 h_aw2 h_fwf h_bvf2
      constructor
      · exact h_ih_tr.1
      · -- Output type freshness for quant: toLMonoTy of quant is LMonoTy.bool (empty freeVars)
        intro v hv n hn
        rw [← h_et] at hv; simp [toLMonoTy, LMonoTy.bool, LMonoTy.freeVars, LMonoTys.freeVars] at hv
    · simp at h
  | .eq m e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    split at h; · simp at h
    rename_i v1 h_res1; obtain ⟨e1t, Env1⟩ := v1; dsimp at h h_res1
    split at h; · simp at h
    rename_i v2 h_res2; obtain ⟨e2t, Env2⟩ := v2; dsimp at h h_res2
    split at h; · simp at h
    rename_i v3 h_mapError
    simp at h; obtain ⟨h_et, h2⟩ := h; subst h_et h2; simp [TEnv.updateSubst]
    have h_sz1 : e1.sizeOf < n := by expr_size h_eq
    have h_sz2 : e2.sizeOf < n := by expr_size h_eq
    have h_ctx1_eq := ih_context e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1 h_ne
    have h_fresh1 := ((ih e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1 h_ne).2 h_fresh h_ctx h_aw h_fwf h_bvf).1
    have h_e1t_type_fresh := ih_output_fresh e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1 h_ne h_fresh h_ctx h_aw h_fwf h_bvf
    have h_ne1 := h_ctx1_eq ▸ h_ne
    have h_ctx1 := ih_ctx e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1 h_ne h_ctx
    have h_bvf1 := transfer_boundVarsFresh h_bvf h_ctx1_eq (resolveAux_genState_mono e1 e1t C Env Env1 h_res1)
    have h_aw1 : TContext.AliasesWF Env1.context := h_ctx1_eq ▸ h_aw
    have h_fresh2 := ((ih e2.sizeOf h_sz2 e2 rfl e2t C Env1 Env2 h_res2 h_ne1).2 h_fresh1 h_ctx1 h_aw1 h_fwf (transfer_boundVarsFresh h_bvf h_ctx1_eq (resolveAux_genState_mono e1 e1t C Env Env1 h_res1))).1
    have h_e2t_type_fresh := ih_output_fresh e2.sizeOf h_sz2 e2 rfl e2t C Env1 Env2 h_res2 h_ne1 h_fresh1 h_ctx1 h_aw1 h_fwf (transfer_boundVarsFresh h_bvf h_ctx1_eq (resolveAux_genState_mono e1 e1t C Env Env1 h_res1))

    have h_unify := unify_of_mapError h_mapError
    constructor
    · exact unify_preserves_SubstFreshForGen h_unify h_fresh2 (fun v hv n_ hn => by
        simp [Constraints.freeVars, Constraint.freeVars] at hv
        cases hv with
        | inl h_e1 =>
          -- v ∈ freeVars e1t.toLMonoTy: use ih_output_fresh
          have h_mono_e2 := resolveAux_genState_mono e2 e2t C Env1 Env2 h_res2
          exact h_e1t_type_fresh v h_e1 n_ (by omega)
        | inr h_e2 =>
          -- v ∈ freeVars e2t.toLMonoTy: use ih_output_fresh
          exact h_e2t_type_fresh v h_e2 n_ hn)
    · -- Output type freshness for eq: toLMonoTy of eq is LMonoTy.bool, vacuously true
      intro v hv
      simp [toLMonoTy] at hv
      simp [LMonoTy.freeVars, LMonoTys.freeVars] at hv
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
    simp at h; obtain ⟨h_et, h2⟩ := h; subst h_et h2; simp [TEnv.updateSubst]
    have h_sz_c : c.sizeOf < n := by expr_size h_eq
    have h_sz_t : t.sizeOf < n := by expr_size h_eq
    have h_sz_e : e.sizeOf < n := by expr_size h_eq
    have h_ctx1_eq := ih_context c.sizeOf h_sz_c c rfl ct C Env Env1 h_res_c h_ne
    have h_fresh1 := ((ih c.sizeOf h_sz_c c rfl ct C Env Env1 h_res_c h_ne).2 h_fresh h_ctx h_aw h_fwf h_bvf).1
    have h_ct_type_fresh := ih_output_fresh c.sizeOf h_sz_c c rfl ct C Env Env1 h_res_c h_ne h_fresh h_ctx h_aw h_fwf h_bvf
    have h_ne1 := h_ctx1_eq ▸ h_ne
    have h_ctx1 := ih_ctx c.sizeOf h_sz_c c rfl ct C Env Env1 h_res_c h_ne h_ctx
    have h_bvf1 := transfer_boundVarsFresh h_bvf h_ctx1_eq (resolveAux_genState_mono c ct C Env Env1 h_res_c)
    have h_aw1 : TContext.AliasesWF Env1.context := h_ctx1_eq ▸ h_aw
    have h_ctx2_eq := ih_context t.sizeOf h_sz_t t rfl tht C Env1 Env2 h_res_t h_ne1
    have h_fresh2 := ((ih t.sizeOf h_sz_t t rfl tht C Env1 Env2 h_res_t h_ne1).2 h_fresh1 h_ctx1 h_aw1 h_fwf h_bvf1).1
    have h_tht_type_fresh := ih_output_fresh t.sizeOf h_sz_t t rfl tht C Env1 Env2 h_res_t h_ne1 h_fresh1 h_ctx1 h_aw1 h_fwf h_bvf1

    have h_ne2 := h_ctx2_eq ▸ h_ne1
    have h_ctx2 := ih_ctx t.sizeOf h_sz_t t rfl tht C Env1 Env2 h_res_t h_ne1 h_ctx1
    have h_aw2 : TContext.AliasesWF Env2.context := h_ctx2_eq ▸ h_aw1
    have h_bvf2 := transfer_boundVarsFresh h_bvf1 h_ctx2_eq (resolveAux_genState_mono t tht C Env1 Env2 h_res_t)
    have h_fresh3 := ((ih e.sizeOf h_sz_e e rfl elt C Env2 Env3 h_res_e h_ne2).2 h_fresh2 h_ctx2 h_aw2 h_fwf h_bvf2).1
    have h_elt_type_fresh := ih_output_fresh e.sizeOf h_sz_e e rfl elt C Env2 Env3 h_res_e h_ne2 h_fresh2 h_ctx2 h_aw2 h_fwf h_bvf2
    have h_unify := unify_of_mapError h_mapError
    constructor
    · exact unify_preserves_SubstFreshForGen h_unify h_fresh3 (fun v hv n_ hn => by
        simp [Constraints.freeVars, Constraint.freeVars, LMonoTy.freeVars, LMonoTys.freeVars] at hv
        -- hv : v ∈ freeVars ct.toLMonoTy ∨ v ∈ freeVars tht.toLMonoTy ∨ v ∈ freeVars elt.toLMonoTy
        rcases hv with hv_c | hv_t | hv_e
        · -- v ∈ freeVars ct.toLMonoTy
          have h_mono_t := resolveAux_genState_mono t tht C Env1 Env2 h_res_t
          have h_mono_e := resolveAux_genState_mono e elt C Env2 Env3 h_res_e
          exact h_ct_type_fresh v hv_c n_ (by omega)
        · -- v ∈ freeVars tht.toLMonoTy
          have h_mono_e := resolveAux_genState_mono e elt C Env2 Env3 h_res_e
          exact h_tht_type_fresh v hv_t n_ (by omega)
        · -- v ∈ freeVars elt.toLMonoTy
          exact h_elt_type_fresh v hv_e n_ hn)
    · -- Output type freshness for ite: output type is tht.toLMonoTy (the then-branch metadata type)
      intro v hv k hk
      simp [toLMonoTy] at hv
      -- Env3.genState.tyGen ≥ Env2.genState.tyGen
      have h_mono_e := resolveAux_genState_mono e elt C Env2 Env3 h_res_e
      exact h_tht_type_fresh v hv k (by omega)⟩

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
private theorem resolveAux_preserves_SubstFreshForGen :
    ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState →
      ContextFreshForGen Env.context Env.genEnv.genState →
      Env.context.types ≠ [] →
      TContext.AliasesWF Env.context →
      FactoryWF C.functions →
      (∀ y ty, Env.context.types.find? y = some ty →
        ∀ v, v ∈ LTy.boundVars ty →
          ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) →
      SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState :=
  fun e et C Env Env' h h_sf h_cf h_ne h_aw h_fwf h_bvf =>
    ((resolveAux_preserves_combined e.sizeOf e rfl et C Env Env' h h_ne).2 h_sf h_cf h_aw h_fwf h_bvf).1

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
omit [DecidableEq T.IDMeta] in
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

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
      FactoryWF C.functions →
      (∀ y ty, Env.context.types.find? y = some ty →
        ∀ v, v ∈ LTy.boundVars ty →
          ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) →
      Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  intro e
  suffices ∀ (n : Nat) (e : LExpr T.mono), e.sizeOf = n →
      ∀ (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      EnvFreshForGen Env →
      Env.context.types ≠ [] →
      TContext.AliasesWF Env.context →
      FactoryWF C.functions →
      (∀ y ty, Env.context.types.find? y = some ty →
        ∀ v, v ∈ LTy.boundVars ty →
          ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) →
      Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst by
    exact this e.sizeOf e rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro e h_eq et C Env Env' h h_env_fresh h_ne h_aw h_fwf h_bvf
  match e with
  | .const m c =>
    simp [resolveAux, inferConst] at h
    split at h
    · simp [Bind.bind, Except.bind] at h
      obtain ⟨_, h_env⟩ := h; rw [← h_env]
      exact Subst.absorbs_refl _ Env.stateSubstInfo.isWF
    · exact absurd h (by simp [Bind.bind, Except.bind])
  | bvar m i =>
    simp [resolveAux] at h
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
      e1 e1t C Env Env1 h_res1 h_fresh h_env_fresh.2 h_ne h_aw h_fwf h_bvf
    have h_ne1 := h_ctx1_eq ▸ h_ne
    have h_aw1 : TContext.AliasesWF Env1.context := h_ctx1_eq ▸ h_aw
    have h_bvf1 := transfer_boundVarsFresh h_bvf h_ctx1_eq (resolveAux_genState_mono e1 e1t C Env Env1 h_res1)
    -- Absorption from IHs
    have h_abs1 := ih e1.sizeOf (by expr_size h_eq) e1 rfl e1t C Env Env1 h_res1 h_env_fresh h_ne h_aw h_fwf h_bvf
    have h_abs2 := ih e2.sizeOf (by expr_size h_eq) e2 rfl e2t C Env1 Env2 h_res2
      ⟨h_fresh1, h_ctx1_eq ▸
        ContextFreshForGen.mono _ _ _ h_env_fresh.2
          (resolveAux_genState_mono e1 e1t C Env Env1 h_res1)⟩ h_ne1 h_aw1 h_fwf h_bvf1
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
  | .abs m _ bty body =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_tbv; obtain ⟨xv, xty, Env1⟩ := v1; simp at h h_tbv
    split at h; · simp at h
    rename_i v2 h_rec; obtain ⟨et', Env2⟩ := v2; simp at h
    obtain ⟨_, h_env⟩ := h; rw [← h_env]
    simp [TEnv.eraseFromContext, TEnv.updateContext]
    have h_sz : (varOpen 0 (xv, some xty) body).sizeOf < n := by
      expr_size h_eq
    -- typeBoundVar absorbs, then recursive call absorbs
    have h_abs1 := typeBoundVar_absorbs C Env bty xv xty Env1 h_tbv
    -- For the recursive call, need EnvFreshForGen Env1
    have h_aw1 := typeBoundVar_preserves_AliasesWF C Env bty xv xty Env1 h_tbv h_aw
    have h_env_fresh1 : EnvFreshForGen Env1 :=
      ⟨typeBoundVar_preserves_SubstFreshForGen C Env bty xv xty Env1 h_tbv h_env_fresh.1 h_aw,
       typeBoundVar_preserves_ContextFreshForGen C Env bty xv xty Env1 h_tbv h_env_fresh.2⟩
    have h_ne1 : Env1.context.types ≠ [] :=
      typeBoundVar_context_types_ne_nil C Env bty xv xty Env1 h_tbv
    have h_bvf1 := typeBoundVar_preserves_boundVarsFresh C Env bty xv xty Env1 h_tbv h_bvf
    exact Subst.absorbs_trans
      Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
      h_abs1
      (ih _ h_sz _ rfl et' C Env1 Env2 h_rec h_env_fresh1 h_ne1 h_aw1 h_fwf h_bvf1)
  | .quant m qk _ bty tr body =>
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
        expr_size h_eq
      have h_sz_tr : (varOpen 0 (xv, some xty) tr).sizeOf < n := by
        expr_size h_eq
      have h_abs1 := typeBoundVar_absorbs C Env bty xv xty Env1 h_tbv
      have h_aw1 := typeBoundVar_preserves_AliasesWF C Env bty xv xty Env1 h_tbv h_aw
      have h_bvf1 := typeBoundVar_preserves_boundVarsFresh C Env bty xv xty Env1 h_tbv h_bvf
      have h_env_fresh1 : EnvFreshForGen Env1 :=
        ⟨typeBoundVar_preserves_SubstFreshForGen C Env bty xv xty Env1 h_tbv h_env_fresh.1 h_aw,
         typeBoundVar_preserves_ContextFreshForGen C Env bty xv xty Env1 h_tbv h_env_fresh.2⟩
      have h_ne1 : Env1.context.types ≠ [] :=
        typeBoundVar_context_types_ne_nil C Env bty xv xty Env1 h_tbv
      -- Chain: Env → Env1 (typeBoundVar) → Env2 (resolveAux e') → Env3 (resolveAux tr')
      have h_ctx2_eq := resolveAux_context _ et' C Env1 Env2 h_rec_e h_ne1
      have h_ne2 := h_ctx2_eq ▸ h_ne1
      have h_aw2 : TContext.AliasesWF Env2.context := h_ctx2_eq ▸ h_aw1
      have h_bvf2 := transfer_boundVarsFresh h_bvf1 h_ctx2_eq (resolveAux_genState_mono _ et' C Env1 Env2 h_rec_e)
      have h_env_fresh2 : EnvFreshForGen Env2 :=
        ⟨resolveAux_preserves_SubstFreshForGen _ et' C Env1 Env2 h_rec_e h_env_fresh1.1 h_env_fresh1.2 h_ne1 h_aw1 h_fwf h_bvf1,
         h_ctx2_eq ▸
           ContextFreshForGen.mono _ _ _ h_env_fresh1.2
             (resolveAux_genState_mono _ et' C Env1 Env2 h_rec_e)⟩
      exact Subst.absorbs_trans
        Env.stateSubstInfo.subst Env2.stateSubstInfo.subst Env3.stateSubstInfo.subst
        (Subst.absorbs_trans
          Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
          h_abs1
          (ih _ h_sz_e _ rfl et' C Env1 Env2 h_rec_e h_env_fresh1 h_ne1 h_aw1 h_fwf h_bvf1))
        (ih _ h_sz_tr _ rfl trT C Env2 Env3 h_rec_tr h_env_fresh2 h_ne2 h_aw2 h_fwf h_bvf2)
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
      e1 e1t C Env Env1 h_res1 h_env_fresh.1 h_env_fresh.2 h_ne h_aw h_fwf h_bvf
    have h_ne1 := h_ctx1_eq ▸ h_ne
    have h_aw1 : TContext.AliasesWF Env1.context := h_ctx1_eq ▸ h_aw
    have h_bvf1 := transfer_boundVarsFresh h_bvf h_ctx1_eq (resolveAux_genState_mono e1 e1t C Env Env1 h_res1)
    exact Subst.absorbs_trans
      Env.stateSubstInfo.subst Env2.stateSubstInfo.subst v3.subst
      (Subst.absorbs_trans
        Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
        (ih e1.sizeOf (by expr_size h_eq) e1 rfl e1t C Env Env1 h_res1 h_env_fresh h_ne h_aw h_fwf h_bvf)
        (ih e2.sizeOf (by expr_size h_eq) e2 rfl e2t C Env1 Env2 h_res2
          ⟨h_fresh1, h_ctx1_eq ▸
            ContextFreshForGen.mono _ _ _ h_env_fresh.2
              (resolveAux_genState_mono e1 e1t C Env Env1 h_res1)⟩ h_ne1 h_aw1 h_fwf h_bvf1))
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
      c ct C Env Env1 h_res_c h_env_fresh.1 h_env_fresh.2 h_ne h_aw h_fwf h_bvf
    have h_bvf1 := transfer_boundVarsFresh h_bvf h_ctx1_eq (resolveAux_genState_mono c ct C Env Env1 h_res_c)
    have h_ctx2_eq := resolveAux_context t tht C Env1 Env2 h_res_t h_ne1
    have h_ne2 := h_ctx2_eq ▸ h_ne1
    have h_aw2 : TContext.AliasesWF Env2.context := h_ctx2_eq ▸ h_aw1
    have h_ctx2 : ContextFreshForGen Env2.context Env2.genEnv.genState :=
      h_ctx2_eq ▸
        ContextFreshForGen.mono _ _ _ h_ctx1 (resolveAux_genState_mono t tht C Env1 Env2 h_res_t)
    have h_fresh2 := resolveAux_preserves_SubstFreshForGen
      t tht C Env1 Env2 h_res_t h_fresh1 h_ctx1 h_ne1 h_aw1 h_fwf h_bvf1
    have h_bvf2 := transfer_boundVarsFresh h_bvf1 h_ctx2_eq (resolveAux_genState_mono t tht C Env1 Env2 h_res_t)
    exact Subst.absorbs_trans
      Env.stateSubstInfo.subst Env3.stateSubstInfo.subst v4.subst
      (Subst.absorbs_trans
        Env.stateSubstInfo.subst Env2.stateSubstInfo.subst Env3.stateSubstInfo.subst
        (Subst.absorbs_trans
          Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
          (ih c.sizeOf (by expr_size h_eq) c rfl ct C Env Env1 h_res_c h_env_fresh h_ne h_aw h_fwf h_bvf)
          (ih t.sizeOf (by expr_size h_eq) t rfl tht C Env1 Env2 h_res_t ⟨h_fresh1, h_ctx1⟩ h_ne1 h_aw1 h_fwf h_bvf1))
        (ih e.sizeOf (by expr_size h_eq) e rfl elt C Env2 Env3 h_res_e ⟨h_fresh2, h_ctx2⟩ h_ne2 h_aw2 h_fwf h_bvf2))
      (unify_absorbs _ _ _ h_unify)

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
  induction xs <;> grind

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

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
          simp
        simp
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

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Each var produced by `genTyVars` is `tyPrefix ++ toString k` for some
    `k ≥ Env.genState.tyGen`. -/
private theorem TGenEnv.genTyVars_is_genName
    (n : Nat) (Env : TGenEnv T.IDMeta) (tvs : List TyIdentifier) (Env' : TGenEnv T.IDMeta)
    (h : TGenEnv.genTyVars n Env = .ok (tvs, Env'))
    (tv : TyIdentifier) (h_mem : tv ∈ tvs) :
    ∃ k, k ≥ Env.genState.tyGen ∧ tv = TState.tyPrefix ++ toString k := by
  induction n generalizing Env tvs Env' with
  | zero =>
    simp [TGenEnv.genTyVars] at h; grind
  | succ m ih =>
    simp only [TGenEnv.genTyVars, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_gen1; obtain ⟨tv1, Env1⟩ := v1
    split at h; · simp at h
    rename_i v2 h_gen_rest; obtain ⟨rest, Env2⟩ := v2
    simp at h
    obtain ⟨h_tvs, h_env⟩ := h; subst h_tvs; subst h_env
    have h_tv1_name : tv1 = TState.tyPrefix ++ toString Env.genState.tyGen := by
      simp only [TGenEnv.genTyVar] at h_gen1
      split at h_gen1; · simp at h_gen1
      simp at h_gen1; rw [← h_gen1.1]
      simp [TState.genTySym, TState.incTyGen]
    have h_gen1_mono : Env1.genState.tyGen = Env.genState.tyGen + 1 := by
      simp only [TGenEnv.genTyVar] at h_gen1
      split at h_gen1; · simp at h_gen1
      simp at h_gen1; rw [← h_gen1.2]
      simp [TState.genTySym, TState.incTyGen]
    rcases List.mem_cons.mp h_mem with h_eq | h_rest
    · exact ⟨Env.genState.tyGen, Nat.le_refl _, h_eq ▸ h_tv1_name⟩
    · simp at h_gen_rest
      obtain ⟨k, h_k_ge, h_eq⟩ := ih Env1 rest Env2 h_gen_rest h_rest
      exact ⟨k, by omega, h_eq⟩

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
private theorem HasType_LTy_instantiate
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono) (ty : LTy)
    (mty : LMonoTy) (genEnv genEnv' : TGenEnv T.IDMeta)
    (h_ty : HasType C Γ e ty)
    (h_inst : LTy.instantiate ty genEnv = .ok (mty, genEnv'))
    (h_nodup : (LTy.boundVars ty).Nodup)
    (h_bv_fresh : ∀ v, v ∈ LTy.boundVars ty →
      ∀ n, n ≥ genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) :
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
        -- v ∈ (x :: xs) = boundVars ty
        have h_v_bv : v ∈ LTy.boundVars (.forAll (x :: xs) body) := by
          simp [LTy.boundVars]; exact List.mem_cons.mp hv
        -- tv ∈ freshtvs, so tv = tyPrefix ++ toString k for some k ≥ genEnv.genState.tyGen
        -- (each genTyVar output is tyPrefix ++ toString genState.tyGen, then counter increments)
        have h_tv_is_gen := TGenEnv.genTyVars_is_genName
          (x :: xs).length genEnv freshtvs genEnv1 h_gen tv htv_mem
        obtain ⟨k, h_k_ge, h_tv_eq⟩ := h_tv_is_gen
        -- v ≠ tv: h_bv_fresh says v ≠ tyPrefix ++ toString k for k ≥ genState.tyGen
        exact fun h_eq => absurd (h_tv_eq ▸ h_eq) (h_bv_fresh v h_v_bv k h_k_ge)
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
      | cons hd tl ih => simp [LMonoTys.substLogic, hS]
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
          simp only [List.zip, List.zipWith, List.find?, BEq.beq,
                      LMonoTys.substLogic, hS_ne]
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
      simp only [LMonoTy.subst, hS_ne]
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
      induction vals <;> simp [LMonoTys.substLogic, hS]
    have h_bodies : LMonoTys.substLogic S (LMonoTys.openVars vars vals bodies) =
        LMonoTys.openVars vars vals bodies := by
      induction (LMonoTys.openVars vars vals bodies) <;> simp [LMonoTys.substLogic, hS]
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
  | nil => simp [List.zip, Map.find?]
  | cons v vs ih =>
    cases vals with
    | nil => simp [List.zip, Map.find?]
    | cons vl vls =>
      simp only [List.zip, List.zipWith, List.find?, Map.find?, BEq.beq]
      by_cases h_eq : v = x
      · simp [h_eq]
      · simp [h_eq]; exact ih vls

/-- `openVars` with empty vars/vals is identity. -/
private theorem openVars_nil_id (body : LMonoTy) :
    LMonoTy.openVars [] [] body = body := by
  match body with
  | .ftvar _ => simp [LMonoTy.openVars, List.zip]
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
        simp only [LMonoTy.subst, h_ne, LMonoTy.openVars, Maps.find?]
        rw [map_find_eq_list_find' (v :: vs) (vl :: vls) x]
        generalize (List.zip (v :: vs) (vl :: vls)).find? (fun p => p.1 == x) = res
        match res with
        | some (_, val) => rfl
        | none => rfl
      | .bitvec n =>
        simp [LMonoTy.subst, LMonoTy.openVars]
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
      | [] => simp [LMonoTys.substLogic, LMonoTys.openVars]
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

/-- Substitution composition: when σ = zip(ids, map ftvar fvs) covers all free vars of mty,
    applying outer S after σ equals applying σ' = zip(ids, map (subst S ∘ ftvar) fvs) directly.
    Proved via `subst_single_scope_eq_openVars` + `subst_openVars_comm`. -/
private theorem subst_compose_ftvar_closed' (S : Subst)
    (ids : List TyIdentifier) (freshtvs : List TyIdentifier)
    (h_len : ids.length = freshtvs.length) (mty : LMonoTy)
    (h_closed : ∀ v, v ∈ LMonoTy.freeVars mty → v ∈ ids) :
    LMonoTy.subst S (LMonoTy.subst [List.zip ids (List.map LMonoTy.ftvar freshtvs)] mty) =
    LMonoTy.subst [List.zip ids (List.map (fun v => LMonoTy.subst S (.ftvar v)) freshtvs)] mty := by
  -- Convert subst [zip ...] to openVars, use subst_openVars_comm, then convert back.
  have h_vals_len : ids.length = (List.map LMonoTy.ftvar freshtvs).length := by simp; omega
  have h_vals_len' : ids.length = (List.map (fun v => LMonoTy.subst S (.ftvar v)) freshtvs).length := by simp; omega
  -- Step 1: inner subst → openVars
  rw [subst_single_scope_eq_openVars ids _ mty h_closed h_vals_len]
  -- Step 2: subst_openVars_comm
  rw [subst_openVars_comm S ids _ mty h_closed h_vals_len]
  -- Step 3: substLogic S (map ftvar fvs) = map (subst S ∘ ftvar) fvs
  have h_substLogic_map : LMonoTys.substLogic S (List.map LMonoTy.ftvar freshtvs) =
      List.map (fun v => LMonoTy.subst S (.ftvar v)) freshtvs := by
    clear h_vals_len h_vals_len' h_len h_closed
    induction freshtvs with
    | nil => simp [LMonoTys.substLogic]
    | cons fv fvs' ih =>
      unfold LMonoTys.substLogic; split
      · rename_i hS; simp [LMonoTy.subst_emptyS hS]
      · simp only [List.map]; exact congrArg _ ih
  rw [h_substLogic_map]
  -- Step 4: openVars → subst (reverse direction)
  rw [← subst_single_scope_eq_openVars ids _ mty h_closed h_vals_len']

private theorem Map.keys_erase_subset [DecidableEq α] (m : Map α β) (x : α) :
    ∀ k, k ∈ Map.keys (Map.erase m x) → k ∈ Map.keys m := by
  intro k hk; induction m with
  | nil => simp [Map.erase, Map.keys] at hk
  | cons pair rest ih =>
    obtain ⟨a, b⟩ := pair; simp only [Map.erase] at hk; split at hk
    · simp [Map.keys]; right; exact ih hk
    · simp [Map.keys] at hk ⊢
      grind

private theorem Maps.keys_erase_subset (S : Maps TyIdentifier LMonoTy) (x : TyIdentifier) :
    ∀ k, k ∈ Maps.keys (Maps.erase S x) → k ∈ Maps.keys S := by
  intro k hk; induction S with
  | nil => simp [Maps.erase, Maps.keys] at hk
  | cons scope rest ih =>
    simp only [Maps.erase, Maps.keys] at hk ⊢
    rcases List.mem_append.mp hk with h | h
    · exact List.mem_append_left _ (Map.keys_erase_subset scope x k h)
    · exact List.mem_append_right _ (ih h)

/-- Erasing key `a` removes `a` from a single Map's keys. -/
private theorem Map.keys_erase_self_not_mem [DecidableEq α]
    (m : Map α β) (a : α)
    (h : a ∈ Map.keys (Map.erase m a)) : False := by
  induction m with
  | nil => simp [Map.erase, Map.keys] at h
  | cons pair rest ih =>
    obtain ⟨k, v⟩ := pair
    simp only [Map.erase] at h
    by_cases h_eq : k = a
    · simp [h_eq] at h; exact ih h
    · simp [h_eq, Map.keys] at h
      grind

/-- Erasing key `a` from Maps `S` removes `a` from the keys. -/
private theorem Maps.keys_erase_self_not_mem
    (S : Maps TyIdentifier LMonoTy) (a : TyIdentifier)
    (h : a ∈ Maps.keys (Maps.erase S a)) : False := by
  induction S with
  | nil => simp [Maps.erase, Maps.keys] at h
  | cons scope rest ih =>
    simp only [Maps.erase, Maps.keys] at h
    rcases List.mem_append.mp h with h_scope | h_rest
    · exact Map.keys_erase_self_not_mem scope a h_scope
    · exact ih h_rest

/-- Keys of `go xs S` are a subset of keys of `S`. -/
private theorem keys_go_subset_keys (S : Subst) (xs : List TyIdentifier)
    (a : TyIdentifier) (h : a ∈ Maps.keys (LTy.subst.go xs S)) :
    a ∈ Maps.keys S := by
  induction xs generalizing S with
  | nil => simp [LTy.subst.go] at h; exact h
  | cons x rest ih =>
    simp [LTy.subst.go] at h
    exact Maps.keys_erase_subset S x a (ih (Maps.erase S x) h)

/-- Keys of `go xs S` are not in `xs`. More precisely, if `a ∈ keys (go xs S)`,
    then `a ∉ xs`. -/
private theorem keys_go_not_mem_xs (S : Subst) (xs : List TyIdentifier)
    (a : TyIdentifier) (h : a ∈ Maps.keys (LTy.subst.go xs S)) :
    a ∉ xs := by
  induction xs generalizing S with
  | nil => simp
  | cons x rest ih =>
    simp [LTy.subst.go] at h
    intro h_mem
    rcases List.mem_cons.mp h_mem with rfl | h_rest
    · -- a = x
      have h_a_key := keys_go_subset_keys (Maps.erase S a) rest a h
      exact (Maps.keys_erase_self_not_mem S a h_a_key).elim
    · exact ih (Maps.erase S x) h h_rest

/-- If all keys of `S` that are NOT in `xs` are also not free vars of `mty`,
    then `subst (go xs S) mty = mty`. This follows because `go xs S` erases
    keys in `xs`, and the remaining keys are not free vars of `mty`. -/
private theorem subst_go_irrel_body (S : Subst)
    (xs : List TyIdentifier) (body : LMonoTy)
    (h : ∀ k, k ∈ Maps.keys S → k ∉ xs → k ∉ LMonoTy.freeVars body) :
    LMonoTy.subst (LTy.subst.go xs S) body = body := by
  apply LMonoTy.subst_no_relevant_keys
  intro k hk_fv hk_key
  have hk_S := keys_go_subset_keys S xs k hk_key
  have hk_not_xs := keys_go_not_mem_xs S xs k hk_key
  exact h k hk_S hk_not_xs hk_fv

/-- When `allKeysFresh S ctx` and `forAll xs body` is in the context,
    `subst (go xs S) body = body`: the bound-var-erased substitution
    has no effect on the body. -/
private theorem allKeysFresh_go_body_irrel {T : LExprParams} [DecidableEq T.IDMeta]
    (S : Subst) (ctx : TContext T.IDMeta)
    (x_id : T.Identifier) (xs : List TyIdentifier) (body : LMonoTy)
    (h_fresh : Subst.allKeysFresh S ctx)
    (h_find : Maps.find? ctx.types x_id = some (.forAll xs body)) :
    LMonoTy.subst (LTy.subst.go xs S) body = body := by
  apply subst_go_irrel_body
  intro k hk_S hk_not_xs
  -- k ∈ keys S, k ∉ xs. By allKeysFresh, k is fresh in ctx.
  have h_k_fresh := h_fresh k hk_S
  -- k is fresh in ctx means: for all (y, ty) in ctx.types, k ∉ LTy.freeVars ty
  have h_k_not_fv := h_k_fresh x_id (.forAll xs body) h_find
  -- LTy.freeVars (forAll xs body) = (freeVars body).removeAll xs
  -- k ∉ (freeVars body).removeAll xs means: k ∉ freeVars body ∨ k ∈ xs
  -- Since k ∉ xs, we get k ∉ freeVars body
  -- h_k_not_fv : k ∉ LTy.freeVars (.forAll xs body)
  -- LTy.freeVars (forAll xs body) = (LMonoTy.freeVars body).removeAll xs
  -- removeAll keeps elements NOT in xs. So if k ∈ freeVars body and k ∉ xs,
  -- then k ∈ removeAll, contradicting h_k_not_fv.
  intro hk_fv
  apply h_k_not_fv
  show k ∈ (LMonoTy.freeVars body).removeAll xs
  simp only [List.removeAll, List.mem_filter, List.elem_eq_mem,
             Bool.not_eq_true', decide_eq_false_iff_not]
  exact ⟨hk_fv, hk_not_xs⟩

/-- Variant of `allKeysFresh_go_body_irrel` using `polyKeysFresh` instead of `allKeysFresh`.
    Since `xs` is non-empty (required by the polymorphic case), `polyKeysFresh` suffices. -/
private theorem polyKeysFresh_go_body_irrel {T : LExprParams} [DecidableEq T.IDMeta]
    (S : Subst) (ctx : TContext T.IDMeta)
    (x_id : T.Identifier) (xs : List TyIdentifier) (body : LMonoTy)
    (h_fresh : Subst.polyKeysFresh (T := T) S ctx)
    (h_find : Maps.find? ctx.types x_id = some (.forAll xs body))
    (h_xs_ne : xs ≠ []) :
    LMonoTy.subst (LTy.subst.go xs S) body = body := by
  apply subst_go_irrel_body
  intro k hk_S hk_not_xs
  have h_k_not_fv := h_fresh k hk_S x_id (.forAll xs body) h_find (by
    cases xs with | nil => exact absurd rfl h_xs_ne | cons _ _ => exact List.cons_ne_nil _ _)
  intro hk_fv
  apply h_k_not_fv
  show k ∈ (LMonoTy.freeVars body).removeAll xs
  simp only [List.removeAll, List.mem_filter, List.elem_eq_mem,
             Bool.not_eq_true', decide_eq_false_iff_not]
  exact ⟨hk_fv, hk_not_xs⟩

/-- `polyKeysFresh` is preserved when context is extended with a monomorphic entry
    (one whose `boundVars` is `[]`). The new entry has no bound variables, so the
    `boundVars ≠ []` guard in `polyKeysFresh` is vacuously false for it. -/
private theorem polyKeysFresh_insert_mono {T : LExprParams} [DecidableEq T.IDMeta]
    (S : Subst) (ctx : TContext T.IDMeta) (xv : T.Identifier) (mty : LMonoTy)
    (h : Subst.polyKeysFresh (T := T) S ctx)
    (h_fresh : Maps.find? ctx.types xv = none) :
    Subst.polyKeysFresh (T := T) S
      { ctx with types := ctx.types.insert xv (.forAll [] mty) } := by
  intro a ha x ty hf hbv
  simp at hf
  by_cases h_eq : x = xv
  · subst h_eq
    rw [Maps.find?_insert_self] at hf
    simp at hf; subst hf
    simp [LTy.boundVars] at hbv
  · rw [Maps.find?_insert_ne _ _ _ _ h_eq] at hf
    exact h a ha x ty hf hbv

/-- `polyKeysFresh` is preserved through `typeBoundVar`: the new entry added by
    `typeBoundVar` is monomorphic (`forAll [] xty`), so `polyKeysFresh` for the
    extended context follows from `polyKeysFresh` for the original context. -/
private theorem polyKeysFresh_typeBoundVar {T : LExprParams} [DecidableEq T.IDMeta]
    [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta]
    [ToFormat (LFunc T)] [ToFormat T.Metadata]
    (S : Subst) (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
    (h_tbv : typeBoundVar C Env bty = .ok (xv, xty, Env1))
    (h_poly : Subst.polyKeysFresh (T := T) S Env.context) :
    Subst.polyKeysFresh (T := T) S Env1.context := by
  intro a ha x ty hf hbv
  -- typeBoundVar adds (xv, forAll [] xty) to context.
  -- If x = xv: type is forAll [] xty, boundVars = [], contradicts hbv.
  -- If x ≠ xv: same entry as in Env.context, use h_poly.
  -- Key: typeBoundVar adds via addInNewestContext, which is Maps.insert when xv is fresh.
  -- The xv entry is monomorphic (boundVars = []).
  -- For the general case, we use the fact that find? in Env1.context for x ≠ xv
  -- gives the same result as in Env.context (by typeBoundVar_context decomposition).
  -- For x = xv: boundVars = [] contradicts hbv.
  -- This follows from the structure of typeBoundVar.
  simp only [typeBoundVar, Bind.bind, Except.bind] at h_tbv
  split at h_tbv; · simp at h_tbv
  rename_i v_gen h_gen; obtain ⟨xv_raw, Env_g⟩ := v_gen; simp at h_tbv
  have h_g_ctx := liftGenEnv_context Env xv_raw Env_g h_gen
  revert h_tbv; cases bty with
  | some bty_val =>
    simp only []; intro h_tbv
    generalize h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g = res_ic at h_tbv
    match res_ic with
    | .error _ => simp at h_tbv
    | .ok (mty_ic, Env_ic) =>
      simp at h_tbv
      obtain ⟨h_xv_eq, h_xty_eq, h_env1⟩ := h_tbv
      subst h_xv_eq; subst h_xty_eq
      -- Env1 = addInNewestContext Env_ic [(xv_raw, forAll [] mty_ic)]
      rw [← h_env1] at hf
      simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at hf
      -- Env_ic.context = Env.context (by instantiateWithCheck context preservation)
      have h_ic_ctx := (LMonoTy_instantiateWithCheck_context' bty_val C Env_g _ Env_ic h_ic).trans h_g_ctx
      -- find? in addInNewestContext
      have h_types_eq : Env_ic.genEnv.context.types = Env.genEnv.context.types :=
        congrArg TContext.types h_ic_ctx
      rw [h_types_eq] at hf
      -- Use Maps.find?_addInNewest_single to split: either found the new entry or same as original
      rcases Maps.find?_addInNewest_single Env.genEnv.context.types xv_raw (.forAll [] mty_ic) x with ⟨h_found, h_xeq⟩ | h_same
      · -- Found the new entry: ty = forAll [] mty_ic and x = xv_raw
        rw [h_found] at hf; simp at hf; subst hf
        simp [LTy.boundVars] at hbv
      · -- Same as original: lookup in original context
        rw [h_same] at hf
        exact h_poly a ha x ty (by simp [TEnv.context]; exact hf) hbv
  | none =>
    simp; intro h_tbv
    generalize h_tg : TEnv.genTyVar Env_g = res_tg at h_tbv
    match res_tg with
    | .error _ => simp at h_tbv
    | .ok (xtyid, Env_tg) =>
      simp at h_tbv
      obtain ⟨h_xv_eq, h_xty_eq, h_env1⟩ := h_tbv
      subst h_xv_eq; subst h_xty_eq
      rw [← h_env1] at hf
      simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at hf
      have h_tg_ctx := (TEnv.genTyVar_context Env_g xtyid Env_tg h_tg).trans h_g_ctx
      have h_types_eq : Env_tg.genEnv.context.types = Env.genEnv.context.types :=
        congrArg TContext.types h_tg_ctx
      rw [h_types_eq] at hf
      -- Use Maps.find?_addInNewest_single to split
      rcases Maps.find?_addInNewest_single Env.genEnv.context.types xv_raw (.forAll [] (.ftvar xtyid)) x with ⟨h_found, h_xeq⟩ | h_same
      · rw [h_found] at hf; simp at hf; subst hf
        simp [LTy.boundVars] at hbv
      · rw [h_same] at hf
        exact h_poly a ha x ty (by simp [TEnv.context]; exact hf) hbv


/-- `LMonoTys.subst` distributes over cons. -/
private theorem LMonoTys.subst_cons_eq (S : Subst) (hd : LMonoTy) (tl : LMonoTys) :
    LMonoTys.subst S (hd :: tl) = LMonoTy.subst S hd :: LMonoTys.subst S tl := by
  by_cases hS : Subst.hasEmptyScopes S
  · -- S empty: subst is identity on both mono types and mono type lists
    have h1 : LMonoTy.subst S hd = hd := LMonoTy.subst_emptyS hS
    have h2 : LMonoTys.subst S tl = tl := by
      rw [LMonoTys.subst_eq_substLogic]; induction tl with
      | nil => simp [LMonoTys.substLogic, hS]
      | cons h t ih => simp [LMonoTys.substLogic, hS]
    have h3 : LMonoTys.subst S (hd :: tl) = hd :: tl := by
      rw [LMonoTys.subst_eq_substLogic]; simp [LMonoTys.substLogic, hS]
    rw [h1, h2, h3]
  · -- S non-empty: substLogic directly gives cons
    have hSF : Subst.hasEmptyScopes S = false := Bool.eq_false_iff.mpr hS
    show LMonoTys.subst S (hd :: tl) = LMonoTy.subst S hd :: LMonoTys.subst S tl
    rw [LMonoTys.subst_eq_substLogic (S := S) (mtys := hd :: tl)]
    rw [LMonoTys.subst_eq_substLogic (S := S) (mtys := tl)]
    simp only [LMonoTys.substLogic, hSF]
    simp [Bool.false_eq_true]

/-- Substitution composition for the "open" case: like `subst_compose_ftvar_closed'`,
    but instead of requiring all free vars of `mty` to be in `ids`,
    only requires that free vars NOT in `ids` are not keys of `S`.

    The proof is by induction on `mty`:
    - `ftvar v` with `v ∈ ids`: both sides look up `v` in `zip ids _` and find
      corresponding values; the LHS applies `S` after finding `ftvar ftvs_i`,
      giving `subst S (ftvar ftvs_i)` = `tys_i` which is what the RHS finds.
    - `ftvar v` with `v ∉ ids`: both sides leave `v` alone; the LHS additionally
      applies `S` to `ftvar v`, which is identity since `v ∉ keys S` by `h_extra`.
    - `bitvec`, `tcons`: structural. -/
private theorem subst_compose_ftvar_open (S : Subst)
    (ids : List TyIdentifier) (freshtvs : List TyIdentifier)
    (h_len : ids.length = freshtvs.length) (mty : LMonoTy)
    (h_extra : ∀ v, v ∈ LMonoTy.freeVars mty → v ∉ ids → v ∉ Maps.keys S) :
    LMonoTy.subst S (LMonoTy.subst [List.zip ids (List.map LMonoTy.ftvar freshtvs)] mty) =
    LMonoTy.subst [List.zip ids (List.map (fun v => LMonoTy.subst S (.ftvar v)) freshtvs)] mty := by
  -- Split ids into nil/cons for hasEmptyScopes reasoning. `cases ids` substitutes in goal AND hypotheses.
  cases ids with
  | nil =>
    cases freshtvs with
    | cons _ _ => simp at h_len
    | nil =>
      have h_e1 : Subst.hasEmptyScopes [List.zip ([] : List TyIdentifier) (List.map LMonoTy.ftvar ([] : List TyIdentifier))] = true := by
        simp [List.zip, Subst.hasEmptyScopes, Map.isEmpty]
      have h_e2 : Subst.hasEmptyScopes [List.zip ([] : List TyIdentifier) (List.map (fun v => LMonoTy.subst S (.ftvar v)) ([] : List TyIdentifier))] = true := by
        simp [List.zip, Subst.hasEmptyScopes, Map.isEmpty]
      rw [LMonoTy.subst_emptyS h_e1, LMonoTy.subst_emptyS h_e2]
      exact LMonoTy.subst_no_relevant_keys S mty (fun v hv => h_extra v hv (by simp))
  | cons id ids' =>
    cases freshtvs with
    | nil => simp at h_len
    | cons ftv ftvs' =>
      have h_ne1 : Subst.hasEmptyScopes [List.zip (id :: ids') (List.map LMonoTy.ftvar (ftv :: ftvs'))] = false := by
        simp [Subst.hasEmptyScopes, List.all, List.zip, Map.isEmpty]
      have h_ne2 : Subst.hasEmptyScopes [List.zip (id :: ids') (List.map (fun v => LMonoTy.subst S (.ftvar v)) (ftv :: ftvs'))] = false := by
        simp [Subst.hasEmptyScopes, List.all, List.zip, Map.isEmpty]
      have h_len' : ids'.length = ftvs'.length := by simp at h_len; exact h_len
      have h_find_corr : ∀ (as : List TyIdentifier) (bs : List TyIdentifier) (x : TyIdentifier),
          as.length = bs.length → x ∈ as →
          (match Map.find? (List.zip as (List.map LMonoTy.ftvar bs)) x with
            | some sty => LMonoTy.subst S sty | none => LMonoTy.subst S (.ftvar x)) =
          (match Map.find? (List.zip as (List.map (fun v => LMonoTy.subst S (.ftvar v)) bs)) x with
            | some sty => sty | none => .ftvar x) := by
        intro as bs x h_ab_len h_x_as
        induction as generalizing bs with
        | nil => simp at h_x_as
        | cons a as' ih =>
          cases bs with
          | nil => simp at h_ab_len
          | cons b bs' =>
            simp only [List.map, List.zip, List.zipWith, Map.find?]
            by_cases h_eq : a = x
            · simp [h_eq]
            · simp [h_eq]
              have h_x_as' : x ∈ as' := by
                cases h_x_as with | head => exact absurd rfl h_eq | tail _ h => exact h
              exact ih bs' (by simp at h_ab_len; exact h_ab_len) h_x_as'
      -- Induction on mty. After `cases ids`, h_extra has (id :: ids') directly.
      induction mty with
      | ftvar x =>
        by_cases h_mem : x ∈ (id :: ids')
        · -- x ∈ ids: use subst_compose_ftvar_closed'
          exact subst_compose_ftvar_closed' S (id :: ids') (ftv :: ftvs') h_len (.ftvar x)
            (fun w hw => by simp [LMonoTy.freeVars] at hw; subst hw; exact h_mem)
        · -- x ∉ ids: delegate to subst_compose_ftvar_closed' with vacuous condition
          -- When x ∉ ids, ftvar x has no free vars in ids, so the closed condition is vacuously true
          -- for ftvar x (since freeVars (ftvar x) = [x] and x ∉ ids).
          -- But subst_compose_ftvar_closed' needs ALL freeVars ∈ ids, not just ∉ ids...
          -- So we handle it differently: show both substs leave ftvar x alone.
          have h_not_key : x ∉ Maps.keys S := h_extra x (by simp [LMonoTy.freeVars]) h_mem
          -- LHS: subst S (subst [zip1] (ftvar x))
          -- subst [zip1] (ftvar x) = ftvar x (since x ∉ keys of zip, because x ∉ ids)
          have maps_keys_single : ∀ (m : Map TyIdentifier LMonoTy),
              Maps.keys [m] = Map.keys m := by
            intro m; simp [Maps.keys]
          have h_z1_not_key : x ∉ Maps.keys [List.zip (id :: ids') (List.map LMonoTy.ftvar (ftv :: ftvs'))] := by
            rw [maps_keys_single]
            exact fun hk => h_mem (Map.keys_zip_subset (id :: ids') _ hk)
          have h_z2_not_key : x ∉ Maps.keys [List.zip (id :: ids') (List.map (fun v => LMonoTy.subst S (.ftvar v)) (ftv :: ftvs'))] := by
            rw [maps_keys_single]
            exact fun hk => h_mem (Map.keys_zip_subset (id :: ids') _ hk)
          have h1 := LMonoTy.subst_no_relevant_keys
            [List.zip (id :: ids') (List.map LMonoTy.ftvar (ftv :: ftvs'))] (.ftvar x)
            (fun v hv => by simp [LMonoTy.freeVars] at hv; subst hv; exact h_z1_not_key)
          have h2 := LMonoTy.subst_no_relevant_keys
            [List.zip (id :: ids') (List.map (fun v => LMonoTy.subst S (.ftvar v)) (ftv :: ftvs'))] (.ftvar x)
            (fun v hv => by simp [LMonoTy.freeVars] at hv; subst hv; exact h_z2_not_key)
          have h3 := LMonoTy.subst_no_relevant_keys S (.ftvar x)
            (fun v hv => by simp [LMonoTy.freeVars] at hv; subst hv; exact h_not_key)
          rw [h1, h3, h2]
      | bitvec n =>
        simp [LMonoTy.subst]
      | tcons name args ih_args =>
        -- Per-arg IH: for each a ∈ args with appropriate h_extra restriction,
        -- subst S (subst [zip1] a) = subst [zip2] a.
        -- Lift to tcons level.
        have h_per_arg : ∀ a, a ∈ args →
            LMonoTy.subst S (LMonoTy.subst [List.zip (id :: ids') (List.map LMonoTy.ftvar (ftv :: ftvs'))] a) =
            LMonoTy.subst [List.zip (id :: ids') (List.map (fun v => LMonoTy.subst S (.ftvar v)) (ftv :: ftvs'))] a :=
          fun a ha => ih_args a ha (fun v hv hni => by
            apply h_extra v _ hni; simp only [LMonoTy.freeVars]
            -- v ∈ freeVars a and a ∈ args → v ∈ LMonoTys.freeVars args
            have : ∀ (l : LMonoTys), a ∈ l → v ∈ LMonoTy.freeVars a → v ∈ LMonoTys.freeVars l := by
              intro l h_mem h_fv; induction l with
              | nil => exact absurd h_mem (by simp)
              | cons x xs ih_l =>
                simp only [LMonoTys.freeVars]
                cases h_mem with
                | head => exact List.mem_append_left _ h_fv
                | tail _ h_rest => exact List.mem_append_right _ (ih_l h_rest)
            exact this args ha hv)
        -- Reduce: subst distributes over tcons when non-empty
        -- Use h_per_arg to show each arg matches, then combine for the whole tcons.
        -- Avoid simp on the subst structure; instead use the per-arg proof directly.
        -- Show: subst S (subst [zip1] (tcons name args)) = subst [zip2] (tcons name args)
        -- This is exactly what the goal is after the `induction mty` + `tcons` case.
        -- The approach: rewrite both sides via LMonoTy.subst_tcons or similar,
        -- then reduce to per-arg.
        -- Actually, let's just note that subst_compose_ftvar_closed' on each arg gives us
        -- per-arg equality, and then we can combine using List.map extensionality.
        -- But we don't have List.map because subst on tcons isn't literally List.map.
        --
        -- Simplest: show by induction on args that the whole tcons result follows.
        -- Use the fact that the goal is just the original theorem applied to (.tcons name args),
        -- and we have h_per_arg for each element.
        -- Let's proceed by proving a helper that lifts per-element to LMonoTys:
        -- LHS: subst S (subst [zip1] (.tcons name args))
        -- = subst S (.tcons name (subst [zip1] args))   [since h_ne1]
        -- = .tcons name (subst S (subst [zip1] args))   [if S non-empty; identity if S empty]
        -- RHS: subst [zip2] (.tcons name args) = .tcons name (subst [zip2] args)  [since h_ne2]
        -- So need: subst S (subst [zip1] args) = subst [zip2] args (list-level)
        --          OR: subst [zip1] args = subst [zip2] args (when S empty)
        -- Prove the list-level result by induction, using h_per_arg.
        -- Show the goal directly by converting to LMonoTy.subst on the full tcons.
        -- Goal: subst S (subst [zip1] (.tcons name args)) = subst [zip2] (.tcons name args)
        -- LHS = subst S (.tcons name (LMonoTys.subst [zip1] args))
        --      = .tcons name (LMonoTys.subst S (LMonoTys.subst [zip1] args))  [or identity if S empty]
        -- RHS = .tcons name (LMonoTys.subst [zip2] args)
        -- Convert from LMonoTy.subst on tcons to just tcons of LMonoTys.subst:
        show LMonoTy.subst S (LMonoTy.subst [List.zip (id :: ids') (List.map LMonoTy.ftvar (ftv :: ftvs'))] (.tcons name args)) =
             LMonoTy.subst [List.zip (id :: ids') (List.map (fun v => LMonoTy.subst S (.ftvar v)) (ftv :: ftvs'))] (.tcons name args)
        -- Use LMonoTy.subst_tcons or manual rewriting
        -- Goal: subst S (subst [zip1] (.tcons name args)) = subst [zip2] (.tcons name args)
        -- Prove list-level equality first, then lift to tcons.
        suffices h_list : LMonoTys.subst S (LMonoTys.subst [List.zip (id :: ids') (List.map LMonoTy.ftvar (ftv :: ftvs'))] args) =
            LMonoTys.subst [List.zip (id :: ids') (List.map (fun v => LMonoTy.subst S (.ftvar v)) (ftv :: ftvs'))] args by
          -- Use h_list to close the main goal about tcons
          -- Use h_list on both sides, leveraging the `subst_compose_ftvar_closed'`-like approach.
          -- The goal after the suffices is:
          -- subst S (subst [zip1] (.tcons name args)) = subst [zip2] (.tcons name args)
          -- Which equals: subst S (.tcons name (subst [zip1] args)) = .tcons name (subst [zip2] args)
          -- Use LMonoTy.subst_tcons_pair-like reasoning... but we don't have that for general args.
          -- Let's just do everything directly.
          -- LHS step 1: subst [zip1] (.tcons name args) = .tcons name (LMonoTys.subst [zip1] args)
          --   (since hasEmptyScopes [zip1] = false)
          -- LHS step 2: subst S (.tcons name (LMonoTys.subst [zip1] args))
          --   if hasEmptyScopes S: = .tcons name (LMonoTys.subst [zip1] args)
          --   else: = .tcons name (LMonoTys.subst S (LMonoTys.subst [zip1] args))
          -- RHS: = .tcons name (LMonoTys.subst [zip2] args)
          -- In all cases: .tcons name (...) = .tcons name (LMonoTys.subst [zip2] args)
          -- The ... = LMonoTys.subst [zip2] args by h_list (+ identity of S when empty)
          --
          -- Actually, both sides of the original goal are `LMonoTy.subst _ (.tcons name args)`.
          -- The original goal is exactly what the theorem states for (.tcons name args).
          -- Just rewrite both substs on tcons to expose the list part, then use h_list.
          -- Use the fact that `subst [zip] (.tcons name args) = .tcons name (subst [zip] args)` when zip non-empty
          -- subst_compose_ftvar_closed' already proved for elements where all freeVars ∈ ids.
          -- But we can't use it here since not all freeVars of args may be in ids.
          --
          -- Direct approach: convert goal to and/from substLogic form where we have more control.
          -- Use LMonoTy.subst_tcons to unfold subst on tcons:
          rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons, LMonoTy.subst_tcons]
          -- Goal: .tcons name (subst S (subst [zip1] args)) = .tcons name (subst [zip2] args)
          exact congrArg _ h_list
        -- Prove h_list by induction on args (using a suffices to avoid generalization issues)
        suffices ∀ (l : LMonoTys),
            (∀ a, a ∈ l →
              LMonoTy.subst S (LMonoTy.subst [List.zip (id :: ids') (List.map LMonoTy.ftvar (ftv :: ftvs'))] a) =
              LMonoTy.subst [List.zip (id :: ids') (List.map (fun v => LMonoTy.subst S (.ftvar v)) (ftv :: ftvs'))] a) →
            LMonoTys.subst S (LMonoTys.subst [List.zip (id :: ids') (List.map LMonoTy.ftvar (ftv :: ftvs'))] l) =
            LMonoTys.subst [List.zip (id :: ids') (List.map (fun v => LMonoTy.subst S (.ftvar v)) (ftv :: ftvs'))] l from
          this args h_per_arg
        intro l h_pa
        induction l with
        | nil =>
          rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic]
          simp [LMonoTys.substLogic]
        | cons hd tl ih_tl =>
          have h_hd := h_pa hd (.head _)
          have h_tl := ih_tl (fun a ha => h_pa a (.tail _ ha))
          -- Use subst_cons_eq to distribute over cons, then combine h_hd and h_tl
          simp only [LMonoTys.subst_cons_eq, h_hd, h_tl]

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
               List.zip, List.zipWith, List.find?, BEq.beq]
    simp only [Ne.symm h_w_ne]
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
        simp [LMonoTy.openVars, List.zip, List.zipWith, BEq.beq]
      rw [h_head]
      -- Goal: vl :: openVarsList (v::vs) (vl::vls) (vs.map ftvar) = vl :: vls
      congr 1
      -- Goal: openVarsList (v::vs) (vl::vls) (vs.map ftvar) = vls
      -- Strip the (v, vl) prefix using h_v_notin
      rw [openVarsList_cons_skip_map_ftvar v vl vs vls vs h_v_notin]
      -- Goal: openVarsList vs vls (vs.map ftvar) = vls — by IH
      exact ih vls (by simp at h_len; exact h_len) (List.nodup_cons.mp h_nodup).2

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    | .error e => simp at h_tcons
    | .ok substInfo =>
      simp at h_tcons
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
            · simp; congr 1
              -- Need: substLogic S [alias.type] = [subst S alias.type]
              unfold LMonoTys.substLogic
              have hS_false : Subst.hasEmptyScopes [List.zip alias.typeArgs fvs] = false := by
                revert hS; cases Subst.hasEmptyScopes [List.zip alias.typeArgs fvs] <;> simp
              simp only [hS_false]
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
                simp only [List.map, LMonoTys.freeVars, LMonoTy.freeVars] at h
                cases List.mem_append.mp h <;> grind
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
            rw [LMonoTys.substLogic_length]; exact h_fvs_len)



omit [ToString
  T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    simp at h_tcons
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

mutual
/-- `AliasEquiv` is preserved under type substitution. -/
private theorem AliasEquiv_subst (aliases : List TypeAlias)
    (a b : LMonoTy) (S : Subst) (h : AliasEquiv aliases a b)
    (h_aw : ∀ alias, alias ∈ aliases → TypeAlias.WF alias) :
    AliasEquiv aliases (LMonoTy.subst S a) (LMonoTy.subst S b) := by
  by_cases hS : Subst.hasEmptyScopes S
  · simp [LMonoTy.subst_emptyS hS]; exact h
  · match h with
    | .refl => exact .refl
    | .expand h_exp =>
      obtain ⟨alias, h_mem, h_name, h_len, h_expand⟩ := h_exp
      subst h_expand
      simp [LMonoTy.subst, hS, TypeAlias.expand]
      rw [subst_openVars_comm S alias.typeArgs _ alias.type
        (h_aw alias h_mem).fvs_closed h_len]
      rw [LMonoTys.subst_eq_substLogic]
      have h_sl_len := LMonoTys.substLogic_length
      refine .expand ⟨alias, h_mem, h_name, ?_⟩
      rw [h_sl_len]; exact ⟨h_len, rfl⟩
    | .collapse h_exp =>
      obtain ⟨alias, h_mem, h_name, h_len, h_expand⟩ := h_exp
      subst h_expand
      simp [LMonoTy.subst, hS, TypeAlias.expand]
      rw [subst_openVars_comm S alias.typeArgs _ alias.type
        (h_aw alias h_mem).fvs_closed h_len]
      rw [LMonoTys.subst_eq_substLogic]
      have h_sl_len := LMonoTys.substLogic_length
      refine .collapse ⟨alias, h_mem, h_name, ?_⟩
      rw [h_sl_len]; exact ⟨h_len, rfl⟩
    | .cong_tcons h_args =>
      simp [LMonoTy.subst, hS]
      exact .cong_tcons (AliasEquivList_subst aliases _ _ S h_args h_aw)
    | .trans h1 h2 =>
      exact .trans (AliasEquiv_subst aliases _ _ S h1 h_aw) (AliasEquiv_subst aliases _ _ S h2 h_aw)

/-- `AliasEquivList` is preserved under type substitution. -/
private theorem AliasEquivList_subst (aliases : List TypeAlias)
    (as bs : LMonoTys) (S : Subst) (h : AliasEquivList aliases as bs)
    (h_aw : ∀ alias, alias ∈ aliases → TypeAlias.WF alias) :
    AliasEquivList aliases (LMonoTys.subst S as) (LMonoTys.subst S bs) := by
  by_cases hS : Subst.hasEmptyScopes S
  · simp [LMonoTys.subst, hS]; exact h
  · match h with
    | .nil => simp [LMonoTys.subst, hS, LMonoTys.subst.substAux]; exact .nil
    | .cons h_hd h_tl =>
      rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic]
      simp [LMonoTys.substLogic, hS]
      exact .cons (AliasEquiv_subst aliases _ _ S h_hd h_aw)
        (by rw [← LMonoTys.subst_eq_substLogic, ← LMonoTys.subst_eq_substLogic]
            exact AliasEquivList_subst aliases _ _ S h_tl h_aw)
end

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
mutual
/-- `AliasEquiv` is symmetric. -/
theorem AliasEquiv.symm (h : AliasEquiv aliases a b) : AliasEquiv aliases b a := by
  match h with
  | .refl => exact .refl
  | .expand h_exp => exact .collapse h_exp
  | .collapse h_exp => exact .expand h_exp
  | .cong_tcons h_args => exact .cong_tcons (AliasEquivList.symm h_args)
  | .trans h1 h2 => exact .trans (AliasEquiv.symm h2) (AliasEquiv.symm h1)

/-- `AliasEquivList` is symmetric. -/
theorem AliasEquivList.symm (h : AliasEquivList aliases as bs) : AliasEquivList aliases bs as := by
  match h with
  | .nil => exact .nil
  | .cons h_hd h_tl => exact .cons (AliasEquiv.symm h_hd) (AliasEquivList.symm h_tl)
end

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
mutual
/-- `LMonoTy.resolveAliases` (with `tconsAliasSimple`) produces alias-equivalent output. -/
private theorem resolveAliases_aliasEquiv
    (mty : LMonoTy) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env'))
    (h_aliases : Γ.aliases = Env.context.aliases)
    (h_aliases_wf : TContext.AliasesWF Γ) :
    AliasEquiv Γ.aliases mty mty' := by
  match mty with
  | .ftvar _ | .bitvec _ =>
    simp [LMonoTy.resolveAliases] at h
    obtain ⟨rfl, _⟩ := h; exact .refl
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_args; obtain ⟨args', Env1⟩ := v1; simp at h h_args
    -- tconsAliasSimple is pure: split on find?
    simp only [LMonoTy.tconsAliasSimple] at h
    have h_ctx_pres := LMonoTys.resolveAliases_context args Env args' Env1 h_args
    have h_args_equiv := resolveAliasList_aliasEquiv args Env args' Env1 h_args h_aliases h_aliases_wf
    split at h
    · -- No alias: mty' = tcons name args'
      obtain ⟨rfl, _⟩ := h
      exact .cong_tcons h_args_equiv
    · -- Alias found: mty' = expand alias args'
      rename_i alias h_find
      obtain ⟨rfl, _⟩ := h
      have h_alias_in : alias ∈ Γ.aliases := by
        rw [h_aliases, ← h_ctx_pres]; exact List.mem_of_find?_eq_some h_find
      have h_pred := List.find?_some h_find
      simp [BEq.beq, decide_eq_true_eq] at h_pred
      exact .trans (.cong_tcons h_args_equiv)
        (.expand ⟨alias, h_alias_in, h_pred.1, h_pred.2, rfl⟩)

/-- `LMonoTys.resolveAliases` produces pointwise alias-equivalent outputs. -/
private theorem resolveAliasList_aliasEquiv
    (mtys : LMonoTys) (Env : TEnv T.IDMeta) (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env'))
    (h_aliases : Γ.aliases = Env.context.aliases)
    (h_aliases_wf : TContext.AliasesWF Γ) :
    AliasEquivList Γ.aliases mtys mtys' := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases] at h
    obtain ⟨rfl, _⟩ := h; exact .nil
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_hd; obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    split at h; · simp at h
    rename_i v2 h_tl; obtain ⟨mrest', Env2⟩ := v2
    simp at h; obtain ⟨rfl, _⟩ := h
    have h_ctx_pres := LMonoTy.resolveAliases_context mty Env mty' Env1 h_hd
    exact .cons
      (resolveAliases_aliasEquiv mty Env mty' Env1 h_hd h_aliases h_aliases_wf)
      (resolveAliasList_aliasEquiv mrest Env1 mrest' Env2 h_tl
        (by rw [h_aliases, ← h_ctx_pres]) h_aliases_wf)
end

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
mutual
/-- `LMonoTy.resolveAliases` preserves `stateSubstInfo` (with `tconsAliasSimple`,
    alias resolution is pure — it never modifies the substitution). -/
private theorem LMonoTy_resolveAliases_subst_eq
    (mty : LMonoTy) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  match mty with
  | .ftvar _ | .bitvec _ =>
    simp [LMonoTy.resolveAliases] at h; grind
  | .tcons _ args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_args; obtain ⟨args', Env1⟩ := v1; simp at h h_args
    simp only [LMonoTy.tconsAliasSimple] at h
    split at h <;> (obtain ⟨_, h2⟩ := h; rw [← h2])
    all_goals exact LMonoTys_resolveAliases_subst_eq args Env args' Env1 h_args

private theorem LMonoTys_resolveAliases_subst_eq
    (mtys : LMonoTys) (Env : TEnv T.IDMeta) (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases] at h; grind
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    split at h; · simp at h
    rename_i v1 h_hd; obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    split at h; · simp at h
    rename_i v2 h_tl; obtain ⟨mrest', Env2⟩ := v2
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    exact (LMonoTys_resolveAliases_subst_eq mrest Env1 mrest' Env2 h_tl).trans
      (LMonoTy_resolveAliases_subst_eq mty Env mty' Env1 h_hd)
end

/-- `subst S (ftvar v) = t` when `S` is non-empty and `find? S v = some t`. -/
private theorem LMonoTy.subst_ftvar_eq (S : Subst) (v : TyIdentifier) (t : LMonoTy)
    (h_ne : Subst.hasEmptyScopes S = false) (h_find : Maps.find? S v = some t) :
    LMonoTy.subst S (.ftvar v) = t := by
  simp only [LMonoTy.subst, h_ne, h_find, Bool.false_eq_true, ↓reduceIte]

/-- Helper: `Map.find?` on `l.map (fun v => (v, f v))` returns `some (f v)` for `v ∈ l`. -/
private theorem Map.find?_of_map_self {α : Type} [DecidableEq α] {β : Type}
    (l : List α) (f : α → β) (v : α) (hv : v ∈ l) :
    Map.find? (l.map (fun x => (x, f x))) v = some (f v) := by
  induction l with
  | nil => simp at hv
  | cons w ws ih =>
    simp only [List.map, Map.find?]
    grind

theorem AnnotCompat_subst {aliases : List TypeAlias} {ann xty : LMonoTy}
    (S : Subst)
    (h : AnnotCompat aliases ann xty)
    (h_aw : ∀ alias, alias ∈ aliases → TypeAlias.WF alias) :
    AnnotCompat aliases ann (LMonoTy.subst S xty) := by
  obtain ⟨σ, h_ae⟩ := h
  have h_ae_S := AliasEquiv_subst aliases (LMonoTy.subst [σ] ann) xty S h_ae h_aw
  -- Build σ' mapping each v ∈ freeVars ann to subst S (subst [σ] (ftvar v))
  let g : TyIdentifier → LMonoTy := fun v => LMonoTy.subst S (LMonoTy.subst [σ] (.ftvar v))
  refine ⟨(LMonoTy.freeVars ann).map (fun v => (v, g v)), ?_⟩
  suffices h_eq : LMonoTy.subst [(LMonoTy.freeVars ann).map (fun v => (v, g v))] ann =
      LMonoTy.subst S (LMonoTy.subst [σ] ann) by
    rw [h_eq]; exact h_ae_S
  -- Helper: find? on the constructed map gives the right value
  have h_find : ∀ v, v ∈ LMonoTy.freeVars ann →
      Maps.find? [(LMonoTy.freeVars ann).map (fun v => (v, g v))] v = some (g v) := by
    intro v hv; unfold Maps.find?; rw [Map.find?_of_map_self _ g v hv]
  -- Prove by structural induction with freeVars subset condition
  suffices ∀ (mty : LMonoTy),
      (∀ v, v ∈ LMonoTy.freeVars mty → v ∈ LMonoTy.freeVars ann) →
      LMonoTy.subst [(LMonoTy.freeVars ann).map (fun v => (v, g v))] mty =
        LMonoTy.subst S (LMonoTy.subst [σ] mty) from
    this ann (fun v hv => hv)
  intro mty h_sub
  -- Abbreviate the constructed map
  let σ' := (LMonoTy.freeVars ann).map (fun v => (v, g v))
  by_cases hσ'_e : Subst.hasEmptyScopes [σ']
  · -- σ' empty → ann has no freeVars → mty ground
    have h_no_fv_ann : LMonoTy.freeVars ann = [] := by
      cases h_fv : LMonoTy.freeVars ann with
      | nil => rfl
      | cons v vs =>
        exfalso
        change Subst.hasEmptyScopes [σ'] = true at hσ'_e
        simp only [σ', h_fv, Subst.hasEmptyScopes, List.map] at hσ'_e
        exact absurd hσ'_e (by unfold Map.isEmpty; simp)
    have h_ground : ∀ v, v ∈ LMonoTy.freeVars mty → False := by
      intro v hv; exact absurd (h_no_fv_ann ▸ h_sub v hv) (by simp)
    rw [LMonoTy.subst_emptyS hσ'_e]
    rw [LMonoTy.subst_no_relevant_keys [σ] mty (fun v hv _ => (h_ground v hv).elim)]
    exact (LMonoTy.subst_no_relevant_keys S mty (fun v hv _ => (h_ground v hv).elim)).symm
  · have hσ'_ne : Subst.hasEmptyScopes [σ'] = false := Bool.eq_false_iff.mpr hσ'_e
    induction mty with
    | ftvar v =>
      -- LHS: subst [σ'] (ftvar v) = match find? [σ'] v ... (since σ' non-empty)
      -- RHS: subst S (subst [σ] (ftvar v)) = g v (by def of g)
      -- Use h_find to match
      have hv := h_sub v (by simp [LMonoTy.freeVars])
      have h_fv := h_find v hv
      -- Goal: subst [σ'] (ftvar v) = subst S (subst [σ] (ftvar v))
      exact LMonoTy.subst_ftvar_eq [σ'] v (g v) hσ'_ne h_fv
    | bitvec n =>
      simp only [LMonoTy.subst]
      by_cases hσ : Subst.hasEmptyScopes [σ] <;> by_cases hS : Subst.hasEmptyScopes S <;>
        simp [LMonoTy.subst, hσ, hS]
    | tcons name args ih =>
      rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons, LMonoTy.subst_tcons]; congr 1
      induction args with
      | nil => simp [LMonoTys.subst_eq_substLogic, LMonoTys.substLogic]
      | cons hd tl ih_tl =>
        -- Goal already in cons form after subst_tcons + let unfolding
        -- Just need to combine head (ih) and tail (ih_tl) results
        have h1 := ih hd (.head _) (fun v hv => h_sub v
            (by simp only [LMonoTy.freeVars]; exact List.mem_append_left _ hv))
        have h2 := ih_tl (fun a ha => ih a (.tail _ ha)) (fun v hv => h_sub v
            (by simp only [LMonoTy.freeVars]; exact List.mem_append_right _ hv))
        -- Goal: LMonoTys.subst [σ'] (hd :: tl) = LMonoTys.subst S (LMonoTys.subst [σ] (hd :: tl))
        rw [LMonoTys.subst_cons_eq, LMonoTys.subst_cons_eq, LMonoTys.subst_cons_eq, h1, h2]

omit [ToFormat T.Metadata] [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] in
/-- `LMonoTy.instantiateWithCheck` produces a type that is `AnnotCompat` with
    the input: there exists a substitution σ (renaming free vars to fresh
    generated names) such that the output is alias-equivalent to `subst [σ] mty_in`. -/
private theorem instantiateWithCheck_AnnotCompat [Std.ToFormat T.Metadata]
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta)
    (mty_out : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (mty_out, Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    AnnotCompat Env.context.aliases mty_in mty_out := by
  -- Use the decomposition lemma to extract intermediate values cleanly.
  have ⟨mty_ie, Env_ie, Env_ra, h_ie, h_ra⟩ :=
    LMonoTy.instantiateWithCheck_decompose mty_in C Env mty_out Env' h
  -- h_ie : instantiateEnv mty_in.freeVars [mty_in] Env = .ok ([mty_ie], Env_ie)
  -- h_ra : resolveAliases mty_ie Env_ie = .ok (mty_out, Env_ra)
  -- Step 1: Get the substitution σ from instantiateEnv_decompose
  have ⟨freshtvs, genEnv', h_gen, h_result, h_env_eq⟩ :=
    instantiateEnv_decompose _ _ _ _ _ h_ie
  -- h_result : [mty_ie] = LMonoTys.subst [σ] [mty_in]
  -- Step 2: Get AliasEquiv from resolveAliases_aliasEquiv
  have h_ie_ctx := LMonoTys.instantiateEnv_context _ _ Env _ _ h_ie
  have h_alias := resolveAliases_aliasEquiv mty_ie Env_ie mty_out Env_ra h_ra
      (by rw [h_ie_ctx]) (h_ie_ctx ▸ h_aw)
  -- h_alias : AliasEquiv Env.context.aliases mty_ie mty_out
  -- Step 3: Show mty_ie = subst [σ] mty_in from the singleton list equation h_result,
  -- then substitute to close the goal.
  have h_eq : mty_ie = LMonoTy.subst
      [List.zip (LMonoTy.freeVars mty_in) (List.map LMonoTy.ftvar freshtvs)] mty_in := by
    have h := h_result
    simp only [LMonoTys.subst] at h
    split at h
    · rename_i hS; simp at h; rw [h]; exact (LMonoTy.subst_emptyS hS).symm
    · simp [LMonoTys.subst.substAux] at h; exact h
  subst h_eq
  exact ⟨_, h_ie_ctx ▸ h_alias⟩

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `typeBoundVar` with a `some` annotation produces a type that is
    `AnnotCompat` with the annotation. -/
private theorem typeBoundVar_AnnotCompat [Std.ToFormat T.Metadata]
    (C : LContext T) (Env : TEnv T.IDMeta) (bty_val : LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env (some bty_val) = .ok (xv, xty, Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    AnnotCompat Env.context.aliases bty_val xty := by
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  -- liftGenEnv genVar
  split at h; · simp at h
  rename_i v_gen h_gen; obtain ⟨xv_raw, Env_g⟩ := v_gen; simp at h
  have h_g_ctx : Env_g.context = Env.context := liftGenEnv_context Env _ Env_g h_gen
  -- instantiateWithCheck
  generalize h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g = res_ic at h
  match res_ic with
  | .error _ => simp at h
  | .ok (mty_ic, Env_mid) =>
  simp at h
  obtain ⟨_, h_xty, _⟩ := h; subst h_xty
  exact h_g_ctx ▸ instantiateWithCheck_AnnotCompat bty_val C Env_g mty_ic Env_mid h_ic (h_g_ctx ▸ h_aw)

omit [ToFormat T.Metadata] [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] in
/-- `resolveAliases` preserves typing via `AliasEquiv`. Since `tconsAliasSimple` does
    not modify the substitution, no freshness/substitution argument is needed. -/
private theorem HasType_resolveAliases
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono) (mty_in : LMonoTy)
    (mty_out : LMonoTy) (Env Env' : TEnv T.IDMeta)
    (h_ty : HasType C Γ e (.forAll [] mty_in))
    (h_ra : LMonoTy.resolveAliases mty_in Env = .ok (mty_out, Env'))
    (h_aliases : Γ.aliases = Env.context.aliases)
    (h_aliases_wf : TContext.AliasesWF Γ) :
    HasType C Γ e (.forAll [] mty_out) := by
  exact HasType.talias Γ e mty_in mty_out
    (resolveAliases_aliasEquiv mty_in Env mty_out Env' h_ra h_aliases h_aliases_wf) h_ty


/-- A key of a well-formed substitution does not appear in the free variables
    of any substituted type. Proved via `freeVars_of_subst_subset` + `SubstWF`:
    freeVars after subst ⊆ freeVars(original) ∪ freeVars(values), and keys ∉ freeVars(values). -/
private theorem SubstWF.key_not_in_freeVars_subst
    (S : Subst) (mty : LMonoTy) (a : TyIdentifier)
    (h_key : a ∈ Maps.keys S) (h_wf : SubstWF S) :
    a ∉ LMonoTy.freeVars (LMonoTy.subst S mty) := by
  simp [SubstWF] at h_wf
  have h_not_val : a ∉ Subst.freeVars S := h_wf a h_key
  by_cases hS : Subst.hasEmptyScopes S
  · exact absurd h_key (Subst.isEmpty_implies_keys_empty hS ▸ (by simp))
  · -- Direct induction on mty with hasEmptyScopes = false
    have hSF : Subst.hasEmptyScopes S = false := Bool.eq_false_iff.mpr hS
    induction mty with
    | ftvar v =>
      simp only [LMonoTy.subst, hSF]
      cases h_find : Maps.find? S v with
      | none =>
        -- result is ftvar v, freeVars = [v]
        -- v ∉ keys S (from find? = none). If a = v, contradiction with h_key.
        intro h_eq; simp [LMonoTy.freeVars] at h_eq
        subst h_eq; exact (Maps.find?_of_not_mem_values S h_find) h_key
      | some t =>
        -- result is t: a ∉ freeVars t because a ∉ Subst.freeVars S
        exact fun h => h_not_val (Subst.freeVars_of_find_subset S h_find h)
    | bitvec _ => simp [LMonoTy.subst, hSF, LMonoTy.freeVars]
    | tcons name args ih =>
      simp only [LMonoTy.subst, hSF]
      -- Need: a ∉ LMonoTys.freeVars (LMonoTys.subst S args)
      -- Use subst_eq_substLogic to convert to map form
      rw [LMonoTys.subst_eq_substLogic]
      suffices ∀ (l : LMonoTys), (∀ m, m ∈ l → a ∉ LMonoTy.freeVars (LMonoTy.subst S m)) →
          a ∉ LMonoTys.freeVars (LMonoTys.substLogic S l) by
        exact this args (fun m hm => ih m hm)
      intro l h_all
      induction l with
      | nil => simp [LMonoTys.substLogic, LMonoTys.freeVars]
      | cons hd tl ih_tl =>
        simp only [LMonoTys.substLogic, hSF]
        intro h_abs; rcases List.mem_append.mp h_abs with h_hd | h_tl
        · exact h_all hd (List.mem_cons_self ..) h_hd
        · exact ih_tl (fun m hm => h_all m (List.mem_cons_of_mem _ hm)) h_tl

private theorem Map.values_erase_subset [DecidableEq α] (m : Map α β) (x : α) :
    ∀ v, v ∈ Map.values (Map.erase m x) → v ∈ Map.values m := by
  induction m with
  | nil => simp [Map.erase, Map.values]
  | cons pair rest ih =>
    obtain ⟨k, val⟩ := pair; simp only [Map.erase]; split
    · intro v hv; simp [Map.values]; right; exact ih v hv
    · intro v hv; simp [Map.values] at hv ⊢
      grind

private theorem Maps.values_erase_subset [DecidableEq α] (ms : Maps α β) (x : α) :
    ∀ v, v ∈ Maps.values (Maps.erase ms x) → v ∈ Maps.values ms := by
  induction ms with
  | nil => simp [Maps.erase, Maps.values]
  | cons scope rest ih =>
    intro v hv; simp only [Maps.erase, Maps.values] at hv ⊢
    rcases List.mem_append.mp hv with h | h
    · exact List.mem_append_left _ (Map.values_erase_subset scope x v h)
    · exact List.mem_append_right _ (ih v h)

private theorem Subst.freeVars_erase_subset (S : Subst) (x : TyIdentifier) :
    ∀ a, a ∈ Subst.freeVars (Maps.erase S x) → a ∈ Subst.freeVars S := by
  intro a ha; simp [Subst.freeVars] at ha ⊢
  obtain ⟨mty, h_val, h_fv⟩ := ha
  exact ⟨mty, Maps.values_erase_subset S x mty h_val, h_fv⟩

private theorem SubstWF_erase (S : Subst) (x : TyIdentifier) (h_wf : SubstWF S) :
    SubstWF (Maps.erase S x) := by
  simp [SubstWF] at h_wf ⊢; intro k hk hk_fv
  exact h_wf k (Maps.keys_erase_subset S x k hk) (Subst.freeVars_erase_subset S x k hk_fv)

private theorem SubstWF_go (S : Subst) (xs : List TyIdentifier) (h_wf : SubstWF S) :
    SubstWF (LTy.subst.go xs S) := by
  induction xs generalizing S with
  | nil => simp [LTy.subst.go]; exact h_wf
  | cons x rest ih =>
    simp [LTy.subst.go]
    exact ih (Maps.erase S x) (SubstWF_erase S x h_wf)

private theorem Map.keys_erase_mem_of_ne [DecidableEq α] (m : Map α β) {a x : α}
    (h_key : a ∈ Map.keys m) (h_ne : a ≠ x) :
    a ∈ Map.keys (Map.erase m x) := by
  induction m with
  | nil => simp [Map.keys] at h_key
  | cons pair rest ih =>
    obtain ⟨k, v⟩ := pair; simp only [Map.erase]; simp [Map.keys] at h_key
    rcases h_key with rfl | h
    · split
      · exact absurd (by assumption) h_ne
      · simp [Map.keys]
    · split
      · exact ih h
      · simp [Map.keys]; right; exact ih h

private theorem Maps.keys_erase_mem_of_ne {S : Maps TyIdentifier LMonoTy} {a x : TyIdentifier}
    (h_key : a ∈ Maps.keys S) (h_ne : a ≠ x) :
    a ∈ Maps.keys (Maps.erase S x) := by
  induction S with
  | nil => simp [Maps.keys] at h_key
  | cons scope rest ih =>
    simp only [Maps.erase, Maps.keys] at h_key ⊢
    rcases List.mem_append.mp h_key with h | h
    · exact List.mem_append_left _ (Map.keys_erase_mem_of_ne scope h h_ne)
    · exact List.mem_append_right _ (ih h)

private theorem keys_go_mem (S : Subst) (xs : List TyIdentifier) (a : TyIdentifier)
    (h_key : a ∈ Maps.keys S) (h_not_xs : a ∉ xs) :
    a ∈ Maps.keys (LTy.subst.go xs S) := by
  induction xs generalizing S with
  | nil => simp [LTy.subst.go]; exact h_key
  | cons x rest ih =>
    simp [LTy.subst.go]
    apply ih (Maps.erase S x)
    · exact Maps.keys_erase_mem_of_ne h_key
        (fun h => h_not_xs (h ▸ List.mem_cons_self ..))
    · exact fun h => h_not_xs (List.mem_cons_of_mem x h)

/-- A key of a well-formed substitution does not appear in the free variables
    of any substituted LTy. Lifts `key_not_in_freeVars_subst` from LMonoTy to LTy. -/
private theorem SubstWF.key_not_in_LTy_freeVars_subst
    (S : Subst) (ty : LTy) (a : TyIdentifier)
    (h_key : a ∈ Maps.keys S) (h_wf : SubstWF S) :
    a ∉ LTy.freeVars (LTy.subst S ty) := by
  cases ty with
  | forAll xs body =>
    simp only [LTy.subst, LTy.freeVars]
    intro h_mem
    simp [_root_.List.removeAll, _root_.List.mem_filter] at h_mem
    obtain ⟨h_in_fv, h_not_xs⟩ := h_mem
    exact SubstWF.key_not_in_freeVars_subst (LTy.subst.go xs S) body a
      (keys_go_mem S xs a h_key h_not_xs) (SubstWF_go S xs h_wf) h_in_fv

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
private theorem TContext_types_subst_go_find_reverse
    (scope : Map (T.Identifier) LTy) (S : Subst) (x : T.Identifier) (ty : LTy)
    (h : Map.find? (TContext.types.subst.go S scope) x = some ty) :
    ∃ ty_orig, Map.find? scope x = some ty_orig ∧ ty = LTy.subst S ty_orig := by
  induction scope with
  | nil => simp [TContext.types.subst.go, Map.find?] at h
  | cons pair rest ih =>
    obtain ⟨k, v⟩ := pair
    simp only [TContext.types.subst.go, Map.find?] at h ⊢
    grind

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
private theorem TContext_types_subst_go_find_none_reverse
    (scope : Map (T.Identifier) LTy) (S : Subst) (x : T.Identifier)
    (h : Map.find? (TContext.types.subst.go S scope) x = none) :
    Map.find? scope x = none := by
  induction scope with
  | nil => simp [Map.find?]
  | cons pair rest ih =>
    obtain ⟨k, v⟩ := pair
    simp only [TContext.types.subst.go, Map.find?] at h ⊢
    grind

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
private theorem TContext_types_subst_find_reverse
    (types : Maps (T.Identifier) LTy) (S : Subst) (x : T.Identifier) (ty : LTy)
    (h : Maps.find? (TContext.types.subst types S) x = some ty) :
    ∃ ty_orig, Maps.find? types x = some ty_orig ∧ ty = LTy.subst S ty_orig := by
  induction types with
  | nil => simp [TContext.types.subst, Maps.find?] at h
  | cons scope rest ih =>
    simp only [TContext.types.subst, Maps.find?] at h ⊢
    cases h_go : Map.find? (TContext.types.subst.go S scope) x with
    | some ty_found =>
      rw [h_go] at h; simp at h; subst h
      obtain ⟨ty_orig, h_orig, h_eq⟩ := TContext_types_subst_go_find_reverse scope S x ty_found h_go
      exact ⟨ty_orig, by rw [h_orig], h_eq⟩
    | none =>
      rw [h_go] at h
      obtain ⟨ty_orig, h_orig, h_eq⟩ := ih h
      rw [TContext_types_subst_go_find_none_reverse scope S x h_go]
      exact ⟨ty_orig, h_orig, h_eq⟩

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- A key of a well-formed substitution is fresh in the substituted context.
    SubstWF ensures keys don't appear in values, so after substitution,
    keys are eliminated from all type free variables. -/
private theorem TContext.isFresh_subst_of_key
    (Γ : TContext T.IDMeta) (S : Subst) (a : TyIdentifier)
    (h_key : a ∈ Maps.keys S) (h_wf : SubstWF S) :
    TContext.isFresh (T := T) a (TContext.subst Γ S) := by
  intro x ty h_find
  simp [TContext.subst] at h_find
  obtain ⟨ty_orig, _, h_eq⟩ := TContext_types_subst_find_reverse Γ.types S x ty h_find
  subst h_eq
  exact SubstWF.key_not_in_LTy_freeVars_subst S ty_orig a h_key h_wf

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    (h_bvf : ∀ y ty, Env.context.types.find? y = some ty →
      ∀ v, v ∈ LTy.boundVars ty →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n)
    (h_aw : TContext.AliasesWF Env.context) :
    Env'.context = Env.context ∧
      ∀ (S : Subst), Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        Subst.polyKeysFresh (T := T) S Env.context →
        HasType C (TContext.subst Env.context S) (.fvar m x fty)
          (.forAll [] (LMonoTy.subst S ty_res)) := by
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
        · exact LTy_instantiateWithCheck_context ty C Env mty Env1 h_inst
        · intro S h_abs_S h_wf_S h_fresh_ctx
          -- Decompose instantiateWithCheck to get instantiate + resolveAliases
          simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h_inst
          split at h_inst; · simp at h_inst
          rename_i v_ra h_ra; obtain ⟨mty_ra, Env_ra⟩ := v_ra; dsimp at h_inst h_ra
          split at h_inst; · simp at h_inst
          split at h_inst
          · simp at h_inst
            obtain ⟨h_mty, h_env⟩ := h_inst; subst h_mty; subst h_env
            -- Decompose resolveAliases to get instantiate + resolveAliases
            simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
            split at h_ra; · simp at h_ra
            rename_i v_inst h_lty_inst; obtain ⟨mty_inst, genEnv'⟩ := v_inst
            simp at h_ra h_lty_inst
            -- h_lty_inst : ty.instantiate Env.genEnv = .ok (mty_inst, genEnv')
            -- h_ra : LMonoTy.resolveAliases mty_inst ... = .ok (mty, ...)
            -- Step 1: tvar in substituted context
            have h_find_S := _root_.Lambda.TContext_types_subst_find
              Env.context.types S x ty h_find
            have h_tvar_S := HasType.tvar (C := C) (TContext.subst Env.context S) m x
              (LTy.subst S ty) h_find_S
            -- Step 2: Instantiate LTy.subst S ty
            have h_nodup := h_bvnd x ty h_find
            have h_bv_fresh_ty := h_bvf x ty h_find
            have ⟨mty', h_inst_S⟩ := _root_.Lambda.LTy_subst_instantiate S ty
              Env.genEnv mty_inst genEnv' h_lty_inst
            have h_bv_eq := _root_.Lambda.LTy_subst_boundVars S ty
            have h_nodup_S : (LTy.subst S ty).boundVars.Nodup := h_bv_eq ▸ h_nodup
            have h_bv_fresh_S : ∀ v, v ∈ (LTy.subst S ty).boundVars →
                ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
              rw [h_bv_eq]; exact h_bv_fresh_ty
            have h_mono_S := HasType_LTy_instantiate C (TContext.subst Env.context S)
              (.fvar m x none) (LTy.subst S ty) mty'
              Env.genEnv genEnv' h_tvar_S h_inst_S h_nodup_S h_bv_fresh_S
            -- h_mono_S : HasType C (Γ.subst S) (.fvar m x none) (.forAll [] mty')
            -- Step 3: Alias resolution in substituted context
            have h_ctx_inst := LTy.instantiate_context ty Env.genEnv mty_inst genEnv' h_lty_inst
            have h_aliases_subst : (TContext.subst Env.context S).aliases = Env.context.aliases :=
              _root_.Lambda.TContext.subst_aliases Env.context S
            have h_aw_subst : TContext.AliasesWF (TContext.subst Env.context S) := by
              rw [TContext.AliasesWF]; rw [h_aliases_subst]; exact h_aw
            -- AliasEquiv from resolveAliases: AliasEquiv aliases mty_inst mty
            have h_aliases_env : Env.context.aliases =
                ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context.aliases := by
              simp [TEnv.context]; rw [h_ctx_inst]
            have h_ae := resolveAliases_aliasEquiv mty_inst
              ({Env with genEnv := genEnv'} : TEnv T.IDMeta) mty_ra Env_ra h_ra
              h_aliases_env (by unfold TContext.AliasesWF; exact h_aw)
            -- h_ae : AliasEquiv Env.context.aliases mty_inst mty_ra
            -- Step 4: Bridge mty' to subst S mty_ra via AliasEquiv
            -- For nil case: mty' = subst S body = subst S mty_inst, so
            --   AliasEquiv (subst S mty_inst) (subst S mty_ra) by AliasEquiv_subst
            -- For cons case: mty' = subst [zip bvs ftv] (subst (go bvs S) body)
            --   while mty_inst = subst [zip bvs ftv] body — needs commutation
            -- We handle both via AliasEquiv_subst on mty_inst → mty_ra, then bridge mty' to subst S mty_inst
            have h_ae_S := AliasEquiv_subst Env.context.aliases mty_inst mty_ra S h_ae
              (fun a ha => h_aw a ha)
            -- h_ae_S : AliasEquiv aliases (subst S mty_inst) (subst S mty_ra)
            -- Case split on bound vars of ty for the final proof
            cases ty with
            | forAll xs body =>
            cases xs with
            | nil =>
              -- MONOMORPHIC: mty' = subst S body = subst S mty_inst (go [] S = S)
              simp [LTy.instantiate] at h_lty_inst
              obtain ⟨h1, _⟩ := h_lty_inst; subst h1
              simp [LTy.subst, LTy.subst.go, LTy.instantiate] at h_inst_S
              obtain ⟨h2, _⟩ := h_inst_S; subst h2
              -- mty' = subst S mty_inst, so AliasEquiv .refl → trans with h_ae_S
              exact HasType.talias (TContext.subst Env.context S) _ _ _
                (h_aliases_subst ▸ h_ae_S) h_mono_S
            | cons x_bv rest =>
              -- POLYMORPHIC: use allKeysFresh to show LTy.subst S ty = ty,
              -- then reconstruct proof via original instantiate + resolveAliases
              -- + HasType_subst_fresh_all.
              have h_go_irrel := polyKeysFresh_go_body_irrel S Env.context
                x (x_bv :: rest) body h_fresh_ctx h_find (List.cons_ne_nil _ _)
              have h_subst_ty_eq : LTy.subst S (.forAll (x_bv :: rest) body) =
                  .forAll (x_bv :: rest) body := by
                simp [LTy.subst, h_go_irrel]
              -- Rewrite h_tvar_S: now HasType with the un-substituted type
              rw [h_subst_ty_eq] at h_tvar_S
              -- Apply the original HasType_LTy_instantiate in ctx.subst S
              have h_mono := HasType_LTy_instantiate C (TContext.subst Env.context S)
                (.fvar m x none) (.forAll (x_bv :: rest) body) mty_inst
                Env.genEnv genEnv' h_tvar_S h_lty_inst h_nodup h_bv_fresh_ty
              -- Apply HasType_resolveAliases in ctx.subst S (aliases are the same)
              have h_aliases_S_eq : (TContext.subst Env.context S).aliases =
                  ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context.aliases := by
                rw [h_aliases_subst]; simp [TEnv.context]; rw [h_ctx_inst]
              have h_typed := HasType_resolveAliases C (TContext.subst Env.context S)
                (.fvar m x none) mty_inst mty_ra
                {Env with genEnv := genEnv'} Env_ra h_mono h_ra h_aliases_S_eq h_aw_subst
              -- Apply HasType_subst_fresh_all (freshness from SubstWF_key_isFresh_ctx_subst)
              exact HasType_subst_fresh_all C (TContext.subst Env.context S)
                (.fvar m x none) mty_ra S h_typed
                (fun a ha_key _ => TContext.isFresh_subst_of_key Env.context S a ha_key h_wf_S)
                h_wf_S
          · simp at h_inst
      · -- Case fty = some fty_val
        rename_i fty_val
        split at h
        · simp at h  -- LMonoTy.instantiateWithCheck failed
        · rename_i v2 h_inst2
          obtain ⟨fty_inst, Env2⟩ := v2
          simp at h h_inst2
          split at h
          · simp at h  -- unify failed (via mapError)
          · rename_i S_info h_unify_raw
            simp at h
            obtain ⟨h_ty, h_env⟩ := h
            subst h_ty; subst h_env
            -- Extract unify hypothesis from mapError wrapper
            have h_unify : Constraints.unify [(fty_inst, mty)]
                Env2.stateSubstInfo = .ok S_info := by
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
            · -- HasType with arbitrary absorbing S in substituted context
              intro S h_abs_S h_wf_S h_fresh_ctx
              simp [TEnv.updateSubst] at h_abs_S
              -- Decompose instantiateWithCheck for ty
              simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h_inst
              split at h_inst; · simp at h_inst
              rename_i v_ra h_ra; obtain ⟨mty_ra, Env_ra⟩ := v_ra; dsimp at h_inst h_ra
              split at h_inst; · simp at h_inst
              split at h_inst
              · simp at h_inst
                obtain ⟨h_mty_eq, h_env_eq⟩ := h_inst; subst h_mty_eq; subst h_env_eq
                -- Decompose resolveAliases into instantiate + LMonoTy.resolveAliases
                simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
                split at h_ra; · simp at h_ra
                rename_i v_inst h_lty_inst; obtain ⟨mty_inst, genEnv'⟩ := v_inst
                simp at h_ra h_lty_inst
                -- h_lty_inst : ty.instantiate Env.genEnv = .ok (mty_inst, genEnv')
                -- h_ra : mty_inst.resolveAliases {Env with genEnv := genEnv'} = .ok (mty_ra, Env_ra)
                -- Context chain
                have h_ctx_inst := LTy.instantiate_context ty Env.genEnv mty_inst genEnv' h_lty_inst
                have h_ra_ctx : ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context = Env.context := by
                  simp [TEnv.context]; exact h_ctx_inst
                have h_env_ra_ctx : Env_ra.context = Env.context := by
                  rw [LMonoTy.resolveAliases_context _ _ _ _ h_ra]; exact h_ra_ctx
                have h_aliases_eq : Env.context.aliases =
                    ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context.aliases := by
                  simp [TEnv.context]; rw [h_ctx_inst]
                -- AliasEquiv from resolveAliases: mty_inst ~ mty_ra (= mty after subst)
                have h_ae := resolveAliases_aliasEquiv mty_inst {Env with genEnv := genEnv'}
                  mty_ra Env_ra h_ra h_aliases_eq (by unfold TContext.AliasesWF; exact h_aw)
                -- Under S: subst S mty_inst ~ subst S mty_ra
                have h_ae_S := AliasEquiv_subst Env.context.aliases mty_inst mty_ra S h_ae
                  (fun a ha => h_aw a ha)
                -- AnnotCompat: decompose h_inst2 to get substitution structure
                have ⟨mty_fty_ie, Env_fty_ie, Env_fty_ra, h_fty_ie, h_fty_ra⟩ :=
                  LMonoTy.instantiateWithCheck_decompose fty_val C Env_ra fty_inst Env2 h_inst2
                have ⟨freshtvs_fty, _, h_gen_fty, h_fty_result, _⟩ :=
                  instantiateEnv_decompose _ _ _ _ _ h_fty_ie
                have h_fty_eq : mty_fty_ie = LMonoTy.subst
                    [List.zip (LMonoTy.freeVars fty_val)
                      (List.map LMonoTy.ftvar freshtvs_fty)] fty_val := by
                  have h := h_fty_result; simp only [LMonoTys.subst] at h
                  split at h
                  · rename_i hS; simp at h; rw [h]; exact (LMonoTy.subst_emptyS hS).symm
                  · simp [LMonoTys.subst.substAux] at h; exact h
                -- AliasEquiv from resolveAliases on annotation
                have h_fty_ie_ctx := LMonoTys.instantiateEnv_context _ _ Env_ra _ _ h_fty_ie
                have h_ae_fty : AliasEquiv Env.context.aliases
                    (LMonoTy.subst [List.zip (LMonoTy.freeVars fty_val)
                      (List.map LMonoTy.ftvar freshtvs_fty)] fty_val) fty_inst := by
                  have h_ctx_chain : Env_fty_ie.context.aliases = Env.context.aliases := by
                    rw [h_fty_ie_ctx, h_env_ra_ctx]
                  rw [← h_fty_eq]
                  exact h_ctx_chain ▸ resolveAliases_aliasEquiv mty_fty_ie Env_fty_ie fty_inst Env_fty_ra
                    h_fty_ra rfl (by rw [h_fty_ie_ctx, h_env_ra_ctx]; exact h_aw)
                -- Apply S to annotation AliasEquiv
                have h_ae_fty_S := AliasEquiv_subst Env.context.aliases _ _ S h_ae_fty
                  (fun a ha => h_aw a ha)
                -- Unification + absorption: subst S fty_inst = subst S mty_ra
                have h_eq_abs : LMonoTy.subst S fty_inst = LMonoTy.subst S mty_ra := by
                  have h_eq := unify_makes_equal fty_inst mty_ra Env2.stateSubstInfo S_info h_unify
                  have := congrArg (LMonoTy.subst S) h_eq
                  rw [LMonoTy.subst_absorbs S S_info.subst fty_inst h_abs_S,
                      LMonoTy.subst_absorbs S S_info.subst mty_ra h_abs_S] at this
                  exact this
                rw [h_eq_abs] at h_ae_fty_S
                -- Compose substitution: subst S (subst [σ_fty] fty_val) → subst [σ'] fty_val
                have h_fty_len : (LMonoTy.freeVars fty_val).length = freshtvs_fty.length :=
                  (TGenEnv.genTyVars_length _ _ _ _ h_gen_fty).symm
                rw [subst_compose_ftvar_closed' S _ freshtvs_fty h_fty_len fty_val
                    (fun v hv => hv)] at h_ae_fty_S
                -- Bridge to subst S mty_inst via symm of h_ae_S
                have h_ae_fty_mty : AliasEquiv Env.context.aliases
                    (LMonoTy.subst [List.zip (LMonoTy.freeVars fty_val)
                      (List.map (fun v => LMonoTy.subst S (.ftvar v)) freshtvs_fty)] fty_val)
                    (LMonoTy.subst S mty_inst) :=
                  .trans h_ae_fty_S (AliasEquiv.symm h_ae_S)
                have h_annot : AnnotCompat Env.context.aliases fty_val (LMonoTy.subst S mty_inst) :=
                  ⟨_, h_ae_fty_mty⟩
                -- Case split on ty's bound vars for openFull construction
                have h_aliases_subst : (TContext.subst Env.context S).aliases = Env.context.aliases :=
                  _root_.Lambda.TContext.subst_aliases Env.context S
                have h_find_S := _root_.Lambda.TContext_types_subst_find
                  Env.context.types S x ty h_find
                cases ty with
                | forAll vars body =>
                simp [LTy.boundVars] at h_bvnd h_bvf
                cases vars with
                | nil =>
                  -- Monomorphic case: mty_inst = body
                  simp [LTy.instantiate] at h_lty_inst
                  obtain ⟨h_eq_inst, _⟩ := h_lty_inst; subst h_eq_inst
                  -- LTy.subst S (forAll [] body) = forAll [] (subst (go [] S) body)
                  -- go [] S = S, so openFull (forAll [] (subst S body)) [] = subst S body
                  have h_open : LTy.openFull (LTy.subst S (.forAll [] body)) [] =
                      LMonoTy.subst S body := by
                    simp [LTy.subst, LTy.subst.go, LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe]
                    exact LMonoTy.subst_emptyS (by simp [Subst.hasEmptyScopes, Map.isEmpty])
                  have h_bv_subst : (LTy.subst S (.forAll [] body)).boundVars = [] := by
                    rw [_root_.Lambda.LTy_subst_boundVars]; simp [LTy.boundVars]
                  rw [← h_aliases_subst] at h_annot h_ae_S
                  exact HasType.talias (TContext.subst Env.context S) _ _ _ h_ae_S
                    (HasType.tvar_annotated (C := C) (TContext.subst Env.context S) m x
                      (LTy.subst S (.forAll [] body)) (LMonoTy.subst S body) [] fty_val
                      h_find_S (by simp [h_bv_subst]) h_open h_annot)
                | cons x' xs' =>
                  -- Polymorphic case: use allKeysFresh + subst_compose_ftvar_open
                  simp only [LTy.instantiate, Bind.bind, Except.bind] at h_lty_inst
                  split at h_lty_inst; · simp at h_lty_inst
                  rename_i v_gen h_gen'; obtain ⟨ftvs, gE⟩ := v_gen
                  simp at h_lty_inst h_gen'
                  obtain ⟨h_eq_inst, _⟩ := h_lty_inst; subst h_eq_inst
                  -- mty_inst = subst [zip (x'::xs') (map ftvar ftvs)] body
                  have h_len := TGenEnv.genTyVars_length _ _ _ _ h_gen'
                  let tys := List.map (fun tv => LMonoTy.subst S (.ftvar tv)) ftvs
                  have h_tys_len : tys.length = (x' :: xs').length := by simp [tys, h_len]
                  -- Show go-identity from allKeysFresh
                  have h_go_irrel := polyKeysFresh_go_body_irrel S Env.context
                    x (x' :: xs') body h_fresh_ctx h_find (List.cons_ne_nil _ _)
                  -- LTy.subst S ty = ty (since go-identity holds)
                  have h_subst_ty : LTy.subst S (.forAll (x' :: xs') body) =
                      .forAll (x' :: xs') body := by
                    simp [LTy.subst, h_go_irrel]
                  -- h_extra: free vars of body outside bound vars are not keys of S
                  have h_extra : ∀ v, v ∈ LMonoTy.freeVars body → v ∉ (x' :: xs') →
                      v ∉ Maps.keys S := by
                    intro v hv hni
                    intro h_key
                    have h_fresh_v := h_fresh_ctx v h_key
                    have h_bv_ne : LTy.boundVars (.forAll (x' :: xs') body) ≠ [] := by
                      simp [LTy.boundVars]
                    have h_not_fv := h_fresh_v x (.forAll (x' :: xs') body) h_find h_bv_ne
                    exact h_not_fv (by
                      show v ∈ (LMonoTy.freeVars body).removeAll (x' :: xs')
                      simp only [List.removeAll, List.mem_filter, List.elem_eq_mem,
                                 Bool.not_eq_true', decide_eq_false_iff_not]
                      exact ⟨hv, hni⟩)
                  -- Composition: subst S mty_inst = subst [zip bvs tys] body
                  have h_compose := subst_compose_ftvar_open S (x' :: xs') ftvs
                    h_len.symm body h_extra
                  -- openFull (LTy.subst S ty) tys = subst [zip bvs tys] body = subst S mty_inst
                  have h_open : LTy.openFull (LTy.subst S (.forAll (x' :: xs') body)) tys =
                      LMonoTy.subst S (LMonoTy.subst [List.zip (x' :: xs')
                        (List.map LMonoTy.ftvar ftvs)] body) := by
                    rw [h_subst_ty]
                    simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe, tys]
                    exact h_compose.symm
                  have h_bv_subst : (LTy.subst S (.forAll (x' :: xs') body)).boundVars =
                      x' :: xs' := by
                    rw [_root_.Lambda.LTy_subst_boundVars]; simp [LTy.boundVars]
                  rw [← h_aliases_subst] at h_annot h_ae_S
                  exact HasType.talias (TContext.subst Env.context S) _ _ _ h_ae_S
                    (HasType.tvar_annotated (C := C) (TContext.subst Env.context S) m x
                      (LTy.subst S (.forAll (x' :: xs') body))
                      (LMonoTy.subst S (LMonoTy.subst [List.zip (x' :: xs')
                        (List.map LMonoTy.ftvar ftvs)] body))
                      tys fty_val h_find_S
                      (by simp [h_bv_subst]; exact h_tys_len)
                      h_open h_annot)
              · simp at h_inst

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
omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
private theorem transfer_boundVarsNodup
    {Env Env' : TEnv T.IDMeta}
    (h_nd : ∀ y ty, Env.context.types.find? y = some ty →
      (LTy.boundVars ty).Nodup)
    (h_ctx : Env'.context = Env.context) :
    ∀ y ty, Env'.context.types.find? y = some ty →
      (LTy.boundVars ty).Nodup := by
  intro y ty h_f
  exact h_nd y ty (by rwa [h_ctx] at h_f)

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Build `TEnvWF` for the output of `resolveAux` given `TEnvWF` for the input. -/
theorem TEnvWF.of_resolveAux
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h_res : resolveAux C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions)
    (h_ctx : Env'.context = Env.context) : TEnvWF Env' :=
  { aliasesWF := h_ctx ▸ h_envwf.aliasesWF
    substFreshForGen := resolveAux_preserves_SubstFreshForGen e et C Env Env'
      h_res h_envwf.substFreshForGen h_envwf.ctxFreshForGen h_ne
      h_envwf.aliasesWF h_fwf h_envwf.boundVarsFresh
    ctxFreshForGen := h_ctx ▸ ContextFreshForGen.mono _ _ _
      h_envwf.ctxFreshForGen (resolveAux_genState_mono e et C Env Env' h_res)
    boundVarsNodup := transfer_boundVarsNodup h_envwf.boundVarsNodup h_ctx
    boundVarsFresh := transfer_boundVarsFresh h_envwf.boundVarsFresh h_ctx
      (resolveAux_genState_mono e et C Env Env' h_res) }

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
  | abs _ _ _ _ => rfl
  | quant _ _ _ _ _ _ => rfl
  | ite _ _ _ _ => rfl
  | eq _ _ _ => rfl

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
private theorem resolveAux_output_type_no_future_vars :
    ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      TEnvWF Env →
      Env.context.types ≠ [] →
      FactoryWF C.functions →
      ∀ v, v ∈ LMonoTy.freeVars et.toLMonoTy →
        ∀ n, n ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n :=
  fun e et C Env Env' h h_envwf h_ne h_fwf =>
    ((resolveAux_preserves_combined e.sizeOf e rfl et C Env Env' h h_ne).2
      h_envwf.substFreshForGen h_envwf.ctxFreshForGen h_envwf.aliasesWF h_fwf h_envwf.boundVarsFresh).2

/-- An expression is well-scoped w.r.t. a context: all its free variable
    identifiers appear in the context's `knownVars`.
    This is the standard precondition for type-checking: every free variable
    reference must be bound in the context.
    Propagates through `varOpen`: if `WellScoped e Γ`, then
    `WellScoped (varOpen 0 (xv, some xty) e) (extend Γ xv)`. -/
def WellScoped (e : LExpr T.mono) (Γ : TContext T.IDMeta) : Prop :=
  ∀ x ∈ LExpr.freeVars e, x.1 ∈ TContext.knownVars Γ

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `varOpen k x e` only adds `x` to the free variables: every fvar of the
    opened expression is either an original fvar of `e` or the new `x`. -/
private theorem varOpen_freeVars_subset
    (k : Nat) (x : T.mono.base.Identifier × Option LMonoTy) (e : LExpr T.mono) :
    ∀ y, y ∈ LExpr.freeVars (LExpr.varOpen k x e) → y = x ∨ y ∈ LExpr.freeVars e := by
  induction e generalizing k with
  | const _ _ | op _ _ _ => simp [LExpr.varOpen, LExpr.substK, LExpr.freeVars]
  | bvar _ i =>
    intro y hy
    simp [LExpr.varOpen, LExpr.substK] at hy
    split at hy
    · simp [LExpr.freeVars] at hy; left; exact hy
    · simp [LExpr.freeVars] at hy
  | fvar _ v ty =>
    intro y hy
    simp [LExpr.varOpen, LExpr.substK, LExpr.freeVars] at hy
    right; simp [LExpr.freeVars]; exact hy
  | abs _ _ _ e ih =>
    intro y hy
    simp [LExpr.varOpen, LExpr.substK, LExpr.freeVars] at hy ⊢
    exact ih (k + 1) y hy
  | quant _ _ _ _ tr body ih_tr ih_body =>
    intro y hy
    simp [LExpr.varOpen, LExpr.substK, LExpr.freeVars, List.mem_append] at hy ⊢
    rcases hy with h_tr | h_body
    · rcases ih_tr (k + 1) y h_tr with rfl | h <;> grind
    · rcases ih_body (k + 1) y h_body with rfl | h <;> grind
  | app _ e1 e2 ih1 ih2 =>
    intro y hy
    simp only [LExpr.varOpen, LExpr.substK, LExpr.freeVars, List.mem_append] at hy
    rcases hy with h1 | h2
    · exact (ih1 k y h1).imp_right (List.mem_append_left _)
    · exact (ih2 k y h2).imp_right (List.mem_append_right _)
  | ite m_ite c t e ih_c ih_t ih_e =>
    intro y hy
    simp only [LExpr.varOpen, LExpr.substK, LExpr.freeVars] at hy
    rw [show LExpr.freeVars (.ite m_ite c t e) =
      LExpr.freeVars c ++ LExpr.freeVars t ++ LExpr.freeVars e from rfl]
    simp only [List.mem_append] at hy ⊢
    rcases hy with (h_c | h_t) | h_e
    · exact (ih_c k y h_c).imp_right (fun h => Or.inl (Or.inl h))
    · exact (ih_t k y h_t).imp_right (fun h => Or.inl (Or.inr h))
    · exact (ih_e k y h_e).imp_right (fun h => Or.inr h)
  | eq _ e1 e2 ih1 ih2 =>
    intro y hy
    simp only [LExpr.varOpen, LExpr.substK, LExpr.freeVars, List.mem_append] at hy
    rcases hy with h1 | h2
    · exact (ih1 k y h1).imp_right (List.mem_append_left _)
    · exact (ih2 k y h2).imp_right (List.mem_append_right _)

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `WellScoped` propagates through `varOpen` + context extension:
    if `e` is well-scoped in `Γ` and `xv ∈ knownVars Γ'` where `Γ ⊆ Γ'`,
    then `varOpen 0 (xv, some xty) e` is well-scoped in `Γ'`. -/
private theorem WellScoped_varOpen
    (e : LExpr T.mono) (Γ Γ' : TContext T.IDMeta)
    (xv : T.Identifier) (xty : LMonoTy)
    (h_ws : WellScoped e Γ)
    (h_sub : ∀ v, v ∈ TContext.knownVars Γ → v ∈ TContext.knownVars Γ')
    (h_xv : xv ∈ TContext.knownVars Γ') :
    WellScoped (LExpr.varOpen 0 (xv, some xty) e) Γ' := by
  intro y hy
  rcases varOpen_freeVars_subset 0 (xv, some xty) e y hy with rfl | h_orig
  · exact h_xv
  · exact h_sub y.1 (h_ws y h_orig)

/-- `typeBoundVar` extends `knownVars`: all original variables remain. -/
-- Helper: Map.keys distributes over append
private theorem Map.keys_append {α β : Type} (m1 m2 : Map α β) :
    Map.keys (m1 ++ m2) = Map.keys m1 ++ Map.keys m2 := by
  show Map.keys (List.append m1 m2) = Map.keys m1 ++ Map.keys m2
  induction m1 with
  | nil => rfl
  | cons hd tl ih => obtain ⟨a, _⟩ := hd; exact congrArg (a :: ·) ih

-- addInNewest on cons simplifies to appending to the first scope
private theorem Maps.addInNewest_cons (scope : Map α β) (rest : Maps α β) (m : Map α β) :
    Maps.addInNewest (scope :: rest) m = (scope ++ m) :: rest := by
  simp [Maps.addInNewest, Maps.newest, Maps.pop, Maps.push]

-- Helper: knownVars.go of addInNewest extends with new keys
omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
private theorem knownVars_go_addInNewest_mono
    (types : Maps T.Identifier LTy) (xv : T.Identifier) (ty : LTy)
    (v : T.Identifier) (hv : v ∈ TContext.knownVars.go types) :
    v ∈ TContext.knownVars.go (types.addInNewest [(xv, ty)]) := by
  cases types with
  | nil => simp [TContext.knownVars.go] at hv
  | cons scope rest =>
    rw [Maps.addInNewest_cons]
    simp only [TContext.knownVars.go] at hv ⊢
    rw [Map.keys_append]
    simp only [Map.keys, List.mem_append] at hv ⊢
    grind

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
private theorem knownVars_go_addInNewest_mem
    (types : Maps T.Identifier LTy) (xv : T.Identifier) (ty : LTy) :
    xv ∈ TContext.knownVars.go (types.addInNewest [(xv, ty)]) := by
  cases types with
  | nil =>
    show xv ∈ TContext.knownVars.go [[(xv, ty)]]
    simp [TContext.knownVars.go, Map.keys]
  | cons scope rest =>
    rw [Maps.addInNewest_cons]
    simp only [TContext.knownVars.go]
    rw [Map.keys_append]
    simp only [Map.keys, List.mem_append]
    grind

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
private theorem typeBoundVar_knownVars_mono
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env'))
    (v : T.Identifier) (hv : v ∈ TContext.knownVars Env.context) :
    v ∈ TContext.knownVars Env'.context := by
  -- Decompose typeBoundVar: liftGenEnv → instantiateWithCheck/genTyVar → addInNewestContext
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i v_gen h_gen; obtain ⟨xv_raw, Env_g⟩ := v_gen
  have h_g_ctx : Env_g.context = Env.context := liftGenEnv_context Env _ Env_g h_gen
  revert h; cases bty with
  | some bty_val =>
    simp only []; intro h
    generalize h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g = res_ic at h
    match res_ic with
    | .error _ => simp at h
    | .ok (_, Env_mid) =>
    simp at h
    obtain ⟨_, _, h_env'⟩ := h; subst h_env'
    have h_mid_ctx := (LMonoTy_instantiateWithCheck_context' bty_val C Env_g _ Env_mid h_ic).trans h_g_ctx
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context, TContext.knownVars] at hv ⊢
    rw [show Env_mid.genEnv.context.types = Env.genEnv.context.types from congrArg TContext.types h_mid_ctx]
    exact knownVars_go_addInNewest_mono _ _ _ v hv
  | none =>
    simp; intro h; split at h; · simp at h
    rename_i v_tg h_tg; obtain ⟨xtyid, Env_mid⟩ := v_tg
    simp at h
    obtain ⟨_, _, h_env'⟩ := h; subst h_env'
    have h_mid_ctx := (TEnv.genTyVar_context Env_g xtyid Env_mid h_tg).trans h_g_ctx
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context, TContext.knownVars] at hv ⊢
    rw [show Env_mid.genEnv.context.types = Env.genEnv.context.types from congrArg TContext.types h_mid_ctx]
    exact knownVars_go_addInNewest_mono _ _ _ v hv

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `typeBoundVar` makes `xv` a member of `knownVars`. -/
private theorem typeBoundVar_xv_in_knownVars
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env')) :
    xv ∈ TContext.knownVars Env'.context := by
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  split at h; · simp at h
  rename_i v_gen h_gen; obtain ⟨xv_raw, Env_g⟩ := v_gen
  revert h; cases bty with
  | some bty_val =>
    simp only []; intro h
    generalize h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g = res_ic at h
    match res_ic with
    | .error _ => simp at h
    | .ok (_, Env_mid) =>
    simp at h
    obtain ⟨h_xv, _, h_env'⟩ := h; subst h_xv; subst h_env'
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context, TContext.knownVars]
    exact knownVars_go_addInNewest_mem _ _ _
  | none =>
    simp; intro h; split at h; · simp at h
    rename_i v_tg h_tg; obtain ⟨xtyid, Env_mid⟩ := v_tg
    simp at h
    obtain ⟨h_xv, _, h_env'⟩ := h; subst h_xv; subst h_env'
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context, TContext.knownVars]
    exact knownVars_go_addInNewest_mem _ _ _


omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- WellScoped for varOpen after typeBoundVar: combines `WellScoped_varOpen`
    with `typeBoundVar_knownVars_mono` and `typeBoundVar_xv_in_knownVars`. -/
private theorem WellScoped_varOpen_typeBoundVar
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
    (body : LExpr T.mono)
    (h_tbv : typeBoundVar C Env bty = .ok (xv, xty, Env1))
    (h_ws_body : WellScoped body Env.context) :
    WellScoped (LExpr.varOpen 0 (xv, some xty) body) Env1.context := by
  exact WellScoped_varOpen body Env.context Env1.context xv xty h_ws_body
    (typeBoundVar_knownVars_mono C Env bty xv xty Env1 h_tbv)
    (typeBoundVar_xv_in_knownVars C Env bty xv xty Env1 h_tbv)

theorem resolveAux_HasType :
    ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      TEnvWF Env →
      Env.context.types ≠ [] →
      FactoryWF C.functions →
      WellScoped e Env.context →
      Env'.context = Env.context ∧
      ∀ (S : Subst), Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        Subst.polyKeysFresh (T := T) S Env.context →
        HasType C (TContext.subst Env.context S) e
          (.forAll [] (LMonoTy.subst S et.toLMonoTy)) := by
  -- We use strong induction on LExpr.sizeOf to handle the abs/quant cases,
  -- where resolveAux recurses on (varOpen 0 x e_body) rather than e_body.
  suffices h_strong : ∀ (n : Nat) (e : LExpr T.mono), LExpr.sizeOf e = n →
      ∀ (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      TEnvWF Env →
      Env.context.types ≠ [] →
      FactoryWF C.functions →
      WellScoped e Env.context →
      Env'.context = Env.context ∧
      ∀ (S : Subst), Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        Subst.polyKeysFresh (T := T) S Env.context →
        HasType C (TContext.subst Env.context S) e
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
      FactoryWF C.functions →
      WellScoped e' Env.context →
      Env'.context = Env.context ∧
      ∀ (S : Subst), Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        Subst.polyKeysFresh (T := T) S Env.context →
        HasType C (TContext.subst Env.context S) e'
          (.forAll [] (LMonoTy.subst S et.toLMonoTy)) :=
    fun e' h_lt => ih_n (LExpr.sizeOf e') h_lt e' rfl
  match e with
  | .const m c =>
    intro et C Env Env' h h_envwf _ _ _
    have h_aw := h_envwf.aliasesWF
    simp [resolveAux, inferConst] at h
    split at h
    · rename_i h_known
      simp [Bind.bind, Except.bind] at h
      obtain ⟨h_et, h_env⟩ := h
      constructor
      · rw [← h_env]
      · intro S h_abs_S h_wf_S _
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
    intro et C Env Env' h h_envwf _ _ _
    have h_aw := h_envwf.aliasesWF
    simp [resolveAux] at h
  | .fvar m x fty =>
    -- resolveAux calls inferFVar, which looks up x in context, instantiates
    -- bound type variables, and optionally unifies with the annotation.
    intro et C Env Env' h h_envwf _ _ _
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
      have ⟨h_ctx_pres, h_base_ty⟩ := inferFVar_HasType C Env x fty ty_res Env_res m
        h_infer h_envwf.boundVarsNodup h_envwf.boundVarsFresh h_envwf.aliasesWF
      constructor
      · exact h_ctx_pres
      · -- h_base_ty : ∀ S, absorbs S Env_res.subst → SubstWF S → polyKeysFresh S ctx →
        --   HasType C (TContext.subst Env.context S) (.fvar m x fty) (.forAll [] (subst S ty_res))
        -- Apply directly with the caller's S
        intro S h_abs_S h_wf_S h_poly_fresh
        exact h_base_ty S h_abs_S h_wf_S h_poly_fresh
  | .op m o oty =>
    intro et C Env Env' h h_envwf h_ne h_fwf h_ws
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
        intro S h_abs_S h_wf_S _
        rw [← h_et]; simp [toLMonoTy]
        -- Step 1: HasType.top gives the full polymorphic type
        have h_func_mem : func ∈ C.functions := Array.mem_of_find?_eq_some h_find
        have h_func_wf : LFuncWF func := h_fwf.lfuncs_wf func h_func_mem
        have h_top := HasType.top (TContext.subst Env.context S) m func o type_val h_find h_type
        -- Step 2: HasType_LTy_instantiate gives the mono type
        have h_ty_closed := LFunc.type_freeVars_eq_nil func type_val h_type h_func_wf
        have h_bv_eq := LFunc.type_boundVars_eq_typeArgs func type_val h_type
        have h_nodup : (LTy.boundVars type_val).Nodup := h_bv_eq ▸ h_func_wf.typeArgs_nodup
        have h_bv_fresh : ∀ v, v ∈ LTy.boundVars type_val →
            ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
          rw [h_bv_eq]; intro v hv _ _ h_eq
          exact h_func_wf.typeArgs_no_gen_prefix v hv
            (h_eq ▸ (by rw [String.toList_append]; exact isPrefixOf_append_self _ _))
        -- Decompose instantiateWithCheck to get the genEnv for instantiate
        simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h_inst
        split at h_inst; · simp at h_inst
        rename_i v_ra h_ra; obtain ⟨mty_ra, Env_ra⟩ := v_ra; dsimp at h_inst h_ra
        split at h_inst; · simp at h_inst
        split at h_inst
        · simp at h_inst; obtain ⟨h_mty, h_env⟩ := h_inst
          subst h_mty; subst h_env
          -- ty_inst = mty_ra from resolveAliases
          -- Decompose resolveAliases to get the instantiate step
          simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
          split at h_ra; · simp at h_ra
          rename_i v_inst h_lty_inst; obtain ⟨mty_inst, genEnv'⟩ := v_inst
          simp at h_ra h_lty_inst
          have h_ctx_inst := LTy.instantiate_context type_val Env.genEnv mty_inst genEnv' h_lty_inst
          have h_mono := HasType_LTy_instantiate C (TContext.subst Env.context S) (.op m o none) type_val mty_inst
            Env.genEnv genEnv' h_top h_lty_inst h_nodup h_bv_fresh
          -- h_mono : HasType C (TContext.subst Env.context S) (.op m o none) (.forAll [] mty_inst)
          -- Alias resolution: resolveAliases preserves HasType via talias
          have h_ra_ctx : ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context = Env.context := by
            simp [TEnv.context]; exact h_ctx_inst
          have h_aw_ra : TContext.AliasesWF ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context :=
            h_ra_ctx ▸ h_aw
          -- Aliases of substituted context = aliases of original context
          have h_aliases_subst : (TContext.subst Env.context S).aliases = Env.context.aliases :=
            _root_.Lambda.TContext.subst_aliases Env.context S
          have h_aliases_eq : (TContext.subst Env.context S).aliases =
            ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context.aliases := by
            rw [h_aliases_subst]; simp [TEnv.context]; rw [h_ctx_inst]
          have h_aw_subst : TContext.AliasesWF (TContext.subst Env.context S) := by
            rw [TContext.AliasesWF]; rw [h_aliases_subst]; exact h_aw
          -- HasType_resolveAliases gives HasType ... (.forAll [] mty_ra) via AliasEquiv
          have h_typed := HasType_resolveAliases C (TContext.subst Env.context S) (.op m o none) mty_inst mty_ra
            {Env with genEnv := genEnv'} Env_ra h_mono h_ra h_aliases_eq
            h_aw_subst
          -- h_typed : HasType C (TContext.subst Env.context S) (.op ...) (.forAll [] mty_ra)
          -- Goal: HasType C (TContext.subst Env.context S) (.op ...) (.forAll [] (LMonoTy.subst S mty_ra))
          -- Use HasType_subst_fresh_all: keys of S in freeVars mty_ra are fresh in TContext.subst Γ S
          -- (because SubstWF S means S is idempotent, so keys don't appear in substituted types)
          exact HasType_subst_fresh_all C (TContext.subst Env.context S) (.op m o none) mty_ra S h_typed
            (fun a h_key _ => TContext.isFresh_subst_of_key Env.context S a h_key h_wf_S)
            h_wf_S
        · simp at h_inst
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
        intro S h_abs_S h_wf_S _
        rw [← h_et]; simp [toLMonoTy]
        simp [TEnv.updateSubst] at h_abs_S
        -- Extract unify hypothesis from mapError wrapper
        have h_unify := unify_of_mapError h_mapError
        -- Closed type facts
        have h_func_mem : func ∈ C.functions := Array.mem_of_find?_eq_some h_find
        have h_func_wf : LFuncWF func := h_fwf.lfuncs_wf func h_func_mem
        have h_ty_closed := LFunc.type_freeVars_eq_nil func type_val h_type h_func_wf
        have h_bv_eq := LFunc.type_boundVars_eq_typeArgs func type_val h_type
        -- Decompose instantiateWithCheck for type_val
        -- After subst: ty_inst → mty_ra, Env1 → Env_ra
        simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h_inst
        split at h_inst; · simp at h_inst
        rename_i v_ra h_ra; obtain ⟨mty_ra, Env_ra⟩ := v_ra; dsimp at h_inst h_ra
        split at h_inst; · simp at h_inst
        split at h_inst
        · simp at h_inst
          obtain ⟨h_mty_eq, h_env_eq⟩ := h_inst; subst h_mty_eq; subst h_env_eq
          -- After subst: goal uses mty_ra, h_inst2 uses Env_ra, h_unify uses mty_ra
          -- Decompose resolveAliases into instantiate + LMonoTy.resolveAliases
          simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
          split at h_ra; · simp at h_ra
          rename_i v_inst h_lty_inst; obtain ⟨mty_inst, genEnv'⟩ := v_inst
          simp at h_ra h_lty_inst
          -- Context chain
          have h_ctx_inst := LTy.instantiate_context type_val Env.genEnv mty_inst genEnv' h_lty_inst
          have h_ra_ctx : ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context = Env.context := by
            simp [TEnv.context]; exact h_ctx_inst
          have h_aliases_eq : Env.context.aliases =
              ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context.aliases := by
            simp [TEnv.context]; rw [h_ctx_inst]
          have h_aw_ra : TContext.AliasesWF ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context :=
            h_ra_ctx ▸ h_aw
          -- AliasEquiv from resolveAliases: mty_inst ~ mty_ra
          have h_ae := resolveAliases_aliasEquiv mty_inst {Env with genEnv := genEnv'}
            mty_ra Env_ra h_ra h_aliases_eq h_aw
          -- Under S: subst S mty_inst ~ subst S mty_ra
          have h_ae_S := AliasEquiv_subst Env.context.aliases mty_inst mty_ra S h_ae
            (fun a ha => h_aw a ha)
          -- Env_ra context = Env context (via resolveAliases context preservation)
          have h_env_ra_ctx : Env_ra.context = Env.context := by
            rw [LMonoTy.resolveAliases_context _ _ _ _ h_ra]; exact h_ra_ctx
          -- AnnotCompat: decompose h_inst2 to get substitution structure
          have h_aw1 : TContext.AliasesWF Env_ra.context := h_env_ra_ctx ▸ h_aw
          have ⟨mty_fty_ie, Env_fty_ie, Env_fty_ra, h_fty_ie, h_fty_ra⟩ :=
            LMonoTy.instantiateWithCheck_decompose oty_val C Env_ra oty_inst Env2 h_inst2
          have ⟨freshtvs_fty, _, h_gen_fty, h_fty_result, _⟩ :=
            instantiateEnv_decompose _ _ _ _ _ h_fty_ie
          have h_fty_eq : mty_fty_ie = LMonoTy.subst
              [List.zip (LMonoTy.freeVars oty_val)
                (List.map LMonoTy.ftvar freshtvs_fty)] oty_val := by
            have h := h_fty_result; simp only [LMonoTys.subst] at h
            split at h
            · rename_i hS; simp at h; rw [h]; exact (LMonoTy.subst_emptyS hS).symm
            · simp [LMonoTys.subst.substAux] at h; exact h
          -- AliasEquiv from resolveAliases on annotation: subst [σ] oty_val ~ oty_inst
          have h_fty_ie_ctx := LMonoTys.instantiateEnv_context _ _ Env_ra _ _ h_fty_ie
          have h_ae_fty : AliasEquiv Env.context.aliases
              (LMonoTy.subst [List.zip (LMonoTy.freeVars oty_val)
                (List.map LMonoTy.ftvar freshtvs_fty)] oty_val) oty_inst := by
            have h_ctx_chain : Env_fty_ie.context.aliases = Env.context.aliases := by
              rw [h_fty_ie_ctx, h_env_ra_ctx]
            rw [← h_fty_eq]
            exact h_ctx_chain ▸ resolveAliases_aliasEquiv mty_fty_ie Env_fty_ie oty_inst Env_fty_ra
              h_fty_ra rfl (by rw [h_fty_ie_ctx, h_env_ra_ctx]; exact h_aw)
          -- Apply S to annotation AliasEquiv
          have h_ae_fty_S := AliasEquiv_subst Env.context.aliases _ _ S h_ae_fty
            (fun a ha => h_aw a ha)
          -- Unification + absorption: subst S oty_inst = subst S mty_ra
          have h_eq_abs : LMonoTy.subst S oty_inst = LMonoTy.subst S mty_ra := by
            have h_eq := unify_makes_equal mty_ra oty_inst Env2.stateSubstInfo v3 h_unify
            have := congrArg (LMonoTy.subst S) h_eq
            rw [LMonoTy.subst_absorbs S v3.subst mty_ra h_abs_S,
                LMonoTy.subst_absorbs S v3.subst oty_inst h_abs_S] at this
            exact this.symm
          rw [h_eq_abs] at h_ae_fty_S
          -- Compose substitution: subst S (subst [σ_fty] oty_val) → subst [σ'] oty_val
          have h_fty_len : (LMonoTy.freeVars oty_val).length = freshtvs_fty.length :=
            (TGenEnv.genTyVars_length _ _ _ _ h_gen_fty).symm
          rw [subst_compose_ftvar_closed' S _ freshtvs_fty h_fty_len oty_val
              (fun v hv => hv)] at h_ae_fty_S
          -- Bridge to subst S mty_inst via symm of h_ae_S
          have h_ae_fty_mty : AliasEquiv Env.context.aliases
              (LMonoTy.subst [List.zip (LMonoTy.freeVars oty_val)
                (List.map (fun v => LMonoTy.subst S (.ftvar v)) freshtvs_fty)] oty_val)
              (LMonoTy.subst S mty_inst) :=
            .trans h_ae_fty_S (AliasEquiv.symm h_ae_S)
          have h_annot : AnnotCompat Env.context.aliases oty_val (LMonoTy.subst S mty_inst) :=
            ⟨_, h_ae_fty_mty⟩
          -- Case split on type_val's bound vars for openFull construction
          cases type_val with
          | forAll vars body =>
          simp [LTy.freeVars] at h_ty_closed
          cases vars with
          | nil =>
            -- Monomorphic case: mty_inst = body
            simp [LTy.instantiate] at h_lty_inst
            obtain ⟨h_eq_inst, _⟩ := h_lty_inst; subst h_eq_inst
            -- body has no freeVars (closed type)
            have h_body_fv_nil : LMonoTy.freeVars body = [] := by
              simp only [List.removeAll, List.filter_eq_nil_iff] at h_ty_closed
              match h_fv : LMonoTy.freeVars body with
              | [] => rfl
              | a :: _ => exfalso; have := h_ty_closed a (by simp [h_fv])
                          simp at this
            -- subst S body = body (no free vars to substitute)
            have h_subst_body : LMonoTy.subst S body = body :=
              LMonoTy.subst_no_relevant_keys S body
                (fun x hx => by simp [h_body_fv_nil] at hx)
            rw [h_subst_body] at h_annot h_ae_S
            have h_open : LTy.openFull (.forAll [] body) [] = body := by
              simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe, List.zip_nil_left]
              exact LMonoTy.subst_emptyS (by simp [Subst.hasEmptyScopes, Map.isEmpty])
            have h_aliases_subst : (TContext.subst Env.context S).aliases = Env.context.aliases :=
              _root_.Lambda.TContext.subst_aliases Env.context S
            rw [← h_aliases_subst] at h_annot h_ae_S
            exact HasType.talias (TContext.subst Env.context S) _ _ _ h_ae_S
              (HasType.top_annotated (TContext.subst Env.context S) m func o (.forAll [] body) body [] oty_val
                h_find h_type (by simp [LTy.boundVars]) h_open h_annot)
          | cons x' xs' =>
            -- Polymorphic case
            simp only [LTy.instantiate, Bind.bind, Except.bind] at h_lty_inst
            split at h_lty_inst; · simp at h_lty_inst
            rename_i v_gen h_gen'; obtain ⟨ftvs, gE⟩ := v_gen
            simp at h_lty_inst h_gen'
            obtain ⟨h_eq_inst, _⟩ := h_lty_inst; subst h_eq_inst
            -- Closed condition: all freeVars of body are in bound vars
            have h_body_cl : ∀ tv, tv ∈ LMonoTy.freeVars body → tv ∈ (x' :: xs') := by
              intro tv htv
              simp only [List.removeAll, List.filter_eq_nil_iff] at h_ty_closed
              have := h_ty_closed tv htv
              simp only [List.elem_eq_mem, Bool.not_eq_true', decide_eq_false_iff_not,
                         Decidable.not_not] at this
              exact this
            have h_len := TGenEnv.genTyVars_length _ _ _ _ h_gen'
            -- tys = map (fun tv => subst S (ftvar tv)) ftvs
            let tys := List.map (fun tv => LMonoTy.subst S (.ftvar tv)) ftvs
            have h_tys_len : tys.length = (x' :: xs').length := by simp [tys, h_len]
            -- Composition: subst S (subst [zip vars (map ftvar ftvs)] body) = subst [zip vars tys] body
            rw [subst_compose_ftvar_closed' S (x' :: xs') ftvs h_len.symm body h_body_cl] at h_annot h_ae_S
            have h_open : LTy.openFull (.forAll (x' :: xs') body) tys =
                LMonoTy.subst [List.zip (x' :: xs')
                  (List.map (fun v => LMonoTy.subst S (.ftvar v)) ftvs)] body := by
              simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe, tys]
            rw [← h_open] at h_annot h_ae_S
            have h_aliases_subst : (TContext.subst Env.context S).aliases = Env.context.aliases :=
              _root_.Lambda.TContext.subst_aliases Env.context S
            rw [← h_aliases_subst] at h_annot h_ae_S
            exact HasType.talias (TContext.subst Env.context S) _ _ _ h_ae_S
              (HasType.top_annotated (TContext.subst Env.context S) m func o (.forAll (x' :: xs') body)
                (LTy.openFull (.forAll (x' :: xs') body) tys) tys oty_val
                h_find h_type (by simp [LTy.boundVars]; exact h_tys_len) rfl h_annot)
        · simp at h_inst
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
    intro et C Env Env' h h_envwf h_ne h_fwf h_ws
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
            have h_unify := unify_of_mapError h_mapError
            -- genTyVar preserves subst and context
            have h_gen_subst := TEnv.genTyVar_subst Env2 fresh_name Env3 h_genTyVar
            have h_gen_ctx := TEnv.genTyVar_context Env2 fresh_name Env3 h_genTyVar
            have h_gen_fresh := TEnv.genTyVar_isFresh Env2 fresh_name Env3 h_genTyVar
            -- IHs from recursive calls (using strong induction)
            have ih1 := ih_sub e1 (by expr_size h_sz)
            have ih2 := ih_sub e2 (by expr_size h_sz)
            have ⟨h_ctx1, h_ty1⟩ := ih1 e1t C Env Env1 h_res1 h_envwf h_ne h_fwf (fun x hx => h_ws x (by simp [LExpr.freeVars, List.mem_append]; left; exact hx))
            have h_ne1 := h_ctx1 ▸ h_ne
            -- Build TEnvWF for Env1 (context preserved, subst/gen extended)
            have h_envwf1 := TEnvWF.of_resolveAux e1 e1t C Env Env1 h_res1 h_envwf h_ne h_fwf h_ctx1
            have h_ws2 : WellScoped e2 Env1.context := by
              rw [h_ctx1]; intro x hx; exact h_ws x (by simp [LExpr.freeVars, List.mem_append]; right; exact hx)
            have ⟨h_ctx2, h_ty2⟩ := ih2 e2t C Env1 Env2 h_res2 h_envwf1 h_ne1 h_fwf h_ws2
            -- Absorption chain: v4 absorbs Env3.subst = Env2.subst
            have h_abs_v4_Env3 := unify_absorbs
              [(e1t.toLMonoTy, LMonoTy.tcons "arrow" [e2t.toLMonoTy, .ftvar fresh_name])]
              Env3.stateSubstInfo v4 h_unify
            rw [h_gen_subst] at h_abs_v4_Env3
            -- Now h_abs_v4_Env3 : absorbs v4.subst Env2.subst
            have h_abs_Env2_Env1 := resolveAux_absorbs e2 e2t C Env1 Env2 h_res2 h_envwf1.toEnvFreshForGen h_ne1 h_envwf1.aliasesWF h_fwf h_envwf1.boundVarsFresh
            have h_abs_Env1_Env := resolveAux_absorbs e1 e1t C Env Env1 h_res1 h_envwf.toEnvFreshForGen h_ne h_aw h_fwf h_envwf.boundVarsFresh
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
              intro S h_abs_S h_wf_S h_poly_fresh
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
                  h_envwf1.substFreshForGen h_envwf1.ctxFreshForGen h_ne1 h_envwf1.aliasesWF h_fwf h_envwf1.boundVarsFresh)
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
              have h_ty1_S := h_ty1 S h_abs_S_Env1 h_wf_S h_poly_fresh
              rw [h_ctx1] at h_ty2
              have h_ty2_S := h_ty2 S h_abs_S_Env2 h_wf_S h_poly_fresh
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
                have h_ne_fresh := resolveAux_output_type_no_future_vars e1 e1t C Env Env1 h_res1 h_envwf h_ne h_fwf
                    fresh_name h_mem Env2.genEnv.genState.tyGen h_mono_e2
                exact h_ne_fresh h_gen_name
              have h_e2t_no_fresh : fresh_name ∉ LMonoTy.freeVars e2t.toLMonoTy := by
                intro h_mem
                have h_ne_fresh := resolveAux_output_type_no_future_vars e2 e2t C Env1 Env2 h_res2 h_envwf1 h_ne1 h_fwf
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
              exact HasType.tapp (TContext.subst Env.context S) m e1 e2
                (.forAll [] (LMonoTy.subst S (LMonoTy.subst v4.subst (.ftvar fresh_name))))
                (.forAll [] (LMonoTy.subst S e2t.toLMonoTy))
                (by simp [LTy.isMonoType, LTy.boundVars])
                (by simp [LTy.isMonoType, LTy.boundVars])
                (by simp [LTy.toMonoType]; exact h_ty1_S)
                h_ty2_S
  | .abs m pn bty e_body =>
    intro et C Env Env' h h_envwf h_ne h_fwf h_ws
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
        -- sizeOf (varOpen 0 (xv, some xty) e_body) = sizeOf e_body < 2 + sizeOf e_body = sizeOf (.abs m _ bty e_body) = n
        have ih_body := ih_sub (varOpen 0 (xv, some xty) e_body)
          (by expr_size h_sz)
        -- Build TEnvWF for Env1 (typeBoundVar extends context)
        have h_envwf1 : TEnvWF Env1 :=
          { aliasesWF := typeBoundVar_preserves_AliasesWF C Env bty xv xty Env1 h_tbv h_envwf.aliasesWF
            substFreshForGen := typeBoundVar_preserves_SubstFreshForGen C Env bty xv xty Env1 h_tbv h_envwf.substFreshForGen h_envwf.aliasesWF
            ctxFreshForGen := typeBoundVar_preserves_ContextFreshForGen C Env bty xv xty Env1 h_tbv h_envwf.ctxFreshForGen
            boundVarsNodup := typeBoundVar_preserves_boundVarsNodup C Env bty xv xty Env1 h_tbv h_envwf.boundVarsNodup
            boundVarsFresh := typeBoundVar_preserves_boundVarsFresh C Env bty xv xty Env1 h_tbv h_envwf.boundVarsFresh }
        have h_ne1 : Env1.context.types ≠ [] :=
          typeBoundVar_context_types_ne_nil C Env bty xv xty Env1 h_tbv
        -- WellScoped for the opened body
        have h_ws_body : WellScoped e_body Env.context :=
          fun x hx => h_ws x (by simp [LExpr.freeVars]; exact hx)
        have h_ws_open := WellScoped_varOpen_typeBoundVar C Env bty xv xty Env1
          e_body h_tbv h_ws_body
        have ⟨h_ctx_body, h_ty_body⟩ := ih_body et_body C Env1 Env2 h_res_body h_envwf1 h_ne1 h_fwf h_ws_open
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
          intro S h_abs_S h_wf_S h_poly_fresh
          -- Step 1: Simplify et.toLMonoTy
          -- h_et : et = .abs ⟨m, subst Env2.subst (tcons "arrow" [xty, (varCloseT ..).toLMonoTy])⟩ bty (varCloseT ..)
          -- We need: HasType ... (.forAll [] (subst S et.toLMonoTy))
          -- et.toLMonoTy = subst Env2.subst (tcons "arrow" [xty, (varCloseT ..).toLMonoTy])
          -- (varCloseT ..).toLMonoTy = et_body.toLMonoTy
          have h_et_ty : et.toLMonoTy = LMonoTy.subst Env2.stateSubstInfo.subst
              (.tcons "arrow" [xty, et_body.toLMonoTy]) := by
            subst h_et
            -- Unfold outer toLMonoTy (.abs ⟨_, mty⟩ _ _) = mty, keeping inner intact
            change (LMonoTy.subst Env2.stateSubstInfo.subst
              (.tcons "arrow" [xty, (LExpr.varCloseT 0 xv et_body).toLMonoTy]))
              = LMonoTy.subst Env2.stateSubstInfo.subst (.tcons "arrow" [xty, et_body.toLMonoTy])
            rw [varCloseT_toLMonoTy]
          rw [h_et_ty]
          -- Step 2: Absorption: S absorbs Env2.subst
          have h_abs_Env2 : Subst.absorbs S Env2.stateSubstInfo.subst := by
            rw [← h_env'] at h_abs_S
            simp [TEnv.eraseFromContext, TEnv.updateContext] at h_abs_S
            exact h_abs_S
          -- Build context bridge (needed for polyKeysFresh extension and later)
          have h_xv_fresh_maps : Maps.find? Env.context.types xv = none := by
            have h_per_scope := typeBoundVar_xv_fresh_in_context C Env bty xv xty Env1 h_tbv
            suffices ∀ (types : Maps T.Identifier LTy),
                (∀ m, m ∈ types → Map.find? m xv = none) →
                Maps.find? types xv = none by
              exact this _ h_per_scope
            intro types h_all; induction types with
            | nil => simp [Maps.find?]
            | cons scope rest ih =>
              simp [Maps.find?]
              rw [h_all scope (List.mem_cons_self ..)]
              exact ih (fun m hm => h_all m (List.mem_cons_of_mem _ hm))
          have ⟨Env_mid, h_mid_ctx, h_env1_eq⟩ :
              ∃ Env_mid : TEnv T.IDMeta, Env_mid.context = Env.context ∧
                Env1 = TEnv.addInNewestContext Env_mid [(xv, .forAll [] xty)] := by
            simp only [typeBoundVar, Bind.bind, Except.bind] at h_tbv
            split at h_tbv; · simp at h_tbv
            rename_i v_gen h_gen; obtain ⟨xv_raw, Env_g⟩ := v_gen; simp at h_tbv
            have h_g_ctx := liftGenEnv_context Env _ Env_g h_gen
            revert h_tbv; cases bty with
            | some bty_val =>
              simp only []; intro h_tbv
              generalize h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g = res_ic at h_tbv
              match res_ic with
              | .error _ => simp at h_tbv
              | .ok (_, Env_ic) =>
                simp at h_tbv
                obtain ⟨h_xv_eq, h_xty_eq, h_env1⟩ := h_tbv
                subst h_xv_eq; subst h_xty_eq
                exact ⟨Env_ic,
                  (LMonoTy_instantiateWithCheck_context' bty_val C Env_g _ Env_ic h_ic).trans h_g_ctx,
                  h_env1.symm⟩
            | none =>
              simp; intro h_tbv; split at h_tbv; · simp at h_tbv
              rename_i v_tg h_tg; obtain ⟨xtyid, Env_tg⟩ := v_tg
              simp at h_tbv
              obtain ⟨h_xv_eq, h_xty_eq, h_env1⟩ := h_tbv
              subst h_xv_eq; subst h_xty_eq
              exact ⟨Env_tg,
                (TEnv.genTyVar_context Env_g xtyid Env_tg h_tg).trans h_g_ctx,
                h_env1.symm⟩
          have h_ctx_bridge : Env1.context =
              { Env.context with types := Env.context.types.insert xv (.forAll [] xty) } := by
            subst h_env1_eq
            simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_mid_ctx ⊢
            rw [congrArg TContext.types h_mid_ctx, congrArg TContext.aliases h_mid_ctx]
            congr 1
            exact (Maps.insert_eq_addInNewest_fresh _ _ _ h_xv_fresh_maps).symm
          -- Step 3: Use IH to get body typing under S
          -- Derive polyKeysFresh S Env1.context from polyKeysFresh S Env.context:
          -- Env1.context adds (xv, forAll [] xty) which has boundVars = [], so the
          -- polyKeysFresh condition is vacuously satisfied for the new entry.
          have h_poly_fresh_ext : Subst.polyKeysFresh (T := T) S Env1.context := by
            rw [h_ctx_bridge]
            exact polyKeysFresh_insert_mono S Env.context xv xty h_poly_fresh h_xv_fresh_maps
          have h_body_S := h_ty_body S h_abs_Env2 h_wf_S h_poly_fresh_ext
          -- After rw [← h_et]; simp [toLMonoTy], goal is:
          -- HasType ... (.forAll [] (subst S (subst Env2.subst (tcons "arrow" [xty, et_body.toLMonoTy]))))
          -- By absorption: subst S (subst Env2.subst x) = subst S x
          rw [LMonoTy.subst_absorbs S Env2.stateSubstInfo.subst
            (.tcons "arrow" [xty, et_body.toLMonoTy]) h_abs_Env2]
          -- Goal: HasType ... (.forAll [] (subst S (tcons "arrow" [xty, et_body.toLMonoTy])))
          -- Distribute subst over tcons:
          rw [LMonoTy.subst_tcons_pair S "arrow" xty et_body.toLMonoTy]
          -- Goal: HasType ... (.forAll [] (tcons "arrow" [subst S xty, subst S et_body.toLMonoTy]))
          -- Step 4: Apply tabs to get arrow [xty, subst S ety], then HasType_subst_fresh_all for S
          -- tabs gives: arrow [xty, subst S et_body.toLMonoTy]
          -- Then HasType_subst_fresh_all gives: subst S (arrow [xty, subst S ety])
          --   = arrow [subst S xty, subst S (subst S ety)]
          --   = arrow [subst S xty, subst S ety]  (by idempotence: SubstWF → absorbs S S)
          -- Apply tabs with substituted context directly
          -- Build the substituted context bridge
          have h_ctx_subst_bridge : Env1.context.subst S =
              { Env.context.subst S with types :=
                (Env.context.subst S).types.insert xv (.forAll [] (LMonoTy.subst S xty)) } := by
            rw [h_ctx_bridge]
            exact _root_.Lambda.TContext_subst_insert_fresh Env.context S xv (.forAll [] xty) h_xv_fresh_maps
          -- Option A: Use tabs with x_ty = .forAll [] (subst S xty)
          -- This makes body typing match directly, at the cost of needing AnnotCompat_subst
          have h_tabs := HasType.tabs (TContext.subst Env.context S) m pn (xv, some xty)
            (.forAll [] (LMonoTy.subst S xty))
            e_body (.forAll [] (LMonoTy.subst S et_body.toLMonoTy)) bty
            (by -- LExpr.fresh (xv, some xty) e_body
                intro h_mem
                have h_in_ctx := h_ws (xv, some xty) (by simp [LExpr.freeVars]; exact h_mem)
                have h_per_scope := typeBoundVar_xv_fresh_in_context C Env bty xv xty Env1 h_tbv
                have h_not_known : xv ∉ TContext.knownVars Env.context := by
                  intro h_kv
                  simp [TContext.knownVars] at h_kv
                  have : ∀ (types : Maps T.Identifier LTy),
                      (∀ m, m ∈ types → Map.find? m xv = none) →
                      xv ∉ TContext.knownVars.go types := by
                    intro types h_all h_in
                    induction types with
                    | nil => simp [TContext.knownVars.go] at h_in
                    | cons scope rest ih =>
                      simp [TContext.knownVars.go, List.mem_append] at h_in
                      rcases h_in with h_key | h_rest
                      · exact Map.find?_of_not_mem_values scope
                          (h_all scope (List.mem_cons_self ..)) h_key
                      · exact ih (fun m hm => h_all m (List.mem_cons_of_mem _ hm)) h_rest
                  exact this _ h_per_scope h_kv
                exact h_not_known h_in_ctx)
            (by simp [LTy.isMonoType, LTy.boundVars])
            (by simp [LTy.isMonoType, LTy.boundVars])
            (by -- Body typing: h_body_S gives typing in Env1.context.subst S
                -- which equals {Env.context.subst S with insert xv (.forAll [] (subst S xty))}
                -- This matches exactly what tabs needs
                rw [h_ctx_subst_bridge] at h_body_S
                exact h_body_S)
            (by cases bty with
                | none => exact Or.inl rfl
                | some bty_val =>
                  right; exact ⟨bty_val, rfl,
                    (TContext.subst_aliases Env.context S) ▸
                    AnnotCompat_subst S
                      (typeBoundVar_AnnotCompat C Env bty_val xv xty Env1 h_tbv h_aw)
                      (fun a ha => h_aw a ha)⟩)
          simp [LTy.toMonoType] at h_tabs
          -- h_tabs : HasType C (Env.context.subst S) (.abs m _ bty e_body)
          --   (.forAll [] (.tcons "arrow" [subst S xty, subst S et_body.toLMonoTy]))
          exact h_tabs
  | .quant m qk pn bty tr e_body =>
    intro et C Env Env' h h_envwf h_ne h_fwf h_ws
    have h_aw := h_envwf.aliasesWF
    -- Decompose resolveAux for quant
    simp only [resolveAux, Bind.bind, Except.bind] at h
    -- typeBoundVar
    split at h; · simp at h
    rename_i v1 h_tbv; obtain ⟨xv, xty, Env1⟩ := v1; dsimp at h h_tbv
    -- resolveAux on opened body
    split at h; · simp at h
    rename_i v2 h_res_body; obtain ⟨et_body, Env2⟩ := v2; dsimp at h h_res_body
    -- resolveAux on opened triggers
    split at h; · simp at h
    rename_i v3 h_res_tr; obtain ⟨triggersT, Env3⟩ := v3; dsimp at h h_res_tr
    -- if check (ety != bool): split gives two branches
    split at h
    · -- ety ≠ bool → error path
      simp at h
    · -- ety = bool → success path
      simp at h; obtain ⟨h_et, h_env'⟩ := h
      -- Build TEnvWF for Env1
      have h_envwf1 : TEnvWF Env1 :=
        { aliasesWF := typeBoundVar_preserves_AliasesWF C Env bty xv xty Env1 h_tbv h_envwf.aliasesWF
          substFreshForGen := typeBoundVar_preserves_SubstFreshForGen C Env bty xv xty Env1 h_tbv h_envwf.substFreshForGen h_envwf.aliasesWF
          ctxFreshForGen := typeBoundVar_preserves_ContextFreshForGen C Env bty xv xty Env1 h_tbv h_envwf.ctxFreshForGen
          boundVarsNodup := typeBoundVar_preserves_boundVarsNodup C Env bty xv xty Env1 h_tbv h_envwf.boundVarsNodup
          boundVarsFresh := typeBoundVar_preserves_boundVarsFresh C Env bty xv xty Env1 h_tbv h_envwf.boundVarsFresh }
      have h_ne1 : Env1.context.types ≠ [] :=
        typeBoundVar_context_types_ne_nil C Env bty xv xty Env1 h_tbv
      -- IH for body
      have ih_body := ih_sub (varOpen 0 (xv, some xty) e_body)
        (by expr_size h_sz)
      have ⟨h_ctx2, _⟩ := ih_body et_body C Env1 Env2 h_res_body h_envwf1 h_ne1 h_fwf (WellScoped_varOpen_typeBoundVar C Env bty xv xty Env1 e_body h_tbv
              (fun x hx => h_ws x (by simp [LExpr.freeVars, List.mem_append]; right; exact hx)))
      -- IH for triggers (need TEnvWF Env2)
      have ih_tr := ih_sub (varOpen 0 (xv, some xty) tr)
        (by expr_size h_sz)
      have h_envwf2 := TEnvWF.of_resolveAux _ et_body C Env1 Env2 h_res_body h_envwf1 h_ne1 h_fwf h_ctx2
      have h_ne2 := h_ctx2 ▸ h_ne1
      have h_ws_tr : WellScoped (varOpen 0 (xv, some xty) tr) Env1.context :=
        WellScoped_varOpen_typeBoundVar C Env bty xv xty Env1 tr h_tbv
          (fun x hx => h_ws x (by simp [LExpr.freeVars, List.mem_append]; left; exact hx))
      have ⟨h_ctx3, _⟩ := ih_tr triggersT C Env2 Env3 h_res_tr h_envwf2 h_ne2 h_fwf
        (by rw [h_ctx2]; exact h_ws_tr)
      constructor
      · -- Context preservation: eraseFromContext Env3 xv → Env.context
        rw [← h_env']
        exact typeBoundVar_erase_context C Env bty xv xty Env1 h_tbv Env3
          (h_ctx3.trans h_ctx2)
          (typeBoundVar_xv_fresh_in_context C Env bty xv xty Env1 h_tbv) h_ne
      · -- Typing: quant result type is bool, subst S bool = bool
        intro S h_abs_S h_wf_S h_poly_fresh
        rw [← h_et]; simp [toLMonoTy, LMonoTy.subst_bool]
        -- Goal: HasType C (Env.context.subst S) (.quant m qk _ bty tr e_body) (.forAll [] .bool)
        -- Use tquant rule with x = (xv, some xty), x_ty = .forAll [] (subst S xty)
        -- The if-check gives et_body.toLMonoTy = .bool (ety = bool)
        rename_i h_ety_bool
        -- h_ety_bool : ¬(et_body.toLMonoTy != LMonoTy.bool) = true
        -- i.e., et_body.toLMonoTy = LMonoTy.bool
        have h_ety_eq_bool : et_body.toLMonoTy = LMonoTy.bool := by
          revert h_ety_bool; intro h; simp_all
        -- Get body and trigger typings from IH (under S via absorption)
        -- S absorbs Env'.subst = Env3.subst (eraseFromContext doesn't change subst)
        have h_abs_S_Env3 : Subst.absorbs S Env3.stateSubstInfo.subst := by
          rw [← h_env'] at h_abs_S
          simp [TEnv.eraseFromContext, TEnv.updateContext] at h_abs_S
          exact h_abs_S
        have h_abs_Env3_Env2 : Subst.absorbs Env3.stateSubstInfo.subst Env2.stateSubstInfo.subst :=
          resolveAux_absorbs _ triggersT C Env2 Env3 h_res_tr h_envwf2.toEnvFreshForGen h_ne2 h_envwf2.aliasesWF h_fwf h_envwf2.boundVarsFresh
        have h_abs_S_Env2 : Subst.absorbs S Env2.stateSubstInfo.subst :=
          Subst.absorbs_trans Env2.stateSubstInfo.subst Env3.stateSubstInfo.subst S
            h_abs_Env3_Env2 h_abs_S_Env3
        have h_poly_fresh_ext : Subst.polyKeysFresh (T := T) S Env1.context :=
          polyKeysFresh_typeBoundVar S C Env bty xv xty Env1 h_tbv h_poly_fresh
        have ⟨_, h_ty_body⟩ := ih_body et_body C Env1 Env2 h_res_body h_envwf1 h_ne1 h_fwf (WellScoped_varOpen_typeBoundVar C Env bty xv xty Env1 e_body h_tbv
              (fun x hx => h_ws x (by simp [LExpr.freeVars, List.mem_append]; right; exact hx)))
        have h_body_S := h_ty_body S h_abs_S_Env2 h_wf_S h_poly_fresh_ext
        rw [h_ety_eq_bool, LMonoTy.subst_bool] at h_body_S
        -- h_body_S : HasType C (Env1.context.subst S) (varOpen 0 (xv, some xty) e_body) (.forAll [] .bool)
        -- Trigger typing from IH
        have h_ws_tr' : WellScoped (varOpen 0 (xv, some xty) tr) Env1.context :=
          WellScoped_varOpen_typeBoundVar C Env bty xv xty Env1 tr h_tbv
            (fun x hx => h_ws x (by simp [LExpr.freeVars, List.mem_append]; left; exact hx))
        have ⟨_, h_ty_tr⟩ := ih_tr triggersT C Env2 Env3 h_res_tr h_envwf2 h_ne2 h_fwf
          (by rw [h_ctx2]; exact h_ws_tr')
        have h_tr_S := h_ty_tr S h_abs_S_Env3 h_wf_S (h_ctx2 ▸ h_poly_fresh_ext)
        rw [h_ctx2] at h_tr_S
        -- h_tr_S : HasType C (Env1.context.subst S) (varOpen 0 (xv, some xty) tr) (...)
        -- Freshness and bridge setup (same as abs case)
        have h_xv_fresh_maps : Maps.find? Env.context.types xv = none := by
          have h_per_scope := typeBoundVar_xv_fresh_in_context C Env bty xv xty Env1 h_tbv
          suffices ∀ (types : Maps T.Identifier LTy),
              (∀ m, m ∈ types → Map.find? m xv = none) →
              Maps.find? types xv = none by
            exact this _ h_per_scope
          intro types h_all
          induction types with
          | nil => simp [Maps.find?]
          | cons m rest ih =>
            unfold Maps.find?
            rw [h_all m (.head _)]
            exact ih (fun m' hm' => h_all m' (.tail _ hm'))
        -- Extract Env_mid from typeBoundVar decomposition
        have ⟨Env_mid, h_mid_ctx, h_env1_eq⟩ : ∃ Env_mid : TEnv T.IDMeta,
            Env_mid.context = Env.context ∧
            Env1 = Env_mid.addInNewestContext [(xv, .forAll [] xty)] := by
          simp only [typeBoundVar, Bind.bind, Except.bind] at h_tbv
          generalize h_lift : liftGenEnv HasGen.genVar Env = res_lift at h_tbv
          match res_lift with
          | .error _ => simp at h_tbv
          | .ok (xv_raw, Env_g) =>
            have h_g_ctx : Env_g.context = Env.context := liftGenEnv_context Env xv_raw Env_g h_lift
            revert h_tbv; cases bty with
            | some bty_val =>
              simp only []; intro h_tbv
              generalize h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g = res_ic at h_tbv
              match res_ic with
              | .error _ => simp at h_tbv
              | .ok (mty_ic, Env_mid) =>
                simp at h_tbv
                obtain ⟨h_xv_eq, h_xty_eq, h_env1⟩ := h_tbv
                subst h_xv_eq; subst h_xty_eq
                exact ⟨Env_mid,
                  (LMonoTy_instantiateWithCheck_context bty_val C Env_g mty_ic Env_mid h_ic).trans h_g_ctx,
                  h_env1.symm⟩
            | none =>
              simp; intro h_tbv
              generalize h_tg : TEnv.genTyVar Env_g = res_tg at h_tbv
              match res_tg with
              | .error _ => simp at h_tbv
              | .ok (xtyid, Env_mid) =>
                simp at h_tbv
                obtain ⟨h_xv_eq, h_xty_eq, h_env1⟩ := h_tbv
                subst h_xv_eq; subst h_xty_eq
                exact ⟨Env_mid,
                  (TEnv.genTyVar_context Env_g xtyid Env_mid h_tg).trans h_g_ctx,
                  h_env1.symm⟩
        have h_ctx_bridge : Env1.context =
            { Env.context with types := Env.context.types.insert xv (.forAll [] xty) } := by
          subst h_env1_eq
          simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_mid_ctx ⊢
          have h_types_eq : Env_mid.genEnv.context.types = Env.genEnv.context.types :=
            congrArg TContext.types h_mid_ctx
          have h_aliases_eq : Env_mid.genEnv.context.aliases = Env.genEnv.context.aliases :=
            congrArg TContext.aliases h_mid_ctx
          rw [h_types_eq, h_aliases_eq]
          congr 1
          exact (Maps.insert_eq_addInNewest_fresh _ _ _ h_xv_fresh_maps).symm
        -- Build the substituted context bridge (same as abs case)
        have h_ctx_subst_bridge : Env1.context.subst S =
            { Env.context.subst S with types :=
              (Env.context.subst S).types.insert xv (.forAll [] (LMonoTy.subst S xty)) } := by
          rw [h_ctx_bridge]
          exact _root_.Lambda.TContext_subst_insert_fresh Env.context S xv (.forAll [] xty) h_xv_fresh_maps
        -- Apply tquant with substituted context and substituted x_ty
        have h_tquant := HasType.tquant (TContext.subst Env.context S) m qk pn tr
          (.forAll [] (LMonoTy.subst S (triggersT.toLMonoTy)))
          (xv, some xty) (.forAll [] (LMonoTy.subst S xty)) e_body bty
          (by -- LExpr.fresh (xv, some xty) e_body
              intro h_mem
              have h_in_ctx := h_ws (xv, some xty) (by
                simp [LExpr.freeVars, List.mem_append]; right; exact h_mem)
              have h_per_scope := typeBoundVar_xv_fresh_in_context C Env bty xv xty Env1 h_tbv
              have h_not_known : xv ∉ TContext.knownVars Env.context := by
                intro h_kv
                have : ∀ (types : Maps T.Identifier LTy),
                    (∀ m, m ∈ types → Map.find? m xv = none) →
                    xv ∉ TContext.knownVars.go types := by
                  intro types h_all h_in
                  induction types with
                  | nil => simp [TContext.knownVars.go] at h_in
                  | cons scope rest ih =>
                    simp [TContext.knownVars.go, List.mem_append] at h_in
                    rcases h_in with h_key | h_rest
                    · exact Map.find?_of_not_mem_values scope
                        (h_all scope (List.mem_cons_self ..)) h_key
                    · exact ih (fun m hm => h_all m (List.mem_cons_of_mem _ hm)) h_rest
                exact this _ h_per_scope h_kv
              exact h_not_known h_in_ctx)
          (by simp [LTy.isMonoType, LTy.boundVars])
          (by -- Body typing in substituted context
              rw [h_ctx_subst_bridge] at h_body_S
              exact h_body_S)
          (by -- Trigger typing in substituted context
              rw [h_ctx_subst_bridge] at h_tr_S
              exact h_tr_S)
          (by -- annotation
              cases bty with
              | none => exact Or.inl rfl
              | some bty_val =>
                right; exact ⟨bty_val, rfl,
                  (TContext.subst_aliases Env.context S) ▸
                  AnnotCompat_subst S
                    (typeBoundVar_AnnotCompat C Env bty_val xv xty Env1 h_tbv h_aw)
                    (fun a ha => h_aw a ha)⟩)
        simp at h_tquant
        exact h_tquant
  | .ite m c t e =>
    -- resolveAux recurses on c, t, e, then unifies [(cty, bool), (tty, ety)].
    -- Result type is tty (the then-branch type), and the HasType rule is `tif`.
    intro et C Env Env' h h_envwf h_ne h_fwf h_ws
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
            have h_unify := unify_of_mapError h_mapError
            -- IHs from recursive calls (using strong induction)
            have ih_c := ih_sub c (by expr_size h_sz)
            have ih_t := ih_sub t (by expr_size h_sz)
            have ih_e := ih_sub e (by expr_size h_sz)
            have ⟨h_ctx1, h_ty_c⟩ := ih_c ct C Env Env1 h_res_c h_envwf h_ne h_fwf (by intro x hx; apply h_ws; simp only [WellScoped, LExpr.freeVars] at h_ws ⊢; exact List.mem_append_left _ (List.mem_append_left _ hx))
            have h_ne1 := h_ctx1 ▸ h_ne
            -- (h_sf1 removed: keysFresh no longer in TEnvWF)
            -- Build TEnvWF for Env1
            have h_envwf1 := TEnvWF.of_resolveAux c ct C Env Env1 h_res_c h_envwf h_ne h_fwf h_ctx1
            have ⟨h_ctx2, h_ty_t⟩ := ih_t tht C Env1 Env2 h_res_t h_envwf1 h_ne1 h_fwf (by rw [h_ctx1]; intro x hx; apply h_ws; simp only [LExpr.freeVars]; exact List.mem_append_left _ (List.mem_append_right _ hx))
            have h_ne2 := h_ctx2 ▸ h_ne1
            -- Build TEnvWF for Env2
            have h_envwf2 := TEnvWF.of_resolveAux t tht C Env1 Env2 h_res_t h_envwf1 h_ne1 h_fwf h_ctx2
            have ⟨h_ctx3, h_ty_e⟩ := ih_e elt C Env2 Env3 h_res_e h_envwf2 h_ne2 h_fwf (by rw [h_ctx2, h_ctx1]; intro x hx; apply h_ws; simp only [LExpr.freeVars]; exact List.mem_append_right _ hx)
            -- Absorption chain: v4 absorbs Env3 absorbs Env2 absorbs Env1 absorbs Env
            have h_abs_v4_Env3 := unify_absorbs
              [(ct.toLMonoTy, LMonoTy.bool), (tht.toLMonoTy, elt.toLMonoTy)]
              Env3.stateSubstInfo v4 h_unify
            have h_ne3 := h_ctx3 ▸ h_ne2
            have h_abs_Env3_Env2 := resolveAux_absorbs e elt C Env2 Env3 h_res_e h_envwf2.toEnvFreshForGen h_ne2 h_envwf2.aliasesWF h_fwf h_envwf2.boundVarsFresh
            have h_abs_Env2_Env1 := resolveAux_absorbs t tht C Env1 Env2 h_res_t h_envwf1.toEnvFreshForGen h_ne1 h_envwf1.aliasesWF h_fwf h_envwf1.boundVarsFresh
            have h_abs_Env1_Env := resolveAux_absorbs c ct C Env Env1 h_res_c h_envwf.toEnvFreshForGen h_ne h_aw h_fwf h_envwf.boundVarsFresh
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
              intro S h_abs_S h_wf_S h_poly_fresh
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
              have h_ty_c_S := h_ty_c S h_abs_S_Env1 h_wf_S h_poly_fresh
              rw [h_ctx1] at h_ty_t
              have h_ty_t_S := h_ty_t S h_abs_S_Env2 h_wf_S h_poly_fresh
              rw [h_ctx2, h_ctx1] at h_ty_e
              have h_ty_e_S := h_ty_e S h_abs_S_Env3 h_wf_S h_poly_fresh
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
              exact HasType.tif (Env.context.subst S) m c t e
                (.forAll [] (LMonoTy.subst S tht.toLMonoTy))
                h_ty_c_S h_ty_t_S h_ty_e_S
  | .eq m e1 e2 =>
    -- resolveAux recurses on e1 and e2, then unifies their types.
    -- Result type is LMonoTy.bool (ground), so subst S bool = bool for any S.
    -- We upgrade both IHs to the final substitution via absorption.
    intro et C Env Env' h h_envwf h_ne h_fwf h_ws
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
          have h_unify := unify_of_mapError h_mapError
          -- IHs from recursive calls (using strong induction)
          have ih1 := ih_sub e1 (by expr_size h_sz)
          have ih2 := ih_sub e2 (by expr_size h_sz)
          have ⟨h_ctx1, h_ty1⟩ := ih1 e1t C Env Env1 h_res1 h_envwf h_ne h_fwf (fun x hx => h_ws x (by simp [LExpr.freeVars, List.mem_append]; left; exact hx))
          have h_ne1 := h_ctx1 ▸ h_ne
          -- (h_sf1 removed: keysFresh no longer in TEnvWF)
          -- Build TEnvWF for Env1
          have h_envwf1 := TEnvWF.of_resolveAux e1 e1t C Env Env1 h_res1 h_envwf h_ne h_fwf h_ctx1
          have ⟨h_ctx2, h_ty2⟩ := ih2 e2t C Env1 Env2 h_res2 h_envwf1 h_ne1 h_fwf (by rw [h_ctx1]; intro x hx; exact h_ws x (by simp [LExpr.freeVars, List.mem_append]; right; exact hx))
          -- Absorption chain: v3 absorbs Env2 absorbs Env1 absorbs Env
          have h_abs_v3_Env2 := unify_absorbs [(e1t.toLMonoTy, e2t.toLMonoTy)]
            Env2.stateSubstInfo v3 h_unify
          have h_abs_Env2_Env1 := resolveAux_absorbs e2 e2t C Env1 Env2 h_res2 h_envwf1.toEnvFreshForGen h_ne1 h_envwf1.aliasesWF h_fwf h_envwf1.boundVarsFresh
          have h_abs_Env1_Env := resolveAux_absorbs e1 e1t C Env Env1 h_res1 h_envwf.toEnvFreshForGen h_ne h_aw h_fwf h_envwf.boundVarsFresh
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
            intro S h_abs_S h_wf_S h_poly_fresh
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
            have h_ty1_S := h_ty1 S h_abs_S_Env1 h_wf_S h_poly_fresh
            rw [h_ctx1] at h_ty2
            have h_ty2_S := h_ty2 S h_abs_S_Env2 h_wf_S h_poly_fresh
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
            exact HasType.teq (Env.context.subst S) m e1 e2
              (.forAll [] (LMonoTy.subst S e2t.toLMonoTy))
              h_ty1_S h_ty2_S

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `HasType` transfers from `{types := [[]], aliases}` to `{types := [], aliases}`.
    Both contexts have `find? = none` for all variables and `insert` gives the same
    results, so all HasType constructors behave identically. -/
private theorem HasType_transfer_empty_scope
    (C : LContext T) (aliases : List TypeAlias) (e : LExpr T.mono) (ty : LTy)
    (h : HasType C { types := [[]], aliases := aliases } e ty) :
    HasType C { types := [], aliases := aliases } e ty := by
  -- Both contexts have Maps.find? = none for all x and Maps.insert gives same results.
  -- Key lemma: Maps.insert [[]] x v = Maps.insert [] x v for all x, v
  have h_insert_eq : ∀ (x : T.Identifier) (v : LTy),
      Maps.insert ([[] ] : Maps T.Identifier LTy) x v =
      Maps.insert ([] : Maps T.Identifier LTy) x v := by
    intro x v
    simp [Maps.insert, Maps.find?, Map.find?, Maps.newest, Maps.pop, Maps.push, Map.insert]
  -- Generalize the context to allow induction
  generalize hΓ_eq : ({ types := [[]], aliases := aliases } : TContext T.IDMeta) = Γ' at h
  induction h with
  | tbool_const _ m b h_known =>
    exact HasType.tbool_const _ m b h_known
  | tint_const _ m n h_known =>
    exact HasType.tint_const _ m n h_known
  | treal_const _ m r h_known =>
    exact HasType.treal_const _ m r h_known
  | tstr_const _ m s h_known =>
    exact HasType.tstr_const _ m s h_known
  | tbitvec_const _ m n b h_known =>
    exact HasType.tbitvec_const _ m n b h_known
  | tvar _ m x ty h_find =>
    -- Maps.find? [[]] x = none, but h_find says it's some ty — contradiction
    subst hΓ_eq; simp [Maps.find?, Map.find?] at h_find
  | tvar_annotated _ m x ty_o ty_s tys ann h_find h_len h_open h_compat =>
    subst hΓ_eq; simp [Maps.find?, Map.find?] at h_find
  | tabs _ m _name x x_ty e e_ty o h_fresh hx he h_body h_annot ih =>
    subst hΓ_eq
    rw [h_insert_eq] at h_body
    exact HasType.tabs _ m _ x x_ty e e_ty o h_fresh hx he h_body h_annot
  | tapp _ m e1 e2 t1 t2 h1 h2 h_e1 h_e2 ih1 ih2 =>
    exact HasType.tapp _ m e1 e2 t1 t2 h1 h2 (ih1 hΓ_eq) (ih2 hΓ_eq)
  | tinst _ e ty e_ty x x_ty h_e h_eq ih =>
    exact HasType.tinst _ e ty e_ty x x_ty (ih hΓ_eq) h_eq
  | tgen _ e a ty h_e h_fresh ih =>
    subst hΓ_eq
    apply HasType.tgen _ e a ty (ih rfl)
    intro x ty h_find_x
    simp [Maps.find?] at h_find_x
  | tif _ m c e1 e2 ty h_c h_e1 h_e2 ih_c ih_e1 ih_e2 =>
    exact HasType.tif _ m c e1 e2 ty (ih_c hΓ_eq) (ih_e1 hΓ_eq) (ih_e2 hΓ_eq)
  | teq _ m e1 e2 ty h_e1 h_e2 ih1 ih2 =>
    exact HasType.teq _ m e1 e2 ty (ih1 hΓ_eq) (ih2 hΓ_eq)
  | tquant _ m k _name tr tr_ty x x_ty e o h_fresh hx h_body h_tr h_annot ih_body ih_tr =>
    subst hΓ_eq
    rw [h_insert_eq] at h_body h_tr
    exact HasType.tquant _ m k _ tr tr_ty x x_ty e o h_fresh hx h_body h_tr h_annot
  | top _ m f op ty h_find h_type =>
    exact HasType.top _ m f op ty h_find h_type
  | top_annotated _ m f op ty_o ty_s tys ann h_find h_type h_len h_open h_compat =>
    subst hΓ_eq
    exact HasType.top_annotated _ m f op ty_o ty_s tys ann h_find h_type h_len h_open h_compat
  | talias _ e mty mty' h_equiv h_e ih =>
    subst hΓ_eq
    exact HasType.talias _ e mty mty' h_equiv (ih rfl)

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Derive the find?-based closedness condition from `checkContextTypesClosed`. -/
private theorem ctx_closed_of_check (Env : TEnv T.IDMeta)
    (h : LExpr.checkContextTypesClosed Env) :
    ∀ y ty, Env.context.types.find? y = some ty → LTy.freeVars ty = [] := by
  -- checkContextTypesClosed checks all entries in all scopes.
  -- Maps.find? returns a type from some scope. That type passes the check.
  intro y ty h_find
  -- Walk the scopes to find where find? matched
  have : Env.context.types = Env.genEnv.context.types := rfl
  rw [this] at h_find
  simp only [LExpr.checkContextTypesClosed, TEnv.context] at h
  exact go Env.genEnv.context.types h h_find
where
  go (types : Maps (Identifier T.IDMeta) LTy)
      (h_all : types.all (fun scope => scope.all (fun p => p.2.freeVars == [])))
      {y : Identifier T.IDMeta} {ty : LTy}
      (h_find : Maps.find? types y = some ty) :
      LTy.freeVars ty = [] := by
    match types, h_all with
    | [], _ => simp [Maps.find?] at h_find
    | scope :: rest, h_all =>
      simp only [Maps.find?] at h_find
      simp only [List.all_cons, Bool.and_eq_true] at h_all
      obtain ⟨h_scope, h_rest⟩ := h_all
      cases h_s : Map.find? scope y with
      | none => rw [h_s] at h_find; simp at h_find; exact go rest h_rest h_find
      | some val =>
        rw [h_s] at h_find; simp at h_find; subst h_find
        -- val is in scope and all scope entries have empty freeVars
        exact scope_entry_closed scope h_scope h_s
  scope_entry_closed (scope : Map (Identifier T.IDMeta) LTy)
      (h_all : scope.all (fun p => p.2.freeVars == []))
      {y : Identifier T.IDMeta} {ty : LTy}
      (h_find : Map.find? scope y = some ty) :
      LTy.freeVars ty = [] := by
    match scope, h_all with
    | [], _ => simp [Map.find?] at h_find
    | (k, v) :: rest, h_all =>
      simp only [Map.find?] at h_find
      simp only [List.all_cons, Bool.and_eq_true] at h_all
      obtain ⟨h_hd, h_rest⟩ := h_all
      split at h_find
      · simp at h_find; subst h_find
        -- h_hd : (v.freeVars).beq [] = true, need v.freeVars = []
        -- List.beq returns true iff pointwise BEq holds; for [] this means the list is empty
        grind
      · exact scope_entry_closed rest h_rest h_find

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `checkContextTypesClosed` is preserved when context is unchanged. -/
private theorem checkContextTypesClosed_of_ctx_eq {Env Env' : TEnv T.IDMeta}
    (h : LExpr.checkContextTypesClosed Env) (h_ctx : Env'.context = Env.context) :
    LExpr.checkContextTypesClosed Env' := by
  unfold LExpr.checkContextTypesClosed at h ⊢
  rw [h_ctx]
  exact h

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- When all context types are closed (no free type variables), `allKeysFresh` holds
    for any substitution, because `isFresh` is vacuously true. -/
theorem Subst.allKeysFresh_of_ctx_closed
    {S : Subst} {Γ : TContext T.IDMeta}
    (h_ctx_closed : ∀ y ty, Γ.types.find? y = some ty → LTy.freeVars ty = []) :
    Subst.allKeysFresh (T := T) S Γ := by
  intro a _ x ty hf
  simp [h_ctx_closed x ty hf]


/-- Top-level soundness: if `LExpr.resolve` succeeds, the result is well-typed
    and the output environment is well-formed.

    The `checkContextTypesClosed Env` precondition requires all context types
    to have no free type variables. This is the key enabler for sequential
    composability: it implies `Subst.allKeysFresh S Env.context` for *any*
    substitution `S` (since closed types have empty `freeVars`, making `isFresh`
    vacuously true). In particular, the postcondition
    `Subst.allKeysFresh Env'.subst Env'.context` is guaranteed, ensuring that
    the output environment can be safely passed to the next `resolve` call
    (together with `checkContextTypesClosed Env'`, which is also preserved
    since `resolveAux` does not modify the context).

    Note: `resolve` ensures `context.types ≠ []` internally (adding an empty
    scope if needed), so the caller does not need this precondition. -/
theorem resolve_HasType :
    ∀ (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
      (Env : TEnv T.IDMeta) Env',
      e.resolve C Env = .ok ⟨e_typed, Env'⟩ →
      TEnvWF Env →
      FactoryWF C.functions →
      WellScoped e Env.context →
      Subst.allKeysFresh Env.stateSubstInfo.subst Env.context →
      LExpr.checkContextTypesClosed Env →
      HasType C (TContext.subst Env.context Env'.stateSubstInfo.subst) e (.forAll [] e_typed.toLMonoTy) ∧
      TEnvWF Env' ∧
      LExpr.checkContextTypesClosed Env' ∧
      Subst.allKeysFresh Env'.stateSubstInfo.subst Env'.context := by
  intro e e_typed C Env Env' h h_envwf h_fwf h_ws h_all_fresh h_check
  -- Derive the find?-based closedness from checkContextTypesClosed
  have h_ctx_closed : ∀ y ty, Env.context.types.find? y = some ty → LTy.freeVars ty = [] :=
    ctx_closed_of_check Env h_check
  -- Decompose resolve: it ensures types ≠ [] then calls resolveAux
  unfold LExpr.resolve at h
  simp only [Bind.bind, Except.bind] at h
  -- Case-split on whether Env.context.types is [] or nonempty
  cases h_types : Env.context.types with
  | nil =>
    -- types was empty: resolve initialized to [[]]
    simp [Maps.isEmpty, h_types] at h
    split at h
    · simp at h
    · rename_i v h_aux
      obtain ⟨et, Env'⟩ := v
      simp at h
      obtain ⟨h_typed, h_env'⟩ := h
      -- resolveAux was called on Env with types replaced by [[]]
      -- Build TEnvWF for the updated env
      let Env_upd := Env.updateContext { Env.context with types := [[]] }
      have h_upd_ne : Env_upd.context.types ≠ [] := List.cons_ne_nil _ _
      have h_envwf_upd : TEnvWF Env_upd := {
        aliasesWF := by simp [Env_upd, TEnv.updateContext, TEnv.context]; exact h_envwf.aliasesWF
        substFreshForGen := by simp [Env_upd, TEnv.updateContext]; exact h_envwf.substFreshForGen
        ctxFreshForGen := by
          simp only [Env_upd, TEnv.updateContext, TEnv.context, ContextFreshForGen, TContext.knownTypeVars]
          intro v hv
          simp [TContext.types.knownTypeVars, TContext.types.knownTypeVars.go] at hv
        boundVarsNodup := by
          intro y ty h_f; simp only [Env_upd, TEnv.updateContext, TEnv.context] at h_f
          simp [Maps.find?, Map.find?] at h_f
        boundVarsFresh := by
          intro y ty h_f; simp only [Env_upd, TEnv.updateContext, TEnv.context] at h_f
          simp [Maps.find?, Map.find?] at h_f
      }
      -- WellScoped transfers: both [] and [[]] have knownVars = []
      have h_ws_upd : WellScoped e Env_upd.context := by
        -- h_ws : WellScoped e Env.context where Env.context.types = []
        -- Goal: WellScoped e Env_upd.context where Env_upd.context.types = [[]]
        -- WellScoped says all fvars ∈ knownVars. knownVars collects keys from types.
        -- Both [] and [[]] have the same keys (none), so knownVars is the same.
        have h_kv_eq : Env_upd.context.knownVars = Env.context.knownVars := by
          simp only [Env_upd, TEnv.updateContext, TEnv.context, TContext.knownVars]
          simp only [TEnv.context] at h_types
          rw [h_types]
          simp [TContext.knownVars.go, Map.keys]
        unfold WellScoped at h_ws ⊢
        rw [h_kv_eq]
        exact h_ws
      have h_aux' : resolveAux C Env_upd e = .ok (et, Env') := by
        simp only [Env_upd, TEnv.updateContext] at h_aux ⊢
        exact h_aux
      subst h_env'
      have ⟨h_ctx_upd, h_hastype⟩ := resolveAux_HasType e et C Env_upd Env' h_aux' h_envwf_upd h_upd_ne h_fwf h_ws_upd
      have h_envwf' := TEnvWF.of_resolveAux e et C Env_upd Env' h_aux' h_envwf_upd h_upd_ne h_fwf h_ctx_upd
      rw [← h_typed, applySubstT_toLMonoTy]
      -- Env.context.subst S = Env.context since types = []
      have h_ctx_subst_id : TContext.subst Env.context Env'.stateSubstInfo.subst = Env.context := by
        unfold TContext.subst
        rw [h_types]
        simp only [TContext.types.subst]
        exact congrArg (TContext.mk · _) h_types.symm
      -- Env_upd.context.subst S = Env_upd.context since types = [[]]
      have h_upd_subst_id : TContext.subst Env_upd.context Env'.stateSubstInfo.subst = Env_upd.context := by
        simp [Env_upd, TEnv.updateContext, TEnv.context, TContext.subst, TContext.types.subst, TContext.types.subst.go]
      exact ⟨by
        rw [h_ctx_subst_id]
        have h_upd_eq : Env_upd.context = { types := [[]], aliases := Env.context.aliases } := by
          simp [Env_upd, TEnv.updateContext, TEnv.context]
        have h_ht := h_hastype Env'.stateSubstInfo.subst
          (Subst.absorbs_refl _ Env'.stateSubstInfo.isWF) Env'.stateSubstInfo.isWF
          (by -- polyKeysFresh holds vacuously: Env_upd.context has types = [[]], so
              -- find? always returns none (empty scope), making the condition vacuous.
              intro a _ x ty hf _
              simp [Env_upd, TEnv.updateContext, TEnv.context, Maps.find?, Map.find?] at hf)
        rw [h_upd_subst_id, h_upd_eq] at h_ht
        have h_result := HasType_transfer_empty_scope C Env.context.aliases e _ h_ht
        suffices Env.context = { types := [], aliases := Env.context.aliases } by
          rw [this]; exact h_result
        have h_t : Env.context.types = [] := h_types
        cases h_ctx : Env.context
        simp [TEnv.context] at h_t
        simp_all,
      h_envwf',
      -- checkContextTypesClosed for Env': Env'.context = Env_upd.context with types = [[]]
      by have h_check_upd : LExpr.checkContextTypesClosed Env_upd := by
           simp [LExpr.checkContextTypesClosed, Env_upd, TEnv.updateContext, TEnv.context]
         exact checkContextTypesClosed_of_ctx_eq h_check_upd h_ctx_upd,
      -- allKeysFresh for Env'.subst / Env'.context: from closed types
      by have h_check_upd : LExpr.checkContextTypesClosed Env_upd := by
           simp [LExpr.checkContextTypesClosed, Env_upd, TEnv.updateContext, TEnv.context]
         have h_check' := checkContextTypesClosed_of_ctx_eq h_check_upd h_ctx_upd
         exact Subst.allKeysFresh_of_ctx_closed (ctx_closed_of_check Env' h_check')⟩
  | cons hd tl =>
    -- types was non-empty: resolve passes Env unchanged to resolveAux
    simp [Maps.isEmpty, h_types] at h
    split at h
    · simp at h
    · rename_i v h_aux
      obtain ⟨et, Env'⟩ := v
      simp at h
      obtain ⟨h_typed, h_env'⟩ := h
      subst h_env'
      have h_ne : Env.context.types ≠ [] := by rw [h_types]; exact List.cons_ne_nil _ _
      have ⟨h_ctx_pres, h_hastype⟩ := resolveAux_HasType e et C Env Env' h_aux h_envwf h_ne h_fwf h_ws
      have h_envwf' := TEnvWF.of_resolveAux e et C Env Env' h_aux h_envwf h_ne h_fwf h_ctx_pres
      rw [← h_typed, applySubstT_toLMonoTy]
      have h_all_fresh' : Subst.allKeysFresh Env'.stateSubstInfo.subst Env.context :=
        Subst.allKeysFresh_of_ctx_closed h_ctx_closed
      -- checkContextTypesClosed for Env': context preserved, so types remain closed
      have h_check' : LExpr.checkContextTypesClosed Env' :=
        checkContextTypesClosed_of_ctx_eq h_check h_ctx_pres
      -- contextTypesClosed for Env' (find?-based, for allKeysFresh)
      have h_ctx_closed' : ∀ y ty, Env'.context.types.find? y = some ty → LTy.freeVars ty = [] :=
        ctx_closed_of_check Env' h_check'
      -- allKeysFresh for Env'.subst / Env'.context: from closed types
      have h_all_fresh_out : Subst.allKeysFresh Env'.stateSubstInfo.subst Env'.context :=
        Subst.allKeysFresh_of_ctx_closed h_ctx_closed'
      exact ⟨h_hastype Env'.stateSubstInfo.subst (Subst.absorbs_refl _ Env'.stateSubstInfo.isWF) Env'.stateSubstInfo.isWF
        (Subst.allKeysFresh_implies_polyKeysFresh _ _ h_all_fresh'),
        h_envwf', h_check', h_all_fresh_out⟩

end Proofs

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
  have h_tabs := @LExpr.HasType.tabs (T := ⟨Unit, Unit⟩) _ {} {} () "" ("a", none) t[%a] esM[%0] t[%a] none
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
  · simp only[LTy.openFull, LTy.toMonoTypeUnsafe, List.zip, LTy.boundVars];
    unfold LMonoTy.subst ;
    simp[Subst.hasEmptyScopes, Map.isEmpty, LMonoTys.subst, LMonoTys.subst.substAux, LMonoTy.subst, Maps.find?, Map.find?, LMonoTy.int]
  · exact AnnotCompat.of_eq

end Tests

---------------------------------------------------------------------
end LExpr
end -- public section
end Lambda
