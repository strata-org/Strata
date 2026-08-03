/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.DL.Lambda.LExprWFProps

import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LTy
public import Strata.DL.Lambda.LTyProps
import all Strata.DL.Lambda.LTyProps
import all Strata.DL.Lambda.LTyUnify
public import Strata.DL.Lambda.LTyUnifyProps
import all Strata.DL.Lambda.LTyUnifyProps
import all Strata.Util.HMap
import all Strata.Util.HMaps
import all Strata.DL.Lambda.Identifiers
import all Strata.DL.Util.Func
import all Strata.DL.Util.ListMap
import all Strata.DL.Util.List
public import Strata.DL.Lambda.LExprT
import all Strata.DL.Lambda.LExprT
public import Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.FactoryProps
public meta import Init.Grind.Cases

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
open Strata.Util (HMap HMaps)

public section

namespace LExpr
open LTy

variable {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta]

/-!
### Lean 4 Standard Library Gaps

The `String.startsWith` and `String.drop` APIs go through the
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
  ∃ (σ : SubstOne),
    AliasEquiv aliases (LMonoTy.subst [σ] ann) xty

theorem AnnotCompat.of_eq {aliases : List TypeAlias} {ann : LMonoTy} :
    AnnotCompat aliases ann ann :=
  ⟨HMap.empty, by rw [LMonoTy.subst_single_empty]; exact AliasEquiv.refl⟩

/-- Like `AnnotCompat` but the existential substitution must be identity on rigid
    type variables. When `rigidVars = []` this reduces to `AnnotCompat`.
    When all free vars of `ann` are rigid this forces `AliasEquiv ann mty` directly
    (since σ is identity on all free vars, `subst [σ] ann = ann`). -/
def RigidAnnotCompat (aliases : List TypeAlias) (rigidVars : List TyIdentifier)
    (ann mty : LMonoTy) : Prop :=
  ∃ (σ : SubstOne),
    (∀ v, v ∈ rigidVars → LMonoTy.subst [σ] (.ftvar v) = .ftvar v) ∧
    AliasEquiv aliases (LMonoTy.subst [σ] ann) mty

/-- `RigidAnnotCompat` is reflexive (witnessed by the empty substitution). -/
theorem RigidAnnotCompat.of_eq {aliases : List TypeAlias} {rigidVars : List TyIdentifier}
    {ann : LMonoTy} : RigidAnnotCompat aliases rigidVars ann ann :=
  ⟨HMap.empty, fun _ _ => LMonoTy.subst_single_empty _, by
    rw [LMonoTy.subst_single_empty]; exact .refl⟩

/-- `AliasEquiv` implies `RigidAnnotCompat` (with the empty substitution). -/
theorem RigidAnnotCompat.of_aliasEquiv {aliases : List TypeAlias}
    {rigidVars : List TyIdentifier} {ann mty : LMonoTy}
    (h : AliasEquiv aliases ann mty) : RigidAnnotCompat aliases rigidVars ann mty :=
  ⟨HMap.empty, fun _ _ => LMonoTy.subst_single_empty _, by
    rw [LMonoTy.subst_single_empty]; exact h⟩


-- `AnnotCompat_subst` is defined later (after `AliasEquiv_subst` which it depends on).
-- See the actual definition below the `AliasEquiv_subst` theorem.

/--
Typing relation for `LExpr`s with respect to `LTy`.

The typing relation is parameterized by two contexts. An `LContext` contains
known types and functions while a `TContext` associates free variables with
their types.
-/
inductive HasType {T: LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta] (C: LContext T):
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
            C.functions[op.name]? = some f →
            f.type = .ok ty →
            HasType C Γ (.op m op none) ty
  /--
  Similarly to free variables, an annotated operator has its claimed type `ty_s` if `ty_s` is an
  instantiation of the type `ty_o` recorded for it in `C.functions`, and the annotation
  `ann` is compatible with `ty_s`.
  -/
  | top_annotated: ∀ Γ m f op ty_o ty_s tys ann,
            C.functions[op.name]? = some f →
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
            AliasEquiv Γ.aliases mty mty' →
            HasType C Γ e (.forAll [] mty) →
            HasType C Γ e (.forAll [] mty')


/--
If `LExpr e` is well-typed, then it is well-formed, i.e., contains no dangling
bound variables.
-/
theorem HasType.regularity {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {C : LContext T} {Γ : TContext T.IDMeta} {e : LExpr T.mono} {ty : LTy}
    (h : HasType (T := T) C Γ e ty) :
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


/-- `HasType` does not read `C.rigidTypeVars` (rigidity is enforced by the
    type-checker's post-hoc checks, not by the typing relation). So a judgment
    proved against a context with an overridden rigid-var set transfers to the
    original context. Used when a sub-expression (e.g. a function's measure) is
    type-checked under a temporarily-extended rigid set. -/
theorem HasType.of_rigidTypeVars_irrel [DecidableEq T.IDMeta] [Hashable T.IDMeta] {C : LContext T}
    {rv : List TyIdentifier} {Γ : TContext T.IDMeta} {e : LExpr T.mono} {ty : LTy}
    (h : HasType ({C with rigidTypeVars := rv}) Γ e ty) : HasType C Γ e ty := by
  induction h with
  | tbool_const Γ m b hk => exact HasType.tbool_const _ _ _ hk
  | tint_const Γ m n hk => exact HasType.tint_const _ _ _ hk
  | treal_const Γ m r hk => exact HasType.treal_const _ _ _ hk
  | tstr_const Γ m s hk => exact HasType.tstr_const _ _ _ hk
  | tbitvec_const Γ m n b hk => exact HasType.tbitvec_const _ _ _ _ hk
  | tvar Γ m x ty hf => exact HasType.tvar _ _ _ _ hf
  | tvar_annotated Γ m x ty_o ty_s tys ann hf hl ho ha =>
    exact HasType.tvar_annotated _ _ _ _ _ _ _ hf hl ho ha
  | tabs Γ m name x x_ty e e_ty o hfr hx he ht ho ih =>
    exact HasType.tabs _ _ _ _ _ _ _ _ hfr hx he ih ho
  | tapp Γ m e1 e2 t1 t2 h1 h2 ht1 ht2 ih1 ih2 =>
    exact HasType.tapp _ _ _ _ _ _ h1 h2 ih1 ih2
  | tinst Γ e ty e_ty x x_ty ht he ih => exact HasType.tinst _ _ _ _ _ _ ih he
  | tgen Γ e a ty ht hfr ih => exact HasType.tgen _ _ _ _ ih hfr
  | tif Γ m c e1 e2 ty hc h1 h2 ihc ih1 ih2 => exact HasType.tif _ _ _ _ _ _ ihc ih1 ih2
  | teq Γ m e1 e2 ty h1 h2 ih1 ih2 => exact HasType.teq _ _ _ _ _ ih1 ih2
  | tquant Γ m k name tr tr_ty x x_ty e o hfr hx ht htr ho ih ihtr =>
    exact HasType.tquant _ _ _ _ _ _ _ _ _ _ hfr hx ih ihtr ho
  | top Γ m f op ty hf ht => exact HasType.top _ _ _ _ _ hf ht
  | top_annotated Γ m f op ty_o ty_s tys ann hf ht hl ho ha =>
    exact HasType.top_annotated _ _ _ _ _ _ _ _ hf ht hl ho ha
  | talias Γ e mty mty' hae ht ih => exact HasType.talias _ _ _ _ hae ih

/-- **Γ-congruence for `HasType`.** Typing reads `Γ` only through `Γ.types.find?`
    and `Γ.aliases`, so it is invariant under replacing `Γ₁` by any `Γ₂` that agrees
    pointwise on `find?` and has the same aliases. `Γ₂` is quantified inside the
    conclusion so the binder-extending cases can re-apply the IH at extended contexts.

    Needed by statement-typechecker soundness: `typeCheckAux` types block/branch
    bodies under `pushEmptyContext` (`Γ = []::Γ₀`) while the spec uses `Γ₀`; the two
    agree exactly on `find?`. -/
theorem HasType.find_congr {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {C : LContext T} {Γ₁ : TContext T.IDMeta}
    {e : LExpr T.mono} {ty : LTy}
    (h : HasType C Γ₁ e ty) :
    ∀ (Γ₂ : TContext T.IDMeta),
      (∀ x, Γ₂.types.find? x = Γ₁.types.find? x) →
      Γ₂.aliases = Γ₁.aliases →
      HasType C Γ₂ e ty := by
  induction h with
  | tbool_const Γ m b hk =>
    intro Γ₂ _ _; exact HasType.tbool_const Γ₂ m b hk
  | tint_const Γ m n hk =>
    intro Γ₂ _ _; exact HasType.tint_const Γ₂ m n hk
  | treal_const Γ m r hk =>
    intro Γ₂ _ _; exact HasType.treal_const Γ₂ m r hk
  | tstr_const Γ m s hk =>
    intro Γ₂ _ _; exact HasType.tstr_const Γ₂ m s hk
  | tbitvec_const Γ m n b hk =>
    intro Γ₂ _ _; exact HasType.tbitvec_const Γ₂ m n b hk
  | tvar Γ m x ty h_find =>
    intro Γ₂ h_eq _
    exact HasType.tvar Γ₂ m x ty (by rw [h_eq]; exact h_find)
  | tvar_annotated Γ m x ty_o ty_s tys ann h_find h_len h_open h_annot =>
    intro Γ₂ h_eq h_al
    exact HasType.tvar_annotated Γ₂ m x ty_o ty_s tys ann
      (by rw [h_eq]; exact h_find) h_len h_open (by rw [h_al]; exact h_annot)
  | tabs Γ m name x x_ty e e_ty o h_fresh hx he h_body h_o ih_body =>
    intro Γ₂ h_eq h_al
    refine HasType.tabs Γ₂ m name x x_ty e e_ty o h_fresh hx he
      (ih_body { Γ₂ with types := Γ₂.types.insert x.fst x_ty } ?_ h_al) ?_
    · -- The extended contexts agree on `find?`: both insert `(x.fst, x_ty)`.
      intro y
      by_cases h_xy : y = x.fst
      · -- look up the just-inserted binding on both sides.
        rw [h_xy]
        show (HMaps.insert Γ₂.types x.fst x_ty).find? x.fst = (HMaps.insert Γ.types x.fst x_ty).find? x.fst
        rw [HMaps.find?_insert_self, HMaps.find?_insert_self]
      · show (HMaps.insert Γ₂.types x.fst x_ty).find? y = (HMaps.insert Γ.types x.fst x_ty).find? y
        rw [HMaps.find?_insert_ne _ _ _ _ h_xy, HMaps.find?_insert_ne _ _ _ _ h_xy]; exact h_eq y
    · rw [h_al]; exact h_o
  | tapp Γ m e1 e2 t1 t2 h1 h2 h_e1 h_e2 ih_e1 ih_e2 =>
    intro Γ₂ h_eq h_al
    exact HasType.tapp Γ₂ m e1 e2 t1 t2 h1 h2 (ih_e1 Γ₂ h_eq h_al) (ih_e2 Γ₂ h_eq h_al)
  | tinst Γ e ty e_ty x x_ty h_e h_eqty ih_e =>
    intro Γ₂ h_eq h_al
    exact HasType.tinst Γ₂ e ty e_ty x x_ty (ih_e Γ₂ h_eq h_al) h_eqty
  | tgen Γ e a ty h_e h_isfresh ih_e =>
    intro Γ₂ h_eq h_al
    refine HasType.tgen Γ₂ e a ty (ih_e Γ₂ h_eq h_al) ?_
    -- `isFresh` reads `Γ.types.find?`; transport along the pointwise agreement.
    intro y t h_find; rw [h_eq] at h_find; exact h_isfresh y t h_find
  | tif Γ m c e1 e2 ty h_c h_e1 h_e2 ih_c ih_e1 ih_e2 =>
    intro Γ₂ h_eq h_al
    exact HasType.tif Γ₂ m c e1 e2 ty
      (ih_c Γ₂ h_eq h_al) (ih_e1 Γ₂ h_eq h_al) (ih_e2 Γ₂ h_eq h_al)
  | teq Γ m e1 e2 ty h_e1 h_e2 ih_e1 ih_e2 =>
    intro Γ₂ h_eq h_al
    exact HasType.teq Γ₂ m e1 e2 ty (ih_e1 Γ₂ h_eq h_al) (ih_e2 Γ₂ h_eq h_al)
  | tquant Γ m k name tr tr_ty x x_ty e o h_fresh hx h_body h_tr h_o ih_body ih_tr =>
    intro Γ₂ h_eq h_al
    have h_ext : ∀ y, (({ Γ₂ with types := Γ₂.types.insert x.fst x_ty } : TContext T.IDMeta).types).find? y
        = (({ Γ with types := Γ.types.insert x.fst x_ty } : TContext T.IDMeta).types).find? y := by
      intro y
      by_cases h_xy : y = x.fst
      · -- look up the just-inserted binding on both sides.
        rw [h_xy]
        show (HMaps.insert Γ₂.types x.fst x_ty).find? x.fst = (HMaps.insert Γ.types x.fst x_ty).find? x.fst
        rw [HMaps.find?_insert_self, HMaps.find?_insert_self]
      · show (HMaps.insert Γ₂.types x.fst x_ty).find? y = (HMaps.insert Γ.types x.fst x_ty).find? y
        rw [HMaps.find?_insert_ne _ _ _ _ h_xy, HMaps.find?_insert_ne _ _ _ _ h_xy]; exact h_eq y
    exact HasType.tquant Γ₂ m k name tr tr_ty x x_ty e o h_fresh hx
      (ih_body _ h_ext h_al) (ih_tr _ h_ext h_al) (by rw [h_al]; exact h_o)
  | top Γ m f op ty h_find h_type =>
    intro Γ₂ _ _; exact HasType.top Γ₂ m f op ty h_find h_type
  | top_annotated Γ m f op ty_o ty_s tys ann h_find h_type h_len h_open h_annot =>
    intro Γ₂ _ h_al
    exact HasType.top_annotated Γ₂ m f op ty_o ty_s tys ann h_find h_type
      h_len h_open (by rw [h_al]; exact h_annot)
  | talias Γ e mty mty' h_equiv h_e ih_e =>
    intro Γ₂ h_eq h_al
    exact HasType.talias Γ₂ e mty mty' (by rw [h_al]; exact h_equiv) (ih_e Γ₂ h_eq h_al)



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

theorem LConst.ty_subst [DecidableEq TyIdentifier] (c : LConst) (S : Subst) :
    LMonoTy.subst S c.ty = c.ty := by
  apply LMonoTy.subst_no_key_free
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro k _ hk
  rw [LConst.ty_freeVars] at hk
  simp at hk

/--
`HasType` is preserved under substitution of a single fresh type variable.
If `e` has type `mty` and `a` is fresh in `Γ`, then `e` also has type
`mty[a ↦ t]` for any `t`. This follows from `tgen` (generalize `a`) then
`tinst` (instantiate `a` with `t`).
-/
theorem HasType_subst_fresh {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono) (mty : LMonoTy)
    (a : TyIdentifier) (t : LMonoTy)
    (h : HasType C Γ e (.forAll [] mty))
    (h_fresh : TContext.isFresh a Γ) :
    HasType C Γ e (.forAll [] (LMonoTy.subst (Subst.singleton a t) mty)) := by
  have h_gen := HasType.tgen Γ e a (.forAll [] mty) h h_fresh
  simp [LTy.close] at h_gen
  have h_inst := HasType.tinst Γ e (.forAll [a] mty)
    (.forAll [] (LMonoTy.subst (Subst.singleton a t) mty)) a t h_gen
  simpa [LTy.open, List.removeAll] using h_inst

/--
Helper: `toLMonoTy` commutes with `applySubstT` in the expected way.
For most constructors, `(applySubstT et S).toLMonoTy = LMonoTy.subst S et.toLMonoTy`.
For quantifiers, `toLMonoTy` always returns `LMonoTy.bool`.
-/
theorem applySubstT_toLMonoTy {T : LExprParamsT}
    (et : LExprT T) (S : Subst) :
    (LExpr.applySubstT et S).toLMonoTy = LMonoTy.subst S et.toLMonoTy := by
  cases et <;> try solve | simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.toLMonoTy]
  case quant m k _ ty tr e =>
    simp only [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.toLMonoTy]
    rw [LMonoTy.subst_bool]

/-!
### Proof architecture for `resolve_HasType`

The proof is structured in three layers:

1. **`resolveAux_HasType`**: The induction core, proved via the `resolveAux`
  induction principle.
   States that if `resolveAux C Env e = .ok (et, Env')`, then:
   - `Env'.context.Equiv Env.context` (context is preserved up to `find?`-equivalence), and
   - for any substitution `S` that absorbs `Env'.stateSubstInfo.subst`,
     `HasType C (TContext.subst Env.context S) e (.forAll [] (LMonoTy.subst S et.toLMonoTy))`.

2. **`resolve_HasType_core`**: Lifts `resolveAux_HasType` through `resolve` (which is
   `resolveAux` followed by `applySubstT`, plus the empty-context guard). It exposes the
   *universally-quantified-over-`S`* typing conclusion together with idempotence and
   `TEnvWF Env'`, under the **minimal** preconditions (`TEnvWF`, `FactoryWF`,
   `WellScoped` — no `checkContextTypesClosed`/`allKeysFresh`). This is the form
   consumed by callers that compose substitutions themselves (e.g. `CmdType.inferType_HasType`).

   Note: we require only `FactoryWF`, not `FactoryClosed` — the latter does not hold of
   typechecked terms in general (a `funcDecl` body may capture surrounding-scope variables).

3. **`resolve_HasType`**: The top-level theorem. Building on `resolve_HasType_core`, it adds
   the composability postconditions (`checkContextTypesClosed Env'`,
   `allKeysFresh Env'.subst Env'.context`) under the extra `checkContextTypesClosed Env` /
   `allKeysFresh Env` preconditions, then specializes the universal conclusion to the final
   substitution `Env'.stateSubstInfo.subst`.

#### Key definitions and supporting lemmas (quite a few of these are in LTyUnify.lean):

- **`Subst.absorbs`**: `S_outer` absorbs `S_inner` when every binding in
  `S_inner` is "already known" to `S_outer`.

- **`LMonoTy.subst_absorbs`**: Absorption implies `subst S_outer (subst S_inner mty) = subst S_outer mty`.

- **`resolveAux_properties`**: Each `resolveAux` call preserves invariants (context, freshness, absorption).

- **`Constraint.UnifyOneProperties`** / **`Constraints.UnifyCoreProperties`**: Bundled soundness, absorption, and key-inclusion for `unifyOne` / `unifyCore`.

- **`Constraints.unify_absorbs`**: Unification absorbs the pre-unification substitution.

- **`Constraints.unify_sound`**: Unification makes every constraint pair equal under the output substitution.

- **`unify_makes_equal`**: Unification makes constrained types equal.

- **`HasType_subst_fresh_all`**: Typing is preserved under substitution of fresh variables.
-/

/-!
#### Substitution lemmas for `HasType_subst_fresh_all`
-/

/-- The number of keys in `S` that appear in `freeVars(mty)`. Used as the
    termination measure for `HasType_subst_fresh_all`. -/
noncomputable def relevantKeys (S : Subst) (mty : LMonoTy) : Nat :=
  ((HMaps.keys S).filter (· ∈ LMonoTy.freeVars mty)).length

/--
Applying a single substitution `Subst.singleton a t` strictly decreases
`relevantKeys` when `a ∈ freeVars(mty)`, `HMaps.find? S a = some t`, and
`SubstWF S`.
-/
theorem relevantKeys_decrease
    (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (mty : LMonoTy) (h_find : HMaps.find? S a = some t) (h_wf : SubstWF S)
    (ha_fv : a ∈ LMonoTy.freeVars mty) :
    relevantKeys S (LMonoTy.subst (Subst.singleton a t) mty) < relevantKeys S mty := by
  unfold relevantKeys
  have ha_not_in_t : a ∉ LMonoTy.freeVars t :=
    SubstWF.not_mem_freeVars_of_find S a t h_find h_wf
  have h_wf_single : SubstWF (Subst.singleton a t) := SubstWF.single_subst a t ha_not_in_t
  have ha_not_in_subst : a ∉ LMonoTy.freeVars (LMonoTy.subst (Subst.singleton a t) mty) := by
    have h_keys := LMonoTy.subst_keys_not_in_substituted_type (S := Subst.singleton a t) h_wf_single mty
    simp only [List.all_eq_true, decide_eq_true_eq] at h_keys
    have ha_key : a ∈ HMaps.keys (Subst.singleton a t) := by
      simp only [Subst.singleton, HMaps.keys, List.append_nil, HMap.mem_keys_single_iff]
    exact h_keys a ha_key
  have h_keys_not_in_t : ∀ k, k ∈ HMaps.keys S → k ∉ LMonoTy.freeVars t := by
    intro k hk hk_t
    simp only [SubstWF, List.all_eq_true, decide_eq_true_eq] at h_wf
    have h_t_sub := Subst.freeVars_of_find_subset S h_find
    exact h_wf k hk (h_t_sub hk_t)
  have h_fv_subset := LMonoTy.freeVars_of_subst_subset (Subst.singleton a t) mty
  apply List.filter_length_lt_of_imp_witness
    (a := a)
  · intro k hk hk_in_subst
    rw [decide_eq_true_eq] at hk_in_subst ⊢
    have hk_in_union := h_fv_subset hk_in_subst
    rcases List.mem_append.mp hk_in_union with h | h
    · exact h
    · exact absurd (Subst.freeVars_singleton_subset a t h) (h_keys_not_in_t k hk)
  · exact HMaps.find?_mem_keys S h_find
  · rw [decide_eq_true_eq]; exact ha_fv
  · rw [decide_eq_true_eq]; exact ha_not_in_subst

/-- All keys in substitution `S` are fresh w.r.t. context `Γ`. -/
def Subst.allKeysFresh {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    (S : Subst) (Γ : TContext T.IDMeta) : Prop :=
  ∀ a, a ∈ HMaps.keys S → TContext.isFresh (T := T) a Γ

/-- Weaker variant of `allKeysFresh`: keys of `S` are fresh only with respect to
    **polymorphic** entries in the context (those with non-empty bound variables).
    This condition is preserved through `typeBoundVar` (which adds monomorphic entries)
    and suffices for the polymorphic `fvar` case of `inferFVar_HasType`. -/
@[expose] def Subst.polyKeysFresh {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    (S : Subst) (Γ : TContext T.IDMeta) : Prop :=
  ∀ a, a ∈ HMaps.keys S → ∀ (x : T.Identifier) (ty : LTy),
    Γ.types.find? x = some ty → LTy.boundVars ty ≠ [] → a ∉ LTy.freeVars ty

theorem Subst.allKeysFresh_implies_polyKeysFresh {T : LExprParams} [DecidableEq T.IDMeta]
    [Hashable T.IDMeta]
    (S : Subst) (Γ : TContext T.IDMeta)
    (h : Subst.allKeysFresh S Γ) : Subst.polyKeysFresh (T := T) S Γ := by
  intro a ha x ty hf _
  exact h a ha x ty hf

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
private theorem LMonoTys.instantiate_context {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TGenEnv IDMeta)
    (mtys' : LMonoTys) (Env' : TGenEnv IDMeta)
    (h : LMonoTys.instantiate ids mtys Env = .ok (mtys', Env')) :
    Env'.context = Env.context := by
  simp [LMonoTys.instantiate, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_gen
  obtain ⟨tvs, Env1⟩ := v1; simp at h h_gen
  obtain ⟨_, h2⟩ := h; rw [← h2]
  exact TGenEnv.genTyVars_context ids.length Env tvs Env1 h_gen

/-- `instantiateEnv` preserves the context. -/
theorem LMonoTys.instantiateEnv_context {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
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
theorem LMonoTy.resolveAliases_context {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
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
    elim_err h
    rename_i v1 h_args
    obtain ⟨args', Env1⟩ := v1; simp at h h_args
    simp only [LMonoTy.tconsAliasSimple] at h
    split at h <;> (obtain ⟨_, h2⟩ := h; rw [← h2])
    all_goals exact LMonoTys.resolveAliases_context args Env args' Env1 h_args

theorem LMonoTys.resolveAliases_context {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (mtys : LMonoTys) (Env : TEnv IDMeta) (mtys' : LMonoTys) (Env' : TEnv IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env')) :
    Env'.context = Env.context := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases] at h; grind
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_hd
    obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    elim_err h
    rename_i v2 h_tl
    obtain ⟨mrest', Env2⟩ := v2
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    rw [LMonoTys.resolveAliases_context mrest Env1 mrest' Env2 h_tl,
        LMonoTy.resolveAliases_context mty Env mty' Env1 h_hd]
end

mutual
/-- `LMonoTy.resolveAliases` preserves the full environment (not just context). -/
private theorem LMonoTy.resolveAliases_env {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (mty : LMonoTy) (Env : TEnv IDMeta) (mty' : LMonoTy) (Env' : TEnv IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env')) :
    Env' = Env := by
  match mty with
  | .ftvar _ =>
    simp [LMonoTy.resolveAliases] at h
    obtain ⟨_, h2⟩ := h; exact h2.symm
  | .bitvec _ =>
    simp [LMonoTy.resolveAliases] at h
    obtain ⟨_, h2⟩ := h; exact h2.symm
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_args
    obtain ⟨args', Env1⟩ := v1; simp at h h_args
    simp only [LMonoTy.tconsAliasSimple] at h
    split at h <;> (obtain ⟨_, h2⟩ := h; rw [← h2])
    all_goals exact LMonoTys.resolveAliases_env args Env args' Env1 h_args
private theorem LMonoTys.resolveAliases_env {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (mtys : LMonoTys) (Env : TEnv IDMeta) (mtys' : LMonoTys) (Env' : TEnv IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env')) :
    Env' = Env := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases] at h
    obtain ⟨_, h2⟩ := h; exact h2.symm
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_hd
    obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    elim_err h
    rename_i v2 h_tl
    obtain ⟨mrest', Env2⟩ := v2
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    rw [LMonoTys.resolveAliases_env mrest Env1 mrest' Env2 h_tl,
        LMonoTy.resolveAliases_env mty Env mty' Env1 h_hd]
end

/-- `LTy.instantiate` preserves the context. -/
theorem LTy.instantiate_context {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (ty : LTy) (Env : TGenEnv IDMeta)
    (mty : LMonoTy) (Env' : TGenEnv IDMeta)
    (h : LTy.instantiate ty Env = .ok (mty, Env')) :
    Env'.context = Env.context := by
  simp [LTy.instantiate, Bind.bind, Except.bind] at h
  split at h
  · simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
  · elim_err h
    rename_i v1 h_gen
    obtain ⟨tvs, Env1⟩ := v1; simp at h h_gen
    obtain ⟨_, h2⟩ := h; rw [← h2]
    exact TGenEnv.genTyVars_context _ Env tvs Env1 h_gen

/-- `LTy.resolveAliases` preserves the context. -/
theorem LTy.resolveAliases_context {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (ty : LTy) (Env : TEnv IDMeta) (mty : LMonoTy) (Env' : TEnv IDMeta)
    (h : LTy.resolveAliases ty Env = .ok (mty, Env')) :
    Env'.context = Env.context := by
  simp [LTy.resolveAliases, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_inst
  obtain ⟨mty0, genEnv'⟩ := v1; simp at h h_inst
  have h_ra := LMonoTy.resolveAliases_context _ _ mty Env' h
  rw [h_ra]; simp [TEnv.context]
  exact LTy.instantiate_context ty Env.genEnv mty0 genEnv' h_inst

/-- `LTy.resolveAliases` preserves `stateSubstInfo` (only modifies `genEnv`). -/
theorem LTy.resolveAliases_preserves_stateSubstInfo {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (ty : LTy) (Env : TEnv IDMeta) (mty : LMonoTy) (Env' : TEnv IDMeta)
    (h : LTy.resolveAliases ty Env = .ok (mty, Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  simp [LTy.resolveAliases, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_inst
  obtain ⟨mty0, genEnv'⟩ := v1; simp at h h_inst
  have h_env := LMonoTy.resolveAliases_env mty0 {Env with genEnv := genEnv'} mty Env' h
  rw [h_env]

/-!
### Definitions and lemmas for the `resolveAux`-based proof strategy
-/

mutual
/-- Free variables of `subst (Subst.singleton a t) mty` are either free vars of
    `mty` (possibly minus `a`) or free vars of `t`. Contrapositively: if `b` is
    in the freeVars of the substituted type but NOT in freeVars of `t`,
    then `b` was already in freeVars of `mty`. -/
private theorem LMonoTy.freeVars_subst_single_mem
    (a : TyIdentifier) (t mty : LMonoTy) (b : TyIdentifier)
    (hb : b ∈ LMonoTy.freeVars (LMonoTy.subst (Subst.singleton a t) mty))
    (hb_not_t : b ∉ LMonoTy.freeVars t) :
    b ∈ LMonoTy.freeVars mty := by
  match mty with
  | .ftvar x =>
    by_cases hax : a = x
    · subst hax
      simp only [LMonoTy.subst_unfold, Subst.find?_singleton_self] at hb
      exact absurd hb hb_not_t
    · have h_find_none : HMaps.find? (Subst.singleton a t) x = none := by
        simp only [Subst.singleton, HMaps.find?_single_scope,
          HMap.find?_single_ne a x t (by simp [bne, Ne.symm hax])]
      simp only [LMonoTy.subst_unfold, h_find_none] at hb; exact hb
  | .bitvec _ =>
    rw [LMonoTy.subst_bitvec] at hb; exact hb
  | .tcons name args =>
    rw [LMonoTy.subst_tcons] at hb
    simp only [LMonoTy.freeVars] at hb ⊢
    exact LMonoTys.freeVars_subst_single_mem a t args b hb hb_not_t
termination_by SizeOf.sizeOf mty
decreasing_by all_goals simp_wf; omega

/-- List version: free vars of `subst (Subst.singleton a t) mtys` that are not
    in `freeVars t` must be in `freeVars mtys`. -/
private theorem LMonoTys.freeVars_subst_single_mem
    (a : TyIdentifier) (t : LMonoTy) (mtys : LMonoTys) (b : TyIdentifier)
    (hb : b ∈ LMonoTys.freeVars (LMonoTys.subst (Subst.singleton a t) mtys))
    (hb_not_t : b ∉ LMonoTy.freeVars t) :
    b ∈ LMonoTys.freeVars mtys := by
  match mtys with
  | [] =>
    rw [LMonoTys.subst_eq_map] at hb
    simp only [List.map_nil, LMonoTys.freeVars] at hb
    exact hb
  | y :: ys =>
    rw [LMonoTys.subst_eq_map] at hb
    simp only [List.map_cons, LMonoTys.freeVars] at hb ⊢
    cases List.mem_append.mp hb with
    | inl h_y => exact List.mem_append_left _ (LMonoTy.freeVars_subst_single_mem a t y b h_y hb_not_t)
    | inr h_ys =>
      rw [← LMonoTys.subst_eq_map] at h_ys
      exact List.mem_append_right _ (LMonoTys.freeVars_subst_single_mem a t ys b h_ys hb_not_t)
termination_by SizeOf.sizeOf mtys
decreasing_by all_goals simp_wf; omega
end

variable {T : LExprParams} [ToString T.IDMeta] [DecidableEq T.IDMeta]
  [Std.ToFormat T.IDMeta] [Std.ToFormat (LFunc T)]
  [Std.ToFormat T.Metadata] [Hashable T.IDMeta]

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `HasType` is preserved under substitution when keys relevant to the type
    are fresh. Only keys that appear in `freeVars mty` need to be fresh,
    not all keys. This is the key weakening that avoids requiring `allKeysFresh`
    globally. -/
theorem HasType_subst_fresh_all
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono) (mty : LMonoTy)
    (S : Subst)
    (h : HasType C Γ e (.forAll [] mty))
    (h_fresh : ∀ a, a ∈ HMaps.keys S → a ∈ LMonoTy.freeVars mty → TContext.isFresh (T := T) a Γ)
    (h_wf : SubstWF S) :
    HasType C Γ e (.forAll [] (LMonoTy.subst S mty)) := by
  by_cases hS : Subst.hasEmptyScopes S
  · rw [LMonoTy.subst_of_hasEmptyScopes hS]; exact h
  · suffices h_gen : ∀ (n : Nat) (mty : LMonoTy),
        relevantKeys S mty = n →
        (∀ a, a ∈ HMaps.keys S → a ∈ LMonoTy.freeVars mty → TContext.isFresh (T := T) a Γ) →
        HasType C Γ e (.forAll [] mty) →
        HasType C Γ e (.forAll [] (LMonoTy.subst S mty)) from
      h_gen (relevantKeys S mty) mty rfl h_fresh h
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro mty h_rk h_fresh_mty h_ty
      by_cases h_any : ∃ a, a ∈ HMaps.keys S ∧ a ∈ LMonoTy.freeVars mty
      · obtain ⟨a, ha_key, ha_fv⟩ := h_any
        obtain ⟨t, h_find⟩ := HMaps.find?_of_mem_keys S a ha_key
        have h_a_fresh : TContext.isFresh a Γ := h_fresh_mty a ha_key ha_fv
        have h1 : HasType C Γ e (.forAll [] (LMonoTy.subst (Subst.singleton a t) mty)) :=
          HasType_subst_fresh C Γ e mty a t h_ty h_a_fresh
        have h_fresh_inner : ∀ b, b ∈ HMaps.keys S →
            b ∈ LMonoTy.freeVars (LMonoTy.subst (Subst.singleton a t) mty) →
            TContext.isFresh (T := T) b Γ := by
          intro b hb_key hb_fv
          have hb_not_fvS : b ∉ Subst.freeVars S := by
            have h_wf' := h_wf; simp [SubstWF, List.all_eq_true] at h_wf'
            exact h_wf' b hb_key
          have hb_not_t : b ∉ LMonoTy.freeVars t :=
            fun h => hb_not_fvS (Subst.freeVars_of_find_subset S h_find h)
          have hb_in_mty := LMonoTy.freeVars_subst_single_mem a t mty b hb_fv hb_not_t
          exact h_fresh_mty b hb_key hb_in_mty
        have h_decrease := relevantKeys_decrease S a t mty h_find h_wf ha_fv
        have h2 : HasType C Γ e
            (.forAll [] (LMonoTy.subst S (LMonoTy.subst (Subst.singleton a t) mty))) :=
          ih (relevantKeys S (LMonoTy.subst (Subst.singleton a t) mty))
            (h_rk ▸ h_decrease) (LMonoTy.subst (Subst.singleton a t) mty) rfl h_fresh_inner h1
        rwa [LMonoTy.subst_absorbs_single S a t mty h_find h_wf] at h2
      · have h_no_key : ∀ x, x ∈ LMonoTy.freeVars mty → x ∉ HMaps.keys S :=
          fun x hx hxk => h_any ⟨x, hxk, hx⟩
        rw [LMonoTy.subst_no_relevant_keys S mty h_no_key]; exact h_ty

/--
Two typing contexts are *alias-equivalent* (w.r.t. `aliases`) when every monotype
binding in `Γ` is matched, at the same key, by a monotype binding in `Γ'` that is
alias-equivalent to it. The direction `AliasEquiv aliases mty' mty` (Γ'-type ↝
Γ-type) is the one needed to transport a judgment from `Γ` to `Γ'` via `talias`. -/
def TContextAliasEquiv (aliases : List TypeAlias) (Γ Γ' : TContext T.IDMeta) : Prop :=
  ∀ x ty, Γ.types.find? x = some ty →
    ∃ mty mty', ty = .forAll [] mty ∧
      Γ'.types.find? x = some (.forAll [] mty') ∧
      _root_.Lambda.AliasEquiv aliases mty' mty


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
  elim_err h
  rename_i relS_core h_core
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

/--
Unification produces a substitution that makes the two types equal.
-/
theorem unify_makes_equal (ty1 ty2 : LMonoTy) (S_old S_new : SubstInfo)
    (h : Constraints.unify [(ty1, ty2)] S_old = .ok S_new) :
    LMonoTy.subst S_new.subst ty1 = LMonoTy.subst S_new.subst ty2 := by
  exact Constraints.unify_sound [(ty1, ty2)] S_old S_new h (ty1, ty2) (by simp)

/--
Multi-constraint unification: if `Constraints.unify [(ty1, ty2), (ty3, ty4)] S_old = .ok S_new`,
then both pairs are made equal under `S_new.subst`.
-/
theorem unify_makes_equal₂ (ty1 ty2 ty3 ty4 : LMonoTy) (S_old S_new : SubstInfo)
    (h : Constraints.unify [(ty1, ty2), (ty3, ty4)] S_old = .ok S_new) :
    LMonoTy.subst S_new.subst ty1 = LMonoTy.subst S_new.subst ty2 ∧
    LMonoTy.subst S_new.subst ty3 = LMonoTy.subst S_new.subst ty4 := by
  have h_sound := Constraints.unify_sound [(ty1, ty2), (ty3, ty4)] S_old S_new h
  exact ⟨h_sound (ty1, ty2) (by simp), h_sound (ty3, ty4) (by simp)⟩

/-- Key-inclusion for `Constraints.unify`: output keys come from input keys,
    constraint free vars, or input value free vars. -/
theorem Constraints.unify_keys_incl
    {cs : Constraints} {S S' : SubstInfo}
    (h_unify : Constraints.unify cs S = .ok S') :
    ∀ k, k ∈ HMaps.keys S'.subst →
      k ∈ HMaps.keys S.subst ∨ k ∈ Constraints.freeVars cs ∨ k ∈ Subst.freeVars S.subst := by
  simp only [Constraints.unify, bind, Except.bind] at h_unify
  split at h_unify
  · simp at h_unify
  · rename_i relS h_core
    simp only [Except.ok.injEq] at h_unify; subst h_unify
    exact (Constraints.unifyCore_sound cs S relS h_core).keys_incl

/-- **Predicate transfer through `Constraints.unify`.** If a predicate `P` on type
    variables holds for every free variable of the constraints and every key/range
    variable of the input substitution, then it holds for every key/range variable of
    the unify result. Used to thread the "every type variable avoids `func.typeArgs`"
    invariant through the body's return-type unification (`v_unify`). -/
theorem Constraints.unify_pred
    {cs : Constraints} {S S' : SubstInfo}
    (h_unify : Constraints.unify cs S = .ok S')
    (P : TyIdentifier → Prop)
    (h_cs : ∀ v, v ∈ Constraints.freeVars cs → P v)
    (h_Sk : ∀ v, v ∈ HMaps.keys S.subst → P v)
    (h_Sv : ∀ v, v ∈ Subst.freeVars S.subst → P v) :
    (∀ v, v ∈ HMaps.keys S'.subst → P v) ∧ (∀ v, v ∈ Subst.freeVars S'.subst → P v) := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rcases Constraints.unify_keys_incl h_unify v hv with h | h | h
    · exact h_Sk v h
    · exact h_cs v h
    · exact h_Sv v h
  · have h_incl : Subst.freeVars S'.subst ⊆ Constraints.freeVars cs ++ Subst.freeVars S.subst := by
      simp only [Constraints.unify, Bind.bind, Except.bind] at h_unify
      elim_err h_unify
      rename_i relS h_core
      simp at h_unify; subst h_unify
      exact relS.goodSubset
    rcases List.mem_append.mp (h_incl hv) with h | h
    · exact h_cs v h
    · exact h_Sv v h

/-- Free variables of a substitution `[zip ids (map ftvar freshtvs)]` are a
    subset of `freshtvs`. -/
private theorem Subst.freeVars_zip_ftvar (ids freshtvs : List TyIdentifier)
    (h_len : freshtvs.length = ids.length) :
    Subst.freeVars (Strata.Util.HMaps.ofScopes
      [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) ⊆ freshtvs := by
  intro tv h_tv
  simp only [Subst.freeVars, Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil,
    Strata.Util.HMaps.values, List.append_nil, List.mem_flatMap] at h_tv
  obtain ⟨mty, h_mty_mem, h_tv_fv⟩ := h_tv
  have h_mty_in := HMap.mem_values_ofList _ mty h_mty_mem
  rw [List.map_snd_zip (by simp [h_len])] at h_mty_in
  obtain ⟨tv', h_tv'_mem, h_eq⟩ := List.mem_map.mp h_mty_in
  subst h_eq
  simp only [LMonoTy.freeVars, List.mem_singleton] at h_tv_fv
  subst h_tv_fv; exact h_tv'_mem

/-- If `tv ∈ ids`, then `HMaps.find? (ofScopes [zip ids (map ftvar freshtvs)]) tv`
    returns some `ftvar ftv` where `ftv ∈ freshtvs`. -/
private theorem HMaps.find?_zip_ftvar_mem (ids : List TyIdentifier)
    (freshtvs : List TyIdentifier)
    (h_len : freshtvs.length = ids.length)
    (tv : TyIdentifier) (h_mem : tv ∈ ids) :
    ∃ ftv, ftv ∈ freshtvs ∧
      HMaps.find? (Strata.Util.HMaps.ofScopes
        [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) tv =
        some (.ftvar ftv) := by
  -- single scope: HMaps.find? [m] tv = HMap.find? m tv
  have hsingle : HMaps.find? (Strata.Util.HMaps.ofScopes
        [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) tv
      = HMap.find? (HMap.ofList (List.zip ids (List.map LMonoTy.ftvar freshtvs))) tv := by
    simp only [Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil, HMaps.find?]
    cases HMap.find? (HMap.ofList (List.zip ids (List.map LMonoTy.ftvar freshtvs))) tv <;> rfl
  rw [hsingle]
  -- key tv is present (tv ∈ ids = key list of the zip)
  have h_keys : tv ∈ (List.zip ids (List.map LMonoTy.ftvar freshtvs)).map Prod.fst := by
    rw [List.map_fst_zip (by simp [h_len])]; exact h_mem
  obtain ⟨w, hw⟩ := HMap.find?_ofList_of_mem_keys _ tv h_keys
  -- whatever value w is found, it is a value of the map, hence a `.ftvar` of a freshtv
  have hw_val := HMap.find?_mem_values _ hw
  have hw_in := HMap.mem_values_ofList _ w hw_val
  rw [List.map_snd_zip (by simp [h_len])] at hw_in
  obtain ⟨ftv, hftv_mem, hftv_eq⟩ := List.mem_map.mp hw_in
  exact ⟨ftv, hftv_mem, by rw [hw, ← hftv_eq]⟩

/-- Free variables of `instantiateEnv` output are either original free variables
    or fresh type variables generated by `genTyVars`. In either case, if the
    original free vars are fresh in the context, then all output free vars are
    fresh in the context. -/
theorem LMonoTys.instantiateEnv_freeVars_fresh {T : LExprParams}
    [DecidableEq T.IDMeta] [ToFormat T.IDMeta] [Hashable T.IDMeta]
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
    split at h_inst; any_goals (solve | simp at h_inst | contradiction)
    rename_i v1 h_gen
    obtain ⟨freshtvs, genEnv1⟩ := v1; simp at h_inst h_gen
    obtain ⟨h_eq, _⟩ := h_inst; rw [← h_eq] at h_tv
    have h_subset := LMonoTys.freeVars_of_subst_subset
      (Strata.Util.HMaps.ofScopes [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) mtys h_tv
    rw [List.mem_append] at h_subset
    rcases h_subset with h_orig | h_subst_fv
    · exact h_orig_fresh tv h_orig
    · have h_len : freshtvs.length = ids.length :=
        TGenEnv.genTyVars_length _ _ _ _ h_gen
      have h_in_fresh := Subst.freeVars_zip_ftvar ids freshtvs h_len h_subst_fv
      exact TGenEnv.genTyVars_allFresh ids.length _ freshtvs genEnv1 h_gen tv h_in_fresh

/-- Substituting `[zip ids (map ftvar freshtvs)]` into a monotype whose free
    variables are all in `ids` produces a type whose free variables are all in
    `freshtvs`. -/
private theorem LMonoTy.freeVars_subst_closed
    (ids : List TyIdentifier) (freshtvs : List TyIdentifier)
    (h_len : freshtvs.length = ids.length) (mty : LMonoTy)
    (h_closed : ∀ tv, tv ∈ LMonoTy.freeVars mty → tv ∈ ids) :
    ∀ tv, tv ∈ LMonoTy.freeVars
        (LMonoTy.subst (Strata.Util.HMaps.ofScopes
          [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) mty) →
      tv ∈ freshtvs := by
  intro tv h_tv
  induction mty with
  | ftvar x =>
    simp [LMonoTy.freeVars] at h_closed
    obtain ⟨ftv', hm, hf⟩ := HMaps.find?_zip_ftvar_mem ids freshtvs h_len x h_closed
    rw [LMonoTy.subst_unfold] at h_tv
    simp only [hf, LMonoTy.freeVars, List.mem_singleton] at h_tv
    subst h_tv; exact hm
  | bitvec n =>
    rw [LMonoTy.subst_unfold] at h_tv
    simp [LMonoTy.freeVars] at h_tv
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map] at h_tv
    simp only [LMonoTy.freeVars] at h_tv h_closed ⊢
    induction args with
    | nil => simp [LMonoTys.freeVars] at h_tv
    | cons a arest arih =>
      simp only [List.map_cons, LMonoTys.freeVars, List.mem_append] at h_tv h_closed
      rcases h_tv with h_a | h_rest
      · exact ih a List.mem_cons_self
          (fun tv' h' => h_closed tv' (Or.inl h')) h_a
      · exact arih
          (fun a' h_mem => ih a' (List.mem_cons_of_mem a h_mem))
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
        (LMonoTys.subst (Strata.Util.HMaps.ofScopes
          [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) mtys) →
      tv ∈ freshtvs := by
  intro tv h_tv
  rw [LMonoTys.subst_eq_map] at h_tv
  induction mtys with
  | nil => simp [LMonoTys.freeVars] at h_tv
  | cons mty mrest ih =>
    simp only [List.map_cons, LMonoTys.freeVars, List.mem_append] at h_tv h_closed
    rcases h_tv with h_mty | h_rest
    · exact LMonoTy.freeVars_subst_closed ids freshtvs h_len mty
        (fun tv' h' => h_closed tv' (Or.inl h')) tv h_mty
    · exact ih (fun tv' h' => h_closed tv' (Or.inr h')) h_rest

/-! ### `openVars`/`subst` composition geometry (representation-independent, list-based) -/

mutual
/-- If a type variable is free in `openVars vars vals body` and `body`'s free
    vars are all in `vars`, then it is free in `vals`. -/
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

/-- Non-dropping predicate for an alias list: WF (freeVars ⊆ typeArgs) AND the
    reverse (typeArgs ⊆ freeVars), i.e. every declared arg actually occurs. This
    is exactly what `TEnv.addTypeAlias`'s two guards enforce. -/
def AliasesNonDropping (aliases : List TypeAlias) : Prop :=
  ∀ a ∈ aliases, a.WF ∧ (a.typeArgs ⊆ a.type.freeVars)

/-- `find?` over a nodup-keyed zip returns exactly the paired value. -/
private theorem find_zip_of_mem_nodup
    (vars : List TyIdentifier) (vals : LMonoTys)
    (v : TyIdentifier) (val : LMonoTy)
    (h_mem : (v, val) ∈ List.zip vars vals) (h_nodup : vars.Nodup) :
    (List.zip vars vals).find? (fun p => p.1 == v) = some (v, val) := by
  induction vars generalizing vals with
  | nil => simp only [List.zip_nil_left, List.not_mem_nil] at h_mem
  | cons hv hvs ih =>
    cases vals with
    | nil => simp only [List.zip_nil_right, List.not_mem_nil] at h_mem
    | cons vl vls =>
      rw [List.zip_cons_cons] at h_mem ⊢
      rw [List.find?_cons]
      have h_nd_tail : hv ∉ hvs ∧ hvs.Nodup := List.nodup_cons.mp h_nodup
      by_cases h_eq : hv = v
      · have h_vl : vl = val := by
          rcases List.mem_cons.mp h_mem with h_head | h_tail
          · exact ((Prod.mk.injEq .. ▸ h_head).2).symm
          · have h_v_hvs : v ∈ hvs := (List.of_mem_zip h_tail).1
            exact absurd (h_eq ▸ h_v_hvs) h_nd_tail.1
        simp only [h_eq, beq_self_eq_true, h_vl]
      · have h_beq : (hv == v) = false := by
          simp only [beq_eq_false_iff_ne]; exact h_eq
        simp only [h_beq]
        have h_tail : (v, val) ∈ List.zip hvs vls := by
          rcases List.mem_cons.mp h_mem with h_head | h_t
          · exact absurd (Prod.mk.injEq .. ▸ h_head).1.symm h_eq
          · exact h_t
        exact ih vls h_tail h_nd_tail.2

mutual
/-- Core: if body var `v` is paired with `val` in `zip vars vals` (nodup keys),
    then every free var of `val` appears in `openVars vars vals body`, provided
    `v` occurs in `body`. -/
private theorem openVars_freeVars_superset_core
    (vars : List TyIdentifier) (vals : LMonoTys)
    (v : TyIdentifier) (val : LMonoTy)
    (h_pair : (v, val) ∈ List.zip vars vals) (h_nodup : vars.Nodup)
    (body : LMonoTy) (h_v_body : v ∈ LMonoTy.freeVars body) :
    ∀ tv, tv ∈ LMonoTy.freeVars val →
      tv ∈ LMonoTy.freeVars (LMonoTy.openVars vars vals body) := by
  match body with
  | .ftvar x =>
    intro tv htv
    have h_x : x = v := by
      simp only [LMonoTy.freeVars, List.mem_singleton] at h_v_body
      exact h_v_body.symm
    subst h_x
    simp only [LMonoTy.openVars, find_zip_of_mem_nodup vars vals x val h_pair h_nodup]
    exact htv
  | .bitvec _ =>
    simp only [LMonoTy.freeVars, List.not_mem_nil] at h_v_body
  | .tcons nm args =>
    intro tv htv
    simp only [LMonoTy.openVars, LMonoTy.freeVars] at h_v_body ⊢
    exact openVarsList_freeVars_superset_core vars vals v val h_pair h_nodup args h_v_body tv htv

/-- List version of `openVars_freeVars_superset_core`. -/
private theorem openVarsList_freeVars_superset_core
    (vars : List TyIdentifier) (vals : LMonoTys)
    (v : TyIdentifier) (val : LMonoTy)
    (h_pair : (v, val) ∈ List.zip vars vals) (h_nodup : vars.Nodup)
    (bodies : LMonoTys) (h_v_body : v ∈ LMonoTys.freeVars bodies) :
    ∀ tv, tv ∈ LMonoTy.freeVars val →
      tv ∈ LMonoTys.freeVars (LMonoTys.openVars vars vals bodies) := by
  match bodies with
  | [] => simp only [LMonoTys.freeVars, List.not_mem_nil] at h_v_body
  | hd :: tl =>
    intro tv htv
    simp only [LMonoTys.openVars, LMonoTys.freeVars_of_cons, List.mem_append] at h_v_body ⊢
    cases h_v_body with
    | inl h => exact Or.inl (openVars_freeVars_superset_core vars vals v val h_pair h_nodup hd h tv htv)
    | inr h => exact Or.inr (openVarsList_freeVars_superset_core vars vals v val h_pair h_nodup tl h tv htv)
end

/-- Every free var of `vals` lives in some `val` paired with a `var`. -/
private theorem mem_freeVars_vals_exists_pair
    (vars : List TyIdentifier) (vals : LMonoTys)
    (h_len : vars.length = vals.length)
    (tv : TyIdentifier) (h_tv : tv ∈ LMonoTys.freeVars vals) :
    ∃ v val, (v, val) ∈ List.zip vars vals ∧ tv ∈ LMonoTy.freeVars val := by
  induction vals generalizing vars with
  | nil => simp only [LMonoTys.freeVars, List.not_mem_nil] at h_tv
  | cons vl vls ih =>
    cases vars with
    | nil => simp only [List.length_nil, List.length_cons] at h_len; omega
    | cons hv hvs =>
      simp only [LMonoTys.freeVars_of_cons, List.mem_append] at h_tv
      cases h_tv with
      | inl h =>
        refine ⟨hv, vl, ?_, h⟩
        rw [List.zip_cons_cons]; exact List.mem_cons_self ..
      | inr h =>
        have h_len' : hvs.length = vls.length := by
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len; exact h_len
        obtain ⟨v, val, h_pair, h_in⟩ := ih hvs h_len' h
        refine ⟨v, val, ?_, h_in⟩
        rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ h_pair

/-- REVERSE of `openVars_freeVars_subset`: when every var in `vars` occurs in
    `body` (non-dropping) and `vars` is nodup and lengths match, every free var of
    `vals` shows up in `openVars vars vals body`. -/
theorem openVars_freeVars_superset
    (vars : List TyIdentifier) (vals : LMonoTys) (body : LMonoTy)
    (h_nd : ∀ v, v ∈ vars → v ∈ LMonoTy.freeVars body)
    (h_nodup : vars.Nodup)
    (h_len : vars.length = vals.length) :
    ∀ tv, tv ∈ LMonoTys.freeVars vals →
      tv ∈ LMonoTy.freeVars (LMonoTy.openVars vars vals body) := by
  intro tv htv
  obtain ⟨v, val, h_pair, h_in⟩ := mem_freeVars_vals_exists_pair vars vals h_len tv htv
  have h_v_vars : v ∈ vars := (List.of_mem_zip h_pair).1
  have h_v_body : v ∈ LMonoTy.freeVars body := h_nd v h_v_vars
  exact openVars_freeVars_superset_core vars vals v val h_pair h_nodup body h_v_body tv h_in

/-- `freeVars (tcons name args) = freeVars (expand alias args)` when the alias is
    non-dropping (WF + reverse). Combines subset (⊆, WF) and superset (⊇, non-dropping). -/
private theorem expand_preserves_freeVars
    (alias : TypeAlias) (h_wf : alias.WF)
    (h_ndrop : alias.typeArgs ⊆ alias.type.freeVars)
    (args : LMonoTys) (h_len : alias.typeArgs.length = args.length) :
    ∀ v, v ∈ LMonoTys.freeVars args ↔ v ∈ LMonoTy.freeVars (alias.expand args) := by
  intro v
  simp only [TypeAlias.expand]
  constructor
  · intro hv
    exact openVars_freeVars_superset alias.typeArgs args alias.type
      (fun x hx => h_ndrop hx) h_wf.typeArgs_nodup h_len v hv
  · intro hv
    exact openVars_freeVars_subset alias.typeArgs args alias.type
      h_wf.fvs_closed h_len v hv

mutual
/-- **`AliasEquiv` preserves free type variables** when all aliases are non-dropping
    (WF + every declared arg actually occurs in the body — enforced by
    `TEnv.addTypeAlias`'s guards). -/
theorem AliasEquiv_preserves_freeVars
    (aliases : List TypeAlias)
    (h_ali : AliasesNonDropping aliases)
    (mty mty' : LMonoTy)
    (h : AliasEquiv aliases mty mty') :
    ∀ v, v ∈ LMonoTy.freeVars mty ↔ v ∈ LMonoTy.freeVars mty' := by
  match h with
  | .refl => intro v; exact Iff.rfl
  | @AliasEquiv.expand _ name args mty h_exp =>
    obtain ⟨alias, h_mem, h_name, h_len, h_expand⟩ := h_exp
    subst h_expand
    obtain ⟨h_wf, h_ndrop⟩ := h_ali alias h_mem
    intro v
    simp only [LMonoTy.freeVars]
    exact expand_preserves_freeVars alias h_wf h_ndrop args h_len v
  | @AliasEquiv.collapse _ name args mty h_exp =>
    obtain ⟨alias, h_mem, h_name, h_len, h_expand⟩ := h_exp
    subst h_expand
    obtain ⟨h_wf, h_ndrop⟩ := h_ali alias h_mem
    intro v
    simp only [LMonoTy.freeVars]
    exact (expand_preserves_freeVars alias h_wf h_ndrop args h_len v).symm
  | .cong_tcons h_args =>
    intro v
    simp only [LMonoTy.freeVars]
    exact AliasEquivList_preserves_freeVars aliases h_ali _ _ h_args v
  | .trans h1 h2 =>
    intro v
    exact Iff.trans (AliasEquiv_preserves_freeVars aliases h_ali _ _ h1 v)
      (AliasEquiv_preserves_freeVars aliases h_ali _ _ h2 v)

/-- List form of `AliasEquiv_preserves_freeVars`. -/
theorem AliasEquivList_preserves_freeVars
    (aliases : List TypeAlias)
    (h_ali : AliasesNonDropping aliases)
    (as bs : LMonoTys)
    (h : AliasEquivList aliases as bs) :
    ∀ v, v ∈ LMonoTys.freeVars as ↔ v ∈ LMonoTys.freeVars bs := by
  match h with
  | .nil => intro v; exact Iff.rfl
  | .cons h_hd h_tl =>
    intro v
    simp only [LMonoTys.freeVars_of_cons, List.mem_append]
    exact or_congr (AliasEquiv_preserves_freeVars aliases h_ali _ _ h_hd v)
      (AliasEquivList_preserves_freeVars aliases h_ali _ _ h_tl v)
end

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    elim_err h
    rename_i v1 h_args
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
    elim_err h
    rename_i v1 h_args
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
    elim_err h
    rename_i v1 h_hd
    obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    elim_err h
    rename_i v2 h_tl
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
    elim_err h
    rename_i v1 h_hd
    obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    elim_err h
    rename_i v2 h_tl
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
    elim_err h
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
    elim_err h
    · rename_i v1 h_hd
      obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
      elim_err h
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


omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    elim_err h
    rename_i v1 h_args
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
    elim_err h
    rename_i v1 h_hd
    obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    elim_err h
    rename_i v2 h_tl
    obtain ⟨mrest', Env2⟩ := v2
    simp at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
    exact Subst.absorbs_trans
      Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
      (LMonoTy.resolveAliases_absorbs mty Env mty' Env1 h_hd)
      (LMonoTys.resolveAliases_absorbs mrest Env1 mrest' Env2 h_tl)
end

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `LTy.resolveAliases` produces a substitution that absorbs the input. -/
private theorem LTy_resolveAliases_absorbs
    (ty : LTy) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.resolveAliases ty Env = .ok (mty, Env')) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_inst
  obtain ⟨mty0, genEnv'⟩ := v1; simp at h h_inst
  -- After ty.instantiate, only genEnv changes; stateSubstInfo is preserved.
  have h_subst_eq : ({Env with genEnv := genEnv'} : TEnv T.IDMeta).stateSubstInfo =
      Env.stateSubstInfo := rfl
  exact h_subst_eq ▸ LMonoTy.resolveAliases_absorbs mty0 {Env with genEnv := genEnv'} mty Env' h

/-- Helper: extract a `Constraints.unify` hypothesis from a `mapError` wrapper. -/
theorem unify_of_mapError {constraints : Constraints} {S : SubstInfo} {S' : SubstInfo}
    (h : (Constraints.unify constraints S).mapError format = .ok S') :
    Constraints.unify constraints S = .ok S' := by
  revert h
  generalize Constraints.unify constraints S = res
  intro h_me; match res, h_me with
  | .ok val, h_me => simp [Except.mapError] at h_me; rw [h_me]
  | .error _, h_me => simp [Except.mapError] at h_me

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `LTy.instantiateWithCheck` produces a substitution that absorbs the input. -/
private theorem LTy_instantiateWithCheck_absorbs
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env')) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_res
  obtain ⟨mty0, Env1⟩ := v1
  dsimp at h h_res
  -- h contains `if !checkNoFutureGenVars then error else if isInstanceOfKnownType then ... else ...`
  elim_errs h
  -- true branch: return (mty0, Env1)
  simp at h
  obtain ⟨_, h2⟩ := h; rw [← h2]
  exact LTy_resolveAliases_absorbs ty Env mty0 Env1 h_res

omit [ToString
  T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `LMonoTy.instantiateWithCheck` produces a substitution that absorbs the input. -/
private theorem LMonoTy_instantiateWithCheck_absorbs
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (mty, Env')) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  simp only [LMonoTy.instantiateWithCheck] at h
  elim_err h
  rename_i instTypes Env1 h_inst
  simp [Bind.bind, Except.bind] at h
  elim_err h
  rename_i v2 h_res
  obtain ⟨mtyi, Env2⟩ := v2
  dsimp at h h_res
  elim_errs h
  -- true branch: return (mtyi, Env2)
  simp at h
  obtain ⟨_, h2⟩ := h; rw [← h2]
  -- instantiateEnv only changes genEnv
  have h_subst_eq : Env1.stateSubstInfo = Env.stateSubstInfo := by
    simp [LMonoTys.instantiateEnv] at h_inst
    elim_err h_inst
    simp at h_inst; obtain ⟨_, h_env⟩ := h_inst; rw [← h_env]
  rw [← h_subst_eq]
  exact LMonoTy.resolveAliases_absorbs _ Env1 mtyi Env2 h_res


omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
theorem LMonoTy.subst_remove_not_fv (S : Subst) (k : TyIdentifier) (mty : LMonoTy)
    (h_nfv : k ∉ LMonoTy.freeVars mty) :
    LMonoTy.subst (HMaps.remove S k) mty = LMonoTy.subst S mty := by
  apply LMonoTy.subst_ext
  intro x hx
  exact HMaps.find?_remove_ne S k x (by simp [bne]; exact fun h_eq => h_nfv (h_eq ▸ hx))

/-- Removing a fresh key from the outer substitution preserves absorption.
    This requires that the key is not in the inner substitution (neither as
    a key nor in any value). -/
theorem Subst.absorbs_of_remove (S_outer S_inner : Subst) (k : TyIdentifier)
    (h_abs : Subst.absorbs S_outer S_inner)
    (h_not_key : HMaps.find? S_inner k = none)
    (h_not_fv : ∀ a t, HMaps.find? S_inner a = some t → k ∉ LMonoTy.freeVars t) :
    Subst.absorbs (HMaps.remove S_outer k) S_inner := by
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
  ∀ v, (v ∈ HMaps.keys S.subst ∨ v ∈ Subst.freeVars S.subst) →
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

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Extract `EnvFreshForGen` from the combined `TEnvWF` invariant. -/
theorem TEnvWF.toEnvFreshForGen {Env : TEnv T.IDMeta} (h : TEnvWF Env) : EnvFreshForGen Env :=
  ⟨h.substFreshForGen, h.ctxFreshForGen⟩

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `TEnvWF` is preserved by `updateSubst` provided the new substitution is itself
    gen-fresh: `updateSubst` only touches `stateSubstInfo`, so every other `TEnvWF`
    field (which depends only on `.context`/`.genEnv`) is unchanged, and the lone
    substitution field is supplied directly. The freshness hypothesis is discharged
    by `unify_preserves_SubstFreshForGen` at the use site. -/
theorem TEnvWF.of_updateSubst {Env : TEnv T.IDMeta} {S : SubstInfo}
    (h : TEnvWF Env) (h_sf : SubstFreshForGen S Env.genEnv.genState) :
    TEnvWF (Env.updateSubst S) :=
  ⟨h.aliasesWF, h_sf, h.ctxFreshForGen, h.boundVarsNodup, h.boundVarsFresh⟩

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `ContextFreshForGen` is monotone in the counter. -/
private theorem ContextFreshForGen.mono (Γ : TContext T.IDMeta) (s s' : TState)
    (h : ContextFreshForGen Γ s) (h_le : s.tyGen ≤ s'.tyGen) :
    ContextFreshForGen Γ s' := by
  intro v hv n hn; exact h v hv n (Nat.le_trans h_le hn)

/-- `SubstFreshForGen` is monotone: a larger counter is strictly more permissive. -/
private theorem SubstFreshForGen.mono (S : SubstInfo) (s s' : TState)
    (h : SubstFreshForGen S s) (h_le : s.tyGen ≤ s'.tyGen) :
    SubstFreshForGen S s' := by
  intro v hv n hn; exact h v hv n (Nat.le_trans h_le hn)

/-- Applying a gen-fresh substitution to a gen-fresh monotype yields a gen-fresh
    monotype: every free var of `subst S mty` is either a free var of `mty`
    (fresh by `h_mty`) or comes from a substitution value (fresh by `h_S`). This
    is the reusable kernel behind the per-case output-type-freshness arguments in
    `resolveAux_properties_aux` (the `app`/`eq`/`ite` cases). -/
theorem freeVars_subst_genFresh
    (S : SubstInfo) (mty : LMonoTy) (state : TState)
    (h_S : SubstFreshForGen S state)
    (h_mty : ∀ v, v ∈ LMonoTy.freeVars mty →
      ∀ n, n ≥ state.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    ∀ v, v ∈ LMonoTy.freeVars (LMonoTy.subst S.subst mty) →
      ∀ n, n ≥ state.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  intro v hv n hn
  rcases List.mem_append.mp (LMonoTy.freeVars_of_subst_subset S.subst mty hv) with h | h
  · exact h_mty v h n hn
  · exact h_S v (Or.inr h) n hn

/-- List version of `freeVars_subst_genFresh`: applying a gen-fresh substitution
    to a list of gen-fresh monotypes yields gen-fresh outputs. -/
theorem LMonoTys.freeVars_subst_genFresh
    (S : SubstInfo) (mtys : LMonoTys) (state : TState)
    (h_S : SubstFreshForGen S state)
    (h_mtys : ∀ v, v ∈ LMonoTys.freeVars mtys →
      ∀ n, n ≥ state.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    ∀ v, v ∈ LMonoTys.freeVars (LMonoTys.subst S.subst mtys) →
      ∀ n, n ≥ state.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  intro v hv n hn
  rcases List.mem_append.mp (LMonoTys.freeVars_of_subst_subset S.subst mtys hv) with h | h
  · exact h_mtys v h n hn
  · exact h_S v (Or.inr h) n hn

end Proofs

end LExpr

section TContextEquiv
open LExpr
open Strata.Util (HMap HMaps)
/-! ### `TContext.Equiv` layer + WF/typing transports

Lifts the scope-stack `HMaps.Equiv` to contexts (stack + identical aliases) and
proves that every `resolveAux` invariant respects it: the find?-based predicates
(`AliasesWF`, `isFresh`, `boundVarsFresh`/`Nodup`, `HasType`) and the
`values`-based `ContextFreshForGen`. -/

variable {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]

/-- Two contexts are equivalent when their scope stacks are `HMaps.Equiv` and
    they carry identical aliases. -/
def TContext.Equiv (Γ Γ' : TContext T.IDMeta) : Prop :=
  HMaps.Equiv Γ.types Γ'.types ∧ Γ.aliases = Γ'.aliases

@[refl] theorem TContext.Equiv.refl (Γ : TContext T.IDMeta) : Γ.Equiv Γ :=
  ⟨HMaps.Equiv.refl _, rfl⟩

theorem TContext.Equiv.symm {Γ Γ' : TContext T.IDMeta} (h : Γ.Equiv Γ') : Γ'.Equiv Γ :=
  ⟨h.1.symm, h.2.symm⟩

theorem TContext.Equiv.trans {Γ Γ' Γ'' : TContext T.IDMeta}
    (h1 : Γ.Equiv Γ') (h2 : Γ'.Equiv Γ'') : Γ.Equiv Γ'' :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- An equality of contexts is in particular an equivalence. -/
theorem TContext.Equiv.of_eq {Γ Γ' : TContext T.IDMeta} (h : Γ = Γ') : Γ.Equiv Γ' :=
  h ▸ .refl Γ

/-- Pointwise `find?` agreement (workhorse for the find?-based predicates). -/
theorem TContext.Equiv.find? {Γ Γ' : TContext T.IDMeta} (h : Γ.Equiv Γ') (k : T.Identifier) :
    Γ.types.find? k = Γ'.types.find? k := h.1.find? k

/-- `Γ' ≠ empty stack` when `Γ` isn't. -/
theorem TContext.Equiv.types_ne_nil {Γ Γ' : TContext T.IDMeta} (h : Γ.Equiv Γ')
    (h_ne : Γ.types ≠ []) : Γ'.types ≠ [] := h.1.ne_nil h_ne

/-- `TContext.Equiv` preserves `knownTypeVars` membership (needs the
    values-level strength of `HMaps.Equiv`). -/
theorem TContext.Equiv.mem_knownTypeVars {Γ Γ' : TContext T.IDMeta} (h : Γ.Equiv Γ')
    (tx : TyIdentifier) : tx ∈ TContext.knownTypeVars Γ ↔ tx ∈ TContext.knownTypeVars Γ' := by
  simp only [TContext.knownTypeVars, List.mem_flatMap]
  constructor
  · rintro ⟨ty, h_mem, h_fv⟩; exact ⟨ty, (h.1.mem_values ty).mp h_mem, h_fv⟩
  · rintro ⟨ty, h_mem, h_fv⟩; exact ⟨ty, (h.1.mem_values ty).mpr h_mem, h_fv⟩

/-- `AliasesWF` transports across `TContext.Equiv` (depends only on aliases). -/
theorem TContext.Equiv.aliasesWF {Γ Γ' : TContext T.IDMeta} (h : Γ.Equiv Γ')
    (h_aw : TContext.AliasesWF Γ) : TContext.AliasesWF Γ' := by
  intro a ha; exact h_aw a (h.2 ▸ ha)

/-- `ContextFreshForGen` transports across `TContext.Equiv`. -/
theorem TContext.Equiv.ctxFreshForGen {Γ Γ' : TContext T.IDMeta} (h : Γ.Equiv Γ')
    {s : TState} (h_cf : ContextFreshForGen Γ s) : ContextFreshForGen Γ' s := by
  intro v hv n hn; exact h_cf v ((h.mem_knownTypeVars v).mpr hv) n hn

/-- `isFresh` transports across `TContext.Equiv`. -/
theorem TContext.Equiv.isFresh {Γ Γ' : TContext T.IDMeta} (h : Γ.Equiv Γ')
    {tx : TyIdentifier} (h_fr : TContext.isFresh tx Γ) : TContext.isFresh tx Γ' := by
  intro x ty h_find; exact h_fr x ty ((h.find? x).trans h_find)

/-- The `boundVarsFresh` invariant transports across `TContext.Equiv`. -/
theorem TContext.Equiv.boundVarsFresh {Γ Γ' : TContext T.IDMeta} (h : Γ.Equiv Γ')
    {s : TState}
    (h_bf : ∀ y ty, Γ.types.find? y = some ty →
      ∀ v, v ∈ LTy.boundVars ty → ∀ n, n ≥ s.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    ∀ y ty, Γ'.types.find? y = some ty →
      ∀ v, v ∈ LTy.boundVars ty → ∀ n, n ≥ s.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  intro y ty h_find v hv n hn; exact h_bf y ty ((h.find? y).trans h_find) v hv n hn

/-- The `boundVarsNodup` invariant transports across `TContext.Equiv`. -/
theorem TContext.Equiv.boundVarsNodup {Γ Γ' : TContext T.IDMeta} (h : Γ.Equiv Γ')
    (h_nd : ∀ y ty, Γ.types.find? y = some ty → (LTy.boundVars ty).Nodup) :
    ∀ y ty, Γ'.types.find? y = some ty → (LTy.boundVars ty).Nodup := by
  intro y ty h_find; exact h_nd y ty ((h.find? y).trans h_find)

/-- `insert` congruence at the `TContext.Equiv` level (for `HasType`'s binders). -/
theorem TContext.Equiv.insert {Γ Γ' : TContext T.IDMeta} (h : Γ.Equiv Γ')
    (x : T.Identifier) (t : LTy) :
    ({ Γ with types := Γ.types.insert x t } : TContext T.IDMeta).Equiv
      { Γ' with types := Γ'.types.insert x t } :=
  ⟨HMaps.insert_equiv h.1 x t, h.2⟩

/-- `TContext.subst` respects context equivalence (both `types` via `mapValues`
    and `aliases`, which `subst` leaves unchanged). Needed to transport
    `HasType C (Γ.subst S) …` across `Env'.context.Equiv Env.context`. -/
theorem TContext.Equiv.subst {Γ Γ' : TContext T.IDMeta} (h : Γ.Equiv Γ')
    (S : Subst) : (Γ.subst S).Equiv (Γ'.subst S) :=
  ⟨HMaps.mapValues_equiv _ h.1, h.2⟩

/-- Substituting a context whose `types` are a fresh `addInNewest`-single is
    `Equiv` to inserting the substituted binding into the substituted context.
    Stated at the `find?` level since `HMap` opacity blocks structural equality.
    Used by the abs/quant cases of `resolveAux_HasType` to type the body in
    `(Γ.subst S)` extended with the substituted bound variable. -/
theorem TContext.subst_addInNewest_single_equiv_insert
    (Γ : TContext T.IDMeta) (S : Subst) (xv : T.Identifier) (xty : LTy)
    (h_ne : Γ.types ≠ []) (h_fresh : HMaps.find? Γ.types xv = none) :
    (TContext.subst { Γ with types := Γ.types.addInNewest (HMap.single xv xty) } S).Equiv
      { TContext.subst Γ S with
        types := (TContext.subst Γ S).types.insert xv (LTy.subst S xty) } :=
  ⟨HMaps.mapValues_addInNewest_single_equiv_insert (LTy.subst S) Γ.types xv xty h_ne h_fresh,
   rfl⟩

/-- **Keystone congruence:** typing respects context equivalence. Every
    `HasType` constructor reads the context only through `find?` (tvar,
    tvar_annotated, isFresh in tgen), `insert` (tabs, tquant), or `aliases`
    (talias, annotated), so an `Equiv` transports any derivation. -/
theorem HasType_Equiv [ToString T.IDMeta] [Std.ToFormat T.IDMeta]
    [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    {C : LContext T} {Γ Γ' : TContext T.IDMeta} {e : LExpr T.mono} {ty : LTy}
    (h_ty : HasType C Γ e ty) (h_eq : Γ.Equiv Γ') :
    HasType C Γ' e ty := by
  induction h_ty generalizing Γ' with
  | tbool_const Γ m b h => exact .tbool_const Γ' m b h
  | tint_const Γ m n h => exact .tint_const Γ' m n h
  | treal_const Γ m r h => exact .treal_const Γ' m r h
  | tstr_const Γ m s h => exact .tstr_const Γ' m s h
  | tbitvec_const Γ m n b h => exact .tbitvec_const Γ' m n b h
  | tvar Γ m x ty h_find =>
    exact .tvar Γ' m x ty (by rw [← h_eq.find? x]; exact h_find)
  | tvar_annotated Γ m x ty_o ty_s tys ann h_find h_len h_open h_ac =>
    exact .tvar_annotated Γ' m x ty_o ty_s tys ann (by rw [← h_eq.find? x]; exact h_find)
      h_len h_open (h_eq.2 ▸ h_ac)
  | tabs Γ m name x x_ty e e_ty o h_fresh hx he _ h_o ih =>
    refine .tabs Γ' m name x x_ty e e_ty o h_fresh hx he (ih (h_eq.insert x.fst x_ty)) ?_
    rcases h_o with h_none | ⟨t, h_some, h_ac⟩
    · exact Or.inl h_none
    · exact Or.inr ⟨t, h_some, h_eq.2 ▸ h_ac⟩
  | tapp Γ m e1 e2 t1 t2 h1 h2 _ _ ih1 ih2 =>
    exact .tapp Γ' m e1 e2 t1 t2 h1 h2 (ih1 h_eq) (ih2 h_eq)
  | tinst Γ e ty e_ty x x_ty _ h_open ih =>
    exact .tinst Γ' e ty e_ty x x_ty (ih h_eq) h_open
  | tgen Γ e a ty _ h_fresh ih =>
    exact .tgen Γ' e a ty (ih h_eq) (h_eq.isFresh h_fresh)
  | tif Γ m c e1 e2 ty _ _ _ ihc ih1 ih2 =>
    exact .tif Γ' m c e1 e2 ty (ihc h_eq) (ih1 h_eq) (ih2 h_eq)
  | teq Γ m e1 e2 ty _ _ ih1 ih2 =>
    exact .teq Γ' m e1 e2 ty (ih1 h_eq) (ih2 h_eq)
  | tquant Γ m k name tr tr_ty x x_ty e o h_fresh hx _ _ h_o ihe ihtr =>
    refine .tquant Γ' m k name tr tr_ty x x_ty e o h_fresh hx
      (ihe (h_eq.insert x.fst x_ty)) (ihtr (h_eq.insert x.fst x_ty)) ?_
    rcases h_o with h_none | ⟨t, h_some, h_ac⟩
    · exact Or.inl h_none
    · exact Or.inr ⟨t, h_some, h_eq.2 ▸ h_ac⟩
  | top Γ m f op ty h_find h_type => exact .top Γ' m f op ty h_find h_type
  | top_annotated Γ m f op ty_o ty_s tys ann h_find h_type h_len h_open h_ac =>
    exact .top_annotated Γ' m f op ty_o ty_s tys ann h_find h_type h_len h_open (h_eq.2 ▸ h_ac)
  | talias Γ e mty mty' h_ae _ ih =>
    exact .talias Γ' e mty mty' (h_eq.2 ▸ h_ae) (ih h_eq)

end TContextEquiv

namespace LExpr

section Proofs
attribute [local simp] Pure.pure Except.pure
variable {T : LExprParams} [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]

/-- Prove `e_i.sizeOf < n` (or `≤`) from a hypothesis `h : LExpr.sizeOf e = n`. -/
local macro "expr_size" h:ident : tactic =>
  `(tactic| (subst $h; first | (rw [varOpen_sizeOf]; simp [LExpr.sizeOf]; omega)
                              | (rw [varOpen_sizeOf]; simp [LExpr.sizeOf])
                              | (simp [LExpr.sizeOf]; omega)))

/-! ### Generator-freshness preservation -/

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `Constraints.unify` preserves `SubstFreshForGen`. -/
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
    have h_incl : Subst.freeVars S'.subst ⊆
        Constraints.freeVars cs ++ Subst.freeVars S.subst := by
      simp only [Constraints.unify, Bind.bind, Except.bind] at h_unify
      split at h_unify
      · simp at h_unify
      · rename_i relS h_core
        simp only [Except.ok.injEq] at h_unify; subst h_unify
        exact relS.goodSubset
    rcases List.mem_append.mp (h_incl h_fv) with h | h
    · exact h_fresh_cs v h n hn
    · exact h_fresh_S v (Or.inr h) n hn

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- **`TEnvWF` is preserved through `updateSubst`-of-`unify`.** Replacing the running
    substitution with a `Constraints.unify` result keeps every `TEnvWF` field,
    provided the constraint's free vars are gen-fresh for the input state (needed to
    re-establish `substFreshForGen`). -/
theorem TEnvWF.of_unify_updateSubst
    {cs : Constraints} {S' : SubstInfo} {Env : TEnv T.IDMeta}
    (h_wf : TEnvWF Env)
    (h_unify : Constraints.unify cs Env.stateSubstInfo = .ok S')
    (h_cs_fresh : ∀ v, v ∈ Constraints.freeVars cs →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    TEnvWF (Env.updateSubst S') where
  aliasesWF := h_wf.aliasesWF
  substFreshForGen :=
    unify_preserves_SubstFreshForGen h_unify h_wf.substFreshForGen h_cs_fresh
  ctxFreshForGen := h_wf.ctxFreshForGen
  boundVarsNodup := h_wf.boundVarsNodup
  boundVarsFresh := h_wf.boundVarsFresh

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    simp only [TState.genTySym, TState.incTyGen]
    simp [-Nat.toString_eq_repr]
    intro n hn h_eq
    have h_ne : Env.genState.tyGen ≠ n := by omega
    exact absurd (Nat.toString_injective h_eq) h_ne

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    split at h
    · simp at h
    · rename_i v1 h_gen1; obtain ⟨tv1, Env1⟩ := v1; simp at h
      split at h
      · simp at h
      · rename_i v2 h_gen_rest; obtain ⟨rest, Env2⟩ := v2; simp at h
        obtain ⟨h_tvs, h_env⟩ := h; subst h_tvs; subst h_env
        intro tv h_mem n hn
        cases List.mem_cons.mp h_mem with
        | inl h_eq =>
          subst h_eq
          have h_fresh1 := genTyVar_genFresh' Env tv Env1 h_gen1
          exact h_fresh1 n (Nat.le_trans (genTyVars_tyGen_mono k Env1 rest Env2 h_gen_rest) hn)
        | inr h_in_rest =>
          exact ih Env1 rest Env2 h_gen_rest tv h_in_rest n hn

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
      have h_gen_fresh : ∀ tv', tv' ∈ freshtvs →
          ∀ m, m ≥ genEnv1.genState.tyGen → tv' ≠ TState.tyPrefix ++ toString m :=
        genTyVars_genFresh' ids.length _ freshtvs genEnv1 h_gen
      exact h_gen_fresh tv h_in_fresh

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
mutual
private theorem LMonoTy_resolveAliases_genState_mono
    (mty : LMonoTy) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  match mty with
  | .ftvar _ | .bitvec _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; subst h2; omega
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_args; obtain ⟨args', Env1⟩ := v1; simp at h h_args
    -- tconsAliasSimple doesn't change Env
    simp only [LMonoTy.tconsAliasSimple] at h
    split at h <;> (obtain ⟨_, h2⟩ := h; subst h2)
    all_goals exact LMonoTys_resolveAliases_genState_mono args Env args' Env1 h_args

private theorem LMonoTys_resolveAliases_genState_mono
    (mtys : LMonoTys) (Env : TEnv T.IDMeta) (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; subst h2; omega
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_hd; obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    elim_err h
    rename_i v2 h_tl; obtain ⟨mrest', Env2⟩ := v2
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    exact Nat.le_trans
      (LMonoTy_resolveAliases_genState_mono mty Env mty' Env1 h_hd)
      (LMonoTys_resolveAliases_genState_mono mrest Env1 mrest' Env2 h_tl)
end

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨h1, h2⟩ := h; subst h1; subst h2
    exact ⟨h_fresh, h_input⟩
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_args; obtain ⟨args', Env1⟩ := v1; simp at h h_args
    have h_args_result := LMonoTys_resolveAliases_preserves_SubstFreshForGen args Env args' Env1 h_args
          h_fresh h_aw (fun v hv => h_input v (by simp [LMonoTy.freeVars]; exact hv))
    -- tconsAliasSimple: split on the alias find? match
    simp only [LMonoTy.tconsAliasSimple] at h
    split at h <;> (obtain ⟨h1, h2⟩ := h; subst h1; subst h2)
    · -- No alias: mty' = tcons name args', freeVars = LMonoTys.freeVars args'
      exact ⟨h_args_result.1, h_args_result.2⟩
    · -- Alias found: mty' = expand alias args'. freeVars ⊆ freeVars args'
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
    simp [LMonoTys.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨h1, h2⟩ := h; subst h1; subst h2
    exact ⟨h_fresh, h_input⟩
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_hd; obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    elim_err h
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
        exact h_fv1 v h_in_hd n
          (Nat.le_trans (LMonoTys_resolveAliases_genState_mono mrest Env1 mrest' Env2 h_tl) hn)
      | inr h_in_tl =>
        exact h_ih_tl.2 v h_in_tl n hn
end

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
  elim_err h
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
    · elim_err h_inst
      rename_i v2 h_gen; obtain ⟨freshtvs, Env1⟩ := v2; simp at h_inst
      obtain ⟨_, h2⟩ := h_inst; rw [← h2]
      exact genTyVars_tyGen_mono _ Env.genEnv freshtvs Env1 h_gen
  have h_mty0_fresh : ∀ v, v ∈ LMonoTy.freeVars mty0 →
      ∀ n, n ≥ genEnv'.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
    obtain ⟨vars, body⟩ := ty
    intro v hv n hn
    cases vars with
    | nil =>
      simp [LTy.instantiate] at h_inst
      obtain ⟨h_mty, h_env⟩ := h_inst; subst h_mty; subst h_env
      exact h_ty_fresh v (by simp [LTy.freeVars, List.removeAll]; exact hv) n hn
    | cons x xs =>
      simp [LTy.instantiate, Bind.bind, Except.bind] at h_inst
      elim_err h_inst
      rename_i v_gen h_gen; obtain ⟨freshtvs, Env1⟩ := v_gen; simp at h_inst h_gen
      obtain ⟨h_mty, h_env⟩ := h_inst; subst h_mty; subst h_env
      have h_len : freshtvs.length = (x :: xs).length :=
        TGenEnv.genTyVars_length _ _ _ _ h_gen
      have h_subset := LMonoTy.freeVars_of_subst_subset
        (Strata.Util.HMaps.ofScopes [List.zip (x :: xs) (List.map LMonoTy.ftvar freshtvs)]) body hv
      rw [List.mem_append] at h_subset
      cases h_subset with
      | inl h_body =>
        by_cases h_bound : v ∈ (x :: xs)
        · exact h_bv_fresh v (by simp [LTy.boundVars]; exact List.mem_cons.mp h_bound) n
            (Nat.le_trans h_mono_inst hn)
        · have h_in_fvs : v ∈ LTy.freeVars (.forAll (x :: xs) body) := by
            simp only [LTy.freeVars]
            show v ∈ List.filter (fun a => !List.elem a (x :: xs)) body.freeVars
            grind
          exact h_ty_fresh v h_in_fvs n (Nat.le_trans h_mono_inst hn)
      | inr h_subst_fvs =>
        have h_fresh_gen := genTyVars_genFresh' (x :: xs).length Env.genEnv freshtvs Env1 h_gen
        have h_v_in_freshtvs : v ∈ freshtvs :=
          Subst.freeVars_zip_ftvar (x :: xs) freshtvs h_len h_subst_fvs
        exact h_fresh_gen v h_v_in_freshtvs n hn
  exact (LMonoTy_resolveAliases_preserves_SubstFreshForGen mty0 _ mty Env' h
    (h_eq ▸ SubstFreshForGen.mono _ _ _ h_fresh h_mono_inst)
    (h_ctx_eq ▸ h_aw)
    h_mty0_fresh).1

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
  elim_err h
  rename_i v1 h_res; obtain ⟨mty0, Env1⟩ := v1; dsimp at h h_res
  elim_errs h  -- checkNoFutureGenVars / isInstanceOfKnownType
  simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
  exact LTy_resolveAliases_preserves_SubstFreshForGen ty Env mty0 Env1 h_res h_fresh h_aw h_ty_fresh h_bv_fresh

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `LMonoTy.instantiateWithCheck` preserves `SubstFreshForGen`. -/
private theorem LMonoTy_instantiateWithCheck_preserves_SubstFreshForGen
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (mty, Env'))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_aw : TContext.AliasesWF Env.context) :
    SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState := by
  simp only [LMonoTy.instantiateWithCheck] at h
  split at h
  · simp at h
  · rename_i instTypes Env1 h_inst
    simp [Bind.bind, Except.bind] at h
    elim_err h
    rename_i v2 h_res; obtain ⟨mtyi, Env2⟩ := v2; dsimp at h h_res
    elim_errs h  -- checkNoFutureGenVars / isInstanceOfKnownType
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    have h_subst_eq : Env1.stateSubstInfo = Env.stateSubstInfo := by
      simp [LMonoTys.instantiateEnv] at h_inst
      split at h_inst
      · simp at h_inst
      · simp at h_inst; obtain ⟨_, h_env⟩ := h_inst; rw [← h_env]
    have h_mono : Env1.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen :=
      LMonoTys.instantiateEnv_tyGen_mono _ _ Env _ _ h_inst
    have h_ctx_eq : Env1.context = Env.context :=
      LMonoTys.instantiateEnv_context _ _ Env _ Env1 h_inst
    exact (LMonoTy_resolveAliases_preserves_SubstFreshForGen _ Env1 mtyi Env2 h_res
      (h_subst_eq ▸ SubstFreshForGen.mono _ _ _ h_fresh h_mono)
      (h_ctx_eq ▸ h_aw)
      (by
        have h_closed : ∀ tv, tv ∈ LMonoTys.freeVars [mty_in] → tv ∈ mty_in.freeVars := by
          simp [LMonoTys.freeVars]
        have h_gen := instantiateEnv_freeVars_genFresh_closed
          mty_in.freeVars [mty_in] Env instTypes Env1 h_inst h_closed
        intro v hv n hn
        have h_in_all : v ∈ LMonoTys.freeVars instTypes := by
          have h_len : 0 < instTypes.length := by
            have h_len := LMonoTys.instantiateEnv_length _ _ _ _ _ h_inst; simp at h_len; omega
          cases instTypes with
          | nil => simp at h_len
          | cons hd tl => simp [LMonoTys.freeVars]; left; exact hv
        exact h_gen v h_in_all n hn)).1

/-- Generated names with different indices are different. -/
private theorem tyPrefix_ne_of_ne (a b : Nat) (h : a ≠ b) :
    TState.tyPrefix ++ toString a ≠ TState.tyPrefix ++ toString b := by
  intro h_eq; apply h
  exact absurd (Nat.toString_injective (by simpa [TState.tyPrefix] using h_eq)) h

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

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `instantiateWithCheck` preserves `stateSubstInfo` (only modifies `genEnv`). -/
theorem LTy_instantiateWithCheck_preserves_stateSubstInfo
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  simp [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_ra; obtain ⟨mty', Env1⟩ := v1
  elim_errs h
  simp at h
  obtain ⟨_, h2⟩ := h; rw [← h2]
  exact LTy.resolveAliases_preserves_stateSubstInfo ty Env mty' Env1 h_ra

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Context preservation for `LTy.instantiateWithCheck`. -/
theorem LTy_instantiateWithCheck_context'
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env')) :
    Env'.context = Env.context := by
  simp [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_ra; obtain ⟨mty', Env1⟩ := v1
  elim_errs h  -- checkNoFutureGenVars / isInstanceOfKnownType
  simp at h
  obtain ⟨_, h2⟩ := h; rw [← h2]
  exact LTy.resolveAliases_context ty Env mty' Env1 h_ra

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Context preservation for `LMonoTy.instantiateWithCheck`. -/
theorem LMonoTy_instantiateWithCheck_context'
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (mty, Env')) :
    Env'.context = Env.context := by
  simp [LMonoTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i instTypes Env_mid h_inst
    elim_err h
    rename_i v2 h_ra; obtain ⟨mty', Env2⟩ := v2; simp at h h_ra
    elim_errs h  -- checkNoFutureGenVars / isInstanceOfKnownType
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    rw [LMonoTy.resolveAliases_context _ _ mty' Env2 h_ra]
    exact LMonoTys.instantiateEnv_context _ _ Env _ _ h_inst

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Every free variable of `instantiateWithCheck`'s output monotype is gen-fresh
    for the output state (no future-generated name). -/
theorem LTy_instantiateWithCheck_freeVars_fresh
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env')) :
    ∀ v, v ∈ LMonoTy.freeVars mty →
      ∀ n, n ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_res; obtain ⟨mty0, Env1⟩ := v1; dsimp at h h_res
  elim_err h  -- checkNoFutureGenVars failed → contradiction
  rename_i h_check
  elim_err h  -- isInstanceOfKnownType
  simp at h; obtain ⟨h_mty, h_env⟩ := h
  rw [← h_mty, ← h_env]
  exact checkNoFutureGenVars_imp_fresh mty0 Env1.genEnv.genState (by simp at h_check; exact h_check)

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Free vars of `LMonoTy.instantiateWithCheck` output satisfy freshness for the output gen state. -/
private theorem LMonoTy_instantiateWithCheck_freeVars_fresh
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (mty, Env')) :
    ∀ v, v ∈ LMonoTy.freeVars mty →
      ∀ n, n ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  simp only [LMonoTy.instantiateWithCheck] at h
  split at h
  · simp at h
  · rename_i instTypes Env1 h_inst
    simp [Bind.bind, Except.bind] at h
    elim_err h
    rename_i v2 h_res; obtain ⟨mtyi, Env2⟩ := v2; dsimp at h h_res
    elim_err h  -- checkNoFutureGenVars failed
    rename_i h_check
    elim_err h  -- isInstanceOfKnownType
    simp at h; obtain ⟨h_mty, h_env⟩ := h
    rw [← h_mty, ← h_env]
    exact checkNoFutureGenVars_imp_fresh mtyi Env2.genEnv.genState (by simp at h_check; exact h_check)

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
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
  elim_err h
  rename_i ty_found h_find_ctx
  elim_err h
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
    elim_err h
    rename_i v2 h_inst2; obtain ⟨fty_inst, Env2⟩ := v2; dsimp at h h_inst2
    elim_err h
    rename_i v3 h_mapError
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]; simp [TEnv.updateSubst]
    have h_fresh1 := LTy_instantiateWithCheck_preserves_SubstFreshForGen
      _ C Env mty Env1 h_inst h_fresh h_aw
      (fun v hv n hn => h_ctx v (TContext.mem_knownTypeVars_of_find h_find_ctx hv) n hn)
      (h_bvf _ _ h_find_ctx)
    have h_fresh2 := LMonoTy_instantiateWithCheck_preserves_SubstFreshForGen
      fty_val C Env1 fty_inst Env2 h_inst2 h_fresh1 h_aw1
    have h_unify := Except.mapError_ok_h' h_mapError
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


/-! ### typeBoundVar invariant family -/

/-! ## 1. Context `find?` helpers -/

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- If `xv ∉ ms.keys`, then `m.find? xv = none` for every scope `m ∈ ms`. -/
private theorem not_mem_keys_find_none
    (ms : HMaps (Identifier T.IDMeta) LTy) (xv : Identifier T.IDMeta)
    (h : xv ∉ HMaps.keys ms) :
    ∀ m, m ∈ ms → HMap.find? m xv = none := by
  induction ms with
  | nil => intro m hm; contradiction
  | cons hd tl ih =>
    simp only [HMaps.keys, List.mem_append, not_or] at h
    intro m hm; cases hm with
    | head => exact HMap.not_mem_keys_find?_none hd xv h.1
    | tail _ h_tl => exact ih h.2 m h_tl

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- If `xv ∉ knownVars ctx`, then `HMap.find? m xv = none` for all `m ∈ ctx.types`. -/
private theorem not_mem_knownVars_find_none
    (ctx : TContext T.IDMeta) (xv : Identifier T.IDMeta)
    (h : xv ∉ TContext.knownVars ctx) :
    ∀ m, m ∈ ctx.types → HMap.find? m xv = none :=
  not_mem_keys_find_none ctx.types xv (by simp only [TContext.knownVars] at h; exact h)

/-! ## 2. `typeBoundVar_xv_fresh_in_context` -/

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- The variable `xv` produced by `typeBoundVar` is fresh in the input context:
    it does not appear as a key in any map of `Env.context.types`. -/
theorem typeBoundVar_xv_fresh_in_context
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env1)) :
    ∀ m, m ∈ Env.context.types → HMap.find? m xv = none := by
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  cases h_lift : liftGenEnv HasGen.genVar Env with
  | error _ => rw [h_lift] at h; simp at h
  | ok res_lift =>
    obtain ⟨xv_raw, Env_g⟩ := res_lift
    rw [h_lift] at h; simp only at h
    have h_fresh := liftGenEnv_genVar_fresh Env xv_raw Env_g h_lift
    cases bty with
    | some bty_val =>
      simp only at h
      cases h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g with
      | error _ => rw [h_ic] at h; simp at h
      | ok res_ic =>
        obtain ⟨bty_mty, Env_mid⟩ := res_ic
        rw [h_ic] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h_xv, _, _⟩ := h; subst h_xv
        exact not_mem_knownVars_find_none Env.context xv_raw h_fresh
    | none =>
      simp only at h
      cases h_tg : TEnv.genTyVar Env_g with
      | error _ => rw [h_tg] at h; simp at h
      | ok res_tg =>
        obtain ⟨tv, Env_mid⟩ := res_tg
        rw [h_tg] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h_xv, _, _⟩ := h; subst h_xv
        exact not_mem_knownVars_find_none Env.context xv_raw h_fresh

/-! ## 3. `typeBoundVar_adds_to_context` -/

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- The fresh variable produced by `typeBoundVar` is added to the output context
    with the monomorphic scheme `∀[]. xty`. -/
theorem typeBoundVar_adds_to_context (C : LContext T) (Env : TEnv T.IDMeta)
    (bty : Option LMonoTy) (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env')) :
    Env'.context.types.find? xv = some (.forAll [] xty) := by
  have h_fresh := typeBoundVar_xv_fresh_in_context C Env bty xv xty Env' h
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  cases h_lift : liftGenEnv HasGen.genVar Env with
  | error _ => rw [h_lift] at h; simp at h
  | ok res_lift =>
    obtain ⟨xv_raw, Env_g⟩ := res_lift
    rw [h_lift] at h; simp only at h
    have h_ctx_g := liftGenEnv_context Env xv_raw Env_g h_lift
    cases bty with
    | some bty_val =>
      simp only at h
      cases h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g with
      | error _ => rw [h_ic] at h; simp at h
      | ok res_ic =>
        obtain ⟨bty_mty, Env_mid⟩ := res_ic
        rw [h_ic] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h_xv, h_xty, h_env⟩ := h
        subst h_xv; subst h_xty; subst h_env
        simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context]
        have h_ctx_ic := LMonoTy_instantiateWithCheck_context' bty_val C Env_g _ Env_mid h_ic
        have h_ctx : Env_mid.context = Env.context := by
          simp [TEnv.context] at h_ctx_ic h_ctx_g ⊢; rw [h_ctx_ic, h_ctx_g]
        rw [show Env_mid.genEnv.context.types = Env.context.types from
          congrArg TContext.types h_ctx]
        exact HMaps.find?_addInNewest_self Env.context.types xv_raw _ h_fresh
    | none =>
      simp only at h
      cases h_tg : TEnv.genTyVar Env_g with
      | error _ => rw [h_tg] at h; simp at h
      | ok res_tg =>
        obtain ⟨tv, Env_mid⟩ := res_tg
        rw [h_tg] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h_xv, h_xty, h_env⟩ := h
        subst h_xv; subst h_xty; subst h_env
        simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context]
        have h_ctx_tg := TEnv.genTyVar_context Env_g tv Env_mid h_tg
        have h_ctx : Env_mid.context = Env.context := by
          simp [TEnv.context] at h_ctx_tg h_ctx_g ⊢; rw [h_ctx_tg, h_ctx_g]
        rw [show Env_mid.genEnv.context.types = Env.context.types from
          congrArg TContext.types h_ctx]
        exact HMaps.find?_addInNewest_self Env.context.types xv_raw _ h_fresh

/-! ## 4. `typeBoundVar_preserves_find` -/

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `typeBoundVar` preserves existing context lookups for variables different from the fresh one. -/
theorem typeBoundVar_preserves_find (C : LContext T) (Env : TEnv T.IDMeta)
    (bty : Option LMonoTy) (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env'))
    (y : T.Identifier) (yty : LTy) (h_ne : y ≠ xv)
    (h_ctx : Env.context.types.find? y = some yty) :
    Env'.context.types.find? y = some yty := by
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  cases h_lift : liftGenEnv HasGen.genVar Env with
  | error _ => rw [h_lift] at h; simp at h
  | ok res_lift =>
    obtain ⟨xv_raw, Env_g⟩ := res_lift
    rw [h_lift] at h; simp only at h
    have h_ctx_g := liftGenEnv_context Env xv_raw Env_g h_lift
    cases bty with
    | some bty_val =>
      simp only at h
      cases h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g with
      | error _ => rw [h_ic] at h; simp at h
      | ok res_ic =>
        obtain ⟨bty_mty, Env_mid⟩ := res_ic
        rw [h_ic] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h_xv, _, h_env⟩ := h
        subst h_xv; subst h_env
        simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context]
        have h_ctx_ic := LMonoTy_instantiateWithCheck_context' bty_val C Env_g _ Env_mid h_ic
        have h_ctx_e : Env_mid.context = Env.context := by
          simp [TEnv.context] at h_ctx_ic h_ctx_g ⊢; rw [h_ctx_ic, h_ctx_g]
        rw [show Env_mid.genEnv.context.types = Env.context.types from
          congrArg TContext.types h_ctx_e,
          HMaps.find?_addInNewest_ne Env.context.types xv_raw _ y h_ne]
        exact h_ctx
    | none =>
      simp only at h
      cases h_tg : TEnv.genTyVar Env_g with
      | error _ => rw [h_tg] at h; simp at h
      | ok res_tg =>
        obtain ⟨tv, Env_mid⟩ := res_tg
        rw [h_tg] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h_xv, _, h_env⟩ := h
        subst h_xv; subst h_env
        simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context]
        have h_ctx_tg := TEnv.genTyVar_context Env_g tv Env_mid h_tg
        have h_ctx_e : Env_mid.context = Env.context := by
          simp [TEnv.context] at h_ctx_tg h_ctx_g ⊢; rw [h_ctx_tg, h_ctx_g]
        rw [show Env_mid.genEnv.context.types = Env.context.types from
          congrArg TContext.types h_ctx_e,
          HMaps.find?_addInNewest_ne Env.context.types xv_raw _ y h_ne]
        exact h_ctx

/-! ## 5. `typeBoundVar_context_types_ne_nil` -/

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `typeBoundVar` always produces an environment with non-empty `context.types`,
    because it applies `addInNewestContext` which uses `HMaps.addInNewest`. -/
theorem typeBoundVar_context_types_ne_nil
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env1)) :
    Env1.context.types ≠ [] := by
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  cases h_lift : liftGenEnv HasGen.genVar Env with
  | error _ => rw [h_lift] at h; simp at h
  | ok res_lift =>
    obtain ⟨xv_raw, Env_g⟩ := res_lift
    rw [h_lift] at h; simp only at h
    cases bty with
    | some bty_val =>
      simp only at h
      cases h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g with
      | error _ => rw [h_ic] at h; simp at h
      | ok res_ic =>
        obtain ⟨bty_mty, Env_mid⟩ := res_ic
        rw [h_ic] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, h_env1⟩ := h; rw [← h_env1]
        simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context]
        cases hts : Env_mid.genEnv.context.types <;>
          simp [HMaps.addInNewest]
    | none =>
      simp only at h
      cases h_tg : TEnv.genTyVar Env_g with
      | error _ => rw [h_tg] at h; simp at h
      | ok res_tg =>
        obtain ⟨tv, Env_mid⟩ := res_tg
        rw [h_tg] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, h_env1⟩ := h; rw [← h_env1]
        simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context]
        cases hts : Env_mid.genEnv.context.types <;>
          simp [HMaps.addInNewest]

/-! ## 6. `typeBoundVar_aliases_eq` -/

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
theorem typeBoundVar_aliases_eq
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env')) :
    Env'.context.aliases = Env.context.aliases := by
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  cases h_lift : liftGenEnv HasGen.genVar Env with
  | error _ => rw [h_lift] at h; simp at h
  | ok res_lift =>
    obtain ⟨xv_raw, Env_g⟩ := res_lift
    rw [h_lift] at h; simp only at h
    have h_ctx_g := liftGenEnv_context Env xv_raw Env_g h_lift
    cases bty with
    | some bty_val =>
      simp only at h
      cases h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g with
      | error _ => rw [h_ic] at h; simp at h
      | ok res_ic =>
        obtain ⟨bty_ic, Env_ic⟩ := res_ic
        rw [h_ic] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, h_env⟩ := h; subst h_env
        simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context]
        have h_ctx_ic := LMonoTy_instantiateWithCheck_context' bty_val C Env_g _ Env_ic h_ic
        have h_ctx : Env_ic.context = Env.context := by
          simp [TEnv.context] at h_ctx_ic h_ctx_g ⊢; rw [h_ctx_ic, h_ctx_g]
        exact congrArg TContext.aliases h_ctx
    | none =>
      simp only at h
      cases h_tg : TEnv.genTyVar Env_g with
      | error _ => rw [h_tg] at h; simp at h
      | ok res_tg =>
        obtain ⟨tv, Env_tv⟩ := res_tg
        rw [h_tg] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, h_env⟩ := h; subst h_env
        simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context]
        have h_ctx_tg := TEnv.genTyVar_context Env_g tv Env_tv h_tg
        have h_ctx : Env_tv.context = Env.context := by
          simp [TEnv.context] at h_ctx_tg h_ctx_g ⊢; rw [h_ctx_tg, h_ctx_g]
        exact congrArg TContext.aliases h_ctx

/-! ## Auxiliary: `liftGenEnv` / `genTyVar` preservation helpers -/

omit [ToString T.IDMeta] [Std.ToFormat T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `liftGenEnv HasGen.genVar` preserves the substitution. -/
theorem liftGenEnv_subst
    (Env : TEnv T.IDMeta) (xv : Identifier T.IDMeta) (Env' : TEnv T.IDMeta)
    (h : liftGenEnv HasGen.genVar Env = .ok (xv, Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  simp only [liftGenEnv] at h
  generalize h_gen : HasGen.genVar Env.genEnv = res at h
  match res with
  | .error _ => simp at h
  | .ok (xi, Eg) => simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]

omit [ToString T.IDMeta] [Std.ToFormat T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `liftGenEnv HasGen.genVar` never decreases the type-variable counter. -/
theorem liftGenEnv_tyGen_mono
    (Env : TEnv T.IDMeta) (xv : Identifier T.IDMeta) (Env' : TEnv T.IDMeta)
    (h : liftGenEnv HasGen.genVar Env = .ok (xv, Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  simp only [liftGenEnv] at h
  generalize h_gen : HasGen.genVar Env.genEnv = res at h
  match res with
  | .error _ => simp at h
  | .ok (xi, Eg) =>
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    exact HasGen.genVar_tyGen_mono Env.genEnv xi Eg h_gen

/-! ## `knownTypeVars_addInNewestContext_cases`

`TContext.knownTypeVars` is `types.values.flatMap LTy.freeVars`, so the
case analysis goes through a value-membership lemma. -/

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- A value found in `addInNewest ms (single x t)` is either a value of `ms`
    or the newly added `t`. -/
private theorem mem_values_addInNewest_single
    (ms : HMaps (Identifier T.IDMeta) LTy) (x : Identifier T.IDMeta) (t : LTy) (w : LTy)
    (h : w ∈ (ms.addInNewest (HMap.single x t)).values) :
    w ∈ ms.values ∨ w = t := by
  cases ms with
  | nil =>
    simp only [HMaps.addInNewest, HMaps.values, List.append_nil] at h
    exact Or.inr ((HMap.mem_values_single_iff x t w).mp h)
  | cons scope rest =>
    rw [HMaps.addInNewest_cons] at h
    simp only [HMaps.values, List.mem_append] at h
    rcases h with h_union | h_rest
    · rw [HMap.mem_values_iff_find?] at h_union
      obtain ⟨k, hk⟩ := h_union
      rw [HMap.find?_union] at hk
      cases hs : scope.find? k with
      | some v =>
        rw [hs] at hk; simp only [Option.some_or, Option.some.injEq] at hk
        rw [← hk]
        exact Or.inl (by
          simp only [HMaps.values, List.mem_append]
          exact Or.inl (HMap.find?_mem_values scope hs))
      | none =>
        rw [hs] at hk; simp only [Option.none_or] at hk
        exact Or.inr ((HMap.mem_values_single_iff x t w).mp (HMap.find?_mem_values _ hk))
    · exact Or.inl (by
        simp only [HMaps.values, List.mem_append]; exact Or.inr h_rest)

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Backward direction: vars in knownTypeVars after addInNewest come from
    the old context or from the new type's freeVars. -/
private theorem knownTypeVars_addInNewestContext_cases
    (Env : TEnv T.IDMeta) (xv : T.Identifier) (ty : LTy) (v : TyIdentifier)
    (h : v ∈ TContext.knownTypeVars (Env.addInNewestContext (HMap.single xv ty)).context) :
    v ∈ TContext.knownTypeVars Env.context ∨ v ∈ LTy.freeVars ty := by
  simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context,
    TContext.knownTypeVars, List.mem_flatMap] at h ⊢
  obtain ⟨w, h_w_mem, h_v_fv⟩ := h
  rcases mem_values_addInNewest_single _ xv ty w h_w_mem with h_old | h_eq
  · exact Or.inl ⟨w, h_old, h_v_fv⟩
  · subst h_eq; exact Or.inr h_v_fv

/-! ## 8. `typeBoundVar_preserves_boundVarsNodup` -/

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `typeBoundVar` preserves `boundVarsNodup`.
    The new entry `(xv, forAll [] xty)` has `boundVars = []`, so the Nodup
    condition is vacuously true. Existing entries are unchanged from the input
    environment. -/
theorem typeBoundVar_preserves_boundVarsNodup
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env'))
    (h_bvnd : ∀ y ty, Env.context.types.find? y = some ty →
      (LTy.boundVars ty).Nodup) :
    ∀ y ty, Env'.context.types.find? y = some ty →
      (LTy.boundVars ty).Nodup := by
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  cases h_lift : liftGenEnv HasGen.genVar Env with
  | error _ => rw [h_lift] at h; simp at h
  | ok res_lift =>
    obtain ⟨xv_raw, Env_g⟩ := res_lift
    rw [h_lift] at h; simp only at h
    have h_g_ctx : Env_g.context = Env.context := liftGenEnv_context Env _ Env_g h_lift
    cases bty with
    | some bty_val =>
      simp only at h
      cases h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g with
      | error _ => rw [h_ic] at h; simp at h
      | ok res_ic =>
        obtain ⟨bty_mty, Env_mid⟩ := res_ic
        rw [h_ic] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h_xv, h_xty, h_env⟩ := h
        have h_mid_ctx : Env_mid.context = Env.context :=
          (LMonoTy_instantiateWithCheck_context' bty_val C Env_g bty_mty Env_mid h_ic).trans h_g_ctx
        subst h_xv; subst h_xty; subst h_env
        intro y ty_found h_find
        simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_find
        rw [show Env_mid.genEnv.context.types = Env.context.types from
          congrArg TContext.types h_mid_ctx] at h_find
        rcases HMaps.find?_addInNewest_single Env.context.types xv_raw (.forAll [] bty_mty) y with
          ⟨h_new, _⟩ | h_old
        · rw [h_new] at h_find; injection h_find with h_find; subst h_find
          simp [LTy.boundVars]
        · rw [h_old] at h_find
          exact h_bvnd y ty_found h_find
    | none =>
      simp only at h
      cases h_tg : TEnv.genTyVar Env_g with
      | error _ => rw [h_tg] at h; simp at h
      | ok res_tg =>
        obtain ⟨xtyid, Env_mid⟩ := res_tg
        rw [h_tg] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h_xv, h_xty, h_env⟩ := h
        have h_mid_ctx : Env_mid.context = Env.context :=
          (TEnv.genTyVar_context Env_g xtyid Env_mid h_tg).trans h_g_ctx
        subst h_xv; subst h_xty; subst h_env
        intro y ty_found h_find
        simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_find
        rw [show Env_mid.genEnv.context.types = Env.context.types from
          congrArg TContext.types h_mid_ctx] at h_find
        rcases HMaps.find?_addInNewest_single Env.context.types xv_raw (.forAll [] (LMonoTy.ftvar xtyid)) y with
          ⟨h_new, _⟩ | h_old
        · rw [h_new] at h_find; injection h_find with h_find; subst h_find
          simp [LTy.boundVars]
        · rw [h_old] at h_find
          exact h_bvnd y ty_found h_find

/-! ## 9. `TypeBoundVarInvariant` -/

/-- Bundled invariant for the four properties preserved by `typeBoundVar`
    (all `TEnvWF` fields except `boundVarsNodup`). -/
structure TypeBoundVarInvariant (Env : TEnv T.IDMeta) : Prop where
  substFreshForGen : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState
  ctxFreshForGen : ContextFreshForGen Env.context Env.genEnv.genState
  aliasesWF : TContext.AliasesWF Env.context
  boundVarsFresh : ∀ y ty, Env.context.types.find? y = some ty →
    ∀ v, v ∈ LTy.boundVars ty →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n

/-! ## 10. `typeBoundVar_preserves_invariant` -/

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `typeBoundVar` preserves all four invariant properties at once.
    Decomposes `typeBoundVar` once and proves `SubstFreshForGen`,
    `ContextFreshForGen`, `AliasesWF`, and `boundVarsFresh` together. -/
theorem typeBoundVar_preserves_invariant
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env'))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_ctx : ContextFreshForGen Env.context Env.genEnv.genState)
    (h_aw : TContext.AliasesWF Env.context)
    (h_bf : ∀ y ty, Env.context.types.find? y = some ty →
      ∀ v, v ∈ LTy.boundVars ty →
        ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    TypeBoundVarInvariant Env' := by
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  cases h_lift : liftGenEnv HasGen.genVar Env with
  | error _ => rw [h_lift] at h; simp at h
  | ok res_lift =>
    obtain ⟨xv_raw, Env_g⟩ := res_lift
    rw [h_lift] at h; simp only at h
    have h_gen_subst : Env_g.stateSubstInfo = Env.stateSubstInfo :=
      liftGenEnv_subst Env _ Env_g h_lift
    have h_gen_tyGen : Env_g.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen :=
      liftGenEnv_tyGen_mono Env _ Env_g h_lift
    have h_gen_ctx : Env_g.context = Env.context := liftGenEnv_context Env _ Env_g h_lift
    have h_ctx_gen : ContextFreshForGen Env_g.context Env_g.genEnv.genState :=
      h_gen_ctx ▸ ContextFreshForGen.mono _ _ _ h_ctx h_gen_tyGen
    cases bty with
    | some bty_val =>
      simp only at h
      cases h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g with
      | error _ => rw [h_ic] at h; simp at h
      | ok res_ic =>
        obtain ⟨bty_mty, Env_inst⟩ := res_ic
        rw [h_ic] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, h_env⟩ := h; subst h_env
        have h_iwc_ctx := LMonoTy_instantiateWithCheck_context' bty_val C Env_g _ Env_inst h_ic
        have h_iwc_mono := LMonoTy_instantiateWithCheck_tyGen_mono bty_val C Env_g _ Env_inst h_ic
        have h_fv_fresh := LMonoTy_instantiateWithCheck_freeVars_fresh bty_val C Env_g _ Env_inst h_ic
        have h_mid_ctx : Env_inst.context = Env.context := h_iwc_ctx.trans h_gen_ctx
        exact {
          substFreshForGen := by
            simp only [TEnv.addInNewestContext, TEnv.updateContext]
            exact LMonoTy_instantiateWithCheck_preserves_SubstFreshForGen
              bty_val C Env_g _ Env_inst h_ic
              (h_gen_subst ▸ SubstFreshForGen.mono _ _ _ h_fresh h_gen_tyGen)
              (h_gen_ctx ▸ h_aw)
          ctxFreshForGen := by
            simp only [TEnv.addInNewestContext, TEnv.updateContext]
            intro v hv n hn
            rcases knownTypeVars_addInNewestContext_cases Env_inst _ (.forAll [] _) v hv with
              h_old | h_new
            · exact (h_iwc_ctx ▸ h_ctx_gen) v h_old n (Nat.le_trans h_iwc_mono hn)
            · simp [LTy.freeVars, List.removeAll] at h_new
              exact h_fv_fresh v h_new n hn
          aliasesWF := by
            simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context, TContext.AliasesWF]
            show ∀ a, a ∈ Env_inst.genEnv.context.aliases → a.WF
            rw [show Env_inst.genEnv.context = Env_inst.context from rfl,
                h_iwc_ctx, h_gen_ctx]
            exact h_aw
          boundVarsFresh := by
            intro y ty_found h_find v hv n hn
            simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_find hn
            rw [show Env_inst.genEnv.context.types = Env.context.types from
              congrArg TContext.types h_mid_ctx] at h_find
            rcases HMaps.find?_addInNewest_single Env.context.types xv_raw (.forAll [] bty_mty) y with
              ⟨h_new, _⟩ | h_old
            · rw [h_new] at h_find; injection h_find with h_find; subst h_find
              simp [LTy.boundVars] at hv
            · rw [h_old] at h_find
              exact h_bf y ty_found h_find v hv n (Nat.le_trans (Nat.le_trans h_gen_tyGen h_iwc_mono) hn)
        }
    | none =>
      simp only at h
      cases h_tg : TEnv.genTyVar Env_g with
      | error _ => rw [h_tg] at h; simp at h
      | ok res_tg =>
        obtain ⟨xtyid, Env1⟩ := res_tg
        rw [h_tg] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, h_env⟩ := h; subst h_env
        have h_genTy_ctx := TEnv.genTyVar_context Env_g xtyid Env1 h_tg
        have h_genTy_tyGen := genTyVar_tyGen Env_g xtyid Env1 h_tg
        have h_genTy_name := genTyVar_name_eq Env_g xtyid Env1 h_tg
        have h_genTy_subst := TEnv.genTyVar_subst Env_g xtyid Env1 h_tg
        have h_mid_ctx : Env1.context = Env.context := h_genTy_ctx.trans h_gen_ctx
        have h_ctx1 : ContextFreshForGen Env1.context Env1.genEnv.genState :=
          h_genTy_ctx ▸ ContextFreshForGen.mono _ _ _ h_ctx_gen (by omega)
        have h_xtyid_fresh : ∀ n, n ≥ Env1.genEnv.genState.tyGen →
            xtyid ≠ TState.tyPrefix ++ toString n := by
          rw [h_genTy_name]; exact generated_name_fresh _ _ (by omega)
        exact {
          substFreshForGen := by
            simp only [TEnv.addInNewestContext, TEnv.updateContext]
            rw [h_genTy_subst, h_gen_subst]
            exact SubstFreshForGen.mono _ _ _ h_fresh (by omega)
          ctxFreshForGen := by
            simp only [TEnv.addInNewestContext, TEnv.updateContext]
            intro v hv n hn
            rcases knownTypeVars_addInNewestContext_cases Env1 _ (.forAll [] (.ftvar xtyid)) v hv with
              h_old | h_new
            · exact h_ctx1 v h_old n hn
            · simp [LTy.freeVars, List.removeAll, LMonoTy.freeVars] at h_new
              rw [h_new]; exact h_xtyid_fresh n hn
          aliasesWF := by
            simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context, TContext.AliasesWF]
            show ∀ a, a ∈ Env1.genEnv.context.aliases → a.WF
            rw [show Env1.genEnv.context = Env1.context from rfl,
                h_genTy_ctx, h_gen_ctx]
            exact h_aw
          boundVarsFresh := by
            intro y ty_found h_find v hv n hn
            simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_find hn
            rw [show Env1.genEnv.context.types = Env.context.types from
              congrArg TContext.types h_mid_ctx] at h_find
            rcases HMaps.find?_addInNewest_single Env.context.types xv_raw (.forAll [] (LMonoTy.ftvar xtyid)) y with
              ⟨h_new, _⟩ | h_old
            · rw [h_new] at h_find; injection h_find with h_find; subst h_find
              simp [LTy.boundVars] at hv
            · rw [h_old] at h_find
              exact h_bf y ty_found h_find v hv n (by omega)
        }

/-! ## 11. `TEnvWF.of_typeBoundVar` -/

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `typeBoundVar` preserves environment well-formedness. -/
theorem TEnvWF.of_typeBoundVar
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env'))
    (h_envwf : TEnvWF Env) : TEnvWF Env' :=
  let h_inv := typeBoundVar_preserves_invariant C Env bty xv xty Env' h
    h_envwf.substFreshForGen h_envwf.ctxFreshForGen h_envwf.aliasesWF h_envwf.boundVarsFresh
  { aliasesWF := h_inv.aliasesWF
    substFreshForGen := h_inv.substFreshForGen
    ctxFreshForGen := h_inv.ctxFreshForGen
    boundVarsNodup := typeBoundVar_preserves_boundVarsNodup C Env bty xv xty Env' h h_envwf.boundVarsNodup
    boundVarsFresh := h_inv.boundVarsFresh }

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `find?` is unaffected by pushing an empty scope: the empty head map fails to
    find any key, so lookup falls through to the original scopes. -/
theorem TEnv.pushEmptyContext_find?
    (Env : TEnv T.IDMeta) (y : T.Identifier) :
    (Env.pushEmptyContext).context.types.find? y = Env.context.types.find? y := by
  simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, HMaps.push, HMaps.find?,
    HMap.find?_empty]

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `knownTypeVars` is unaffected by pushing an empty scope: the empty head map
    contributes no type variables. -/
theorem TEnv.pushEmptyContext_knownTypeVars
    (Env : TEnv T.IDMeta) :
    TContext.knownTypeVars (Env.pushEmptyContext).context =
      TContext.knownTypeVars Env.context := by
  simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, HMaps.push,
    TContext.knownTypeVars, HMaps.values, HMap.values_empty, List.nil_append]

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Pushing an empty scope preserves `TEnvWF`. The new empty head scope adds no
    bindings and no type variables, and leaves `aliases`, `genState`, and the
    substitution unchanged. -/
theorem TEnvWF.of_pushEmptyContext
    (Env : TEnv T.IDMeta) (h_envwf : TEnvWF Env) :
    TEnvWF (Env.pushEmptyContext) := by
  have h_subst : (Env.pushEmptyContext).stateSubstInfo = Env.stateSubstInfo := rfl
  have h_gen : (Env.pushEmptyContext).genEnv.genState = Env.genEnv.genState := rfl
  have h_aliases : (Env.pushEmptyContext).context.aliases = Env.context.aliases := rfl
  refine {
    aliasesWF := ?_
    substFreshForGen := ?_
    ctxFreshForGen := ?_
    boundVarsNodup := ?_
    boundVarsFresh := ?_ }
  · simp only [TContext.AliasesWF, h_aliases]; exact h_envwf.aliasesWF
  · rw [h_subst, h_gen]; exact h_envwf.substFreshForGen
  · intro v hv n hn
    rw [TEnv.pushEmptyContext_knownTypeVars] at hv
    rw [h_gen] at hn
    exact h_envwf.ctxFreshForGen v hv n hn
  · intro y ty h_find
    rw [TEnv.pushEmptyContext_find?] at h_find
    exact h_envwf.boundVarsNodup y ty h_find
  · intro y ty h_find v hv n hn
    rw [TEnv.pushEmptyContext_find?] at h_find
    rw [h_gen] at hn
    exact h_envwf.boundVarsFresh y ty h_find v hv n hn


omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Inserting a single monomorphic binding `(x, forAll [] mty)` whose free type
    variables are gen-fresh preserves `TEnvWF`. The new binding has empty
    `boundVars`, so `boundVarsNodup` and `boundVarsFresh` are vacuous on it; its
    type variables are gen-fresh by hypothesis, giving `ctxFreshForGen`;
    `aliases`, `genState`, and the substitution are unchanged. -/
theorem TEnvWF.of_addInNewestContext_singleton
    (Env : TEnv T.IDMeta) (x : T.Identifier) (mty : LMonoTy)
    (h_envwf : TEnvWF Env)
    (h_fresh : ∀ v, v ∈ LMonoTy.freeVars mty →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    TEnvWF (Env.addInNewestContext (HMap.single x (.forAll [] mty))) := by
  have h_subst : (Env.addInNewestContext (HMap.single x (.forAll [] mty))).stateSubstInfo =
      Env.stateSubstInfo := rfl
  have h_gen : (Env.addInNewestContext (HMap.single x (.forAll [] mty))).genEnv.genState =
      Env.genEnv.genState := rfl
  have h_aliases : (Env.addInNewestContext (HMap.single x (.forAll [] mty))).context.aliases =
      Env.context.aliases := rfl
  refine {
    aliasesWF := ?_
    substFreshForGen := ?_
    ctxFreshForGen := ?_
    boundVarsNodup := ?_
    boundVarsFresh := ?_ }
  · simp only [TContext.AliasesWF, h_aliases]; exact h_envwf.aliasesWF
  · rw [h_subst, h_gen]; exact h_envwf.substFreshForGen
  · intro v hv n hn
    rw [h_gen] at hn
    rcases knownTypeVars_addInNewestContext_cases Env x (.forAll [] mty) v hv with
      h_old | h_new
    · exact h_envwf.ctxFreshForGen v h_old n hn
    · have h_new' : v ∈ LMonoTy.freeVars mty := by
        simpa [LTy.freeVars, List.removeAll] using h_new
      exact h_fresh v h_new' n hn
  · intro y ty h_find
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_find
    rcases HMaps.find?_addInNewest_single Env.genEnv.context.types x (.forAll [] mty) y with
      ⟨h_new, _⟩ | h_old
    · rw [h_new] at h_find; injection h_find with h_find; subst h_find
      simp [LTy.boundVars]
    · rw [h_old] at h_find
      exact h_envwf.boundVarsNodup y ty h_find
  · intro y ty h_find v hv n hn
    rw [h_gen] at hn
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_find
    rcases HMaps.find?_addInNewest_single Env.genEnv.context.types x (.forAll [] mty) y with
      ⟨h_new, _⟩ | h_old
    · rw [h_new] at h_find; injection h_find with h_find; subst h_find
      simp [LTy.boundVars] at hv
    · rw [h_old] at h_find
      exact h_envwf.boundVarsFresh y ty h_find v hv n hn

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Inserting a map of monomorphic bindings `(id, forAll [] mty)` whose free type
    variables are all gen-fresh preserves `TEnvWF`. Proved directly at the
    `find?`/`values` level: a lookup or type-variable after `addInNewest m` comes
    either from `m` (whose values are `.forAll []` monotypes with gen-fresh free
    variables) or from the original context (well-formed by hypothesis). -/
theorem TEnvWF.of_addInNewestContext_mono
    (Env : TEnv T.IDMeta) (pairs : List (T.Identifier × LMonoTy))
    (h_envwf : TEnvWF Env)
    (h_fresh : ∀ p ∈ pairs, ∀ v, v ∈ LMonoTy.freeVars p.2 →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    TEnvWF (Env.addInNewestContext
      (HMap.ofList (pairs.map (fun p => (p.1, .forAll [] p.2))))) := by
  -- Every value of the inserted map is a `.forAll []` of some `pairs` monotype.
  have h_vals : ∀ ty, ty ∈ (HMap.ofList (pairs.map (fun p => (p.1, (LTy.forAll [] p.2 : LTy))))).values →
      ∃ p ∈ pairs, ty = .forAll [] p.2 := by
    intro ty h_ty
    have h_ty' := HMap.mem_values_ofList _ ty h_ty
    rw [List.map_map, List.mem_map] at h_ty'
    obtain ⟨p, hp, h_eq⟩ := h_ty'
    exact ⟨p, hp, h_eq.symm⟩
  have h_subst : (Env.addInNewestContext
      (HMap.ofList (pairs.map (fun p => (p.1, (LTy.forAll [] p.2 : LTy)))))).stateSubstInfo =
      Env.stateSubstInfo := rfl
  have h_gen : (Env.addInNewestContext
      (HMap.ofList (pairs.map (fun p => (p.1, (LTy.forAll [] p.2 : LTy)))))).genEnv.genState =
      Env.genEnv.genState := rfl
  have h_aliases : (Env.addInNewestContext
      (HMap.ofList (pairs.map (fun p => (p.1, (LTy.forAll [] p.2 : LTy)))))).context.aliases =
      Env.context.aliases := rfl
  refine {
    aliasesWF := ?_
    substFreshForGen := ?_
    ctxFreshForGen := ?_
    boundVarsNodup := ?_
    boundVarsFresh := ?_ }
  · simp only [TContext.AliasesWF, h_aliases]; exact h_envwf.aliasesWF
  · rw [h_subst, h_gen]; exact h_envwf.substFreshForGen
  · intro v hv n hn
    rw [h_gen] at hn
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context,
      TContext.knownTypeVars, List.mem_flatMap] at hv
    obtain ⟨w, h_w_mem, h_v_fv⟩ := hv
    rcases HMaps.mem_values_addInNewest _ _ w h_w_mem with h_new | h_old
    · obtain ⟨p, hp, rfl⟩ := h_vals w h_new
      have h_v_mty : v ∈ LMonoTy.freeVars p.2 := by
        simpa [LTy.freeVars, List.removeAll] using h_v_fv
      exact h_fresh p hp v h_v_mty n hn
    · exact h_envwf.ctxFreshForGen v (by
        simp only [TContext.knownTypeVars, List.mem_flatMap]; exact ⟨w, h_old, h_v_fv⟩) n hn
  · intro y ty h_find
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_find
    rcases HMaps.find?_addInNewest_mem _ _ y ty h_find with h_new | h_old
    · obtain ⟨p, _, rfl⟩ := h_vals ty (HMap.find?_mem_values _ h_new)
      simp [LTy.boundVars]
    · exact h_envwf.boundVarsNodup y ty h_old
  · intro y ty h_find v hv n hn
    rw [h_gen] at hn
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_find
    rcases HMaps.find?_addInNewest_mem _ _ y ty h_find with h_new | h_old
    · obtain ⟨p, _, rfl⟩ := h_vals ty (HMap.find?_mem_values _ h_new)
      simp [LTy.boundVars] at hv
    · exact h_envwf.boundVarsFresh y ty h_old v hv n hn

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Pushing an empty scope preserves `AliasesResolved`: only `.types` changes,
    `.aliases` is untouched. -/
theorem TContext.AliasesResolved.of_pushEmptyContext
    (Env : TEnv T.IDMeta) (h : TContext.AliasesResolved Env.context) :
    TContext.AliasesResolved Env.pushEmptyContext.context := h

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Inserting bindings in the newest scope preserves `AliasesResolved`: only
    `.types` changes, `.aliases` is untouched. -/
theorem TContext.AliasesResolved.of_addInNewestContext
    (Env : TEnv T.IDMeta) (map : HMap T.Identifier LTy)
    (h : TContext.AliasesResolved Env.context) :
    TContext.AliasesResolved (Env.addInNewestContext map).context := h

/-! ## 12. `LTy_/LMonoTy_instantiateWithCheck_context` (unprimed bridges) -/

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Context preservation for `LTy.instantiateWithCheck`
    (unprimed re-export of `LTy_instantiateWithCheck_context'`). -/
theorem LTy_instantiateWithCheck_context
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env')) :
    Env'.context = Env.context :=
  LTy_instantiateWithCheck_context' ty C Env mty Env' h

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Context preservation for `LMonoTy.instantiateWithCheck`
    (unprimed re-export of `LMonoTy_instantiateWithCheck_context'`). -/
theorem LMonoTy_instantiateWithCheck_context
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (mty, Env')) :
    Env'.context = Env.context :=
  LMonoTy_instantiateWithCheck_context' mty_in C Env mty Env' h

/-! ## 13. `inferFVar_context` -/

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `inferFVar` preserves the context. -/
private theorem inferFVar_context
    (C : LContext T) (Env : TEnv T.IDMeta) (x : T.Identifier)
    (fty : Option LMonoTy) (ty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : inferFVar C Env x fty = .ok (ty, Env')) :
    Env'.context = Env.context := by
  simp only [inferFVar, Bind.bind, Except.bind] at h
  elim_err h
  rename_i ty_scheme h_find
  elim_err h
  rename_i v1 h_inst
  obtain ⟨mty, Env1⟩ := v1; simp at h h_inst
  split at h
  · simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    exact LTy_instantiateWithCheck_context _ C Env mty Env1 h_inst
  · rename_i fty_val
    simp only [Except.mapError] at h
    elim_err h
    rename_i v2 h_inst2
    obtain ⟨fty_inst, Env2⟩ := v2; simp at h h_inst2
    elim_err h
    rename_i v3 h_mapError
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    show Env2.context = Env.context
    rw [LMonoTy_instantiateWithCheck_context _ C Env1 fty_inst Env2 h_inst2,
        LTy_instantiateWithCheck_context _ C Env mty Env1 h_inst]


/-! ### freeVars / LFunc.type / resolveAliases freeVars / polyKeysFresh -/

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
        have h_trest_sub := (ih (mtysSize trest) h_trest_sz).2 trest (Nat.le_refl _)
        exact List.mem_append_right _ (h_trest_sub h2)
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

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Any monotype appearing in `monoty.destructArrow` (where `monoty` is the output of
`LTy.instantiateWithCheck`) has gen-fresh free variables. The input monotypes the
typechecker inserts into the internal env are members of this list, so this supplies
the freshness precondition of `TEnvWF.of_addInNewestContext_mono`. -/
theorem instantiateWithCheck_destructArrow_mem_fresh
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta)
    (monoty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (monoty, Env'))
    (mt : LMonoTy) (h_mem : mt ∈ LMonoTy.destructArrow monoty) :
    ∀ v, v ∈ LMonoTy.freeVars mt →
      ∀ n, n ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  intro v hv n hn
  have h_fresh := LTy_instantiateWithCheck_freeVars_fresh ty C Env monoty Env' h
  have h_in_destr : v ∈ LMonoTys.freeVars (LMonoTy.destructArrow monoty) :=
    LMonoTys.freeVars_mem_subset h_mem hv
  have h_in_monoty : v ∈ LMonoTy.freeVars monoty :=
    LMonoTy.freeVars_destructArrow_subset monoty h_in_destr
  exact h_fresh v h_in_monoty n hn

/-- `freeVars (mkArrow' ret args)` is `freeVars args ++ freeVars ret`. -/
private theorem LMonoTy.freeVars_mkArrow' (ret : LMonoTy) (args : LMonoTys) :
    LMonoTy.freeVars (LMonoTy.mkArrow' ret args) =
    LMonoTys.freeVars args ++ LMonoTy.freeVars ret := by
  induction args with
  | nil => simp [LMonoTy.mkArrow', LMonoTys.freeVars]
  | cons m mrest ih =>
    simp only [LMonoTy.mkArrow'_cons, LMonoTy.arrow, LMonoTy.freeVars,
      LMonoTys.freeVars, List.append_nil]
    rw [ih, List.append_assoc]

/-- The free vars of any component of `monoty.destructArrow` are free vars of `monoty`. -/
private theorem LMonoTy.mem_destructArrow_freeVars_subset (monoty x : LMonoTy)
    (hx : x ∈ LMonoTy.destructArrow monoty) :
    LMonoTy.freeVars x ⊆ LMonoTy.freeVars monoty :=
  fun _ hv =>
    LMonoTy.freeVars_destructArrow_subset monoty (LMonoTys.freeVars_mem_subset hx hv)

/-- The reconstructed output monotype `mkArrow' R DL`, where `R` is the last element of
`drop n (destructArrow monoty)` (or the global last as default) and `DL` is its dropLast,
has free vars contained in those of `monoty`: the declared output is assembled entirely from
`monoty.destructArrow` components. -/
theorem LMonoTy.freeVars_reconstructedOutput_subset (monoty : LMonoTy) (n : Nat) :
    ∀ v, v ∈ LMonoTy.freeVars
        (LMonoTy.mkArrow'
          ((List.drop n monoty.destructArrow).getLast?.getD
            (List.getLast monoty.destructArrow (LMonoTy.destructArrow_non_empty monoty)))
          (List.drop n monoty.destructArrow).dropLast) →
      v ∈ LMonoTy.freeVars monoty := by
  intro v hv
  rw [LMonoTy.freeVars_mkArrow', List.mem_append] at hv
  cases hv with
  | inl h_dl =>
    -- v is a free var of some element of (drop n da).dropLast
    obtain ⟨x, hx_mem, hx_v⟩ := LMonoTys.freeVars_exists h_dl
    have h_x_in_drop : x ∈ List.drop n monoty.destructArrow :=
      List.dropLast_subset _ hx_mem
    have h_x_in_da : x ∈ monoty.destructArrow := List.mem_of_mem_drop h_x_in_drop
    exact LMonoTy.mem_destructArrow_freeVars_subset monoty x h_x_in_da hx_v
  | inr h_r =>
    -- v is a free var of the return type R = getD (getLast? (drop n da)) (getLast da)
    have h_r_in_da : ((List.drop n monoty.destructArrow).getLast?.getD
        (List.getLast monoty.destructArrow (LMonoTy.destructArrow_non_empty monoty)))
        ∈ monoty.destructArrow := by
      cases h_last : (List.drop n monoty.destructArrow).getLast? with
      | none =>
        simp only [Option.getD_none]
        exact List.getLast_mem (LMonoTy.destructArrow_non_empty monoty)
      | some r =>
        simp only [Option.getD_some]
        exact List.mem_of_mem_drop (List.mem_of_getLast? h_last)
    exact LMonoTy.mem_destructArrow_freeVars_subset monoty _ h_r_in_da h_r

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] [Hashable T.IDMeta] in
/-- Factory function types produced by `LFunc.type` have empty `freeVars`
    when the function satisfies `LFuncWF`. -/
private theorem LFunc.type_freeVars_eq_nil
    (func : LFunc T) (ty : LTy) (h_type : func.type = .ok ty)
    (h_wf : LFuncWF func) :
    LTy.freeVars ty = [] := by
  cases ty with
  | forAll vars body =>
  simp [LTy.freeVars]
  apply List.removeAll_eq_nil_of_forall_mem
  unfold LFunc.type LFuncDefined.type at h_type; simp only [Bind.bind, Except.bind] at h_type
  elim_errs h_type
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
      have h_inputs_fv : ∀ (xs : LMonoTys), (∀ ty, ty ∈ xs → ty ∈ func.inputs.values) →
          ∀ v, v ∈ LMonoTys.freeVars xs → v ∈ func.typeArgs := by
        intro xs h_sub v hv
        induction xs with
        | nil => simp [LMonoTys.freeVars] at hv
        | cons t ts ih =>
          simp [LMonoTys.freeVars, List.mem_append] at hv
          rcases hv with hv_t | hv_ts
          · exact h_wf.inputs_typevars_in_typeArgs t (h_sub t List.mem_cons_self) hv_t
          · exact ih (fun ty ht => h_sub ty (List.mem_cons_of_mem _ ht)) hv_ts
      exact h_inputs_fv irest h_irest_sub x hx_irest
    · exact h_wf.output_typevars_in_typeArgs (LMonoTy.freeVars_destructArrow_subset func.output hx_destr)

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] [Hashable T.IDMeta] in
/-- Factory function types produced by `LFunc.type` have `boundVars = func.typeArgs`. -/
theorem LFunc.type_boundVars_eq_typeArgs
    (func : LFunc T) (ty : LTy) (h_type : func.type = .ok ty) :
    LTy.boundVars ty = func.typeArgs := by
  unfold LFunc.type LFuncDefined.type at h_type; simp only [Bind.bind, Except.bind] at h_type
  elim_errs h_type
  generalize h_vals : func.inputs.values = vals at h_type
  cases vals with
  | nil =>
    simp at h_type; subst h_type; simp [LTy.boundVars]
  | cons _ _ =>
    simp at h_type; subst h_type; simp [LTy.boundVars]

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] [Hashable T.IDMeta] in
/-- Factory function types produced by `LFuncDefined.type` have `boundVars = func.typeArgs`. -/
theorem LFuncDefined.type_boundVars_eq_typeArgs
    (func : LFuncDefined T) (ty : LTy) (h_type : func.type = .ok ty) :
    LTy.boundVars ty = func.typeArgs := by
  unfold LFuncDefined.type at h_type; simp only [Bind.bind, Except.bind] at h_type
  elim_errs h_type
  generalize h_vals : func.inputs.values = vals at h_type
  cases vals with
  | nil =>
    simp at h_type; subst h_type; simp [LTy.boundVars]
  | cons _ _ =>
    simp at h_type; subst h_type; simp [LTy.boundVars]

/-! ### `resolveAliases` does not grow free variables. -/

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
mutual
/-- `LMonoTy.resolveAliases` does not grow free variables when aliases are WF. -/
private theorem LMonoTy_resolveAliases_freeVars_subset
    (mty : LMonoTy) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    ∀ v, v ∈ LMonoTy.freeVars mty' → v ∈ LMonoTy.freeVars mty := by
  match mty with
  | .ftvar _ | .bitvec _ =>
    simp [LMonoTy.resolveAliases] at h
    obtain ⟨rfl, _⟩ := h
    intro v hv; exact hv
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
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
    simp [LMonoTys.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨h1, _⟩ := h; subst h1
    intro v hv; exact hv
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_hd; obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    elim_err h
    rename_i v2 h_tl; obtain ⟨mrest', Env2⟩ := v2
    simp at h; obtain ⟨h1, _⟩ := h; subst h1
    have h_ctx_eq := LMonoTy.resolveAliases_context mty Env mty' Env1 h_hd
    intro v hv; simp [LMonoTys.freeVars, List.mem_append] at hv ⊢
    rcases hv with hv_hd | hv_tl
    · left; exact LMonoTy_resolveAliases_freeVars_subset mty Env mty' Env1 h_hd h_aw v hv_hd
    · right; exact LMonoTys_resolveAliases_freeVars_subset mrest Env1 mrest' Env2 h_tl
        (h_ctx_eq ▸ h_aw) v hv_tl
end

/-! ### `transfer_boundVarsFresh` (references `TEnv`). -/

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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

/-! ### 9: `genTyVar_fresh_wrt_input_subst` (touches `Subst` / `TEnv.genTyVar`). -/

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- A type variable produced by `genTyVar` does not appear (as key or in values)
    in any substitution satisfying `SubstFreshForGen` for an earlier gen state.

    This is the key lemma connecting the generator invariant to substitution
    freshness, used by the `app` case of `resolveAux_properties`. -/
theorem genTyVar_fresh_wrt_input_subst
    (Env Env2 Env3 : TEnv T.IDMeta)
    (fresh_name : TyIdentifier)
    (h_gen : TEnv.genTyVar Env2 = .ok (fresh_name, Env3))
    (h_fresh : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_mono : Env2.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen) :
    HMaps.find? Env.stateSubstInfo.subst fresh_name = none ∧
    (∀ a t, HMaps.find? Env.stateSubstInfo.subst a = some t →
      fresh_name ∉ LMonoTy.freeVars t) := by
  have h_name := genTyVar_name_eq Env2 fresh_name Env3 h_gen
  -- fresh_name = TState.tyPrefix ++ toString Env2.genState.tyGen
  -- By SubstFreshForGen + h_mono, no variable in Env.subst equals this name
  constructor
  · apply HMaps.not_mem_keys_find?_none
    intro h_mem
    exact h_fresh fresh_name (Or.inl h_mem) Env2.genEnv.genState.tyGen h_mono h_name
  · intro a t h_find h_fv
    have h_in_fvs := Subst.freeVars_of_find_subset Env.stateSubstInfo.subst h_find h_fv
    exact h_fresh fresh_name (Or.inr h_in_fvs) Env2.genEnv.genState.tyGen h_mono h_name

/-! ### `HasType` instantiation helpers (leaf lemmas for the `resolve_HasType` chain)

`HasType_tinst_all` and `HasType_LTy_instantiate` discharge the instantiation
steps of the `resolve_HasType` chain: from a derivation of a `forAll`-quantified
type they build a derivation of the instantiated type. -/

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    HasType C Γ e (.forAll [] (LMonoTy.subst
      (Strata.Util.HMaps.ofScopes [List.zip vars tys]) body)) := by
  intro vars
  induction vars with
  | nil =>
    intro body tys h_len _ _ h_ty
    have h_tys_nil : tys = [] := by
      cases tys with
      | nil => rfl
      | cons _ _ => simp at h_len
    subst h_tys_nil
    -- [].zip [] = [], so subst (ofScopes [[]]) body = body
    have h_empty : Subst.hasEmptyScopes (Strata.Util.HMaps.ofScopes
        [List.zip ([] : List TyIdentifier) ([] : List LMonoTy)]) = true := by
      simp [List.zip, Strata.Util.HMaps.ofScopes, Subst.hasEmptyScopes,
        HMap.ofList, HMap.isEmpty]
    rw [LMonoTy.subst_of_hasEmptyScopes h_empty]
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
      have h_inst := HasType.tinst Γ e (.forAll (v :: rest) body)
        (LTy.open v t (.forAll (v :: rest) body)) v t h_ty rfl
      have h_open_eq : LTy.open v t (.forAll (v :: rest) body) =
          .forAll rest (LMonoTy.subst (Subst.singleton v t) body) := by
        show (if v ∈ v :: rest then
            LTy.forAll ((v :: rest).removeAll [v]) (LMonoTy.subst (Subst.singleton v t) body)
          else LTy.forAll (v :: rest) body) = _
        simp only [List.mem_cons_self, ↓reduceIte]
        congr 1
        rw [List.cons_removeAll]
        have h_contains_true : [v].contains v = true := by
          unfold List.contains List.elem
          simp
        simp
        exact List.removeAll_not_mem h_v_notin_rest
      rw [h_open_eq] at h_inst
      have h_ih := ih (LMonoTy.subst (Subst.singleton v t) body) rest_tys h_len h_rest_nodup
        (fun w hw s hs => h_no_clash w (List.mem_cons_of_mem v hw) s (List.mem_cons_of_mem t hs))
        h_inst
      have h_t_stable :
          LMonoTy.subst [HMap.ofList (List.zip rest rest_tys)] t = t := by
        apply LMonoTy.subst_no_relevant_keys
        intro x hx h_x_key
        have h_x_in_rest : x ∈ rest := by
          -- key of the single scope `ofList (zip rest rest_tys)` is a key of the zip ⊆ rest
          simp only [HMaps.keys, List.append_nil] at h_x_key
          have h_in_fst := HMap.mem_keys_ofList _ x h_x_key
          simp only [List.mem_map] at h_in_fst
          obtain ⟨p, hp_mem, hp_eq⟩ := h_in_fst
          exact hp_eq ▸ (List.of_mem_zip hp_mem).1
        exact h_no_clash x (List.mem_cons_of_mem v h_x_in_rest) t
          List.mem_cons_self hx
      have h_compose := LMonoTy.subst_cons_single v t
        (HMap.ofList (List.zip rest rest_tys)) body h_t_stable
      -- ofScopes [zip rest rest_tys] = [HMap.ofList (zip rest rest_tys)]
      simp only [Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil] at h_ih
      rw [h_compose] at h_ih
      -- Goal subst uses ofList ((v,t) :: zip rest rest_tys); h_ih uses
      -- [(ofList (zip rest rest_tys)).insert v t]. They agree on find? at every key
      -- because v ∉ keys(zip rest rest_tys) (v ∉ rest).
      simp only [List.zip_cons_cons, Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil]
      have h_v_notin_zip : v ∉ (List.zip rest rest_tys).map Prod.fst := by
        intro hv
        simp only [List.mem_map] at hv
        obtain ⟨p, hp_mem, hp_eq⟩ := hv
        exact h_v_notin_rest (hp_eq ▸ (List.of_mem_zip hp_mem).1)
      have h_find_eq : ∀ k, HMaps.find? [HMap.ofList (((v, t)) :: List.zip rest rest_tys)] k =
          HMaps.find? [(HMap.ofList (List.zip rest rest_tys)).insert v t] k := by
        intro k
        simp only [HMaps.find?]
        rw [HMap.find?_ofList_cons_eq_find?_insert v t (List.zip rest rest_tys) h_v_notin_zip k]
      rw [LMonoTy.subst_find?_congr _ _ body h_find_eq]
      exact h_ih

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    elim_err h
    rename_i v1 h_gen1; obtain ⟨tv1, Env1⟩ := v1
    elim_err h
    rename_i v2 h_gen_rest; obtain ⟨rest, Env2⟩ := v2
    simp at h
    obtain ⟨h_tvs, h_env⟩ := h; subst h_tvs; subst h_env
    have h_tv1_name : tv1 = TState.tyPrefix ++ toString Env.genState.tyGen := by
      simp only [TGenEnv.genTyVar] at h_gen1
      elim_err h_gen1
      simp at h_gen1; rw [← h_gen1.1]
      simp [TState.genTySym, TState.incTyGen]
    have h_gen1_mono : Env1.genState.tyGen = Env.genState.tyGen + 1 := by
      simp only [TGenEnv.genTyVar] at h_gen1
      elim_err h_gen1
      simp at h_gen1; rw [← h_gen1.2]
      simp [TState.genTySym, TState.incTyGen]
    rcases List.mem_cons.mp h_mem with h_eq | h_rest
    · exact ⟨Env.genState.tyGen, Nat.le_refl _, h_eq ▸ h_tv1_name⟩
    · simp at h_gen_rest
      obtain ⟨k, h_k_ge, h_eq⟩ := ih Env1 rest Env2 h_gen_rest h_rest
      exact ⟨k, by omega, h_eq⟩

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- If `e` has polymorphic type `ty` and `LTy.instantiate ty` produces a
    monomorphic `mty` with fresh type variables, then `e` has type `.forAll [] mty`. -/
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
    elim_err h_inst
    rename_i v1 h_gen
    obtain ⟨freshtvs, genEnv1⟩ := v1
    simp at h_inst h_gen
    obtain ⟨h_eq, _⟩ := h_inst; rw [← h_eq]
    have h_len_gen := TGenEnv.genTyVars_length (x :: xs).length genEnv freshtvs genEnv1 h_gen
    have h_map_len : (List.map LMonoTy.ftvar freshtvs).length = (x :: xs).length := by
      simp [h_len_gen]
    apply HasType_tinst_all C Γ e (x :: xs) body (List.map LMonoTy.ftvar freshtvs)
      h_map_len
    · -- Nodup: from h_nodup, since boundVars (.forAll (x :: xs) body) = x :: xs
      have h_bv : LTy.boundVars (.forAll (x :: xs) body) = x :: xs := by simp [LTy.boundVars]
      rw [h_bv] at h_nodup; exact h_nodup
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

/-! ### AnnotCompat_subst chain -/

/-! ### `AliasEquiv` preserved under substitution -/

/-! Local helper: `subst S` commutes with `openVars` on a body whose free vars
    are contained in `vars`, mapping the values through `subst S`. -/
mutual
private theorem subst_openVars_comm (S : Subst)
    (vars : List TyIdentifier) (vals : LMonoTys) (body : LMonoTy)
    (h_wf : ∀ tv, tv ∈ LMonoTy.freeVars body → tv ∈ vars)
    (h_len : vars.length = vals.length) :
    LMonoTy.subst S (LMonoTy.openVars vars vals body) =
    LMonoTy.openVars vars (vals.map (LMonoTy.subst S)) body := by
  match body with
  | .ftvar x =>
    have h_x_in : x ∈ vars := h_wf x (by simp [LMonoTy.freeVars])
    clear h_wf
    induction vars generalizing vals with
    | nil => simp at h_x_in
    | cons v vs ih =>
      cases vals with
      | nil => simp at h_len
      | cons vl vls =>
        by_cases h_eq : v = x
        · subst h_eq
          simp only [LMonoTy.openVars, List.map_cons, List.zip_cons_cons,
            List.find?_cons, beq_self_eq_true]
        · have h_x_vs : x ∈ vs := by
            cases h_x_in with
            | head => exact absurd rfl h_eq
            | tail _ h => exact h
          have hbeq : (v == x) = false := by simp [h_eq]
          simp only [LMonoTy.openVars, List.map_cons, List.zip_cons_cons,
            List.find?_cons, hbeq]
          have h_ih := ih vls (by simpa using h_len) h_x_vs
          simpa only [LMonoTy.openVars] using h_ih
  | .bitvec n =>
    simp only [LMonoTy.openVars, LMonoTy.subst_bitvec]
  | .tcons name args =>
    simp only [LMonoTy.openVars, LMonoTy.subst_tcons]
    congr 1
    exact subst_openVarsList_comm S vars vals args
      (fun tv htv => h_wf tv (by simp only [LMonoTy.freeVars]; exact htv)) h_len

private theorem subst_openVarsList_comm (S : Subst)
    (vars : List TyIdentifier) (vals : LMonoTys) (bodies : LMonoTys)
    (h_wf : ∀ tv, tv ∈ LMonoTys.freeVars bodies → tv ∈ vars)
    (h_len : vars.length = vals.length) :
    LMonoTys.subst S (LMonoTys.openVars vars vals bodies) =
    LMonoTys.openVars vars (vals.map (LMonoTy.subst S)) bodies := by
  match bodies with
  | [] =>
    rw [LMonoTys.openVars, LMonoTys.subst_nil, LMonoTys.openVars]
  | hd :: tl =>
    rw [LMonoTys.openVars, LMonoTys.subst_eq_map, List.map_cons, LMonoTys.openVars]
    congr 1
    · exact subst_openVars_comm S vars vals hd
        (fun tv htv => h_wf tv (by
          simp only [LMonoTys.freeVars]; exact List.mem_append_left _ htv)) h_len
    · rw [← LMonoTys.subst_eq_map]
      exact subst_openVarsList_comm S vars vals tl
        (fun tv htv => h_wf tv (by
          simp only [LMonoTys.freeVars]; exact List.mem_append_right _ htv)) h_len
end

/-! ### `tconsAlias` ≡ `tconsAliasSimple`

The unify-based `LMonoTy.tconsAlias` is a reference specification for the pure,
faster `LMonoTy.tconsAliasSimple` used on the typing path. `tconsAlias_eq_simple`
proves the two agree (under the final substitution) for well-formed aliases.

NB: `subst (HMaps.ofScopes [zip vars vals])` (`ofList`, last-write-wins) and
`openVars vars vals` (`List.find?`, first-match) only agree when `vars` has no
duplicates. Every use here supplies `alias.typeArgs.Nodup` (from
`TypeAlias.WF`), so the bridge below carries a `Nodup` hypothesis. -/

/-- Under `Nodup` keys, `HMap.find?` of an `ofList (zip vars vals)` agrees with the
    first-match `List.find?` that `openVars` uses. -/
private theorem find?_ofList_zip_eq_openVars_ftvar
    (vars : List TyIdentifier) (vals : LMonoTys) (x : TyIdentifier)
    (h_len : vars.length = vals.length) (h_nodup : vars.Nodup) :
    (match HMap.find? (HMap.ofList (List.zip vars vals)) x with
      | some sty => sty | none => .ftvar x) = LMonoTy.openVars vars vals (.ftvar x) := by
  simp only [LMonoTy.openVars]
  have h_keys : (List.zip vars vals).map Prod.fst = vars := List.map_fst_zip (by omega)
  have h_pw : (List.zip vars vals).Pairwise (fun a b => (a.1 == b.1) = false) := by
    have h_vars_nd : ((List.zip vars vals).map Prod.fst).Nodup := by rw [h_keys]; exact h_nodup
    have h_nd_fst : (List.zip vars vals).Pairwise (fun a b => a.1 ≠ b.1) :=
      (List.pairwise_map).mp ((List.nodup_iff_pairwise_ne).mp h_vars_nd)
    exact h_nd_fst.imp (by intro a b h; simpa using h)
  cases h_find : (List.zip vars vals).find? (fun p => p.1 == x) with
  | some p =>
    obtain ⟨k, v⟩ := p
    have h_mem : (⟨k, v⟩ : TyIdentifier × LMonoTy) ∈ List.zip vars vals :=
      List.mem_of_find?_eq_some h_find
    have h_kx : (k == x) = true := by
      have := List.find?_some h_find; simpa using this
    have h_get : HMap.find? (HMap.ofList (List.zip vars vals)) x = some v := by
      simp only [HMap.find?, HMap.ofList]
      exact Std.HashMap.getElem?_ofList_of_mem h_kx h_pw h_mem
    rw [h_get]
  | none =>
    have h_notin : List.contains ((List.zip vars vals).map Prod.fst) x = false := by
      simp only [List.contains_eq_mem, decide_eq_false_iff_not]
      intro hx_mem
      obtain ⟨p, hp_mem, hp_eq⟩ := List.mem_map.mp hx_mem
      have h_pred : (fun p : TyIdentifier × LMonoTy => p.1 == x) p = true := by
        simp [hp_eq]
      exact absurd (List.find?_eq_none.mp h_find p hp_mem) (by simp [h_pred])
    have h_none : HMap.find? (HMap.ofList (List.zip vars vals)) x = none := by
      simp only [HMap.find?, HMap.ofList]
      exact Std.HashMap.getElem?_ofList_of_contains_eq_false h_notin
    rw [h_none]

mutual
/-- Bridge: substituting the single instantiation scope `[zip vars vals]` into a
    `body` whose free vars are all in `vars` equals `openVars vars vals body`,
    provided `vars` has no duplicate keys. -/
private theorem subst_single_scope_eq_openVars
    (vars : List TyIdentifier) (vals : LMonoTys) (body : LMonoTy)
    (h_wf : ∀ tv, tv ∈ LMonoTy.freeVars body → tv ∈ vars)
    (h_len : vars.length = vals.length) (h_nodup : vars.Nodup) :
    LMonoTy.subst (Strata.Util.HMaps.ofScopes [List.zip vars vals]) body =
    LMonoTy.openVars vars vals body := by
  match body with
  | .ftvar x =>
    rw [LMonoTy.subst_unfold]
    simp only [Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil,
               HMaps.find?_single_scope]
    exact find?_ofList_zip_eq_openVars_ftvar vars vals x h_len h_nodup
  | .bitvec n => rw [LMonoTy.subst_bitvec]; simp only [LMonoTy.openVars]
  | .tcons name args =>
    rw [LMonoTy.subst_tcons]
    simp only [LMonoTy.openVars]
    congr 1
    exact subst_single_scope_eq_openVarsList vars vals args
      (fun tv htv => h_wf tv (by simp only [LMonoTy.freeVars]; exact htv)) h_len h_nodup

/-- List version of `subst_single_scope_eq_openVars`. -/
private theorem subst_single_scope_eq_openVarsList
    (vars : List TyIdentifier) (vals : LMonoTys) (bodies : LMonoTys)
    (h_wf : ∀ tv, tv ∈ LMonoTys.freeVars bodies → tv ∈ vars)
    (h_len : vars.length = vals.length) (h_nodup : vars.Nodup) :
    LMonoTys.subst (Strata.Util.HMaps.ofScopes [List.zip vars vals]) bodies =
    LMonoTys.openVars vars vals bodies := by
  match bodies with
  | [] => rw [LMonoTys.subst_nil, LMonoTys.openVars]
  | hd :: tl =>
    rw [LMonoTys.subst_eq_map, List.map_cons, LMonoTys.openVars]
    congr 1
    · exact subst_single_scope_eq_openVars vars vals hd
        (fun tv htv => h_wf tv (by
          simp only [LMonoTys.freeVars]; exact List.mem_append_left _ htv)) h_len h_nodup
    · rw [← LMonoTys.subst_eq_map]
      exact subst_single_scope_eq_openVarsList vars vals tl
        (fun tv htv => h_wf tv (by
          simp only [LMonoTys.freeVars]; exact List.mem_append_right _ htv)) h_len h_nodup
end

/-! ### `subst.go`-geometry / `polyKeysFresh` / `instantiateEnv`. -/

/-- Keys of `subst.go xs S` are a subset of keys of `S`. -/
private theorem keys_go_subset_keys (S : Subst) (xs : List TyIdentifier)
    (a : TyIdentifier) (h : a ∈ HMaps.keys (LTy.subst.go xs S)) :
    a ∈ HMaps.keys S := by
  induction xs generalizing S with
  | nil => simpa [LTy.subst.go] using h
  | cons x rest ih =>
    simp only [LTy.subst.go] at h
    exact HMaps.keys_remove_subset S x a (ih (S.remove x) h)

/-- Keys of `subst.go xs S` are not in `xs`. -/
private theorem keys_go_not_mem_xs (S : Subst) (xs : List TyIdentifier)
    (a : TyIdentifier) (h : a ∈ HMaps.keys (LTy.subst.go xs S)) :
    a ∉ xs := by
  induction xs generalizing S with
  | nil => simp
  | cons x rest ih =>
    simp only [LTy.subst.go] at h
    intro h_mem
    rcases List.mem_cons.mp h_mem with rfl | h_rest
    · -- a = x: but a ∈ keys (go rest (S.remove a)) ⊆ keys (S.remove a), contradiction
      have h_a_key := keys_go_subset_keys (S.remove a) rest a h
      obtain ⟨v, hv⟩ := HMaps.find?_of_mem_keys (S.remove a) a h_a_key
      rw [HMaps.find?_remove_self S a] at hv
      exact absurd hv (by simp)
    · exact ih (S.remove x) h h_rest

/-- If all keys of `S` not in `xs` are also not free vars of `body`, then
    `subst (subst.go xs S) body = body`. -/
private theorem subst_go_irrel_body (S : Subst)
    (xs : List TyIdentifier) (body : LMonoTy)
    (h : ∀ k, k ∈ HMaps.keys S → k ∉ xs → k ∉ LMonoTy.freeVars body) :
    LMonoTy.subst (LTy.subst.go xs S) body = body := by
  apply LMonoTy.subst_no_relevant_keys
  intro k hk_fv hk_key
  have hk_S := keys_go_subset_keys S xs k hk_key
  have hk_not_xs := keys_go_not_mem_xs S xs k hk_key
  exact h k hk_S hk_not_xs hk_fv

/-- A type-var-closed `LTy` (`freeVars = []`) is fixed by ANY substitution — no `boundVars = []`
    (monomorphism) needed. `LTy.subst` removes the bound vars from `S` (`go`), and every free var
    of the body lies among the bound vars (closedness), so no surviving key is relevant. -/
theorem LTy.subst_eq_self_of_closed (S : Subst) (ty : LTy) (h : LTy.freeVars ty = []) :
    LTy.subst S ty = ty := by
  cases ty with
  | forAll xs mty =>
    simp only [LTy.subst]
    congr 1
    apply subst_go_irrel_body
    intro k _ hk_notin hk_fv
    have hmem : k ∈ LTy.freeVars (LTy.forAll xs mty) := by
      rw [LTy.freeVars]
      unfold List.removeAll
      rw [List.mem_filter]
      exact ⟨hk_fv, by simp [hk_notin]⟩
    rw [h] at hmem; exact absurd hmem List.not_mem_nil

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- When `allKeysFresh S ctx` and `forAll xs body` is in the context,
    `subst (go xs S) body = body`: the bound-var-erased substitution
    has no effect on the body. -/
private theorem allKeysFresh_go_body_irrel
    (S : Subst) (ctx : TContext T.IDMeta)
    (x_id : T.Identifier) (xs : List TyIdentifier) (body : LMonoTy)
    (h_fresh : Subst.allKeysFresh (T := T) S ctx)
    (h_find : ctx.types.find? x_id = some (.forAll xs body)) :
    LMonoTy.subst (LTy.subst.go xs S) body = body := by
  apply subst_go_irrel_body
  intro k hk_S hk_not_xs
  -- k ∈ keys S, k ∉ xs. By allKeysFresh, k is fresh in ctx.
  have h_k_fresh := h_fresh k hk_S
  have h_k_not_fv := h_k_fresh x_id (.forAll xs body) h_find
  intro hk_fv
  apply h_k_not_fv
  show k ∈ (LMonoTy.freeVars body).removeAll xs
  simp only [List.removeAll, List.mem_filter, List.elem_eq_mem,
             Bool.not_eq_true', decide_eq_false_iff_not]
  exact ⟨hk_fv, hk_not_xs⟩

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Variant of `allKeysFresh_go_body_irrel` using `polyKeysFresh` instead of `allKeysFresh`.
    Since `xs` is non-empty (required by the polymorphic case), `polyKeysFresh` suffices. -/
private theorem polyKeysFresh_go_body_irrel
    (S : Subst) (ctx : TContext T.IDMeta)
    (x_id : T.Identifier) (xs : List TyIdentifier) (body : LMonoTy)
    (h_fresh : Subst.polyKeysFresh (T := T) S ctx)
    (h_find : ctx.types.find? x_id = some (.forAll xs body))
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

/-! ### `polyKeysFresh` preservation through `typeBoundVar`. -/

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `polyKeysFresh` is preserved through `typeBoundVar`: the new entry added by
    `typeBoundVar` is monomorphic (`forAll [] xty`), so `polyKeysFresh` for the
    extended context follows from `polyKeysFresh` for the original context. -/
private theorem polyKeysFresh_typeBoundVar
    (S : Subst) (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
    (h_tbv : typeBoundVar C Env bty = .ok (xv, xty, Env1))
    (h_poly : Subst.polyKeysFresh (T := T) S Env.context) :
    Subst.polyKeysFresh (T := T) S Env1.context := by
  intro a ha x ty hf hbv
  simp only [typeBoundVar, Bind.bind, Except.bind] at h_tbv
  cases h_lift : liftGenEnv HasGen.genVar Env with
  | error _ => rw [h_lift] at h_tbv; simp at h_tbv
  | ok res_lift =>
    obtain ⟨xv_raw, Env_g⟩ := res_lift
    rw [h_lift] at h_tbv; simp only at h_tbv
    have h_g_ctx : Env_g.context = Env.context := liftGenEnv_context Env _ Env_g h_lift
    cases bty with
    | some bty_val =>
      simp only at h_tbv
      cases h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g with
      | error _ => rw [h_ic] at h_tbv; simp at h_tbv
      | ok res_ic =>
        obtain ⟨mty_ic, Env_ic⟩ := res_ic
        rw [h_ic] at h_tbv
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h_tbv
        obtain ⟨_, _, h_env1⟩ := h_tbv; subst h_env1
        -- Env_ic.context = Env.context (by instantiateWithCheck context preservation)
        have h_ic_ctx : Env_ic.context = Env.context :=
          (LMonoTy_instantiateWithCheck_context' bty_val C Env_g _ Env_ic h_ic).trans h_g_ctx
        -- find? in addInNewestContext
        simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at hf
        rw [show Env_ic.genEnv.context.types = Env.context.types from
          congrArg TContext.types h_ic_ctx] at hf
        -- Use HMaps.find?_addInNewest_single to split
        rcases HMaps.find?_addInNewest_single Env.context.types xv_raw (.forAll [] mty_ic) x with
          ⟨h_found, _⟩ | h_same
        · -- Found the new entry: ty = forAll [] mty_ic
          rw [h_found] at hf; simp at hf; subst hf
          simp [LTy.boundVars] at hbv
        · -- Same as original: lookup in original context
          rw [h_same] at hf
          exact h_poly a ha x ty hf hbv
    | none =>
      simp only at h_tbv
      cases h_tg : TEnv.genTyVar Env_g with
      | error _ => rw [h_tg] at h_tbv; simp at h_tbv
      | ok res_tg =>
        obtain ⟨xtyid, Env_tg⟩ := res_tg
        rw [h_tg] at h_tbv
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h_tbv
        obtain ⟨_, _, h_env1⟩ := h_tbv; subst h_env1
        have h_tg_ctx : Env_tg.context = Env.context :=
          (TEnv.genTyVar_context Env_g xtyid Env_tg h_tg).trans h_g_ctx
        simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at hf
        rw [show Env_tg.genEnv.context.types = Env.context.types from
          congrArg TContext.types h_tg_ctx] at hf
        rcases HMaps.find?_addInNewest_single Env.context.types xv_raw (.forAll [] (LMonoTy.ftvar xtyid)) x with
          ⟨h_found, _⟩ | h_same
        · rw [h_found] at hf; simp at hf; subst hf
          simp [LTy.boundVars] at hbv
        · rw [h_same] at hf
          exact h_poly a ha x ty hf hbv

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Decompose `LMonoTys.instantiateEnv` into its components: fresh vars, substitution, and env. -/
private theorem instantiateEnv_decompose
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TEnv T.IDMeta)
    (result : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.instantiateEnv ids mtys Env = .ok (result, Env')) :
    ∃ (freshtvs : List TyIdentifier) (genEnv' : TGenEnv T.IDMeta),
      TGenEnv.genTyVars ids.length Env.genEnv = .ok (freshtvs, genEnv') ∧
      result = LMonoTys.subst (Strata.Util.HMaps.ofScopes
        [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) mtys ∧
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
    elim_err h_inner
    rename_i v h_gv; obtain ⟨ftvs, gE⟩ := v; simp at h_inner h_gv
    obtain ⟨h_res, h_ge⟩ := h_inner; subst h_ge
    exact ⟨ftvs, gE, h_gv, h_res.symm, rfl⟩

/-- Prepending a binding `(v, vl)` to `vars`/`vals` doesn't affect `openVarsList`
    on `ids.map ftvar` when `v ∉ ids`. -/
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

/-- `openVarsList vars vals (vars.map ftvar) = vals` when lengths match and
    `vars` is duplicate-free: each `ftvar vᵢ` looks up `vals[i]`. -/
private theorem openVarsList_map_ftvar_id
    (vars : List TyIdentifier) (vals : LMonoTys)
    (h_len : vars.length = vals.length)
    (h_nodup : vars.Nodup) :
    LMonoTys.openVars vars vals (vars.map .ftvar) = vals := by
  induction vars generalizing vals with
  | nil => cases vals with
    | nil => simp [LMonoTys.openVars]
    | cons _ _ => simp at h_len
  | cons v vs ih =>
    cases vals with
    | nil => simp at h_len
    | cons vl vls =>
      have h_v_notin : v ∉ vs := (List.nodup_cons.mp h_nodup).1
      simp only [List.map, LMonoTys.openVars]
      have h_head : LMonoTy.openVars (v :: vs) (vl :: vls) (.ftvar v) = vl := by
        simp [LMonoTy.openVars, List.zip, List.zipWith, BEq.beq]
      rw [h_head]
      congr 1
      rw [openVarsList_cons_skip_map_ftvar v vl vs vls vs h_v_notin]
      exact ih vls (by simp at h_len; exact h_len) (List.nodup_cons.mp h_nodup).2

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
  unfold LMonoTy.tconsAlias at h_tcons
  rw [h_find] at h_tcons
  simp only [] at h_tcons
  -- Decompose: instantiateEnv, then unify.
  elim_err h_tcons
  rename_i instTypes updatedEnv h_inst
  generalize h_u : Constraints.unify _ _ = u at h_tcons
  match u with
  | .error e => simp at h_tcons
  | .ok substInfo =>
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h_tcons
    obtain ⟨h_mty, h_env⟩ := h_tcons
    rw [← h_mty, ← h_env]
    simp only [TEnv.updateSubst]
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
    have h_map : instTypes = [LMonoTy.subst (Strata.Util.HMaps.ofScopes [List.zip alias.typeArgs fvs])
          (.tcons name (alias.typeArgs.map .ftvar)),
        LMonoTy.subst (Strata.Util.HMaps.ofScopes [List.zip alias.typeArgs fvs]) alias.type] := by
      rw [h_it, LMonoTys.subst_eq_map]; rfl
    rw [h_map]
    show LMonoTy.subst substInfo.subst (LMonoTy.subst substInfo.subst
        (LMonoTy.subst (Strata.Util.HMaps.ofScopes [List.zip alias.typeArgs fvs]) alias.type)) =
      alias.expand (LMonoTys.subst substInfo.subst args)
    -- Idempotency of the well-formed final substitution.
    rw [LMonoTy.subst_absorbs substInfo.subst substInfo.subst
      (LMonoTy.subst (Strata.Util.HMaps.ofScopes [List.zip alias.typeArgs fvs]) alias.type)
      (Subst.absorbs_refl _ substInfo.isWF)]
    rw [subst_single_scope_eq_openVars alias.typeArgs fvs alias.type h_wf.fvs_closed h_fvs_len h_nodup,
        subst_openVars_comm substInfo.subst alias.typeArgs fvs alias.type h_wf.fvs_closed h_fvs_len]
    simp only [TypeAlias.expand]; congr 1
    -- Unification made the input agree with the instantiated pattern.
    have h_unify_eq := unify_makes_equal (.tcons name args)
      (LMonoTy.subst (Strata.Util.HMaps.ofScopes [List.zip alias.typeArgs fvs])
        (.tcons name (alias.typeArgs.map .ftvar)))
      ({Env with genEnv := genEnv'} : TEnv T.IDMeta).stateSubstInfo substInfo (by
        rw [← h_u]; congr 1
        rw [h_map]; rfl)
    have h_pat_wf : ∀ tv, tv ∈ LMonoTy.freeVars (.tcons name (alias.typeArgs.map .ftvar)) →
        tv ∈ alias.typeArgs := by
      intro tv htv; simp only [LMonoTy.freeVars] at htv
      have h_ftvar_mem : ∀ (ids : List TyIdentifier),
          tv ∈ LMonoTys.freeVars (ids.map .ftvar) → tv ∈ ids := by
        intro ids h; induction ids with
        | nil => simp [LMonoTys.freeVars] at h
        | cons y ys ih =>
          simp only [List.map, LMonoTys.freeVars, LMonoTy.freeVars] at h
          cases List.mem_append.mp h <;> grind
      exact h_ftvar_mem alias.typeArgs htv
    rw [subst_single_scope_eq_openVars alias.typeArgs fvs _ h_pat_wf h_fvs_len h_nodup,
        subst_openVars_comm substInfo.subst alias.typeArgs fvs _ h_pat_wf h_fvs_len] at h_unify_eq
    simp only [LMonoTy.openVars] at h_unify_eq
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map] at h_unify_eq
    have h_args_eq := (LMonoTy.tcons.inj h_unify_eq).2
    rw [LMonoTys.subst_eq_map, h_args_eq]
    exact (openVarsList_map_ftvar_id alias.typeArgs _ (by
      rw [List.length_map]; exact h_fvs_len) h_nodup).symm

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
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
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h_tcons
    obtain ⟨h1, h2⟩ := h_tcons; rw [← h1]
  | some alias =>
    have h_alias_wf := h_aliases_wf alias (List.mem_of_find?_eq_some h_find)
    have h_pred := List.find?_some h_find
    simp only [Bool.and_eq_true, beq_iff_eq] at h_pred
    have h_bridge := tconsAlias_expand_eq name args Env mty' Env' alias
      h_tcons h_find h_alias_wf h_alias_wf.typeArgs_nodup
    rw [h_bridge]; simp only [TypeAlias.expand]
    rw [LMonoTys.subst_eq_map]
    exact (subst_openVars_comm Env'.stateSubstInfo.subst alias.typeArgs args alias.type
      h_alias_wf.fvs_closed h_pred.2).symm

mutual
/-- `AliasEquiv` is preserved under `subst`.
    The alias-equivalence geometry is representation-independent; only the
    witness substitution becomes `subst`. -/
theorem AliasEquiv_subst (aliases : List TypeAlias)
    (a b : LMonoTy) (S : Subst) (h : AliasEquiv aliases a b)
    (h_aw : ∀ alias, alias ∈ aliases → TypeAlias.WF alias) :
    AliasEquiv aliases (LMonoTy.subst S a) (LMonoTy.subst S b) := by
  match h with
  | .refl => exact .refl
  | @AliasEquiv.expand _ name args _ h_exp =>
    obtain ⟨alias, h_mem, h_name, h_len, h_expand⟩ := h_exp
    subst h_expand
    rw [LMonoTy.subst_tcons]
    refine .expand ⟨alias, h_mem, h_name, ?_, ?_⟩
    · rw [LMonoTys.subst_eq_map, List.length_map]; exact h_len
    · simp only [TypeAlias.expand]
      rw [subst_openVars_comm S alias.typeArgs args alias.type
            (h_aw alias h_mem).fvs_closed h_len,
          LMonoTys.subst_eq_map]
  | @AliasEquiv.collapse _ name args _ h_exp =>
    obtain ⟨alias, h_mem, h_name, h_len, h_expand⟩ := h_exp
    subst h_expand
    rw [LMonoTy.subst_tcons]
    refine .collapse ⟨alias, h_mem, h_name, ?_, ?_⟩
    · rw [LMonoTys.subst_eq_map, List.length_map]; exact h_len
    · simp only [TypeAlias.expand]
      rw [subst_openVars_comm S alias.typeArgs args alias.type
            (h_aw alias h_mem).fvs_closed h_len,
          LMonoTys.subst_eq_map]
  | .cong_tcons h_args =>
    rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons]
    exact .cong_tcons (AliasEquivList_subst aliases _ _ S h_args h_aw)
  | .trans h1 h2 =>
    exact .trans (AliasEquiv_subst aliases _ _ S h1 h_aw)
      (AliasEquiv_subst aliases _ _ S h2 h_aw)

/-- `AliasEquivList` is preserved under `subst`. -/
private theorem AliasEquivList_subst (aliases : List TypeAlias)
    (as bs : LMonoTys) (S : Subst) (h : AliasEquivList aliases as bs)
    (h_aw : ∀ alias, alias ∈ aliases → TypeAlias.WF alias) :
    AliasEquivList aliases (LMonoTys.subst S as) (LMonoTys.subst S bs) := by
  match h with
  | .nil => rw [LMonoTys.subst_nil]; exact .nil
  | .cons h_hd h_tl =>
    rw [LMonoTys.subst_eq_map, LMonoTys.subst_eq_map, List.map_cons, List.map_cons]
    refine .cons (AliasEquiv_subst aliases _ _ S h_hd h_aw) ?_
    rw [← LMonoTys.subst_eq_map, ← LMonoTys.subst_eq_map]
    exact AliasEquivList_subst aliases _ _ S h_tl h_aw
end

/-! ### Alias equivalence of `resolveAliases` output + subst-invariance -/

mutual
/-- `AliasEquiv` is symmetric. -/
theorem AliasEquiv.symm {aliases : List TypeAlias} {a b : LMonoTy}
    (h : AliasEquiv aliases a b) : AliasEquiv aliases b a := by
  match h with
  | .refl => exact .refl
  | .expand h_exp => exact .collapse h_exp
  | .collapse h_exp => exact .expand h_exp
  | .cong_tcons h_args => exact .cong_tcons (AliasEquivList.symm h_args)
  | .trans h1 h2 => exact .trans (AliasEquiv.symm h2) (AliasEquiv.symm h1)

/-- `AliasEquivList` is symmetric. -/
theorem AliasEquivList.symm {aliases : List TypeAlias} {as bs : LMonoTys}
    (h : AliasEquivList aliases as bs) : AliasEquivList aliases bs as := by
  match h with
  | .nil => exact .nil
  | .cons h_hd h_tl => exact .cons (AliasEquiv.symm h_hd) (AliasEquivList.symm h_tl)
end

/-- Opening a monomorphic scheme with the empty list is the identity. -/
private theorem openFull_nil_mono (mm : LMonoTy) : (LTy.forAll [] mm).openFull [] = mm := by
  simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe, List.zip_nil_left]
  rw [LMonoTy.subst_of_hasEmptyScopes (by
    simp only [Subst.hasEmptyScopes, HMaps.ofScopes, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, Bool.and_true]
    simp [HMap.isEmpty, HMap.ofList])]

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/--
Generalized (`∀ Γ'`-form) core of `HasType_context_aliasEquiv`, carrying a
PER-KEY freshness reflection hypothesis: every free tyvar occurring in a
`Γ'`-entry at key `x` already occurs in the `Γ`-entry at the SAME key. This is
what threads through the identical `insert`s in `tabs`/`tquant` (the *global*
transfer `isFresh a Γ → isFresh a Γ'` is too weak — it says nothing about the
entry shadowed by an insert) and implies the global transfer needed by `tgen`. -/
theorem HasType_context_aliasEquiv_gen
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono) (ty : LTy)
    (h : HasType C Γ e ty) :
    ∀ (Γ' : TContext T.IDMeta),
      Γ'.aliases = Γ.aliases →
      TContextAliasEquiv Γ.aliases Γ Γ' →
      (∀ (x : T.Identifier) (ty' : LTy), Γ'.types.find? x = some ty' →
        ∀ a, a ∈ LTy.freeVars ty' →
          ∃ ty0, Γ.types.find? x = some ty0 ∧ a ∈ LTy.freeVars ty0) →
      HasType C Γ' e ty := by
  induction h with
  | tbool_const Γ m b hk => intro Γ' _ _ _; exact HasType.tbool_const Γ' m b hk
  | tint_const Γ m n hk => intro Γ' _ _ _; exact HasType.tint_const Γ' m n hk
  | treal_const Γ m r hk => intro Γ' _ _ _; exact HasType.treal_const Γ' m r hk
  | tstr_const Γ m s hk => intro Γ' _ _ _; exact HasType.tstr_const Γ' m s hk
  | tbitvec_const Γ m n b hk => intro Γ' _ _ _; exact HasType.tbitvec_const Γ' m n b hk
  | tvar Γ m x ty h_find =>
    intro Γ' h_al h_ctx h_fr
    obtain ⟨mty, mty', h_ty_eq, h_find', h_ae⟩ := h_ctx x ty h_find
    subst h_ty_eq
    have h_tvar' : HasType C Γ' (.fvar m x none) (.forAll [] mty') :=
      HasType.tvar Γ' m x (.forAll [] mty') h_find'
    exact HasType.talias Γ' (.fvar m x none) mty' mty (by rw [h_al]; exact h_ae) h_tvar'
  | tvar_annotated Γ m x ty_o ty_s tys ann h_find h_len h_open h_annot =>
    intro Γ' h_al h_ctx h_fr
    obtain ⟨mty, mty', h_ty_eq, h_find', h_ae⟩ := h_ctx x ty_o h_find
    subst h_ty_eq
    have h_len0 : tys.length = 0 := by simpa [LTy.boundVars] using h_len
    have h_tys_nil : tys = [] := List.length_eq_zero_iff.mp h_len0
    subst h_tys_nil
    have h_ts : ty_s = mty := by rw [← h_open, openFull_nil_mono]
    subst h_ts
    have h_annot' : AnnotCompat Γ'.aliases ann mty' := by
      rw [h_al]
      obtain ⟨σ, h_σ⟩ := h_annot
      exact ⟨σ, h_σ.trans (AliasEquiv.symm h_ae)⟩
    have h_va : HasType C Γ' (.fvar m x (some ann)) (.forAll [] mty') :=
      HasType.tvar_annotated Γ' m x (.forAll [] mty') mty' [] ann h_find'
        (by simp [LTy.boundVars]) (openFull_nil_mono mty') h_annot'
    exact HasType.talias Γ' (.fvar m x (some ann)) mty' ty_s (by rw [h_al]; exact h_ae) h_va
  | tabs Γ m name x x_ty e e_ty o h_fresh hx he h_body h_o ih_body =>
    intro Γ' h_al h_ctx h_fr
    -- Apply the body IH at the extended contexts `Γ.insert x x_ty` / `Γ'.insert x x_ty`.
    refine HasType.tabs Γ' m name x x_ty e e_ty o h_fresh hx he
      (ih_body { Γ' with types := Γ'.types.insert x.fst x_ty } h_al ?_ ?_) ?_
    · -- TContextAliasEquiv at the extended contexts.
      intro y ty_y h_find_y
      by_cases h_xy : y = x.fst
      · -- shadowed key: both sides hold `x_ty`; use x_ty's mono shape + refl.
        subst h_xy
        rw [HMaps.find?_insert_self] at h_find_y
        -- x_ty is a monotype: x_ty = forAll [] mm.
        obtain ⟨mm, h_xty⟩ : ∃ mm, x_ty = .forAll [] mm := by
          cases x_ty with
          | forAll vs mm =>
            have h_vs : vs = [] := by
              have h_be : (LTy.forAll vs mm).boundVars.isEmpty = true := hx
              simp only [LTy.boundVars, List.isEmpty_iff] at h_be
              exact h_be
            exact ⟨mm, by rw [h_vs]⟩
        obtain ⟨h_yeq⟩ : ty_y = x_ty ∧ True := ⟨by injection h_find_y with h; exact h.symm, trivial⟩
        subst h_yeq
        refine ⟨mm, mm, h_xty, ?_, AliasEquiv.refl⟩
        rw [h_xty, HMaps.find?_insert_self]
      · -- other key: reduce to the Γ/Γ' equivalence.
        rw [HMaps.find?_insert_ne _ _ _ _ h_xy] at h_find_y
        obtain ⟨mty, mty', h_ty_eq, h_find', h_ae⟩ := h_ctx y ty_y h_find_y
        refine ⟨mty, mty', h_ty_eq, ?_, h_ae⟩
        rw [HMaps.find?_insert_ne _ _ _ _ h_xy]; exact h_find'
    · -- per-key freshness reflection at the extended contexts.
      intro y ty_y h_find_y a h_mem
      by_cases h_xy : y = x.fst
      · -- shadowed key: both sides hold `x_ty`; reflection is trivial.
        subst h_xy
        rw [HMaps.find?_insert_self] at h_find_y
        obtain ⟨h_yeq⟩ : ty_y = x_ty ∧ True := ⟨by injection h_find_y with h; exact h.symm, trivial⟩
        subst h_yeq
        exact ⟨ty_y, HMaps.find?_insert_self _ _ _, h_mem⟩
      · -- other key: reduce to the Γ/Γ' reflection.
        rw [HMaps.find?_insert_ne _ _ _ _ h_xy] at h_find_y
        obtain ⟨ty0, h_find0, h_mem0⟩ := h_fr y ty_y h_find_y a h_mem
        exact ⟨ty0, by rw [HMaps.find?_insert_ne _ _ _ _ h_xy]; exact h_find0, h_mem0⟩
    · rw [h_al]; exact h_o
  | tapp Γ m e1 e2 t1 t2 h1 h2 h_e1 h_e2 ih_e1 ih_e2 =>
    intro Γ' h_al h_ctx h_fr
    exact HasType.tapp Γ' m e1 e2 t1 t2 h1 h2 (ih_e1 Γ' h_al h_ctx h_fr) (ih_e2 Γ' h_al h_ctx h_fr)
  | tinst Γ e ty e_ty x x_ty h_e h_eqty ih_e =>
    intro Γ' h_al h_ctx h_fr
    subst h_eqty
    exact HasType.tinst Γ' e ty (LTy.open x x_ty ty) x x_ty (ih_e Γ' h_al h_ctx h_fr) rfl
  | tgen Γ e a ty h_e h_isfresh ih_e =>
    intro Γ' h_al h_ctx h_fr
    -- Derive `isFresh a Γ'` from `isFresh a Γ` (`h_isfresh`) via the per-key
    -- reflection: any `a`-occurrence in a Γ'-entry reflects to a Γ-entry at the
    -- same key, contradicting `h_isfresh`.
    have h_fresh' : TContext.isFresh a Γ' := by
      intro x ty' h_find h_mem
      obtain ⟨ty0, h_find0, h_mem0⟩ := h_fr x ty' h_find a h_mem
      exact h_isfresh x ty0 h_find0 h_mem0
    exact HasType.tgen Γ' e a ty (ih_e Γ' h_al h_ctx h_fr) h_fresh'
  | tif Γ m c e1 e2 ty h_c h_e1 h_e2 ih_c ih_e1 ih_e2 =>
    intro Γ' h_al h_ctx h_fr
    exact HasType.tif Γ' m c e1 e2 ty (ih_c Γ' h_al h_ctx h_fr) (ih_e1 Γ' h_al h_ctx h_fr)
      (ih_e2 Γ' h_al h_ctx h_fr)
  | teq Γ m e1 e2 ty h_e1 h_e2 ih_e1 ih_e2 =>
    intro Γ' h_al h_ctx h_fr
    exact HasType.teq Γ' m e1 e2 ty (ih_e1 Γ' h_al h_ctx h_fr) (ih_e2 Γ' h_al h_ctx h_fr)
  | tquant Γ m k name tr tr_ty x x_ty e o h_fresh hx h_body h_tr h_o ih_body ih_tr =>
    intro Γ' h_al h_ctx h_fr
    -- x_ty is a monotype: x_ty = forAll [] mm.
    obtain ⟨mm, h_xty⟩ : ∃ mm, x_ty = .forAll [] mm := by
      cases x_ty with
      | forAll vs mm =>
        have h_vs : vs = [] := by
          have h_be : (LTy.forAll vs mm).boundVars.isEmpty = true := hx
          simp only [LTy.boundVars, List.isEmpty_iff] at h_be
          exact h_be
        exact ⟨mm, by rw [h_vs]⟩
    -- Shared: TContextAliasEquiv at the extended contexts.
    have h_ctx_ext : TContextAliasEquiv Γ.aliases
        { Γ with types := Γ.types.insert x.fst x_ty }
        { Γ' with types := Γ'.types.insert x.fst x_ty } := by
      intro y ty_y h_find_y
      by_cases h_xy : y = x.fst
      · subst h_xy
        rw [HMaps.find?_insert_self] at h_find_y
        obtain ⟨h_yeq⟩ : ty_y = x_ty ∧ True := ⟨by injection h_find_y with h; exact h.symm, trivial⟩
        subst h_yeq
        refine ⟨mm, mm, h_xty, ?_, AliasEquiv.refl⟩
        rw [h_xty, HMaps.find?_insert_self]
      · rw [HMaps.find?_insert_ne _ _ _ _ h_xy] at h_find_y
        obtain ⟨mty, mty', h_ty_eq, h_find', h_ae⟩ := h_ctx y ty_y h_find_y
        refine ⟨mty, mty', h_ty_eq, ?_, h_ae⟩
        rw [HMaps.find?_insert_ne _ _ _ _ h_xy]; exact h_find'
    -- Shared: per-key freshness reflection at the extended contexts.
    have h_fr_ext : ∀ (y : T.Identifier) (ty' : LTy),
        ({ Γ' with types := Γ'.types.insert x.fst x_ty } : TContext T.IDMeta).types.find? y = some ty' →
        ∀ a, a ∈ LTy.freeVars ty' →
          ∃ ty0, ({ Γ with types := Γ.types.insert x.fst x_ty } : TContext T.IDMeta).types.find? y = some ty0
            ∧ a ∈ LTy.freeVars ty0 := by
      intro y ty_y h_find_y a h_mem
      by_cases h_xy : y = x.fst
      · subst h_xy
        rw [HMaps.find?_insert_self] at h_find_y
        obtain ⟨h_yeq⟩ : ty_y = x_ty ∧ True := ⟨by injection h_find_y with h; exact h.symm, trivial⟩
        subst h_yeq
        exact ⟨ty_y, HMaps.find?_insert_self _ _ _, h_mem⟩
      · rw [HMaps.find?_insert_ne _ _ _ _ h_xy] at h_find_y
        obtain ⟨ty0, h_find0, h_mem0⟩ := h_fr y ty_y h_find_y a h_mem
        exact ⟨ty0, by rw [HMaps.find?_insert_ne _ _ _ _ h_xy]; exact h_find0, h_mem0⟩
    exact HasType.tquant Γ' m k name tr tr_ty x x_ty e o h_fresh hx
      (ih_body _ h_al h_ctx_ext h_fr_ext) (ih_tr _ h_al h_ctx_ext h_fr_ext)
      (by rw [h_al]; exact h_o)
  | top Γ m f op ty h_find h_type => intro Γ' _ _ _; exact HasType.top Γ' m f op ty h_find h_type
  | top_annotated Γ m f op ty_o ty_s tys ann h_find h_type h_len h_open h_annot =>
    intro Γ' h_al h_ctx h_fr
    exact HasType.top_annotated Γ' m f op ty_o ty_s tys ann h_find h_type h_len h_open
      (by rw [h_al]; exact h_annot)
  | talias Γ e mty mty' h_equiv h_e ih_e =>
    intro Γ' h_al h_ctx h_fr
    exact HasType.talias Γ' e mty mty' (by rw [h_al]; exact h_equiv) (ih_e Γ' h_al h_ctx h_fr)

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/--
`HasType` transfers along an alias-equivalent context: if `e : ty` in `Γ`, and
`Γ'` has the same aliases and bindings alias-equivalent to `Γ`'s, then `e : ty`
in `Γ'`. The `h_fresh` hypothesis (per-key freshness reflection: every free tyvar
in a `Γ'`-entry reflects to the `Γ`-entry at the same key) is required by the
`tgen` generalization rule and is dischargeable at the call sites because aliases
are non-dropping, so `freeVars(Γ'-entry) ⊆ freeVars(Γ-entry)`. -/
theorem HasType_context_aliasEquiv
    (C : LContext T) (Γ Γ' : TContext T.IDMeta) (e : LExpr T.mono) (ty : LTy)
    (h : HasType C Γ e ty)
    (h_alias : Γ'.aliases = Γ.aliases)
    (h_ctx : TContextAliasEquiv Γ.aliases Γ Γ')
    (h_fresh : ∀ (x : T.Identifier) (ty' : LTy), Γ'.types.find? x = some ty' →
      ∀ a, a ∈ LTy.freeVars ty' →
        ∃ ty0, Γ.types.find? x = some ty0 ∧ a ∈ LTy.freeVars ty0) :
    HasType C Γ' e ty :=
  HasType_context_aliasEquiv_gen C Γ e ty h Γ' h_alias h_ctx h_fresh

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
mutual
/-- `LMonoTy.resolveAliases` (with `tconsAliasSimple`) produces alias-equivalent output. -/
private theorem resolveAliases_aliasEquiv {Γ : TContext T.IDMeta}
    (mty : LMonoTy) (Env : TEnv T.IDMeta) (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env'))
    (h_aliases : Γ.aliases = Env.context.aliases)
    (h_aliases_wf : ∀ a, a ∈ Γ.aliases → a.WF) :
    AliasEquiv Γ.aliases mty mty' := by
  match mty with
  | .ftvar _ | .bitvec _ =>
    simp [LMonoTy.resolveAliases] at h
    obtain ⟨rfl, _⟩ := h; exact .refl
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_args; obtain ⟨args', Env1⟩ := v1; simp at h h_args
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
private theorem resolveAliasList_aliasEquiv {Γ : TContext T.IDMeta}
    (mtys : LMonoTys) (Env : TEnv T.IDMeta) (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env'))
    (h_aliases : Γ.aliases = Env.context.aliases)
    (h_aliases_wf : ∀ a, a ∈ Γ.aliases → a.WF) :
    AliasEquivList Γ.aliases mtys mtys' := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases] at h
    obtain ⟨rfl, _⟩ := h; exact .nil
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_hd; obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    elim_err h
    rename_i v2 h_tl; obtain ⟨mrest', Env2⟩ := v2
    simp at h; obtain ⟨rfl, _⟩ := h
    have h_ctx_pres := LMonoTy.resolveAliases_context mty Env mty' Env1 h_hd
    exact .cons
      (resolveAliases_aliasEquiv mty Env mty' Env1 h_hd h_aliases h_aliases_wf)
      (resolveAliasList_aliasEquiv mrest Env1 mrest' Env2 h_tl
        (by rw [h_aliases, ← h_ctx_pres]) h_aliases_wf)
end

mutual
/-- `LMonoTy.resolveAliases` preserves `stateSubstInfo` (with `tconsAliasSimple`,
    alias resolution is pure — it never modifies the substitution). -/
private theorem LMonoTy_resolveAliases_subst_eq {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (mty : LMonoTy) (Env : TEnv IDMeta) (mty' : LMonoTy) (Env' : TEnv IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  match mty with
  | .ftvar _ =>
    simp [LMonoTy.resolveAliases] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
  | .bitvec _ =>
    simp [LMonoTy.resolveAliases] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
  | .tcons _ args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_args; obtain ⟨args', Env1⟩ := v1; simp at h h_args
    simp only [LMonoTy.tconsAliasSimple] at h
    split at h <;> (obtain ⟨_, h2⟩ := h; rw [← h2])
    all_goals exact LMonoTys_resolveAliases_subst_eq args Env args' Env1 h_args

private theorem LMonoTys_resolveAliases_subst_eq {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (mtys : LMonoTys) (Env : TEnv IDMeta) (mtys' : LMonoTys) (Env' : TEnv IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_hd; obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    elim_err h
    rename_i v2 h_tl; obtain ⟨mrest', Env2⟩ := v2
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    exact (LMonoTys_resolveAliases_subst_eq mrest Env1 mrest' Env2 h_tl).trans
      (LMonoTy_resolveAliases_subst_eq mty Env mty' Env1 h_hd)
end

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `LTy.resolveAliases` preserves `stateSubstInfo` (it only touches `genEnv`). -/
private theorem LTy_resolveAliases_subst_eq
    (ty : LTy) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.resolveAliases ty Env = .ok (mty, Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  simp [LTy.resolveAliases, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_inst
  obtain ⟨mty0, genEnv'⟩ := v1; simp at h h_inst
  exact LMonoTy_resolveAliases_subst_eq mty0
    {Env with genEnv := genEnv'} mty Env' h

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `LTy.resolveAliases` leaves the type-generator counter monotone (non-decreasing). -/
private theorem LTy_resolveAliases_genState_mono
    (ty : LTy) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.resolveAliases ty Env = .ok (mty, Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  simp [LTy.resolveAliases, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_inst
  obtain ⟨mty0, genEnv'⟩ := v1; simp at h h_inst
  have h_ra_mono := LMonoTy_resolveAliases_genState_mono mty0
    {Env with genEnv := genEnv'} mty Env' h
  simp [LTy.instantiate, Bind.bind, Except.bind] at h_inst
  split at h_inst
  · simp at h_inst; obtain ⟨_, h2⟩ := h_inst; rw [← h2] at h_ra_mono; exact h_ra_mono
  · elim_err h_inst
    rename_i v2 h_gen
    obtain ⟨tvs, Env1⟩ := v2; simp at h_inst h_gen
    obtain ⟨_, h2⟩ := h_inst; rw [← h2] at h_ra_mono
    exact Nat.le_trans (genTyVars_tyGen_mono _ Env.genEnv tvs Env1 h_gen) h_ra_mono

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `LTy.instantiateWithCheck` preserves `TEnvWF`. -/
theorem LTy_instantiateWithCheck_TEnvWF
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env'))
    (h_wf : TEnvWF Env) : TEnvWF Env' := by
  have h_ctx := LTy_instantiateWithCheck_context' ty C Env mty Env' h
  simp [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_ra; obtain ⟨mty', Env1⟩ := v1
  elim_errs h
  simp at h
  obtain ⟨_, h2⟩ := h; subst h2
  have h_subst := LTy_resolveAliases_subst_eq ty Env mty' Env1 h_ra
  have h_gen_mono := LTy_resolveAliases_genState_mono ty Env mty' Env1 h_ra
  exact {
    aliasesWF := h_ctx ▸ h_wf.aliasesWF
    substFreshForGen := h_subst ▸ SubstFreshForGen.mono _ _ _ h_wf.substFreshForGen h_gen_mono
    ctxFreshForGen := h_ctx ▸ ContextFreshForGen.mono _ _ _
      h_wf.ctxFreshForGen h_gen_mono
    boundVarsNodup := fun y xty hf => h_wf.boundVarsNodup y xty (h_ctx ▸ hf)
    boundVarsFresh := fun y xty hf v hv n hn =>
      h_wf.boundVarsFresh y xty (h_ctx ▸ hf) v hv n (Nat.le_trans h_gen_mono hn)
  }

/-- `subst S (ftvar v) = t` when `find? S v = some t`. -/
private theorem LMonoTy.subst_ftvar_eq
    (S : Subst) (v : TyIdentifier) (t : LMonoTy)
    (h_find : HMaps.find? S v = some t) :
    LMonoTy.subst S (.ftvar v) = t := by
  rw [LMonoTy.subst_unfold]; simp only [h_find]

omit [ToString
  T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `LTy.instantiate` opens the scheme's bound variables with freshly generated
    type variables — i.e. it is exactly `LTy.openFull ty` applied to those fresh
    variables, with the count matching `ty.boundVars`. -/
theorem LTy_instantiate_eq_openFull (ty : LTy) (Env Env' : TGenEnv T.IDMeta)
    (mty : LMonoTy) (h : LTy.instantiate ty Env = .ok (mty, Env')) :
    ∃ tys, tys.length = (LTy.boundVars ty).length ∧ LTy.openFull ty tys = mty := by
  match ty with
  | .forAll [] body =>
    simp only [LTy.instantiate, Except.ok.injEq, Prod.mk.injEq] at h
    refine ⟨[], by simp [LTy.boundVars], ?_⟩
    simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe, List.zip_nil_left]
    rw [LMonoTy.subst_of_hasEmptyScopes (by
      simp only [Subst.hasEmptyScopes, HMaps.ofScopes, List.map_cons, List.map_nil, List.all_cons,
        List.all_nil, Bool.and_true]
      simp [HMap.isEmpty, HMap.ofList]), h.1]
  | .forAll (x :: xs) body =>
    simp only [LTy.instantiate, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_gen; obtain ⟨freshtvs, genEnv1⟩ := v1
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    have h_len := TGenEnv.genTyVars_length (x :: xs).length Env freshtvs genEnv1 h_gen
    refine ⟨freshtvs.map LMonoTy.ftvar, ?_, ?_⟩
    · simp [LTy.boundVars, h_len]
    · simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe]
      rw [← h.1]

omit [ToString
  T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `LTy.instantiateWithCheck` produces a monotype that is an instantiation of the
    declared scheme `ty`, up to alias equivalence: there is a list of monotypes `tys`
    (one per bound variable of `ty`) such that `openFull ty tys` is alias-equivalent
    to the produced monotype. `instantiateWithCheck` first instantiates the scheme's
    ∀-bound variables with fresh type variables (`LTy.instantiate`, giving `openFull`)
    and then resolves type aliases (`LMonoTy.resolveAliases`, giving the `AliasEquiv`). -/
theorem LTy_instantiateWithCheck_isInstance
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    ∃ tys, tys.length = (LTy.boundVars ty).length ∧
      AliasEquiv Env.context.aliases (LTy.openFull ty tys) mty := by
  -- Peel off `LTy.resolveAliases`; the two registration checks are pure (`mty = mty_ra`).
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_ra; obtain ⟨mty_ra, Env_ra⟩ := v1
  elim_errs h
  cases h
  -- Decompose `LTy.resolveAliases` into `instantiate` then `LMonoTy.resolveAliases`.
  simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
  elim_err h_ra
  rename_i v2 h_inst; obtain ⟨mty_inst, genEnv1⟩ := v2
  obtain ⟨tys, h_len, h_open⟩ :=
    LTy_instantiate_eq_openFull ty Env.genEnv genEnv1 mty_inst h_inst
  refine ⟨tys, h_len, ?_⟩
  rw [h_open]
  have h_ctx_inst := LTy.instantiate_context ty Env.genEnv mty_inst genEnv1 h_inst
  have h_aliases_eq : Env.context.aliases =
      ({Env with genEnv := genEnv1} : TEnv T.IDMeta).context.aliases := by
    simp [TEnv.context]; rw [h_ctx_inst]
  exact resolveAliases_aliasEquiv (Γ := Env.context) mty_inst
    { Env with genEnv := genEnv1 } mty_ra Env_ra h_ra h_aliases_eq h_aw

/-- `LMonoTys.subst` distributes over `cons`. -/
theorem subst_cons_eq' (S : Subst) (hd : LMonoTy) (tl : LMonoTys) :
    LMonoTys.subst S (hd :: tl) = LMonoTy.subst S hd :: LMonoTys.subst S tl := by
  rw [LMonoTys.subst_eq_map, LMonoTys.subst_eq_map, List.map_cons]

/-- `subst σ` distributes over `openVars` for a renaming `σ` when the body's free
    vars are covered by `vars` (so args-substitution suffices). -/
theorem subst_openVars_comm' (σ : Subst)
    (vars : List TyIdentifier) (vals : LMonoTys) (body : LMonoTy)
    (h_wf : ∀ tv, tv ∈ LMonoTy.freeVars body → tv ∈ vars)
    (h_len : vars.length = vals.length) :
    LMonoTy.subst σ (LMonoTy.openVars vars vals body) =
      LMonoTy.openVars vars (LMonoTys.subst σ vals) body := by
  rw [LMonoTys.subst_eq_map]
  exact subst_openVars_comm σ vars vals body h_wf h_len

/-- Renaming commutes with `tconsAliasSimple` when aliases are WF. Renaming preserves
    arity so the same alias matches; the expand step commutes because the alias body's
    free vars are all in its typeArgs. -/
theorem tconsAliasSimple_subst_comm (σ : Subst) (name : String) (args : LMonoTys)
    (aliases : List TypeAlias) (h_aw : ∀ a, a ∈ aliases → TypeAlias.WF a) :
    LMonoTy.tconsAliasSimple name (LMonoTys.subst σ args) aliases =
      LMonoTy.subst σ (LMonoTy.tconsAliasSimple name args aliases) := by
  have h_len : (LMonoTys.subst σ args).length = args.length :=
    LMonoTys.subst_length σ args
  simp only [LMonoTy.tconsAliasSimple]
  have h_find_eq : aliases.find? (fun a => a.name == name && a.typeArgs.length == (LMonoTys.subst σ args).length)
      = aliases.find? (fun a => a.name == name && a.typeArgs.length == args.length) := by
    rw [h_len]
  rw [h_find_eq]
  cases h_alias : aliases.find? (fun a => a.name == name && a.typeArgs.length == args.length) with
  | none =>
    rw [LMonoTy.subst_tcons]
  | some alias =>
    have h_alias_wf := h_aw alias (List.mem_of_find?_eq_some h_alias)
    have h_pred := List.find?_some h_alias
    simp only [Bool.and_eq_true, beq_iff_eq] at h_pred
    -- expand alias (subst σ args) = subst σ (expand alias args)
    simp only [TypeAlias.expand]
    have h_ta_len : alias.typeArgs.length = args.length := h_pred.2
    rw [subst_openVars_comm' σ alias.typeArgs args alias.type h_alias_wf.fvs_closed h_ta_len]

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Variables produced by `genTyVars` are distinct: the recursion emits
    `tyPrefix ++ toString k` for strictly increasing `k`. -/
theorem genTyVars_nodup
    (n : Nat) (Env : TGenEnv T.IDMeta) (tvs : List TyIdentifier) (Env' : TGenEnv T.IDMeta)
    (h : TGenEnv.genTyVars n Env = .ok (tvs, Env')) :
    tvs.Nodup := by
  induction n generalizing Env tvs Env' with
  | zero =>
    simp only [TGenEnv.genTyVars, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, _⟩ := h; subst h1; exact List.nodup_nil
  | succ m ih =>
    simp only [TGenEnv.genTyVars, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_gen1; obtain ⟨tv1, Env1⟩ := v1
    elim_err h
    rename_i v2 h_gen_rest; obtain ⟨rest, Env2⟩ := v2
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_tvs, _⟩ := h; subst h_tvs
    have h_tv1_name : tv1 = TState.tyPrefix ++ toString Env.genState.tyGen := by
      simp only [TGenEnv.genTyVar] at h_gen1
      elim_err h_gen1
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_gen1; rw [← h_gen1.1]
      simp [TState.genTySym, TState.incTyGen]
    have h_gen1_mono : Env1.genState.tyGen = Env.genState.tyGen + 1 := by
      simp only [TGenEnv.genTyVar] at h_gen1
      elim_err h_gen1
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_gen1; rw [← h_gen1.2]
      simp [TState.genTySym, TState.incTyGen]
    have h_rest_nodup := ih Env1 rest Env2 h_gen_rest
    refine List.nodup_cons.mpr ⟨?_, h_rest_nodup⟩
    -- tv1 ∉ rest: each element of rest has index ≥ Env1.genState.tyGen = tyGen+1 > tyGen
    intro h_mem
    obtain ⟨k, h_k_ge, h_k_eq⟩ :=
      TGenEnv.genTyVars_is_genName m Env1 rest Env2 h_gen_rest tv1 h_mem
    rw [h_tv1_name] at h_k_eq
    have h_str_inj : Env.genState.tyGen = k := by
      rw [String.ext_iff] at h_k_eq
      simp only [String.toList_append] at h_k_eq
      exact Nat.toString_injective (String.toList_injective
        (List.append_cancel_left h_k_eq))
    omega

/-- The zip `zip fresh (map ftvar ids)` has distinct keys when `fresh.Nodup`. -/
private theorem zip_ftvar_distinct (fresh ids : List TyIdentifier) (h_nodup : fresh.Nodup) :
    List.Pairwise (fun a b => (a.fst == b.fst) = false)
      (List.zip fresh (List.map LMonoTy.ftvar ids)) := by
  induction fresh generalizing ids with
  | nil => simp
  | cons f fs ih =>
    cases ids with
    | nil => simp
    | cons i is =>
      simp only [List.map_cons, List.zip_cons_cons, List.pairwise_cons]
      obtain ⟨h_notin, h_nd⟩ := List.pairwise_cons.mp h_nodup
      refine ⟨fun p hp => ?_, ih is h_nd⟩
      simp only [beq_eq_false_iff_ne]
      intro h_eq; exact h_notin p.1 (List.of_mem_zip hp).1 (h_eq ▸ rfl)

/-- Round-trip on a single `.ftvar`: for `x ∈ ids`, the forward renaming
    `σ = ofList (zip ids (map ftvar freshtvs))` sends `x` to some fresh `ftv ∈ freshtvs`,
    and the inverse renaming `ρ₀ = ofList (zip freshtvs (map ftvar ids))` sends `ftv`
    back to `x`. Requires `freshtvs.Nodup` so the inverse lookup is unambiguous.
    (`ids.Nodup` is NOT needed: the forward value is read off whatever entry the map
    holds, and its unique fresh preimage inverts back to a correct `ids` slot.) -/
theorem find?_zip_ftvar_roundtrip
    (ids freshtvs : List TyIdentifier)
    (h_len : ids.length = freshtvs.length)
    (h_nodup : freshtvs.Nodup)
    (x : TyIdentifier) (h_mem : x ∈ ids) :
    ∃ ftv, ftv ∈ freshtvs ∧
      HMap.find? (HMap.ofList (List.zip ids (List.map LMonoTy.ftvar freshtvs))) x = some (.ftvar ftv) ∧
      HMap.find? (HMap.ofList (List.zip freshtvs (List.map LMonoTy.ftvar ids))) ftv = some (.ftvar x) := by
  -- Forward lookup succeeds (x is a key), returning some `.ftvar`-value.
  have h_keys : x ∈ (List.zip ids (List.map LMonoTy.ftvar freshtvs)).map Prod.fst := by
    rw [List.map_fst_zip (by simp [h_len])]; exact h_mem
  obtain ⟨w, hw⟩ := HMap.find?_ofList_of_mem_keys _ x h_keys
  -- `(x, w)` is a genuine entry, so it sits at a shared index `i`.
  obtain ⟨i, hi, h_get⟩ := List.getElem_of_mem (HMap.find?_ofList_mem _ x w hw)
  have hi_ids : i < ids.length := by
    simp only [List.length_zip, List.length_map] at hi; omega
  have hi_f : i < freshtvs.length := by omega
  have h_zget : (List.zip ids (List.map LMonoTy.ftvar freshtvs))[i]'hi =
      (ids[i], (List.map LMonoTy.ftvar freshtvs)[i]'(by simp [List.length_map]; omega)) :=
    List.getElem_zip
  rw [h_zget] at h_get
  have h_xi : ids[i] = x := (Prod.mk.injEq .. ▸ h_get).1
  have h_wi : (List.map LMonoTy.ftvar freshtvs)[i]'(by simp [List.length_map]; omega) = w :=
    (Prod.mk.injEq .. ▸ h_get).2
  rw [List.getElem_map] at h_wi
  refine ⟨freshtvs[i], List.getElem_mem hi_f, by rw [hw, ← h_wi], ?_⟩
  -- Backward: `(freshtvs[i], .ftvar ids[i]) ∈ zip freshtvs (map ftvar ids)`, and
  -- `freshtvs.Nodup` makes the lookup return it.
  apply HMap.find?_ofList_of_mem _ _ _ (zip_ftvar_distinct freshtvs ids h_nodup)
  have h_bget : (List.zip freshtvs (List.map LMonoTy.ftvar ids))[i]'(by
        simp [List.length_zip, List.length_map]; omega) =
      (freshtvs[i], LMonoTy.ftvar ids[i]) := by rw [List.getElem_zip, List.getElem_map]
  rw [h_xi] at h_bget
  exact h_bget ▸ List.getElem_mem _

/-- `subst [ρ₀]` inverts the fresh-renaming `subst [σ]` on a body whose free vars
    are all in `ids`, where `σ = zip ids (map ftvar freshtvs)` and
    `ρ₀ = zip freshtvs (map ftvar ids)`. Requires `freshtvs` distinct so the inverse
    lookup is well-defined. -/
theorem subst_rename_inverse
    (ids freshtvs : List TyIdentifier)
    (h_len : ids.length = freshtvs.length)
    (h_fresh_nodup : freshtvs.Nodup)
    (body : LMonoTy)
    (h_closed : ∀ v, v ∈ LMonoTy.freeVars body → v ∈ ids) :
    LMonoTy.subst (HMaps.ofScopes [List.zip freshtvs (List.map LMonoTy.ftvar ids)])
      (LMonoTy.subst (HMaps.ofScopes [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) body)
      = body := by
  -- Generalize over the body so the induction hypothesis carries the closedness premise.
  suffices H : ∀ b : LMonoTy, (∀ v, v ∈ LMonoTy.freeVars b → v ∈ ids) →
      LMonoTy.subst (HMaps.ofScopes [List.zip freshtvs (List.map LMonoTy.ftvar ids)])
        (LMonoTy.subst (HMaps.ofScopes [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) b) = b from
    H body h_closed
  intro b
  induction b with
  | ftvar x =>
    intro hcl
    have h_x_ids : x ∈ ids := hcl x (by simp [LMonoTy.freeVars])
    obtain ⟨ftv, _, h_fwd, h_bwd⟩ :=
      find?_zip_ftvar_roundtrip ids freshtvs h_len h_fresh_nodup x h_x_ids
    -- `HMaps.find?` on a single scope is the scope's `HMap.find?`.
    have h_fwd' : HMaps.find? (HMaps.ofScopes [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) x
        = some (.ftvar ftv) := by
      simp only [HMaps.ofScopes, List.map_cons, List.map_nil, HMaps.find?_single_scope]; exact h_fwd
    have h_bwd' : HMaps.find? (HMaps.ofScopes [List.zip freshtvs (List.map LMonoTy.ftvar ids)]) ftv
        = some (.ftvar x) := by
      simp only [HMaps.ofScopes, List.map_cons, List.map_nil, HMaps.find?_single_scope]; exact h_bwd
    rw [LMonoTy.subst_ftvar_eq _ x (.ftvar ftv) h_fwd']
    exact LMonoTy.subst_ftvar_eq _ ftv (.ftvar x) h_bwd'
  | bitvec n =>
    intro _
    rw [LMonoTy.subst_bitvec, LMonoTy.subst_bitvec]
  | tcons name args ih =>
    intro hcl
    -- Reduce to a list-level round-trip over the arguments.
    have h_list : ∀ (l : LMonoTys),
        (∀ ty ∈ l, LMonoTy.subst (HMaps.ofScopes [List.zip freshtvs (List.map LMonoTy.ftvar ids)])
          (LMonoTy.subst (HMaps.ofScopes [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) ty) = ty) →
        LMonoTys.subst (HMaps.ofScopes [List.zip freshtvs (List.map LMonoTy.ftvar ids)])
          (LMonoTys.subst (HMaps.ofScopes [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) l) = l := by
      intro l
      induction l with
      | nil => intro _; rw [LMonoTys.subst_nil, LMonoTys.subst_nil]
      | cons hd tl ihl =>
        intro hall
        rw [subst_cons_eq', subst_cons_eq']
        rw [hall hd List.mem_cons_self]
        rw [ihl (fun ty hty => hall ty (List.mem_cons_of_mem hd hty))]
    rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons]
    congr 1
    apply h_list args
    intro ty hty
    exact ih ty hty (fun v hv => hcl v (by
      simp only [LMonoTy.freeVars]
      exact LMonoTys.freeVars_mem_subset hty hv))

section
omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata]
mutual
/-- Renaming commutes with `resolveAliases`, transferring across environments with
    equal alias lists: for a renaming `σ` (each var maps to a `.ftvar`), resolving the
    renamed type at `Env2` yields the renamed value. -/
theorem LMonoTy_resolveAliases_subst_comm (σ : Subst)
    (h_ren : ∀ x, ∃ w, LMonoTy.subst σ (.ftvar x) = .ftvar w)
    (mty : LMonoTy) (Env1 Env2 : TEnv T.IDMeta)
    (h_ctx : Env1.context.aliases = Env2.context.aliases)
    (h_aw : TContext.AliasesWF Env1.context)
    (v1 : LMonoTy)
    (h : LMonoTy.resolveAliases mty Env1 = .ok (v1, Env1)) :
    LMonoTy.resolveAliases (LMonoTy.subst σ mty) Env2 = .ok (LMonoTy.subst σ v1, Env2) := by
  match mty with
  | .ftvar x =>
    simp only [LMonoTy.resolveAliases, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, _⟩ := h; subst h1
    obtain ⟨w, hw⟩ := h_ren x
    rw [hw]
    simp only [LMonoTy.resolveAliases, pure, Except.pure]
  | .bitvec n =>
    simp only [LMonoTy.resolveAliases, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, _⟩ := h; subst h1
    rw [LMonoTy.subst_bitvec]
    simp only [LMonoTy.resolveAliases, pure, Except.pure]
  | .tcons name args =>
    -- Resolve args at Env1; env is unchanged.
    simp only [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v h_args; obtain ⟨args1, Enva⟩ := v; simp only at h h_args
    have h_enva : Enva = Env1 := LMonoTys.resolveAliases_env args Env1 args1 Enva h_args
    rw [h_enva] at h_args h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, _⟩ := h; subst h1
    -- Apply list IH.
    have h_ih := LMonoTys_resolveAliases_subst_comm σ h_ren args Env1 Env2 h_ctx h_aw args1 h_args
    rw [LMonoTy.subst_tcons]
    simp only [LMonoTy.resolveAliases, Bind.bind, Except.bind]
    rw [h_ih]
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, and_true]
    -- Now: tconsAliasSimple name (subst σ args1) Env2.aliases = subst σ (tconsAliasSimple name args1 Env1.aliases)
    rw [← h_ctx]
    exact tconsAliasSimple_subst_comm σ name args1 Env1.context.aliases h_aw

/-- List version of `LMonoTy_resolveAliases_subst_comm`. -/
theorem LMonoTys_resolveAliases_subst_comm (σ : Subst)
    (h_ren : ∀ x, ∃ w, LMonoTy.subst σ (.ftvar x) = .ftvar w)
    (mtys : LMonoTys) (Env1 Env2 : TEnv T.IDMeta)
    (h_ctx : Env1.context.aliases = Env2.context.aliases)
    (h_aw : TContext.AliasesWF Env1.context)
    (vs1 : LMonoTys)
    (h : LMonoTys.resolveAliases mtys Env1 = .ok (vs1, Env1)) :
    LMonoTys.resolveAliases (LMonoTys.subst σ mtys) Env2 = .ok (LMonoTys.subst σ vs1, Env2) := by
  match mtys with
  | [] =>
    simp only [LMonoTys.resolveAliases, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, _⟩ := h; subst h1
    rw [LMonoTys.subst_nil]
    simp only [LMonoTys.resolveAliases, pure, Except.pure]
  | mty :: mrest =>
    simp only [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v h_hd; obtain ⟨mty1, Envh⟩ := v; simp only at h h_hd
    have h_envh : Envh = Env1 := LMonoTy.resolveAliases_env mty Env1 mty1 Envh h_hd
    rw [h_envh] at h_hd h
    elim_err h
    rename_i v2 h_tl; obtain ⟨mrest1, Envt⟩ := v2; simp only at h h_tl
    have h_envt : Envt = Env1 := LMonoTys.resolveAliases_env mrest Env1 mrest1 Envt h_tl
    rw [h_envt] at h_tl
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, _⟩ := h; subst h1
    have h_ih_hd := LMonoTy_resolveAliases_subst_comm σ h_ren mty Env1 Env2 h_ctx h_aw mty1 h_hd
    have h_ih_tl := LMonoTys_resolveAliases_subst_comm σ h_ren mrest Env1 Env2 h_ctx h_aw mrest1 h_tl
    rw [subst_cons_eq']
    simp only [LMonoTys.resolveAliases, Bind.bind, Except.bind]
    rw [h_ih_hd]
    dsimp only
    rw [h_ih_tl]
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, and_true]
    rw [subst_cons_eq']
end
end

/-- Free variables of a list of `.ftvar`s: `flatMap freeVars ∘ map ftvar = id`. -/
theorem flatMap_freeVars_ftvar (l : List TyIdentifier) :
    List.flatMap LMonoTy.freeVars (List.map LMonoTy.ftvar l) = l := by
  induction l with
  | nil => simp
  | cons a as ih => simp [LMonoTy.freeVars, List.flatMap_cons, ih]

/-- Free variables of the inverse renaming `ofList (zip l1 (map ftvar l2))` are all
    in `l2` (when `l1.length = l2.length`). Membership form: `HMap.values` is
    unordered, so we cannot pin the exact list, only the value set. -/
theorem freeVars_zip_map_ftvar_mem (l1 l2 : List TyIdentifier) (h : l1.length = l2.length)
    (v : TyIdentifier)
    (hv : v ∈ Subst.freeVars [HMap.ofList (List.zip l1 (List.map LMonoTy.ftvar l2))]) :
    v ∈ l2 := by
  simp only [Subst.freeVars, HMaps.values, List.append_nil, List.mem_flatMap] at hv
  obtain ⟨mty, h_mty, h_fv⟩ := hv
  have h_mty_in := HMap.mem_values_ofList _ mty h_mty
  rw [List.map_snd_zip (by simp [h]), List.mem_map] at h_mty_in
  obtain ⟨w, hw, rfl⟩ := h_mty_in
  simp only [LMonoTy.freeVars, List.mem_singleton] at h_fv; subst h_fv; exact hw

/-- Keys of the renaming `ofList (zip l1 (map ftvar l2))` are exactly the members of
    `l1` when lengths match. -/
theorem mem_keys_zip_map_ftvar (l1 l2 : List TyIdentifier) (h : l1.length = l2.length)
    (k : TyIdentifier) :
    k ∈ (HMap.ofList (List.zip l1 (List.map LMonoTy.ftvar l2))).keys ↔ k ∈ l1 := by
  constructor
  · intro hk
    have := HMap.mem_keys_ofList _ k hk
    rw [List.map_fst_zip (by simp [h])] at this; exact this
  · intro hk
    have h_keys : k ∈ (List.zip l1 (List.map LMonoTy.ftvar l2)).map Prod.fst := by
      rw [List.map_fst_zip (by simp [h])]; exact hk
    obtain ⟨v, hv⟩ := HMap.find?_ofList_of_mem_keys _ k h_keys
    exact HMap.find?_mem_keys _ hv

/-- Every value of the renaming `ofList (zip l1 (map ftvar l2))` is a `.ftvar` of some
    member of `l2` when lengths match. -/
theorem values_zip_map_ftvar_mem (l1 l2 : List TyIdentifier) (h : l1.length = l2.length)
    (v : LMonoTy) (hv : v ∈ (HMap.ofList (List.zip l1 (List.map LMonoTy.ftvar l2))).values) :
    ∃ w, w ∈ l2 ∧ v = .ftvar w := by
  have := HMap.mem_values_ofList _ v hv
  rw [List.map_snd_zip (by simp [h]), List.mem_map] at this
  obtain ⟨w, hw, rfl⟩ := this; exact ⟨w, hw, rfl⟩

/-- Any single-scope zip renaming `ofScopes [zip ids (map ftvar freshtvs)]` sends every
    `.ftvar` to some `.ftvar` (it is a genuine variable renaming). -/
theorem subst_zip_ftvar_renaming (ids freshtvs : List TyIdentifier) (y : TyIdentifier) :
    ∃ w, LMonoTy.subst (HMaps.ofScopes [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) (.ftvar y)
      = .ftvar w := by
  rw [LMonoTy.subst_unfold]
  simp only [HMaps.ofScopes, List.map_cons, List.map_nil, HMaps.find?_single_scope]
  cases h_f : HMap.find? (HMap.ofList (List.zip ids (List.map LMonoTy.ftvar freshtvs))) y with
  | none => exact ⟨y, rfl⟩
  | some t =>
    have h_tval := HMap.mem_values_ofList _ t (HMap.find?_mem_values _ h_f)
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h_tval
    obtain ⟨w, _, hw⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    exact ⟨w, by rw [hw]⟩

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- **Instantiation inverse.** `LTy.instantiateWithCheck` instantiates the scheme's
    ∀-bound variables with fresh type variables (in *declaration* order) and resolves
    aliases. There is a *renaming* `ρ` (the fresh variables back to the scheme's body,
    in declaration order) such that applying `ρ` to the produced monotype `mty` recovers
    exactly the alias-*resolved* raw scheme body: resolving aliases on
    `LTy.toMonoTypeUnsafe ty` yields `LMonoTy.subst ρ mty`.

    This is the structural (equality, not `AliasEquiv`) form, so it is decomposable
    component-by-component via `mkArrow'`-injectivity, avoiding any abstract
    `AliasEquiv` inversion across the arrow spine. -/
theorem LTy_instantiateWithCheck_inverse
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env'))
    (h_aw : TContext.AliasesWF Env.context)
    -- Closedness: every free var of the scheme body is ∀-bound. Required: for an open
    -- scheme a free `w` is neither instantiated nor bound, forcing `ρ₀ : w↦w` into both
    -- keys and range, contradicting the range⊆boundVars conjunct.
    (h_closed : LTy.freeVars ty = [])
    -- No bound var uses the generator prefix `$__ty`. Required even when closed: the
    -- scheme `∀"$__ty0". "$__ty0"` instantiates to a no-op (the "fresh" var IS `$__ty0`),
    -- forcing `ρ₀ : "$__ty0"↦"$__ty0"` — key = range var, so not `SubstWF`.
    (h_no_gen_prefix : ∀ x ∈ LTy.boundVars ty,
      ¬ (TState.tyPrefix.toList.isPrefixOf x.toList = true)) :
    -- `ρ` is a *single-scope* renaming `[ρ₀]` (the fresh→user inverse is built as one
    -- scope, so that `LMonoTy.subst_compose` applies).
    ∃ (ρ₀ : SubstOne) (Env_r : TEnv T.IDMeta), SubstWF [ρ₀] ∧
      LMonoTy.resolveAliases (LTy.toMonoTypeUnsafe ty) Env = .ok (LMonoTy.subst [ρ₀] mty, Env_r) ∧
      (∀ x ∈ ρ₀.keys, TContext.isFresh (T := T) x Env.context) ∧
      -- ρ₀'s keys cover the instantiation variables (`freeVars mty`), and its
      -- range is the scheme's bound variables (the user type arguments).
      (∀ v, v ∈ LMonoTy.freeVars mty → v ∈ ρ₀.keys) ∧
      (∀ v, v ∈ Subst.freeVars [ρ₀] → v ∈ LTy.boundVars ty) ∧
      -- ρ₀ is a genuine variable renaming: every range value is a `.ftvar`. Needed
      -- because a renaming preserves `destructArrow` length (the `Subst.freeVars`-based
      -- facts above are vacuous for a ground range and do not stop `subst ρ₀` from
      -- collapsing/injecting arrow structure).
      (∀ mty ∈ ρ₀.values, ∃ w, mty = LMonoTy.ftvar w) := by
  -- Decompose `instantiateWithCheck` = `resolveAliases ty` (then pure checks).
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_ra; obtain ⟨mty_ra, Env_ra⟩ := v1
  elim_errs h
  cases h  -- mty := mty_ra
  -- Decompose `LTy.resolveAliases` = `instantiate` then `LMonoTy.resolveAliases`.
  simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
  elim_err h_ra
  rename_i v2 h_inst; obtain ⟨mty_inst, genEnv1⟩ := v2
  -- `h_ra : LMonoTy.resolveAliases mty_inst {Env with genEnv := genEnv1} = .ok (mty_ra, Env_ra)`
  -- `h_inst : LTy.instantiate ty Env.genEnv = .ok (mty_inst, genEnv1)`
  cases ty with
  | forAll xs body =>
    cases xs with
    | nil =>
      -- Monomorphic: instantiate is identity, ρ₀ = [].
      simp only [LTy.instantiate, Except.ok.injEq, Prod.mk.injEq] at h_inst
      obtain ⟨h_mty_inst, h_genEnv1⟩ := h_inst
      subst h_mty_inst; subst h_genEnv1
      -- Now h_ra : resolveAliases body {Env with genEnv := Env.genEnv} = .ok (mty_ra, Env_ra)
      have h_env_eq : ({Env with genEnv := Env.genEnv} : TEnv T.IDMeta) = Env := rfl
      rw [h_env_eq] at h_ra
      -- body is closed: freeVars body = []
      have h_body_closed : LMonoTy.freeVars body = [] := by
        have h_c := h_closed
        simp only [LTy.freeVars, List.removeAll] at h_c
        exact List.eq_nil_iff_forall_not_mem.mpr (by simpa using h_c)
      -- freeVars mty_ra ⊆ freeVars body = []
      have h_mtyra_closed : LMonoTy.freeVars mty_ra = [] := by
        have h_sub := LMonoTy_resolveAliases_freeVars_subset body Env mty_ra Env_ra h_ra h_aw
        cases h_fv : LMonoTy.freeVars mty_ra with
        | nil => rfl
        | cons v vs =>
          exfalso
          have hv : v ∈ LMonoTy.freeVars mty_ra := by rw [h_fv]; exact List.mem_cons_self
          have := h_sub v hv; rw [h_body_closed] at this; exact absurd this (by simp)
      have h_subst_id : LMonoTy.subst [(HMap.empty : SubstOne)] mty_ra = mty_ra :=
        LMonoTy.subst_single_empty mty_ra
      refine ⟨HMap.empty, Env_ra, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- SubstWF [HMap.empty]
        exact SubstWF_of_pushEmptyScope [] SubstWF_of_empty
      · -- resolveAliases (toMonoTypeUnsafe ty) Env = .ok (subst [HMap.empty] mty_ra, Env_ra)
        show LMonoTy.resolveAliases (LTy.toMonoTypeUnsafe (LTy.forAll [] body)) Env
          = .ok (LMonoTy.subst [HMap.empty] mty_ra, Env_ra)
        simp only [LTy.toMonoTypeUnsafe, h_subst_id]
        exact h_ra
      · -- keys empty = [] : vacuous
        intro x hx; simp [HMap.keys_empty] at hx
      · -- freeVars mty_ra → keys empty : vacuous since freeVars mty_ra = []
        intro v hv; rw [h_mtyra_closed] at hv; exact absurd hv (by simp)
      · -- Subst.freeVars [HMap.empty] = [] : vacuous
        intro v hv; simp [Subst.freeVars, HMaps.values, HMap.values_empty] at hv
      · -- values empty = [] : vacuous
        intro mty hmty; simp [HMap.values_empty] at hmty
    | cons x rest =>
      -- Polymorphic: instantiate generates fresh vars and substitutes.
      simp only [LTy.instantiate, Bind.bind, Except.bind] at h_inst
      elim_err h_inst
      rename_i v3 h_gen; obtain ⟨freshtvs, genEnvg⟩ := v3
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_inst
      obtain ⟨h_mty_inst, h_genEnv1⟩ := h_inst
      subst h_mty_inst; subst h_genEnv1
      -- mty_inst = subst [zip (x::rest) (map ftvar freshtvs)] body
      -- S = fresh instantiation renaming; ρ₀ = its inverse.
      -- body's free vars are all in (x::rest) since ty is closed.
      have h_body_closed : ∀ v, v ∈ LMonoTy.freeVars body → v ∈ (x :: rest) := by
        intro v hv
        by_cases h_not : v ∈ (x :: rest)
        · exact h_not
        · exfalso
          have h_c := h_closed
          simp only [LTy.freeVars, List.removeAll] at h_c
          have h_in_filter : v ∈ List.filter (fun x_1 => !List.elem x_1 (x :: rest)) body.freeVars := by
            rw [List.mem_filter]
            refine ⟨hv, ?_⟩
            simp only [List.elem_eq_mem, Bool.not_eq_true', decide_eq_false_iff_not]
            exact h_not
          rw [h_c] at h_in_filter; exact absurd h_in_filter (by simp)
      have h_len : (x :: rest).length = freshtvs.length :=
        (TGenEnv.genTyVars_length _ _ _ _ h_gen).symm
      have h_fresh_nodup : freshtvs.Nodup := genTyVars_nodup _ _ _ _ h_gen
      -- Env_ra = {Env with genEnv := genEnvg}; context = Env.context.
      have h_env_ra : Env_ra = ({Env with genEnv := genEnvg} : TEnv T.IDMeta) :=
        LMonoTy.resolveAliases_env _ _ _ _ h_ra
      have h_gen_ctx : genEnvg.context = Env.genEnv.context :=
        TGenEnv.genTyVars_context _ _ _ _ h_gen
      have h_ctx_ra : Env_ra.context = Env.context := by
        rw [h_env_ra]; simp only [TEnv.context]; exact h_gen_ctx
      -- Abbreviations for the two substitutions.
      -- S = zip (x::rest) (map ftvar freshtvs), ρ₀ = zip freshtvs (map ftvar (x::rest))
      have h_len' : freshtvs.length = (x :: rest).length := h_len.symm
      -- freshtvs are disjoint from (x::rest): each fresh var has the gen prefix, no
      -- bound var does (`h_no_gen_prefix`).
      have h_disjoint : ∀ w, w ∈ freshtvs → w ∉ (x :: rest) := by
        intro w hw_fresh hw_bound
        obtain ⟨k, h_wk⟩ := TGenEnv.genTyVars_prefixed _ _ _ _ h_gen w hw_fresh
        have h_pref : TState.tyPrefix.toList.isPrefixOf w.toList = true := by
          rw [h_wk]; simp [String.toList_append]
        exact h_no_gen_prefix w (by simp only [LTy.boundVars]; exact hw_bound) h_pref
      -- The inverse renaming as a single `HMap` scope, plus the `ofScopes`-vs-`[·]` bridge.
      have h_scope_eq : HMaps.ofScopes [List.zip freshtvs (List.map LMonoTy.ftvar (x :: rest))]
          = [HMap.ofList (List.zip freshtvs (List.map LMonoTy.ftvar (x :: rest)))] := by
        simp only [HMaps.ofScopes, List.map_cons, List.map_nil]
      refine ⟨HMap.ofList (List.zip freshtvs (List.map LMonoTy.ftvar (x :: rest))), Env,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- SubstWF: keys ⊆ freshtvs, freeVars ⊆ (x::rest); disjoint by h_disjoint.
        show SubstWF [HMap.ofList (List.zip freshtvs (List.map LMonoTy.ftvar (x :: rest)))] = true
        unfold SubstWF
        rw [List.all_eq_true]
        intro w hw
        simp only [HMaps.keys, List.append_nil] at hw
        have hw_fresh : w ∈ freshtvs := (mem_keys_zip_map_ftvar freshtvs (x :: rest) h_len' w).mp hw
        simp only [decide_eq_true_eq]
        intro h_fv
        exact h_disjoint w hw_fresh
          (freeVars_zip_map_ftvar_mem freshtvs (x :: rest) h_len' w (by
            simpa only [h_scope_eq] using h_fv))
      · -- resolveAliases commutes with the renaming, and the renaming inverts instantiation.
        show LMonoTy.resolveAliases (LTy.toMonoTypeUnsafe (LTy.forAll (x :: rest) body)) Env
          = .ok (LMonoTy.subst [HMap.ofList (List.zip freshtvs (List.map LMonoTy.ftvar (x :: rest)))]
              mty_ra, Env)
        simp only [LTy.toMonoTypeUnsafe]
        rw [← h_scope_eq]
        -- Reshape h_ra to canonical form at the literal env (defeq: `.fst`/`.snd`, eta).
        have h_ra' : LMonoTy.resolveAliases
            (LMonoTy.subst (HMaps.ofScopes [List.zip (x :: rest) (List.map LMonoTy.ftvar freshtvs)]) body)
            ({genEnv := genEnvg, stateSubstInfo := Env.stateSubstInfo} : TEnv T.IDMeta)
            = .ok (mty_ra, ({genEnv := genEnvg, stateSubstInfo := Env.stateSubstInfo} : TEnv T.IDMeta)) := by
          rw [h_env_ra] at h_ra; exact h_ra
        have h_ctx_alias : ({genEnv := genEnvg, stateSubstInfo := Env.stateSubstInfo} : TEnv T.IDMeta).context.aliases
            = Env.context.aliases := by
          simp only [TEnv.context]; rw [h_gen_ctx]
        have h_aw_ra : TContext.AliasesWF
            ({genEnv := genEnvg, stateSubstInfo := Env.stateSubstInfo} : TEnv T.IDMeta).context := by
          simp only [TEnv.context]; rw [h_gen_ctx]; exact h_aw
        -- ρ₀ commutes through resolveAliases applied to (subst σ body); transfer env → Env.
        have h_comm2 := LMonoTy_resolveAliases_subst_comm
          (HMaps.ofScopes [List.zip freshtvs (List.map LMonoTy.ftvar (x :: rest))])
          (fun y => subst_zip_ftvar_renaming freshtvs (x :: rest) y)
          (LMonoTy.subst (HMaps.ofScopes [List.zip (x :: rest) (List.map LMonoTy.ftvar freshtvs)]) body)
          _ Env h_ctx_alias h_aw_ra mty_ra h_ra'
        -- subst ρ₀ (subst σ body) = body (ρ₀ inverts σ on the closed body).
        have h_inv : LMonoTy.subst (HMaps.ofScopes [List.zip freshtvs (List.map LMonoTy.ftvar (x :: rest))])
            (LMonoTy.subst (HMaps.ofScopes [List.zip (x :: rest) (List.map LMonoTy.ftvar freshtvs)]) body)
            = body :=
          subst_rename_inverse (x :: rest) freshtvs h_len h_fresh_nodup body h_body_closed
        rw [h_inv] at h_comm2
        exact h_comm2
      · -- keys ⊆ freshtvs, all fresh in Env.context via genTyVars_allFresh.
        intro w hw
        exact TGenEnv.genTyVars_allFresh _ _ _ _ h_gen w
          ((mem_keys_zip_map_ftvar freshtvs (x :: rest) h_len' w).mp hw)
      · -- freeVars mty_ra ⊆ keys.
        intro v hv
        -- mty_ra = resolveAliases of (subst σ body); freeVars ⊆ freeVars(subst σ body) ⊆ freshtvs.
        have h_ra_env : LMonoTy.resolveAliases
            (LMonoTy.subst (HMaps.ofScopes [List.zip (x :: rest) (List.map (fun tv => LMonoTy.ftvar tv) freshtvs)]) body)
            ({genEnv := genEnvg, stateSubstInfo := Env.stateSubstInfo} : TEnv T.IDMeta)
            = .ok (mty_ra, Env_ra) := h_ra
        have h_fv_sub := LMonoTy_resolveAliases_freeVars_subset _ _ _ _ h_ra_env (by
          simp only [TEnv.context]; rw [h_gen_ctx]; exact h_aw)
        have h_v_body := h_fv_sub v hv
        have h_v_fresh := LMonoTy.freeVars_subst_closed (x :: rest) freshtvs h_len.symm body h_body_closed v h_v_body
        exact (mem_keys_zip_map_ftvar freshtvs (x :: rest) h_len' v).mpr h_v_fresh
      · -- Subst.freeVars [ρ₀] ⊆ (x::rest) = boundVars.
        intro v hv
        simp only [LTy.boundVars]
        exact freeVars_zip_map_ftvar_mem freshtvs (x :: rest) h_len' v (by
          simpa only [h_scope_eq] using hv)
      · -- values: every value is a ftvar of some (x::rest) member.
        intro mty hmty
        obtain ⟨w, _, h_eq⟩ := values_zip_map_ftvar_mem freshtvs (x :: rest) h_len' mty hmty
        exact ⟨w, h_eq⟩

/-! ### `AnnotCompat` preserved under substitution -/

/-- Build a single-scope `SubstOne` mapping each `v ∈ l` to `g v`. Folding
    `insert` (rather than `ofList`) sidesteps any distinctness obligation: for
    `v ∈ l`, `find?` returns `g v` regardless of duplicates in `l`. -/
private def buildSubstOne (l : List TyIdentifier) (g : TyIdentifier → LMonoTy) : SubstOne :=
  l.foldr (fun v acc => acc.insert v (g v)) HMap.empty

private theorem find?_buildSubstOne (l : List TyIdentifier) (g : TyIdentifier → LMonoTy)
    (v : TyIdentifier) (hv : v ∈ l) :
    HMap.find? (buildSubstOne l g) v = some (g v) := by
  induction l with
  | nil => simp at hv
  | cons w ws ih =>
    simp only [buildSubstOne, List.foldr_cons]
    by_cases h_eq : v = w
    · subst h_eq; rw [HMap.find?_insert_self]
    · have h_bne : v != w := bne_iff_ne.mpr h_eq
      rw [HMap.find?_insert_ne _ w v (g w) h_bne]
      exact ih (by cases hv with | head => exact absurd rfl h_eq | tail _ h => exact h)

private theorem find?_buildSubstOne_none (l : List TyIdentifier) (g : TyIdentifier → LMonoTy)
    (v : TyIdentifier) (hv : v ∉ l) :
    HMap.find? (buildSubstOne l g) v = none := by
  induction l with
  | nil => simp [buildSubstOne, HMap.find?_empty]
  | cons w ws ih =>
    simp only [buildSubstOne, List.foldr_cons]
    have h_ne : v ≠ w := fun h => hv (h ▸ List.mem_cons_self)
    rw [HMap.find?_insert_ne _ w v (g w) (bne_iff_ne.mpr h_ne)]
    exact ih (fun h => hv (List.mem_cons_of_mem w h))

/-- General homomorphism lemma: `subst [buildSubstOne l g]` agrees with any
    substitution-homomorphism `F` that maps `ftvar v` (for `v ∈ l`) to `g v`,
    fixes `bitvec`, and distributes over `tcons` via `List.map`. This factors the
    repeated structural induction shared by `AnnotCompat_subst` and
    `instantiateWithCheck_AnnotCompat`. -/
private theorem subst_buildSubstOne_hom
    (l : List TyIdentifier) (g : TyIdentifier → LMonoTy) (F : LMonoTy → LMonoTy)
    (h_ftvar : ∀ v, v ∈ l → F (.ftvar v) = g v)
    (h_bitvec : ∀ n, F (.bitvec n) = .bitvec n)
    (h_tcons : ∀ name args, F (.tcons name args) = .tcons name (args.map F))
    (mty : LMonoTy) (h_sub : ∀ v, v ∈ LMonoTy.freeVars mty → v ∈ l) :
    LMonoTy.subst [buildSubstOne l g] mty = F mty := by
  induction mty with
  | ftvar v =>
    have hv := h_sub v (by simp [LMonoTy.freeVars])
    have h_find : HMaps.find? [buildSubstOne l g] v = some (g v) := by
      rw [HMaps.find?_single_scope]; exact find?_buildSubstOne _ g v hv
    rw [LMonoTy.subst_ftvar_eq _ v (g v) h_find, h_ftvar v hv]
  | bitvec n =>
    rw [LMonoTy.subst_bitvec, h_bitvec]
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons, h_tcons]
    congr 1
    rw [LMonoTys.subst_eq_map]
    apply List.map_congr_left
    intro a ha
    exact ih a ha (fun v hv => h_sub v (by
      simp only [LMonoTy.freeVars]; exact LMonoTys.freeVars_mem_subset ha hv))

/-- `AnnotCompat` is preserved under `subst` on the target type. The
    alias-equivalence geometry is handled by `AliasEquiv_subst`; the witness
    substitution is rebuilt as a single-scope `SubstOne` (`buildSubstOne`)
    composing the original witness `σ` with the outer `S`. -/
theorem AnnotCompat_subst {aliases : List TypeAlias} {ann xty : LMonoTy}
    (S : Subst)
    (h : AnnotCompat aliases ann xty)
    (h_aw : ∀ alias, alias ∈ aliases → TypeAlias.WF alias) :
    AnnotCompat aliases ann (LMonoTy.subst S xty) := by
  obtain ⟨σ, h_ae⟩ := h
  have h_ae_S := AliasEquiv_subst aliases (LMonoTy.subst [σ] ann) xty S h_ae h_aw
  -- Build σ' mapping each v ∈ freeVars ann to subst S (subst [σ] (ftvar v))
  refine ⟨buildSubstOne (LMonoTy.freeVars ann)
    (fun v => LMonoTy.subst S (LMonoTy.subst [σ] (.ftvar v))), ?_⟩
  rw [subst_buildSubstOne_hom (LMonoTy.freeVars ann)
      (fun v => LMonoTy.subst S (LMonoTy.subst [σ] (.ftvar v)))
      (fun m => LMonoTy.subst S (LMonoTy.subst [σ] m))
      (fun v _ => rfl)
      (fun n => by
        show LMonoTy.subst S (LMonoTy.subst [σ] (.bitvec n)) = _
        rw [LMonoTy.subst_bitvec, LMonoTy.subst_bitvec])
      (fun name args => by
        show LMonoTy.subst S (LMonoTy.subst [σ] (.tcons name args)) =
          .tcons name (args.map (fun m => LMonoTy.subst S (LMonoTy.subst [σ] m)))
        rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons,
            LMonoTys.subst_eq_map, LMonoTys.subst_eq_map, List.map_map]
        rfl)
      ann (fun v hv => hv)]
  exact h_ae_S

/-- `RigidAnnotCompat` is preserved under substitution when `S` is identity on
    rigid vars. Rebuilds the witness as a single-scope `SubstOne` via
    `buildSubstOne`. -/
theorem RigidAnnotCompat_subst {aliases : List TypeAlias} {rigidVars : List TyIdentifier}
    {ann xty : LMonoTy}
    (S : Subst)
    (h : RigidAnnotCompat aliases rigidVars ann xty)
    (h_aw : ∀ alias, alias ∈ aliases → TypeAlias.WF alias)
    (h_rigid : ∀ v, v ∈ rigidVars → LMonoTy.subst S (.ftvar v) = .ftvar v) :
    RigidAnnotCompat aliases rigidVars ann (LMonoTy.subst S xty) := by
  obtain ⟨σ, h_σ_rigid, h_ae⟩ := h
  have h_ae_S := AliasEquiv_subst aliases (LMonoTy.subst [σ] ann) xty S h_ae h_aw
  let g : TyIdentifier → LMonoTy := fun v => LMonoTy.subst S (LMonoTy.subst [σ] (.ftvar v))
  refine ⟨buildSubstOne (LMonoTy.freeVars ann) g, fun v hv => ?_, ?_⟩
  · -- σ' is identity on rigid vars.
    show LMonoTy.subst [buildSubstOne (LMonoTy.freeVars ann) g] (.ftvar v) = .ftvar v
    by_cases h_mem : v ∈ LMonoTy.freeVars ann
    · have h_gv : g v = .ftvar v := by
        show LMonoTy.subst S (LMonoTy.subst [σ] (.ftvar v)) = .ftvar v
        rw [h_σ_rigid v hv, h_rigid v hv]
      have h_find : HMaps.find? [buildSubstOne (LMonoTy.freeVars ann) g] v = some (.ftvar v) := by
        rw [HMaps.find?_single_scope]; rw [find?_buildSubstOne _ g v h_mem, h_gv]
      exact LMonoTy.subst_ftvar_eq _ v (.ftvar v) h_find
    · have h_none : HMaps.find? [buildSubstOne (LMonoTy.freeVars ann) g] v = none := by
        rw [HMaps.find?_single_scope]; exact find?_buildSubstOne_none _ g v h_mem
      simp only [LMonoTy.subst_unfold, h_none]
  · -- The alias-equivalence part, identical to `AnnotCompat_subst`.
    rw [subst_buildSubstOne_hom (LMonoTy.freeVars ann) g
        (fun m => LMonoTy.subst S (LMonoTy.subst [σ] m))
        (fun v _ => rfl)
        (fun n => by
          show LMonoTy.subst S (LMonoTy.subst [σ] (.bitvec n)) = _
          rw [LMonoTy.subst_bitvec, LMonoTy.subst_bitvec])
        (fun name args => by
          show LMonoTy.subst S (LMonoTy.subst [σ] (.tcons name args)) =
            .tcons name (args.map (fun m => LMonoTy.subst S (LMonoTy.subst [σ] m)))
          rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons,
              LMonoTys.subst_eq_map, LMonoTys.subst_eq_map, List.map_map]
          rfl)
        ann (fun v hv => hv)]
    exact h_ae_S

/-! ### `instantiateWithCheck` produces an `AnnotCompat` output -/

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)]
  [ToFormat T.Metadata] in
/-- `LMonoTy.instantiateWithCheck` produces a type that is `AnnotCompat` with
    the input: there exists a substitution `σ` (renaming free vars to fresh
    generated names) such that the output is alias-equivalent to
    `subst [σ] mty_in`. -/
private theorem instantiateWithCheck_AnnotCompat [Std.ToFormat T.Metadata]
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta)
    (mty_out : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (mty_out, Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    AnnotCompat Env.context.aliases mty_in mty_out := by
  -- Decompose into instantiateEnv then resolveAliases.
  have ⟨mty_ie, Env_ie, Env_ra, h_ie, h_ra⟩ :=
    LMonoTy.instantiateWithCheck_decompose mty_in C Env mty_out Env' h
  -- Extract the substitution σ from instantiateEnv_decompose.
  have ⟨freshtvs, genEnv', h_gen, h_result, h_env_eq⟩ :=
    instantiateEnv_decompose _ _ _ _ _ h_ie
  -- Get AliasEquiv from resolveAliases_aliasEquiv.
  have h_ie_ctx := LMonoTys.instantiateEnv_context _ _ Env _ _ h_ie
  have h_alias := resolveAliases_aliasEquiv (Γ := Env.context) mty_ie Env_ie mty_out Env_ra h_ra
      (by rw [h_ie_ctx]) (h_ie_ctx ▸ h_aw)
  -- Show mty_ie = subst (ofScopes [σ]) mty_in from the singleton equation h_result.
  have h_eq : mty_ie = LMonoTy.subst (Strata.Util.HMaps.ofScopes
      [List.zip (LMonoTy.freeVars mty_in) (List.map LMonoTy.ftvar freshtvs)]) mty_in := by
    have h := h_result
    rw [LMonoTys.subst_eq_map] at h
    simpa using h
  subst h_eq
  -- AnnotCompat witness: the single scope `HMap.ofList (zip ...)` IS the SubstOne.
  refine ⟨HMap.ofList (List.zip (LMonoTy.freeVars mty_in) (List.map LMonoTy.ftvar freshtvs)), ?_⟩
  show AliasEquiv Env.context.aliases (LMonoTy.subst
    (Strata.Util.HMaps.ofScopes [List.zip (LMonoTy.freeVars mty_in) (List.map LMonoTy.ftvar freshtvs)]) mty_in) _
  exact h_ie_ctx ▸ h_alias

/-! ### `typeBoundVar` with an annotation produces an `AnnotCompat` -/

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `typeBoundVar` with a `some` annotation produces a type that is
    `AnnotCompat` with the annotation. -/
private theorem typeBoundVar_AnnotCompat [Std.ToFormat T.Metadata]
    (C : LContext T) (Env : TEnv T.IDMeta) (bty_val : LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env (some bty_val) = .ok (xv, xty, Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    AnnotCompat Env.context.aliases bty_val xty := by
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v_gen h_gen; obtain ⟨xv_raw, Env_g⟩ := v_gen; simp at h
  have h_g_ctx : Env_g.context = Env.context := liftGenEnv_context Env _ Env_g h_gen
  generalize h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g = res_ic at h
  match res_ic with
  | .error _ => simp at h
  | .ok (mty_ic, Env_mid) =>
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, h_xty, _⟩ := h
  subst h_xty
  exact h_g_ctx ▸ instantiateWithCheck_AnnotCompat bty_val C Env_g mty_ic Env_mid h_ic (h_g_ctx ▸ h_aw)

/-- A key of a well-formed substitution does not appear in the free variables
    of any substituted type. Proved via `freeVars_of_subst_subset` + `SubstWF`:
    freeVars after subst ⊆ freeVars(original) ∪ freeVars(values), and keys ∉ freeVars(values). -/
private theorem SubstWF.key_not_in_freeVars_subst
    (S : Subst) (mty : LMonoTy) (a : TyIdentifier)
    (h_key : a ∈ HMaps.keys S) (h_wf : SubstWF S) :
    a ∉ LMonoTy.freeVars (LMonoTy.subst S mty) := by
  simp [SubstWF] at h_wf
  have h_not_val : a ∉ Subst.freeVars S := h_wf a h_key
  by_cases hS : Subst.hasEmptyScopes S
  · -- `hasEmptyScopes` ⇒ `find? S a = none`, contradicting `a ∈ keys S`.
    obtain ⟨v, hv⟩ := (HMaps.mem_keys_iff_find? S a).mp h_key
    rw [Subst.find?_none_of_hasEmptyScopes hS a] at hv; exact absurd hv (by simp)
  · -- Direct induction on mty with hasEmptyScopes = false
    have hSF : Subst.hasEmptyScopes S = false := Bool.eq_false_iff.mpr hS
    induction mty with
    | ftvar v =>
      cases h_find : HMaps.find? S v with
      | none =>
        -- result is ftvar v, freeVars = [v]. If a = v, then find? S a = none
        -- contradicts a ∈ keys S.
        simp only [LMonoTy.subst_unfold, h_find, LMonoTy.freeVars, List.mem_singleton]
        intro h_eq; subst h_eq
        obtain ⟨w, hw⟩ := (HMaps.mem_keys_iff_find? S a).mp h_key
        rw [h_find] at hw; exact absurd hw (by simp)
      | some t =>
        -- result is t: a ∉ freeVars t because a ∉ Subst.freeVars S
        simp only [LMonoTy.subst_unfold, h_find]
        exact fun h => h_not_val (Subst.freeVars_of_find_subset S h_find h)
    | bitvec _ => simp [LMonoTy.subst_bitvec, LMonoTy.freeVars]
    | tcons name args ih =>
      rw [LMonoTy.subst_tcons]
      -- Need: a ∉ LMonoTys.freeVars (LMonoTys.subst S args)
      rw [LMonoTys.subst_eq_map]
      suffices h_notfv_gen : ∀ (l : LMonoTys), (∀ m, m ∈ l → a ∉ LMonoTy.freeVars (LMonoTy.subst S m)) →
          a ∉ LMonoTys.freeVars (l.map (LMonoTy.subst S)) by
        exact h_notfv_gen args (fun m hm => ih m hm)
      intro l h_all
      induction l with
      | nil => simp [LMonoTys.freeVars]
      | cons hd tl ih_tl =>
        simp only [List.map_cons, LMonoTys.freeVars]
        intro h_abs; rcases List.mem_append.mp h_abs with h_hd | h_tl
        · exact h_all hd (List.mem_cons_self ..) h_hd
        · exact ih_tl (fun m hm => h_all m (List.mem_cons_of_mem _ hm)) h_tl

private theorem Subst.freeVars_remove_subset (S : Subst) (x : TyIdentifier) :
    ∀ a, a ∈ Subst.freeVars (HMaps.remove S x) → a ∈ Subst.freeVars S := by
  intro a ha; simp [Subst.freeVars] at ha ⊢
  obtain ⟨mty, h_val, h_fv⟩ := ha
  exact ⟨mty, HMaps.values_remove_subset S x mty h_val, h_fv⟩

private theorem SubstWF_remove (S : Subst) (x : TyIdentifier) (h_wf : SubstWF S) :
    SubstWF (HMaps.remove S x) := by
  simp [SubstWF] at h_wf ⊢; intro k hk hk_fv
  exact h_wf k (HMaps.keys_remove_subset S x k hk) (Subst.freeVars_remove_subset S x k hk_fv)

private theorem SubstWF_go (S : Subst) (xs : List TyIdentifier) (h_wf : SubstWF S) :
    SubstWF (LTy.subst.go xs S) := by
  induction xs generalizing S with
  | nil => simp [LTy.subst.go]; exact h_wf
  | cons x rest ih =>
    simp [LTy.subst.go]
    exact ih (HMaps.remove S x) (SubstWF_remove S x h_wf)

private theorem keys_go_mem (S : Subst) (xs : List TyIdentifier) (a : TyIdentifier)
    (h_key : a ∈ HMaps.keys S) (h_not_xs : a ∉ xs) :
    a ∈ HMaps.keys (LTy.subst.go xs S) := by
  induction xs generalizing S with
  | nil => simp [LTy.subst.go]; exact h_key
  | cons x rest ih =>
    simp [LTy.subst.go]
    apply ih (HMaps.remove S x)
    · exact HMaps.keys_remove_mem_of_ne h_key
        (fun h => h_not_xs (h ▸ List.mem_cons_self ..))
    · exact fun h => h_not_xs (List.mem_cons_of_mem x h)

/-- A key of a well-formed substitution does not appear in the free variables
    of any substituted LTy. Lifts `key_not_in_freeVars_subst` from LMonoTy to LTy. -/
private theorem SubstWF.key_not_in_LTy_freeVars_subst
    (S : Subst) (ty : LTy) (a : TyIdentifier)
    (h_key : a ∈ HMaps.keys S) (h_wf : SubstWF S) :
    a ∉ LTy.freeVars (LTy.subst S ty) := by
  cases ty with
  | forAll xs body =>
    simp only [LTy.subst, LTy.freeVars]
    intro h_mem
    simp [_root_.List.removeAll, _root_.List.mem_filter] at h_mem
    obtain ⟨h_in_fv, h_not_xs⟩ := h_mem
    exact SubstWF.key_not_in_freeVars_subst (LTy.subst.go xs S) body a
      (keys_go_mem S xs a h_key h_not_xs) (SubstWF_go S xs h_wf) h_in_fv

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- A key of a well-formed substitution is fresh in the substituted context.
    SubstWF ensures keys don't appear in values, so after substitution,
    keys are eliminated from all type free variables. -/
private theorem TContext.isFresh_subst_of_key
    (Γ : TContext T.IDMeta) (S : Subst) (a : TyIdentifier)
    (h_key : a ∈ HMaps.keys S) (h_wf : SubstWF S) :
    TContext.isFresh (T := T) a (TContext.subst Γ S) := by
  intro x ty h_find
  simp [TContext.subst] at h_find
  obtain ⟨ty_orig, _, h_eq⟩ := TContext_types_subst_find_reverse Γ.types S x ty h_find
  subst h_eq
  exact SubstWF.key_not_in_LTy_freeVars_subst S ty_orig a h_key h_wf

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `inferFVar` produces a substitution that absorbs the input. -/
private theorem inferFVar_absorbs
    (C : LContext T) (Env : TEnv T.IDMeta) (x : T.Identifier) (fty : Option LMonoTy)
    (ty_res : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : inferFVar C Env x fty = .ok (ty_res, Env')) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  simp only [inferFVar, Bind.bind, Except.bind] at h
  elim_err h
  rename_i ty h_find
  -- Split on result of LTy.instantiateWithCheck
  elim_err h
  rename_i v1 h_inst
  obtain ⟨mty, Env1⟩ := v1
  dsimp at h h_inst
  -- Now h has `match fty with | none => ... | some fty => ...`
  cases fty with
  | none =>
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    exact LTy_instantiateWithCheck_absorbs ty C Env mty Env1 h_inst
  | some fty_val =>
    simp only [Except.mapError] at h
    -- Split on result of LMonoTy.instantiateWithCheck
    elim_err h
    rename_i v2 h_inst2
    obtain ⟨fty_inst, Env2⟩ := v2
    dsimp at h h_inst2
    -- Split on result of Constraints.unify (wrapped in mapError)
    elim_err h
    rename_i v3 h_mapError
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    simp [TEnv.updateSubst]
    have h_unify := unify_of_mapError h_mapError
    exact Subst.absorbs_trans
      Env.stateSubstInfo.subst Env2.stateSubstInfo.subst v3.subst
      (Subst.absorbs_trans
        Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
        (LTy_instantiateWithCheck_absorbs ty C Env mty Env1 h_inst)
        (LMonoTy_instantiateWithCheck_absorbs fty_val C Env1 fty_inst Env2 h_inst2))
      (Constraints.unify_absorbs _ _ _ h_unify)

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/--
For an unannotated `x`, `inferFVar` looks up `x` in the context to get a scheme
that is monomorphic by `h_mono` (so `forAll [] mty_ctx`), and the inferred type
`ty_res` is alias-equivalent to `mty_ctx` under any substitution `S`. Unlike
`inferFVar_HasType`, extracts only the alias-equivalence fact, so it serves both
`HasType` and `HasTypeA`. -/
theorem inferFVar_none_find_aliasEquiv
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (x : Identifier T.IDMeta)
    (ty_res : LMonoTy)
    (h : inferFVar C Env x none = .ok (ty_res, Env'))
    (h_mono : ∀ y t, Env.context.types.find? y = some t → LTy.boundVars t = [])
    (h_aw : TContext.AliasesWF Env.context) :
    ∃ mty_ctx, Env.context.types.find? x = some (.forAll [] mty_ctx) ∧
      ∀ S, AliasEquiv Env.context.aliases (LMonoTy.subst S mty_ctx)
        (LMonoTy.subst S ty_res) := by
  simp only [inferFVar, Bind.bind, Except.bind] at h
  elim_err h  -- context lookup failed
  rename_i ty h_find
  elim_err h  -- instantiateWithCheck failed
  rename_i v1 h_inst
  obtain ⟨mty, Env1⟩ := v1
  simp at h h_inst
  -- `fty = none` branch: return `(mty, Env1)`
  obtain ⟨h_ty, h_env⟩ := h
  subst h_ty; subst h_env
  -- `h_mono` forces `ty = forAll [] body`
  have h_bv := h_mono x ty h_find
  cases ty with
  | forAll xs body =>
    simp only [LTy.boundVars] at h_bv
    subst h_bv
    refine ⟨body, h_find, ?_⟩
    -- Decompose `instantiateWithCheck` to its `resolveAliases` core
    simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h_inst
    elim_err h_inst
    rename_i v_ra h_ra; obtain ⟨mty_ra, Env_ra⟩ := v_ra; dsimp at h_inst h_ra
    elim_errs h_inst
    simp at h_inst
    obtain ⟨h_mty, h_env⟩ := h_inst; subst h_mty; subst h_env
    -- Decompose `resolveAliases` into `instantiate` + `LMonoTy.resolveAliases`
    simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
    elim_err h_ra
    rename_i v_inst h_lty_inst; obtain ⟨mty_inst, genEnv'⟩ := v_inst
    simp at h_ra h_lty_inst
    -- `instantiate` on nil binders leaves the body unchanged
    simp only [LTy.instantiate, Except.ok.injEq, Prod.mk.injEq] at h_lty_inst
    obtain ⟨h_mi, h_ge⟩ := h_lty_inst; subst h_mi; subst h_ge
    -- `AliasEquiv aliases body mty_ra` from `resolveAliases`
    have h_aliases_env : Env.context.aliases =
        ({genEnv := Env.genEnv, stateSubstInfo := Env.stateSubstInfo}
          : TEnv T.IDMeta).context.aliases := by
      simp [TEnv.context]
    have h_ae := resolveAliases_aliasEquiv body
      ({genEnv := Env.genEnv, stateSubstInfo := Env.stateSubstInfo} : TEnv T.IDMeta)
      mty_ra Env_ra h_ra
      h_aliases_env h_aw
    intro S
    exact AliasEquiv_subst Env.context.aliases body mty_ra S h_ae
      (fun a ha => h_aw a ha)

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
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
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  cases h_lift : liftGenEnv HasGen.genVar Env with
  | error _ => rw [h_lift] at h; simp at h
  | ok res_lift =>
    obtain ⟨xv_raw, Env_g⟩ := res_lift
    rw [h_lift] at h; simp only at h
    -- liftGenEnv preserves stateSubstInfo
    have h_gen_subst : Env_g.stateSubstInfo = Env.stateSubstInfo :=
      liftGenEnv_subst Env _ Env_g h_lift
    cases bty with
    | some bty_val =>
      simp only at h
      cases h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g with
      | error _ => rw [h_ic] at h; simp at h
      | ok res_ic =>
        obtain ⟨bty_mty, Env_inst⟩ := res_ic
        rw [h_ic] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, h_env⟩ := h; subst h_env
        simp only [TEnv.addInNewestContext, TEnv.updateContext]
        have h_abs := LMonoTy_instantiateWithCheck_absorbs bty_val C Env_g _ Env_inst h_ic
        rw [h_gen_subst] at h_abs
        exact h_abs
    | none =>
      simp only at h
      cases h_tg : TEnv.genTyVar Env_g with
      | error _ => rw [h_tg] at h; simp at h
      | ok res_tg =>
        obtain ⟨xtyid, Env1⟩ := res_tg
        rw [h_tg] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, h_env⟩ := h; subst h_env
        simp only [TEnv.addInNewestContext, TEnv.updateContext]
        -- genTyVar preserves stateSubstInfo
        have h_subst := TEnv.genTyVar_subst Env_g xtyid Env1 h_tg
        rw [h_subst, h_gen_subst]
        exact Subst.absorbs_refl _ Env.stateSubstInfo.isWF

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `inferFVar` never decreases the type-variable generator counter. -/
private theorem inferFVar_tyGen_mono
    (C : LContext T) (Env : TEnv T.IDMeta) (x : T.Identifier) (fty : Option LMonoTy)
    (ty_res : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : inferFVar C Env x fty = .ok (ty_res, Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  simp only [inferFVar] at h
  elim_err h
  rename_i ty h_find
  simp only [Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_iwc
  obtain ⟨ty_inst, Env1⟩ := v1; simp at h h_iwc
  cases fty with
  | none =>
    simp at h; obtain ⟨_, h_env⟩ := h; subst h_env
    exact LTy_instantiateWithCheck_tyGen_mono ty C Env ty_inst Env1 h_iwc
  | some fty_val =>
    simp only [Except.mapError] at h
    elim_err h
    rename_i v2 h_iwc2
    obtain ⟨fty_inst, Env2⟩ := v2; simp at h h_iwc2
    elim_err h
    simp at h; obtain ⟨_, h_env⟩ := h; subst h_env
    simp [TEnv.updateSubst]
    exact Nat.le_trans
      (LTy_instantiateWithCheck_tyGen_mono ty C Env ty_inst Env1 h_iwc)
      (LMonoTy_instantiateWithCheck_tyGen_mono fty_val C Env1 fty_inst Env2 h_iwc2)

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `typeBoundVar` never decreases the type-variable generator counter. -/
private theorem typeBoundVar_tyGen_mono
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  cases h_lift : liftGenEnv HasGen.genVar Env with
  | error _ => rw [h_lift] at h; simp at h
  | ok res_lift =>
    obtain ⟨xv_raw, Env_g⟩ := res_lift
    rw [h_lift] at h; simp only at h
    have h_gen_tyGen : Env_g.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen :=
      liftGenEnv_tyGen_mono Env _ Env_g h_lift
    cases bty with
    | some bty_val =>
      simp only at h
      cases h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g with
      | error _ => rw [h_ic] at h; simp at h
      | ok res_ic =>
        obtain ⟨bty_mty, Env_inst⟩ := res_ic
        rw [h_ic] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, h_env⟩ := h; subst h_env
        simp only [TEnv.addInNewestContext, TEnv.updateContext]
        exact Nat.le_trans h_gen_tyGen
          (LMonoTy_instantiateWithCheck_tyGen_mono bty_val C Env_g _ Env_inst h_ic)
    | none =>
      simp only at h
      cases h_tg : TEnv.genTyVar Env_g with
      | error _ => rw [h_tg] at h; simp at h
      | ok res_tg =>
        obtain ⟨xtyid, Env1⟩ := res_tg
        rw [h_tg] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, h_env⟩ := h; subst h_env
        simp only [TEnv.addInNewestContext, TEnv.updateContext]
        have h_tyGen := genTyVar_tyGen Env_g xtyid Env1 h_tg
        omega

/-! ### `resolveAux` combined properties (strong induction over `e.sizeOf`)

The keystone invariant-preservation result: `resolveAux` never decreases the
generator counter, preserves the context up to `TContext.Equiv` (find?-level, per
the opacity constraint), preserves `SubstFreshForGen` + output-type freshness, and
produces an absorbing substitution. -/


omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `Equiv`-based transfer of the `boundVarsFresh` invariant across a
    context-preserving, generator-monotone step. -/
private theorem transfer_boundVarsFresh_equiv
    {Env Env' : TEnv T.IDMeta}
    (h_bf : ∀ y ty, Env.context.types.find? y = some ty →
      ∀ v, v ∈ LTy.boundVars ty →
        ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n)
    (h_ctx : Env'.context.Equiv Env.context)
    (h_mono : Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen) :
    ∀ y ty, Env'.context.types.find? y = some ty →
      ∀ v, v ∈ LTy.boundVars ty →
        ∀ n, n ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  intro y ty h_f v hv n hn
  exact h_bf y ty ((h_ctx.find? y).symm.trans h_f) v hv n (Nat.le_trans h_mono hn)

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `typeBoundVar` extends the context's newest scope with exactly the single
    binding `xv ↦ forAll [] xty` (structural). Used by the abs/quant erase-cancel. -/
private theorem typeBoundVar_types_addInNewest
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env')) :
    Env'.context.types = Env.context.types.addInNewest (HMap.single xv (.forAll [] xty)) := by
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  cases h_lift : liftGenEnv HasGen.genVar Env with
  | error _ => rw [h_lift] at h; simp at h
  | ok res_lift =>
    obtain ⟨xv_raw, Env_g⟩ := res_lift
    rw [h_lift] at h; simp only at h
    have h_ctx_g := liftGenEnv_context Env xv_raw Env_g h_lift
    cases bty with
    | some bty_val =>
      simp only at h
      cases h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g with
      | error _ => rw [h_ic] at h; simp at h
      | ok res_ic =>
        obtain ⟨bty_mty, Env_mid⟩ := res_ic
        rw [h_ic] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h_xv, h_xty, h_env⟩ := h
        subst h_xv; subst h_xty; subst h_env
        simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context]
        have h_ctx_ic := LMonoTy_instantiateWithCheck_context' bty_val C Env_g _ Env_mid h_ic
        have h_ctx : Env_mid.context = Env.context := by
          simp [TEnv.context] at h_ctx_ic h_ctx_g ⊢; rw [h_ctx_ic, h_ctx_g]
        show Env_mid.genEnv.context.types.addInNewest _ = _
        rw [show Env_mid.genEnv.context.types = Env.genEnv.context.types from
          congrArg TContext.types h_ctx]
    | none =>
      simp only at h
      cases h_tg : TEnv.genTyVar Env_g with
      | error _ => rw [h_tg] at h; simp at h
      | ok res_tg =>
        obtain ⟨tv, Env_mid⟩ := res_tg
        rw [h_tg] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h_xv, h_xty, h_env⟩ := h
        subst h_xv; subst h_xty; subst h_env
        simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context]
        have h_ctx_tg := TEnv.genTyVar_context Env_g tv Env_mid h_tg
        have h_ctx : Env_mid.context = Env.context := by
          simp [TEnv.context] at h_ctx_tg h_ctx_g ⊢; rw [h_ctx_tg, h_ctx_g]
        show Env_mid.genEnv.context.types.addInNewest _ = _
        rw [show Env_mid.genEnv.context.types = Env.genEnv.context.types from
          congrArg TContext.types h_ctx]

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- The abs/quant erase-cancel, at `TContext.Equiv` level: after `typeBoundVar`
    adds `xv` and the body resolves to a context `Equiv` to the extended one,
    erasing `xv` recovers a context `Equiv` to the original. -/
private theorem eraseFromContext_typeBoundVar_equiv
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
    (h_tbv : typeBoundVar C Env bty = .ok (xv, xty, Env1))
    (Env2 : TEnv T.IDMeta) (h_body : Env2.context.Equiv Env1.context)
    (h_ne : Env.context.types ≠ []) :
    (Env2.eraseFromContext xv).context.Equiv Env.context := by
  have h_fresh := typeBoundVar_xv_fresh_in_context C Env bty xv xty Env1 h_tbv
  have h_add := typeBoundVar_types_addInNewest C Env bty xv xty Env1 h_tbv
  refine ⟨?_, ?_⟩
  · -- types: remove xv Env2.types ≈ remove xv Env1.types ≈ remove xv (addInNewest ..) ≈ Env.types
    show HMaps.Equiv ((Env2.context.types).remove xv) Env.context.types
    have step1 : HMaps.Equiv ((Env2.context.types).remove xv) ((Env1.context.types).remove xv) :=
      HMaps.remove_equiv h_body.1 xv
    have step2 : HMaps.Equiv ((Env1.context.types).remove xv)
        ((Env.context.types.addInNewest (HMap.single xv (.forAll [] xty))).remove xv) := by
      rw [h_add]
    have step3 : HMaps.Equiv
        ((Env.context.types.addInNewest (HMap.single xv (.forAll [] xty))).remove xv)
        Env.context.types :=
      HMaps.remove_addInNewest_single_fresh_equiv Env.context.types xv _ h_ne h_fresh
    exact (step1.trans step2).trans step3
  · -- aliases: erase doesn't touch aliases; typeBoundVar preserves aliases
    have h_erase_al : (Env2.eraseFromContext xv).context.aliases = Env2.context.aliases := rfl
    rw [h_erase_al, h_body.2]
    exact typeBoundVar_aliases_eq C Env bty xv xty Env1 h_tbv

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- The type `xty` produced by `typeBoundVar` has only generator-fresh free
    variables (below the OUTPUT generator counter). Used for the abs/quant output-
    type freshness obligation. -/
private theorem typeBoundVar_xty_freeVars_fresh
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env1)) :
    ∀ v, v ∈ LMonoTy.freeVars xty →
      ∀ k, k ≥ Env1.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString k := by
  intro v hv k hk
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  cases h_lift : liftGenEnv HasGen.genVar Env with
  | error _ => rw [h_lift] at h; simp at h
  | ok res_lift =>
    obtain ⟨xv_raw, Env_g⟩ := res_lift
    rw [h_lift] at h; simp only at h
    cases bty with
    | some bty_val =>
      simp only at h
      cases h_ic : LMonoTy.instantiateWithCheck bty_val C Env_g with
      | error _ => rw [h_ic] at h; simp at h
      | ok res_ic =>
        obtain ⟨bty_mty, Env_inst⟩ := res_ic
        rw [h_ic] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, h_xty, h_env⟩ := h; subst h_xty; subst h_env
        have h_fv_fresh := LMonoTy_instantiateWithCheck_freeVars_fresh bty_val C Env_g bty_mty Env_inst h_ic
        simp only [TEnv.addInNewestContext, TEnv.updateContext] at hk
        exact h_fv_fresh v hv k hk
    | none =>
      simp only at h
      cases h_tg : TEnv.genTyVar Env_g with
      | error _ => rw [h_tg] at h; simp at h
      | ok res_tg =>
        obtain ⟨xtyid, Env_ty⟩ := res_tg
        rw [h_tg] at h; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, h_xty, h_env⟩ := h; subst h_xty; subst h_env
        simp only [LMonoTy.freeVars, List.mem_singleton] at hv
        simp only [TEnv.addInNewestContext, TEnv.updateContext] at hk
        rw [hv, genTyVar_name_eq Env_g xtyid Env_ty h_tg]
        exact generated_name_fresh _ _ (by
          have := genTyVar_tyGen Env_g xtyid Env_ty h_tg; omega) k hk

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
set_option maxHeartbeats 800000 in
private theorem resolveAux_properties_aux :
    ∀ (n : Nat) (e : LExpr T.mono), e.sizeOf = n →
      ∀ (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      Env.context.types ≠ [] →
      TContext.AliasesWF Env.context →
      FactoryWF C.functions →
      SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState →
      ContextFreshForGen Env.context Env.genEnv.genState →
      (∀ y ty, Env.context.types.find? y = some ty →
        ∀ v, v ∈ LTy.boundVars ty →
          ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) →
      Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen ∧
      Env'.context.Equiv Env.context ∧
      (SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState ∧
       (∀ v, v ∈ LMonoTy.freeVars et.toLMonoTy →
         ∀ k, k ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString k)) ∧
      Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro e h_eq et C Env Env' h h_ne h_aw h_fwf h_sf h_cf h_bvf
  match e with
  | .const m c =>
    simp [resolveAux, inferConst] at h
    elim_err h
    simp [Bind.bind, Except.bind] at h; obtain ⟨h_et, h2⟩ := h; rw [← h2]
    exact ⟨Nat.le_refl _, TContext.Equiv.refl _,
      ⟨h_sf, fun v hv => by rw [← h_et] at hv; simp [toLMonoTy, LConst.ty_freeVars] at hv⟩,
      Subst.absorbs_refl _ Env.stateSubstInfo.isWF⟩
  | .bvar _ _ => simp [resolveAux] at h
  | .fvar m x fty =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_infer; obtain ⟨ty_res, Env_res⟩ := v1; simp at h
    obtain ⟨h_et, h2⟩ := h; rw [← h2]
    refine ⟨inferFVar_tyGen_mono C Env x fty _ Env_res h_infer,
            TContext.Equiv.of_eq (inferFVar_context C Env x fty _ Env_res h_infer),
            ⟨inferFVar_preserves_SubstFreshForGen C Env x fty _ Env_res h_infer h_sf h_cf h_aw h_bvf, ?_⟩,
            inferFVar_absorbs C Env x fty _ Env_res h_infer⟩
    subst h_et h2
    intro v hv k hk
    simp [toLMonoTy] at hv
    simp only [inferFVar, Bind.bind, Except.bind] at h_infer
    elim_err h_infer
    rename_i ty_found h_find_ctx
    elim_err h_infer
    rename_i v2 h_inst; obtain ⟨mty, Env1⟩ := v2; dsimp at h_infer h_inst
    have h_mty_fresh := LTy_instantiateWithCheck_freeVars_fresh _ C Env mty Env1 h_inst
    cases fty with
    | none => grind
    | some fty_val =>
      simp only [Except.mapError] at h_infer
      elim_err h_infer
      rename_i v3 h_inst2; obtain ⟨fty_inst, Env2⟩ := v3; dsimp at h_infer h_inst2
      elim_err h_infer
      simp at h_infer; obtain ⟨h_ty, h_env2⟩ := h_infer
      rw [← h_ty] at hv; rw [← h_env2] at hk; simp [TEnv.updateSubst] at hk
      exact h_mty_fresh v hv k (Nat.le_trans (LMonoTy_instantiateWithCheck_tyGen_mono fty_val C Env1 fty_inst Env2 h_inst2) hk)
  | .op m o oty =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_err h
    rename_i func h_find
    elim_err h
    rename_i type_val h_type
    elim_err h
    rename_i v1 h_inst; obtain ⟨ty_inst, Env1⟩ := v1; dsimp at h h_inst
    have h_func_mem : func ∈ C.functions.toArray := Factory.getElem?_is_some_implies_mem h_find
    have h_func_wf : LFuncWF func := h_fwf.lfuncs_wf func h_func_mem
    have h_ty_closed : LTy.freeVars type_val = [] := LFunc.type_freeVars_eq_nil func type_val h_type h_func_wf
    have h_ty_fresh_vacuous : ∀ v, v ∈ LTy.freeVars type_val →
        ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
      intro v hv; simp [h_ty_closed] at hv
    have h_bv_fresh : ∀ v, v ∈ LTy.boundVars type_val →
        ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
      rw [LFunc.type_boundVars_eq_typeArgs func type_val h_type]
      intro v hv _ _ h_eq
      exact (h_func_wf.typeArgs_no_gen_prefix v hv) (h_eq ▸ (by rw [String.toList_append]; exact isPrefixOf_append_self _ _))
    cases oty with
    | none =>
      simp at h; obtain ⟨h_et, h2⟩ := h; subst h_et h2
      exact ⟨LTy_instantiateWithCheck_tyGen_mono type_val C Env ty_inst Env1 h_inst,
             TContext.Equiv.of_eq (LTy_instantiateWithCheck_context _ C Env ty_inst Env1 h_inst),
             ⟨LTy_instantiateWithCheck_preserves_SubstFreshForGen type_val C Env ty_inst Env1 h_inst h_sf h_aw h_ty_fresh_vacuous h_bv_fresh,
              fun v hv k hk => by simp [toLMonoTy] at hv; exact LTy_instantiateWithCheck_freeVars_fresh type_val C Env ty_inst Env1 h_inst v hv k hk⟩,
             LTy_instantiateWithCheck_absorbs type_val C Env ty_inst Env1 h_inst⟩
    | some oty_val =>
      simp only [Except.mapError] at h
      elim_err h
      rename_i v2 h_inst2; obtain ⟨oty_inst, Env2⟩ := v2; dsimp at h h_inst2
      elim_err h
      rename_i v3 h_mapError
      simp at h; obtain ⟨h_et, h2⟩ := h; subst h_et h2; simp [TEnv.updateSubst]
      have h_aw1 : TContext.AliasesWF Env1.context :=
        (LTy_instantiateWithCheck_context' _ C Env ty_inst Env1 h_inst) ▸ h_aw
      have h_ctx1 : ContextFreshForGen Env1.context Env1.genEnv.genState :=
        (LTy_instantiateWithCheck_context' _ C Env ty_inst Env1 h_inst) ▸
          ContextFreshForGen.mono _ _ _ h_cf (LTy_instantiateWithCheck_tyGen_mono _ C Env ty_inst Env1 h_inst)
      have h_fresh1 := LTy_instantiateWithCheck_preserves_SubstFreshForGen type_val C Env ty_inst Env1 h_inst h_sf h_aw h_ty_fresh_vacuous h_bv_fresh
      have h_fresh2 := LMonoTy_instantiateWithCheck_preserves_SubstFreshForGen oty_val C Env1 oty_inst Env2 h_inst2 h_fresh1 h_aw1
      have h_unify := unify_of_mapError h_mapError
      refine ⟨Nat.le_trans (LTy_instantiateWithCheck_tyGen_mono type_val C Env ty_inst Env1 h_inst)
                (LMonoTy_instantiateWithCheck_tyGen_mono oty_val C Env1 oty_inst Env2 h_inst2),
             ?_, ⟨?_, ?_⟩,
             Subst.absorbs_trans Env.stateSubstInfo.subst Env2.stateSubstInfo.subst v3.subst
               (Subst.absorbs_trans Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
                 (LTy_instantiateWithCheck_absorbs type_val C Env ty_inst Env1 h_inst)
                 (LMonoTy_instantiateWithCheck_absorbs oty_val C Env1 oty_inst Env2 h_inst2))
               (Constraints.unify_absorbs _ _ _ h_unify)⟩
      · show (TEnv.updateSubst Env2 v3).context.Equiv Env.context
        apply TContext.Equiv.of_eq
        show Env2.context = Env.context
        rw [LMonoTy_instantiateWithCheck_context _ C Env1 oty_inst Env2 h_inst2,
            LTy_instantiateWithCheck_context _ C Env ty_inst Env1 h_inst]
      · exact unify_preserves_SubstFreshForGen h_unify h_fresh2 (fun v hv n hn => by
          simp [Constraints.freeVars, Constraint.freeVars] at hv
          cases hv with
          | inl h_ty =>
            exact LTy_instantiateWithCheck_freeVars_fresh type_val C Env ty_inst Env1
              h_inst v h_ty n (Nat.le_trans
              (LMonoTy_instantiateWithCheck_tyGen_mono oty_val C Env1 oty_inst Env2 h_inst2) hn)
          | inr h_oty =>
            exact LMonoTy_instantiateWithCheck_freeVars_fresh oty_val C Env1 oty_inst Env2
              h_inst2 v h_oty n hn)
      · intro v hv k hk; simp [toLMonoTy] at hv
        exact LTy_instantiateWithCheck_freeVars_fresh type_val C Env ty_inst Env1 h_inst v hv k
          (Nat.le_trans (LMonoTy_instantiateWithCheck_tyGen_mono oty_val C Env1 oty_inst Env2 h_inst2) hk)
  | .app m e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    elim_err h
    rename_i v1 h_res1; obtain ⟨e1t, Env1⟩ := v1; dsimp at h h_res1
    elim_err h
    rename_i v2 h_res2; obtain ⟨e2t, Env2⟩ := v2; dsimp at h h_res2
    elim_err h
    rename_i v3 h_gen; obtain ⟨fresh_name, Env3⟩ := v3; dsimp at h h_gen
    elim_err h
    rename_i v4 h_mapError
    simp at h; obtain ⟨h_et, h2⟩ := h; subst h_et h2; simp [TEnv.updateSubst]
    have h_sz1 : e1.sizeOf < n := by expr_size h_eq
    have h_sz2 : e2.sizeOf < n := by expr_size h_eq
    have ⟨h_mono1, h_ctx1_eq, ⟨h_sf1, h_otf1⟩, h_abs1⟩ :=
      ih e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1 h_ne h_aw h_fwf h_sf h_cf h_bvf
    have h_ne1 := h_ctx1_eq.symm.types_ne_nil h_ne
    have h_cf1 := h_ctx1_eq.symm.ctxFreshForGen (ContextFreshForGen.mono _ _ _ h_cf h_mono1)
    have h_aw1 : TContext.AliasesWF Env1.context := h_ctx1_eq.symm.aliasesWF h_aw
    have h_bvf1 := transfer_boundVarsFresh_equiv h_bvf h_ctx1_eq h_mono1
    have ⟨h_mono2, h_ctx2_eq, ⟨h_sf2, h_otf2⟩, h_abs2⟩ :=
      ih e2.sizeOf h_sz2 e2 rfl e2t C Env1 Env2 h_res2 h_ne1 h_aw1 h_fwf h_sf1 h_cf1 h_bvf1
    have h_gen_subst := TEnv.genTyVar_subst Env2 fresh_name Env3 h_gen
    have h_gen_ctx := TEnv.genTyVar_context Env2 fresh_name Env3 h_gen
    have h_gen_name := genTyVar_name_eq Env2 fresh_name Env3 h_gen
    have h_gen_tyGen := genTyVar_tyGen Env2 fresh_name Env3 h_gen
    have h_unify := unify_of_mapError h_mapError
    have h_sf3 : SubstFreshForGen Env3.stateSubstInfo Env3.genEnv.genState := by
      rw [h_gen_subst]; exact SubstFreshForGen.mono _ _ _ h_sf2 (by omega)
    have h_cs_fresh : ∀ v, v ∈ Constraints.freeVars
        [(e1t.toLMonoTy, LMonoTy.tcons "arrow" [e2t.toLMonoTy, .ftvar fresh_name])] →
        ∀ k, k ≥ Env3.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString k := by
      intro w hw k hk
      simp [Constraints.freeVars, Constraint.freeVars, LMonoTy.freeVars, LMonoTys.freeVars] at hw
      rcases hw with hw1 | hw2 | hw3
      · exact h_otf1 w hw1 k (by omega)
      · exact h_otf2 w hw2 k (by omega)
      · rw [hw3, h_gen_name]
        exact generated_name_fresh Env2.genEnv.genState.tyGen Env3.genEnv.genState (by omega) k hk
    have h_sf4 := unify_preserves_SubstFreshForGen h_unify h_sf3 h_cs_fresh
    rw [h_gen_subst] at h_unify
    have h_abs_chain := Subst.absorbs_trans
      Env.stateSubstInfo.subst Env2.stateSubstInfo.subst v4.subst
      (Subst.absorbs_trans Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
        h_abs1 h_abs2)
      (Constraints.unify_absorbs _ _ _ h_unify)
    have ⟨h_not_key, h_not_fv⟩ :=
      genTyVar_fresh_wrt_input_subst Env Env2 Env3 fresh_name h_gen h_sf (Nat.le_trans h_mono1 h_mono2)
    refine ⟨by omega, ?_, ⟨?_, ?_⟩,
            Subst.absorbs_of_remove v4.subst Env.stateSubstInfo.subst fresh_name h_abs_chain h_not_key h_not_fv⟩
    · -- context: genTyVar/unify/updateSubst don't change context
      show (TEnv.updateSubst Env3 _).context.Equiv Env.context
      exact (TContext.Equiv.of_eq h_gen_ctx).trans (h_ctx2_eq.trans h_ctx1_eq)
    · -- SubstFreshForGen (remove preserves freshness)
      intro v hv n_ hn
      exact h_sf4 v (by
        cases hv with
        | inl h_key => exact Or.inl (HMaps.keys_remove_subset _ _ _ h_key)
        | inr h_fv =>
          exact Or.inr (by
            simp only [Subst.freeVars, List.mem_flatMap] at h_fv ⊢
            obtain ⟨ty, h_ty_mem, h_v_fv⟩ := h_fv
            exact ⟨ty, HMaps.values_remove_subset _ _ _ h_ty_mem, h_v_fv⟩)) n_ hn
    · -- Output type freshness
      intro v hv k hk; simp [toLMonoTy] at hv
      have hv_in := LMonoTy.freeVars_of_subst_subset v4.subst (.ftvar fresh_name) hv
      simp [LMonoTy.freeVars] at hv_in
      rcases hv_in with hv_fresh | hv_fv
      · rw [hv_fresh, h_gen_name]
        exact generated_name_fresh Env2.genEnv.genState.tyGen Env3.genEnv.genState (by omega) k hk
      · exact h_sf4 v (Or.inr hv_fv) k hk
  | .abs m _ bty body =>
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_tbv; obtain ⟨xv_id, xty_val, Env1⟩ := v1; simp at h h_tbv
    elim_err h
    rename_i v2 h_rec; obtain ⟨et', Env2⟩ := v2; simp at h
    obtain ⟨h_et, h_env⟩ := h; rw [← h_env]; simp [TEnv.eraseFromContext, TEnv.updateContext]
    have h_sz : (varOpen 0 (xv_id, some xty_val) body).sizeOf < n := by expr_size h_eq
    have h_inv1 := typeBoundVar_preserves_invariant C Env bty xv_id xty_val Env1 h_tbv h_sf h_cf h_aw h_bvf
    have h_ne1 : Env1.context.types ≠ [] := typeBoundVar_context_types_ne_nil C Env bty xv_id xty_val Env1 h_tbv
    have ⟨h_mono_body, h_ctx_body, ⟨h_sf_body, h_otf_body⟩, h_abs_body⟩ :=
      ih _ h_sz (varOpen 0 (xv_id, some xty_val) body) rfl et' C Env1 Env2 h_rec
        h_ne1 h_inv1.aliasesWF h_fwf h_inv1.substFreshForGen h_inv1.ctxFreshForGen h_inv1.boundVarsFresh
    refine ⟨Nat.le_trans (typeBoundVar_tyGen_mono C Env bty xv_id xty_val Env1 h_tbv) h_mono_body,
            ?_,
            ⟨h_sf_body, ?_⟩,
            Subst.absorbs_trans Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
              (typeBoundVar_absorbs C Env bty xv_id xty_val Env1 h_tbv) h_abs_body⟩
    · -- context: erase-cancel via the Equiv helper
      show (Env2.eraseFromContext xv_id).context.Equiv Env.context
      exact eraseFromContext_typeBoundVar_equiv C Env bty xv_id xty_val Env1 h_tbv Env2 h_ctx_body h_ne
    · -- Output type freshness for abs
      intro v hv k hk
      rw [← h_et] at hv; simp [toLMonoTy] at hv
      have hv_in := LMonoTy.freeVars_of_subst_subset Env2.stateSubstInfo.subst
        (.tcons "arrow" [xty_val, (Lambda.LExpr.varCloseT 0 xv_id et').toLMonoTy]) hv
      simp [List.mem_append] at hv_in
      rcases hv_in with hv_ty | hv_subst
      · simp [LMonoTy.freeVars, LMonoTys.freeVars, List.mem_append] at hv_ty
        rcases hv_ty with hv_xty | hv_ety
        · -- v from xty_val: gen-fresh from typeBoundVar (lifted to Env2 via h_mono_body)
          exact typeBoundVar_xty_freeVars_fresh C Env bty xv_id xty_val Env1 h_tbv v hv_xty k
            (by omega)
        · -- v from varCloseT et': varCloseT preserves toLMonoTy
          have h_close_ty : (Lambda.LExpr.varCloseT 0 xv_id et').toLMonoTy = et'.toLMonoTy := by
            match et' with
            | .const _ _ | .op _ _ _ | .bvar _ _ | .abs _ _ _ _ | .app _ _ _
            | .ite _ _ _ _ | .eq _ _ _ | .quant _ _ _ _ _ _ => rfl
            | .fvar _ y _ => simp only [Lambda.LExpr.varCloseT]; split <;> rfl
          rw [h_close_ty] at hv_ety
          exact h_otf_body v hv_ety k hk
      · exact h_sf_body v (Or.inr hv_subst) k hk
  | .quant m qk _ bty tr body =>
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    elim_err h
    rename_i v1 h_tbv; obtain ⟨xv_id, xty_val, Env1⟩ := v1; simp at h h_tbv
    elim_err h
    rename_i v2 h_rec_e; obtain ⟨et', Env2⟩ := v2; simp at h h_rec_e
    elim_err h
    rename_i v3 h_rec_tr; obtain ⟨trT, Env3⟩ := v3; simp at h h_rec_tr
    elim_err h
    rename_i v4 h_mapError
    simp at h; obtain ⟨h_et, h_env⟩ := h; rw [← h_env]
    simp [TEnv.eraseFromContext, TEnv.updateContext, TEnv.updateSubst]
    have h_sz_e : (varOpen 0 (xv_id, some xty_val) body).sizeOf < n := by expr_size h_eq
    have h_sz_tr : (varOpen 0 (xv_id, some xty_val) tr).sizeOf < n := by expr_size h_eq
    have h_inv1 := typeBoundVar_preserves_invariant C Env bty xv_id xty_val Env1 h_tbv h_sf h_cf h_aw h_bvf
    have h_ne1 : Env1.context.types ≠ [] := typeBoundVar_context_types_ne_nil C Env bty xv_id xty_val Env1 h_tbv
    have ⟨h_mono_e, h_ctx2_eq, ⟨h_sf2, h_otf_e⟩, h_abs_e⟩ :=
      ih _ h_sz_e _ rfl et' C Env1 Env2 h_rec_e h_ne1
        h_inv1.aliasesWF h_fwf h_inv1.substFreshForGen h_inv1.ctxFreshForGen h_inv1.boundVarsFresh
    have h_ne2 := h_ctx2_eq.symm.types_ne_nil h_ne1
    have h_cf2 := h_ctx2_eq.symm.ctxFreshForGen (ContextFreshForGen.mono _ _ _ h_inv1.ctxFreshForGen h_mono_e)
    have h_aw2 : TContext.AliasesWF Env2.context := h_ctx2_eq.symm.aliasesWF h_inv1.aliasesWF
    have h_bvf2 := transfer_boundVarsFresh_equiv h_inv1.boundVarsFresh h_ctx2_eq h_mono_e
    have ⟨h_mono_tr, h_ctx3_eq, ⟨h_sf3, _⟩, h_abs_tr⟩ :=
      ih _ h_sz_tr _ rfl trT C Env2 Env3 h_rec_tr h_ne2 h_aw2 h_fwf h_sf2 h_cf2 h_bvf2
    have h_mono_tbv := typeBoundVar_tyGen_mono C Env bty xv_id xty_val Env1 h_tbv
    have h_unify := unify_of_mapError h_mapError
    refine ⟨by omega,
            ?_,
            ⟨unify_preserves_SubstFreshForGen h_unify h_sf3 (fun v hv n_ hn => by
                simp [Constraints.freeVars, Constraint.freeVars, LMonoTy.freeVars, LMonoTys.freeVars] at hv
                exact h_otf_e v hv n_ (by omega)),
             fun v hv n hn => by rw [← h_et] at hv; simp [toLMonoTy, LMonoTy.bool, LMonoTy.freeVars, LMonoTys.freeVars] at hv⟩,
            Subst.absorbs_trans Env.stateSubstInfo.subst Env3.stateSubstInfo.subst v4.subst
              (Subst.absorbs_trans Env.stateSubstInfo.subst Env2.stateSubstInfo.subst Env3.stateSubstInfo.subst
                (Subst.absorbs_trans Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
                  (typeBoundVar_absorbs C Env bty xv_id xty_val Env1 h_tbv) h_abs_e)
                h_abs_tr)
              (Constraints.unify_absorbs _ _ _ h_unify)⟩
    · -- context: erase-cancel; the body/trigger + unify + updateSubst give Env3.updateSubst v4 ≈ Env1
      show ((TEnv.updateSubst Env3 v4).eraseFromContext xv_id).context.Equiv Env.context
      apply eraseFromContext_typeBoundVar_equiv C Env bty xv_id xty_val Env1 h_tbv (Env3.updateSubst v4) _ h_ne
      -- (Env3.updateSubst v4).context = Env3.context ≈ Env2.context ≈ Env1.context
      exact (TContext.Equiv.of_eq (rfl : (Env3.updateSubst v4).context = Env3.context)).trans
        (h_ctx3_eq.trans h_ctx2_eq)
  | .eq m e1 e2 =>
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    elim_err h
    rename_i v1 h_res1; obtain ⟨e1t, Env1⟩ := v1; dsimp at h h_res1
    elim_err h
    rename_i v2 h_res2; obtain ⟨e2t, Env2⟩ := v2; dsimp at h h_res2
    elim_err h
    rename_i v3 h_mapError
    simp at h; obtain ⟨h_et, h2⟩ := h; subst h_et h2; simp [TEnv.updateSubst]
    have h_sz1 : e1.sizeOf < n := by expr_size h_eq
    have h_sz2 : e2.sizeOf < n := by expr_size h_eq
    have ⟨h_mono1, h_ctx1_eq, ⟨h_sf1, h_otf1⟩, h_abs1⟩ :=
      ih e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h_res1 h_ne h_aw h_fwf h_sf h_cf h_bvf
    have h_ne1 := h_ctx1_eq.symm.types_ne_nil h_ne
    have h_cf1 := h_ctx1_eq.symm.ctxFreshForGen (ContextFreshForGen.mono _ _ _ h_cf h_mono1)
    have h_aw1 : TContext.AliasesWF Env1.context := h_ctx1_eq.symm.aliasesWF h_aw
    have h_bvf1 := transfer_boundVarsFresh_equiv h_bvf h_ctx1_eq h_mono1
    have ⟨h_mono2, h_ctx2_eq, ⟨h_sf2, h_otf2⟩, h_abs2⟩ :=
      ih e2.sizeOf h_sz2 e2 rfl e2t C Env1 Env2 h_res2 h_ne1 h_aw1 h_fwf h_sf1 h_cf1 h_bvf1
    have h_unify := unify_of_mapError h_mapError
    refine ⟨by omega, ?_, ⟨?_, ?_⟩,
            Subst.absorbs_trans Env.stateSubstInfo.subst Env2.stateSubstInfo.subst v3.subst
              (Subst.absorbs_trans Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
                h_abs1 h_abs2)
              (Constraints.unify_absorbs _ _ _ h_unify)⟩
    · show (TEnv.updateSubst Env2 v3).context.Equiv Env.context
      exact h_ctx2_eq.trans h_ctx1_eq
    · exact unify_preserves_SubstFreshForGen h_unify h_sf2 (fun v hv n_ hn => by
        simp [Constraints.freeVars, Constraint.freeVars] at hv
        cases hv with
        | inl h_e1 => exact h_otf1 v h_e1 n_ (by omega)
        | inr h_e2 => exact h_otf2 v h_e2 n_ hn)
    · intro v hv; simp [toLMonoTy, LMonoTy.freeVars, LMonoTys.freeVars] at hv
  | .ite m c t e =>
    simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h
    elim_err h
    rename_i v1 h_res_c; obtain ⟨ct, Env1⟩ := v1; dsimp at h h_res_c
    elim_err h
    rename_i v2 h_res_t; obtain ⟨tht, Env2⟩ := v2; dsimp at h h_res_t
    elim_err h
    rename_i v3 h_res_e; obtain ⟨elt, Env3⟩ := v3; dsimp at h h_res_e
    elim_err h
    rename_i v4 h_mapError
    simp at h; obtain ⟨h_et, h2⟩ := h; subst h_et h2; simp [TEnv.updateSubst]
    have h_sz_c : c.sizeOf < n := by expr_size h_eq
    have h_sz_t : t.sizeOf < n := by expr_size h_eq
    have h_sz_e : e.sizeOf < n := by expr_size h_eq
    have ⟨h_mono_c, h_ctx1_eq, ⟨h_sf1, h_otf_c⟩, h_abs_c⟩ :=
      ih c.sizeOf h_sz_c c rfl ct C Env Env1 h_res_c h_ne h_aw h_fwf h_sf h_cf h_bvf
    have h_ne1 := h_ctx1_eq.symm.types_ne_nil h_ne
    have h_cf1 := h_ctx1_eq.symm.ctxFreshForGen (ContextFreshForGen.mono _ _ _ h_cf h_mono_c)
    have h_aw1 : TContext.AliasesWF Env1.context := h_ctx1_eq.symm.aliasesWF h_aw
    have h_bvf1 := transfer_boundVarsFresh_equiv h_bvf h_ctx1_eq h_mono_c
    have ⟨h_mono_t, h_ctx2_eq, ⟨h_sf2, h_otf_t⟩, h_abs_t⟩ :=
      ih t.sizeOf h_sz_t t rfl tht C Env1 Env2 h_res_t h_ne1 h_aw1 h_fwf h_sf1 h_cf1 h_bvf1
    have h_ne2 := h_ctx2_eq.symm.types_ne_nil h_ne1
    have h_cf2 := h_ctx2_eq.symm.ctxFreshForGen (ContextFreshForGen.mono _ _ _ h_cf1 h_mono_t)
    have h_aw2 : TContext.AliasesWF Env2.context := h_ctx2_eq.symm.aliasesWF h_aw1
    have h_bvf2 := transfer_boundVarsFresh_equiv h_bvf1 h_ctx2_eq h_mono_t
    have ⟨h_mono_e, h_ctx3_eq, ⟨h_sf3, h_otf_e⟩, h_abs_e⟩ :=
      ih e.sizeOf h_sz_e e rfl elt C Env2 Env3 h_res_e h_ne2 h_aw2 h_fwf h_sf2 h_cf2 h_bvf2
    have h_unify := unify_of_mapError h_mapError
    refine ⟨by omega, ?_, ⟨?_, ?_⟩,
            Subst.absorbs_trans Env.stateSubstInfo.subst Env3.stateSubstInfo.subst v4.subst
              (Subst.absorbs_trans Env.stateSubstInfo.subst Env2.stateSubstInfo.subst Env3.stateSubstInfo.subst
                (Subst.absorbs_trans Env.stateSubstInfo.subst Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst
                  h_abs_c h_abs_t)
                h_abs_e)
              (Constraints.unify_absorbs _ _ _ h_unify)⟩
    · show (TEnv.updateSubst Env3 v4).context.Equiv Env.context
      exact h_ctx3_eq.trans (h_ctx2_eq.trans h_ctx1_eq)
    · exact unify_preserves_SubstFreshForGen h_unify h_sf3 (fun v hv n_ hn => by
        simp [Constraints.freeVars, Constraint.freeVars, LMonoTy.freeVars, LMonoTys.freeVars] at hv
        rcases hv with hv_c | hv_t | hv_e
        · exact h_otf_c v hv_c n_ (by omega)
        · exact h_otf_t v hv_t n_ (by omega)
        · exact h_otf_e v hv_e n_ hn)
    · intro v hv k hk; simp [toLMonoTy] at hv
      exact h_otf_t v hv k (by omega)

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Combined properties of `resolveAux`: generator monotonicity, context
    preservation (up to `TContext.Equiv`), substitution freshness preservation,
    output type freshness, and absorption. -/
structure ResolveAuxProperties (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h_ne : Env.context.types ≠ [])
    (h_aw : TContext.AliasesWF Env.context)
    (h_fwf : FactoryWF C.functions)
    (h_sf : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_cf : ContextFreshForGen Env.context Env.genEnv.genState)
    (h_bvf : ∀ y ty, Env.context.types.find? y = some ty →
      ∀ v, v ∈ LTy.boundVars ty →
        ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) : Prop where
  /-- `resolveAux` never decreases the generator counter. -/
  genState_mono : Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen
  /-- `resolveAux` preserves the context up to find?-equivalence. -/
  context : Env'.context.Equiv Env.context
  /-- `resolveAux` preserves `SubstFreshForGen` and output type freshness. -/
  preserves :
    SubstFreshForGen Env'.stateSubstInfo Env'.genEnv.genState ∧
    (∀ v, v ∈ LMonoTy.freeVars et.toLMonoTy →
      ∀ k, k ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString k)
  /-- `resolveAux` produces a substitution that absorbs the input substitution. -/
  absorbs : Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Prove all `ResolveAuxProperties` for `resolveAux`. -/
theorem resolveAux_properties
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h : resolveAux C Env e = .ok (et, Env'))
    (h_ne : Env.context.types ≠ [])
    (h_aw : TContext.AliasesWF Env.context)
    (h_fwf : FactoryWF C.functions)
    (h_sf : SubstFreshForGen Env.stateSubstInfo Env.genEnv.genState)
    (h_cf : ContextFreshForGen Env.context Env.genEnv.genState)
    (h_bvf : ∀ y ty, Env.context.types.find? y = some ty →
      ∀ v, v ∈ LTy.boundVars ty →
        ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    ResolveAuxProperties e et C Env Env' h_ne h_aw h_fwf h_sf h_cf h_bvf :=
  let ⟨h1, h2, h3, h4⟩ := resolveAux_properties_aux e.sizeOf e rfl et C Env Env' h h_ne h_aw h_fwf h_sf h_cf h_bvf
  { genState_mono := h1, context := h2, preserves := h3, absorbs := h4 }

/-! ### `resolveAux` induction principle + `TEnvWF` propagation

`TEnvWF.of_resolveAux` and the reusable
`resolveAux_ind`. Context-preservation
hypotheses are stated up to `TContext.Equiv`. -/

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Build `TEnvWF` for the output of `resolveAux` given `TEnvWF` for the input.
    Context-preservation is up to `TContext.Equiv`. -/
theorem TEnvWF.of_resolveAux
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h_res : resolveAux C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions)
    (h_ctx : Env'.context.Equiv Env.context) : TEnvWF Env' :=
  let props := resolveAux_properties e et C Env Env' h_res h_ne
    h_envwf.aliasesWF h_fwf h_envwf.substFreshForGen h_envwf.ctxFreshForGen h_envwf.boundVarsFresh
  { aliasesWF := h_ctx.symm.aliasesWF h_envwf.aliasesWF
    substFreshForGen := props.preserves.1
    ctxFreshForGen := h_ctx.symm.ctxFreshForGen
      (ContextFreshForGen.mono _ _ _ h_envwf.ctxFreshForGen props.genState_mono)
    boundVarsNodup := h_ctx.symm.boundVarsNodup h_envwf.boundVarsNodup
    boundVarsFresh := transfer_boundVarsFresh_equiv h_envwf.boundVarsFresh h_ctx
      props.genState_mono }

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Reusable induction principle for `resolveAux`. Handles strong induction on
    expression size, monadic decomposition, and propagation of `TEnvWF` /
    `types ≠ []` through the chain of environments. Context-preservation
    hypotheses are stated up to `TContext.Equiv`. -/
theorem resolveAux_ind
    (P : (e : LExpr T.mono) → (et : LExprT T.mono) → (C : LContext T) →
         (Env Env' : TEnv T.IDMeta) → Prop)
    -- Base cases
    (h_const : ∀ m c et C Env Env',
      resolveAux C Env (.const m c) = .ok (et, Env') →
      TEnvWF Env → Env.context.types ≠ [] → FactoryWF C.functions →
      P (.const m c) et C Env Env')
    (h_op : ∀ m o oty et C Env Env',
      resolveAux C Env (.op m o oty) = .ok (et, Env') →
      TEnvWF Env → Env.context.types ≠ [] → FactoryWF C.functions →
      P (.op m o oty) et C Env Env')
    (h_fvar : ∀ m x fty et C Env Env',
      resolveAux C Env (.fvar m x fty) = .ok (et, Env') →
      TEnvWF Env → Env.context.types ≠ [] → FactoryWF C.functions →
      P (.fvar m x fty) et C Env Env')
    -- Recursive: app (fully decomposed)
    (h_app : ∀ m e1 e2 et C Env Env'
      (e1t : LExprT T.mono) (Env1 : TEnv T.IDMeta)
      (e2t : LExprT T.mono) (Env2 : TEnv T.IDMeta)
      (fresh_name : String) (Env_gen : TEnv T.IDMeta)
      (substInfo : SubstInfo),
      resolveAux C Env (.app m e1 e2) = .ok (et, Env') →
      resolveAux C Env e1 = .ok (e1t, Env1) →
      resolveAux C Env1 e2 = .ok (e2t, Env2) →
      TEnv.genTyVar Env2 = .ok (fresh_name, Env_gen) →
      Constraints.unify [(e1t.toLMonoTy, .tcons "arrow" [e2t.toLMonoTy, .ftvar fresh_name])]
        Env_gen.stateSubstInfo = .ok substInfo →
      et = .app ⟨m, LMonoTy.subst substInfo.subst (.ftvar fresh_name)⟩ e1t e2t →
      Env'.stateSubstInfo.subst = HMaps.remove substInfo.subst fresh_name →
      Subst.absorbs (HMaps.remove substInfo.subst fresh_name) Env1.stateSubstInfo.subst →
      Subst.absorbs (HMaps.remove substInfo.subst fresh_name) Env2.stateSubstInfo.subst →
      fresh_name ∉ LMonoTy.freeVars e1t.toLMonoTy →
      fresh_name ∉ LMonoTy.freeVars e2t.toLMonoTy →
      LMonoTy.subst substInfo.subst e1t.toLMonoTy =
        LMonoTy.subst substInfo.subst (.tcons "arrow" [e2t.toLMonoTy, .ftvar fresh_name]) →
      TEnvWF Env → Env.context.types ≠ [] → FactoryWF C.functions →
      TEnvWF Env1 → Env1.context.Equiv Env.context →
      TEnvWF Env2 → Env2.context.Equiv Env.context →
      P e1 e1t C Env Env1 → P e2 e2t C Env1 Env2 →
      P (.app m e1 e2) et C Env Env')
    -- Recursive: abs
    (h_abs : ∀ m name bty body et C Env Env'
      (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
      (et_body : LExprT T.mono) (Env2 : TEnv T.IDMeta),
      resolveAux C Env (.abs m name bty body) = .ok (et, Env') →
      typeBoundVar C Env bty = .ok (xv, xty, Env1) →
      resolveAux C Env1 (LExpr.varOpen 0 (xv, some xty) body) = .ok (et_body, Env2) →
      et = .abs ⟨m, LMonoTy.subst Env2.stateSubstInfo.subst
        (.tcons "arrow" [xty, (LExpr.varCloseT 0 xv et_body).toLMonoTy])⟩
        name bty (LExpr.varCloseT 0 xv et_body) →
      Env' = Env2.eraseFromContext xv →
      TEnvWF Env → Env.context.types ≠ [] → FactoryWF C.functions →
      TEnvWF Env1 → Env1.context.types ≠ [] →
      Env1.context.aliases = Env.context.aliases →
      P (LExpr.varOpen 0 (xv, some xty) body) et_body C Env1 Env2 →
      P (.abs m name bty body) et C Env Env')
    -- Recursive: quant
    (h_quant : ∀ m qk name bty triggers body et C Env Env'
      (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
      (et_body : LExprT T.mono) (Env2 : TEnv T.IDMeta)
      (et_tr : LExprT T.mono) (Env3 : TEnv T.IDMeta)
      (substInfo : SubstInfo),
      resolveAux C Env (.quant m qk name bty triggers body) = .ok (et, Env') →
      typeBoundVar C Env bty = .ok (xv, xty, Env1) →
      resolveAux C Env1 (LExpr.varOpen 0 (xv, some xty) body) = .ok (et_body, Env2) →
      resolveAux C Env2 (LExpr.varOpen 0 (xv, some xty) triggers) = .ok (et_tr, Env3) →
      Constraints.unify [(et_body.toLMonoTy, LMonoTy.bool)] Env3.stateSubstInfo = .ok substInfo →
      et = .quant ⟨m, LMonoTy.subst substInfo.subst xty⟩ qk name
        (LMonoTy.subst substInfo.subst xty)
        (LExpr.varCloseT 0 xv et_tr) (LExpr.varCloseT 0 xv et_body) →
      Env' = (Env3.updateSubst substInfo).eraseFromContext xv →
      Subst.absorbs Env3.stateSubstInfo.subst Env2.stateSubstInfo.subst →
      TEnvWF Env → Env.context.types ≠ [] → FactoryWF C.functions →
      TEnvWF Env1 → Env1.context.types ≠ [] →
      Env1.context.aliases = Env.context.aliases →
      TEnvWF Env2 → Env2.context.Equiv Env1.context →
      P (LExpr.varOpen 0 (xv, some xty) body) et_body C Env1 Env2 →
      P (LExpr.varOpen 0 (xv, some xty) triggers) et_tr C Env2 Env3 →
      P (.quant m qk name bty triggers body) et C Env Env')
    -- Recursive: eq (with unify decomposition)
    (h_eq : ∀ m e1 e2 et C Env Env'
      (e1t : LExprT T.mono) (Env1 : TEnv T.IDMeta)
      (e2t : LExprT T.mono) (Env2 : TEnv T.IDMeta)
      (substInfo : SubstInfo),
      resolveAux C Env (.eq m e1 e2) = .ok (et, Env') →
      resolveAux C Env e1 = .ok (e1t, Env1) →
      resolveAux C Env1 e2 = .ok (e2t, Env2) →
      Constraints.unify [(e1t.toLMonoTy, e2t.toLMonoTy)]
        Env2.stateSubstInfo = .ok substInfo →
      et = .eq ⟨m, LMonoTy.bool⟩ e1t e2t →
      Env'.stateSubstInfo.subst = substInfo.subst →
      Subst.absorbs Env1.stateSubstInfo.subst Env.stateSubstInfo.subst →
      Subst.absorbs Env2.stateSubstInfo.subst Env1.stateSubstInfo.subst →
      TEnvWF Env → Env.context.types ≠ [] → FactoryWF C.functions →
      TEnvWF Env1 → Env1.context.Equiv Env.context →
      TEnvWF Env2 → Env2.context.Equiv Env.context →
      P e1 e1t C Env Env1 → P e2 e2t C Env1 Env2 →
      P (.eq m e1 e2) et C Env Env')
    -- Recursive: ite (with unify decomposition)
    (h_ite : ∀ m c th el et C Env Env'
      (ct : LExprT T.mono) (Env1 : TEnv T.IDMeta)
      (tht : LExprT T.mono) (Env2 : TEnv T.IDMeta)
      (elt : LExprT T.mono) (Env3 : TEnv T.IDMeta)
      (substInfo : SubstInfo),
      resolveAux C Env (.ite m c th el) = .ok (et, Env') →
      resolveAux C Env c = .ok (ct, Env1) →
      resolveAux C Env1 th = .ok (tht, Env2) →
      resolveAux C Env2 el = .ok (elt, Env3) →
      Constraints.unify [(ct.toLMonoTy, LMonoTy.bool), (tht.toLMonoTy, elt.toLMonoTy)]
        Env3.stateSubstInfo = .ok substInfo →
      et = .ite ⟨m, tht.toLMonoTy⟩ ct tht elt →
      Env'.stateSubstInfo.subst = substInfo.subst →
      Subst.absorbs Env2.stateSubstInfo.subst Env1.stateSubstInfo.subst →
      Subst.absorbs Env3.stateSubstInfo.subst Env2.stateSubstInfo.subst →
      TEnvWF Env → Env.context.types ≠ [] → FactoryWF C.functions →
      TEnvWF Env1 → Env1.context.Equiv Env.context →
      TEnvWF Env2 → Env2.context.Equiv Env.context →
      TEnvWF Env3 → Env3.context.Equiv Env.context →
      P c ct C Env Env1 → P th tht C Env1 Env2 → P el elt C Env2 Env3 →
      P (.ite m c th el) et C Env Env')
    -- Main statement
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h_res : resolveAux C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions) :
    P e et C Env Env' := by
  have h_main : ∀ (n : Nat) (e : LExpr T.mono), e.sizeOf = n →
      ∀ (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      TEnvWF Env → Env.context.types ≠ [] → FactoryWF C.functions →
      P e et C Env Env' := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
    intro e h_sz et C Env Env' h_res h_envwf' h_ne' h_fwf'
    match e with
    | .const m c => exact h_const m c et C Env Env' h_res h_envwf' h_ne' h_fwf'
    | .op m o oty => exact h_op m o oty et C Env Env' h_res h_envwf' h_ne' h_fwf'
    | .fvar m x fty => exact h_fvar m x fty et C Env Env' h_res h_envwf' h_ne' h_fwf'
    | .bvar _ _ => simp [resolveAux] at h_res
    | .app m e1 e2 =>
      have h_orig := h_res
      simp only [resolveAux, Bind.bind, Except.bind] at h_res
      elim_err h_res
      rename_i v1 h1; obtain ⟨e1t, Env1⟩ := v1; dsimp at h_res h1
      elim_err h_res
      rename_i v2 h2; obtain ⟨e2t, Env2⟩ := v2; dsimp at h_res h2
      elim_err h_res
      rename_i v3 h3; obtain ⟨fresh_name, Env_gen⟩ := v3; dsimp at h_res h3
      elim_err h_res
      rename_i substInfo h_unify
      have h_unify' := unify_of_mapError h_unify
      have h_sz1 : e1.sizeOf < n := by subst h_sz; simp [LExpr.sizeOf]; omega
      have h_sz2 : e2.sizeOf < n := by subst h_sz; simp [LExpr.sizeOf]; omega
      have h_props1 := resolveAux_properties e1 e1t C Env Env1 h1 h_ne'
        h_envwf'.aliasesWF h_fwf' h_envwf'.substFreshForGen h_envwf'.ctxFreshForGen
        h_envwf'.boundVarsFresh
      have h_ctx1 := h_props1.context
      have h_envwf1 := TEnvWF.of_resolveAux e1 e1t C Env Env1 h1 h_envwf' h_ne' h_fwf' h_ctx1
      have h_ne1 : Env1.context.types ≠ [] := h_ctx1.symm.types_ne_nil h_ne'
      have h_props2 := resolveAux_properties e2 e2t C Env1 Env2 h2 h_ne1
        h_envwf1.aliasesWF h_fwf' h_envwf1.substFreshForGen h_envwf1.ctxFreshForGen
        h_envwf1.boundVarsFresh
      have h_ctx2 : Env2.context.Equiv Env.context := h_props2.context.trans h_ctx1
      have h_envwf2 := TEnvWF.of_resolveAux e2 e2t C Env1 Env2 h2 h_envwf1 h_ne1 h_fwf' h_props2.context
      have h_gen_subst := TEnv.genTyVar_subst Env2 fresh_name Env_gen h3
      have h_gen_name := genTyVar_name_eq Env2 fresh_name Env_gen h3
      have h_unify_gen := h_unify'
      rw [h_gen_subst] at h_unify_gen
      have h_abs_unify := Constraints.unify_absorbs _ _ _ h_unify_gen
      have h_fresh_e1 : HMaps.find? Env1.stateSubstInfo.subst fresh_name = none ∧
          (∀ a t, HMaps.find? Env1.stateSubstInfo.subst a = some t →
            fresh_name ∉ LMonoTy.freeVars t) :=
        genTyVar_fresh_wrt_input_subst Env1 Env2 Env_gen fresh_name h3
          h_envwf1.substFreshForGen h_props2.genState_mono
      have h_fresh_e2 : HMaps.find? Env2.stateSubstInfo.subst fresh_name = none ∧
          (∀ a t, HMaps.find? Env2.stateSubstInfo.subst a = some t →
            fresh_name ∉ LMonoTy.freeVars t) :=
        genTyVar_fresh_wrt_input_subst Env2 Env2 Env_gen fresh_name h3
          h_props2.preserves.1 (Nat.le_refl _)
      have h_abs_rem_e2 := Subst.absorbs_of_remove
        substInfo.subst Env2.stateSubstInfo.subst fresh_name
        h_abs_unify h_fresh_e2.1 h_fresh_e2.2
      have h_abs_rem_e1 := Subst.absorbs_of_remove
        substInfo.subst Env1.stateSubstInfo.subst fresh_name
        (Subst.absorbs_trans _ _ _ h_props2.absorbs h_abs_unify)
        h_fresh_e1.1 h_fresh_e1.2
      have h_e1t_no_fresh : fresh_name ∉ LMonoTy.freeVars e1t.toLMonoTy := by
        intro h_mem
        exact absurd h_gen_name
          (h_props1.preserves.2 fresh_name h_mem Env2.genEnv.genState.tyGen
            h_props2.genState_mono)
      have h_e2t_no_fresh : fresh_name ∉ LMonoTy.freeVars e2t.toLMonoTy := by
        intro h_mem
        exact absurd h_gen_name
          (h_props2.preserves.2 fresh_name h_mem Env2.genEnv.genState.tyGen
            (Nat.le_refl _))
      have h_unify_eq : LMonoTy.subst substInfo.subst e1t.toLMonoTy =
          LMonoTy.subst substInfo.subst
            (LMonoTy.tcons "arrow" [e2t.toLMonoTy, .ftvar fresh_name]) := by
        have h_p := Constraints.unify_sound _ _ _ h_unify_gen _ (List.Mem.head _)
        simp at h_p; exact h_p
      cases h_res
      have h_ih1 := ih e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h1 h_envwf' h_ne' h_fwf'
      have h_ih2 := ih e2.sizeOf h_sz2 e2 rfl e2t C Env1 Env2 h2 h_envwf1 h_ne1 h_fwf'
      exact h_app m e1 e2 _ C Env _ e1t Env1 e2t Env2 fresh_name Env_gen substInfo
        h_orig h1 h2 h3 h_unify' rfl rfl h_abs_rem_e1 h_abs_rem_e2
        h_e1t_no_fresh h_e2t_no_fresh h_unify_eq
        h_envwf' h_ne' h_fwf' h_envwf1 h_ctx1 h_envwf2 h_ctx2
        h_ih1 h_ih2
    | .abs m name bty body =>
      have h_orig := h_res
      simp only [resolveAux, Bind.bind, Except.bind] at h_res
      elim_err h_res
      rename_i v1 h_tbv; obtain ⟨xv, xty, Env1⟩ := v1; dsimp at h_res h_tbv
      elim_err h_res
      rename_i v2 h_res_body; obtain ⟨et_body, Env2⟩ := v2; dsimp at h_res h_res_body
      have h_sz_body : (LExpr.varOpen 0 (xv, some xty) body).sizeOf < n := by
        subst h_sz; simp [LExpr.sizeOf, LExpr.varOpen_sizeOf]
      have h_envwf1 := TEnvWF.of_typeBoundVar C Env bty xv xty Env1 h_tbv h_envwf'
      have h_ne1 := typeBoundVar_context_types_ne_nil C Env bty xv xty Env1 h_tbv
      have h_aliases_eq := typeBoundVar_aliases_eq C Env bty xv xty Env1 h_tbv
      have h_ih := ih _ h_sz_body _ rfl et_body C Env1 Env2 h_res_body h_envwf1 h_ne1 h_fwf'
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨h_et, h_env'⟩ := h_res
      subst h_et h_env'
      exact h_abs m name bty body _ C Env _ xv xty Env1 et_body Env2
        h_orig h_tbv h_res_body rfl rfl h_envwf' h_ne' h_fwf' h_envwf1 h_ne1 h_aliases_eq h_ih
    | .quant m qk name bty triggers body =>
      have h_orig := h_res
      simp only [resolveAux, Bind.bind, Except.bind, Except.mapError] at h_res
      elim_err h_res
      rename_i v1 h_tbv; obtain ⟨xv, xty, Env1⟩ := v1; dsimp at h_res h_tbv
      elim_err h_res
      rename_i v2 h_res_body; obtain ⟨et_body, Env2⟩ := v2; dsimp at h_res h_res_body
      elim_err h_res
      rename_i v3 h_res_tr; obtain ⟨et_tr, Env3⟩ := v3; dsimp at h_res h_res_tr
      elim_err h_res
      rename_i substInfo h_mapError
      have h_unify := unify_of_mapError h_mapError
      have h_sz_body : (LExpr.varOpen 0 (xv, some xty) body).sizeOf < n := by
        subst h_sz; simp [LExpr.sizeOf, LExpr.varOpen_sizeOf]; omega
      have h_sz_tr : (LExpr.varOpen 0 (xv, some xty) triggers).sizeOf < n := by
        subst h_sz; simp [LExpr.sizeOf, LExpr.varOpen_sizeOf]; omega
      have h_envwf1 := TEnvWF.of_typeBoundVar C Env bty xv xty Env1 h_tbv h_envwf'
      have h_ne1 := typeBoundVar_context_types_ne_nil C Env bty xv xty Env1 h_tbv
      have h_aliases_eq := typeBoundVar_aliases_eq C Env bty xv xty Env1 h_tbv
      have h_props_body := resolveAux_properties (LExpr.varOpen 0 (xv, some xty) body) et_body
        C Env1 Env2 h_res_body h_ne1 h_envwf1.aliasesWF h_fwf'
        h_envwf1.substFreshForGen h_envwf1.ctxFreshForGen h_envwf1.boundVarsFresh
      have h_ctx2 := h_props_body.context
      have h_envwf2 := TEnvWF.of_resolveAux (LExpr.varOpen 0 (xv, some xty) body) et_body
        C Env1 Env2 h_res_body h_envwf1 h_ne1 h_fwf' h_ctx2
      have h_ne2 : Env2.context.types ≠ [] := h_ctx2.symm.types_ne_nil h_ne1
      have h_props_tr := resolveAux_properties (LExpr.varOpen 0 (xv, some xty) triggers) et_tr
        C Env2 Env3 h_res_tr h_ne2 h_envwf2.aliasesWF h_fwf'
        h_envwf2.substFreshForGen h_envwf2.ctxFreshForGen h_envwf2.boundVarsFresh
      have h_ih_body := ih _ h_sz_body _ rfl et_body C Env1 Env2 h_res_body h_envwf1 h_ne1 h_fwf'
      have h_ih_tr := ih _ h_sz_tr _ rfl et_tr C Env2 Env3 h_res_tr h_envwf2 h_ne2 h_fwf'
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
      obtain ⟨h_et, h_env'⟩ := h_res
      subst h_et h_env'
      exact h_quant m qk name bty triggers body _ C Env _ xv xty Env1 et_body Env2 et_tr Env3 substInfo
        h_orig h_tbv h_res_body h_res_tr h_unify rfl rfl h_props_tr.absorbs h_envwf' h_ne' h_fwf' h_envwf1 h_ne1 h_aliases_eq
        h_envwf2 h_ctx2 h_ih_body h_ih_tr
    | .eq m e1 e2 =>
      have h_orig := h_res
      simp only [resolveAux, Bind.bind, Except.bind] at h_res
      elim_err h_res
      rename_i v1 h1; obtain ⟨e1t, Env1⟩ := v1; dsimp at h_res h1
      elim_err h_res
      rename_i v2 h2; obtain ⟨e2t, Env2⟩ := v2; dsimp at h_res h2
      elim_err h_res
      rename_i substInfo h_unify
      have h_unify' := unify_of_mapError h_unify
      have h_sz1 : e1.sizeOf < n := by subst h_sz; simp [LExpr.sizeOf]; omega
      have h_sz2 : e2.sizeOf < n := by subst h_sz; simp [LExpr.sizeOf]; omega
      have h_props1 := resolveAux_properties e1 e1t C Env Env1 h1 h_ne'
        h_envwf'.aliasesWF h_fwf' h_envwf'.substFreshForGen h_envwf'.ctxFreshForGen
        h_envwf'.boundVarsFresh
      have h_ctx1 := h_props1.context
      have h_envwf1 := TEnvWF.of_resolveAux e1 e1t C Env Env1 h1 h_envwf' h_ne' h_fwf' h_ctx1
      have h_ne1 : Env1.context.types ≠ [] := h_ctx1.symm.types_ne_nil h_ne'
      have h_props2 := resolveAux_properties e2 e2t C Env1 Env2 h2 h_ne1
        h_envwf1.aliasesWF h_fwf' h_envwf1.substFreshForGen h_envwf1.ctxFreshForGen
        h_envwf1.boundVarsFresh
      have h_ctx2 : Env2.context.Equiv Env.context := h_props2.context.trans h_ctx1
      have h_envwf2 := TEnvWF.of_resolveAux e2 e2t C Env1 Env2 h2 h_envwf1 h_ne1 h_fwf' h_props2.context
      cases h_res
      have h_ih1 := ih e1.sizeOf h_sz1 e1 rfl e1t C Env Env1 h1 h_envwf' h_ne' h_fwf'
      have h_ih2 := ih e2.sizeOf h_sz2 e2 rfl e2t C Env1 Env2 h2 h_envwf1 h_ne1 h_fwf'
      exact h_eq m e1 e2 _ C Env _ e1t Env1 e2t Env2 substInfo
        h_orig h1 h2 h_unify' rfl rfl h_props1.absorbs h_props2.absorbs
        h_envwf' h_ne' h_fwf' h_envwf1 h_ctx1 h_envwf2 h_ctx2
        h_ih1 h_ih2
    | .ite m c th el =>
      have h_orig := h_res
      simp only [resolveAux, Bind.bind, Except.bind] at h_res
      elim_err h_res
      rename_i vc hc; obtain ⟨ct, Env1⟩ := vc; dsimp at h_res hc
      elim_err h_res
      rename_i vt ht; obtain ⟨tht, Env2⟩ := vt; dsimp at h_res ht
      elim_err h_res
      rename_i ve he; obtain ⟨elt, Env3⟩ := ve; dsimp at h_res he
      elim_err h_res
      rename_i substInfo h_unify
      have h_unify' := unify_of_mapError h_unify
      have h_szc : c.sizeOf < n := by subst h_sz; simp [LExpr.sizeOf]; omega
      have h_szt : th.sizeOf < n := by subst h_sz; simp [LExpr.sizeOf]; omega
      have h_sze : el.sizeOf < n := by subst h_sz; simp [LExpr.sizeOf]; omega
      have h_props1 := resolveAux_properties c ct C Env Env1 hc h_ne'
        h_envwf'.aliasesWF h_fwf' h_envwf'.substFreshForGen h_envwf'.ctxFreshForGen
        h_envwf'.boundVarsFresh
      have h_ctx1 := h_props1.context
      have h_envwf1 := TEnvWF.of_resolveAux c ct C Env Env1 hc h_envwf' h_ne' h_fwf' h_ctx1
      have h_ne1 : Env1.context.types ≠ [] := h_ctx1.symm.types_ne_nil h_ne'
      have h_props2 := resolveAux_properties th tht C Env1 Env2 ht h_ne1
        h_envwf1.aliasesWF h_fwf' h_envwf1.substFreshForGen h_envwf1.ctxFreshForGen
        h_envwf1.boundVarsFresh
      have h_ctx2 : Env2.context.Equiv Env.context := h_props2.context.trans h_ctx1
      have h_envwf2 := TEnvWF.of_resolveAux th tht C Env1 Env2 ht h_envwf1 h_ne1 h_fwf' h_props2.context
      have h_ne2 : Env2.context.types ≠ [] := h_ctx2.symm.types_ne_nil h_ne'
      have h_props3 := resolveAux_properties el elt C Env2 Env3 he h_ne2
        h_envwf2.aliasesWF h_fwf' h_envwf2.substFreshForGen h_envwf2.ctxFreshForGen
        h_envwf2.boundVarsFresh
      have h_ctx3 : Env3.context.Equiv Env.context := h_props3.context.trans h_ctx2
      have h_envwf3 := TEnvWF.of_resolveAux el elt C Env2 Env3 he h_envwf2 h_ne2 h_fwf' h_props3.context
      cases h_res
      have h_ihc := ih c.sizeOf h_szc c rfl ct C Env Env1 hc h_envwf' h_ne' h_fwf'
      have h_iht := ih th.sizeOf h_szt th rfl tht C Env1 Env2 ht h_envwf1 h_ne1 h_fwf'
      have h_ihe := ih el.sizeOf h_sze el rfl elt C Env2 Env3 he h_envwf2 h_ne2 h_fwf'
      exact h_ite m c th el _ C Env _ ct Env1 tht Env2 elt Env3 substInfo
        h_orig hc ht he h_unify' rfl rfl h_props2.absorbs h_props3.absorbs
        h_envwf' h_ne' h_fwf' h_envwf1 h_ctx1 h_envwf2 h_ctx2
        h_envwf3 h_ctx3 h_ihc h_iht h_ihe
  exact h_main e.sizeOf e rfl et C Env Env' h_res h_envwf h_ne h_fwf


omit [ToString T.IDMeta] [HasGen T.IDMeta]
  [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Alias resolution preserves `HasType`. -/
private theorem HasType_resolveAliases
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono) (mty_in : LMonoTy)
    (mty_out : LMonoTy) (Env Env' : TEnv T.IDMeta)
    (h_ty : HasType C Γ e (.forAll [] mty_in))
    (h_ra : LMonoTy.resolveAliases mty_in Env = .ok (mty_out, Env'))
    (h_aliases : Γ.aliases = Env.context.aliases)
    (h_aliases_wf : TContext.AliasesWF Γ) :
    HasType C Γ e (.forAll [] mty_out) :=
  HasType.talias Γ e mty_in mty_out
    (resolveAliases_aliasEquiv mty_in Env mty_out Env' h_ra h_aliases h_aliases_wf) h_ty

/-! ### Support lemmas for `resolve_HasType`

Freshness/alias-preservation helpers threaded into `inferFVar_HasType` and the
`resolveAux_HasType` induction core. -/


/-! ### Substitution-composition lemma for `inferFVar_HasType`

`inferFVar`/`instantiate`/`openFull` all produce the SAME
`subst (ofScopes [zip ids (map ftvar fts)])`, so
composing the outer engine store `S` over the inner instantiation substitution
is a pure `subst ∘ subst` fact.

NB: `LMonoTy.freeVars` is NOT deduplicated, so a list `subst [zip …]`
(`List.find?`, first-match) and this `subst (ofScopes […])` (`ofList`,
last-write-wins) genuinely disagree on a duplicated free var — hence the
composition stays entirely in `find?` terms and is proved via
`LMonoTy.subst_ext` (agreement on free vars through `find?`), never by
converting to the list representation. -/

/-- `find?` in the single empty scope always misses. -/
private theorem find?_ofScopes_nilScope (x : TyIdentifier) :
    HMaps.find? (Strata.Util.HMaps.ofScopes ([[]] : List (List (TyIdentifier × LMonoTy)))) x = none := by
  simp only [Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil, HMaps.find?_single_scope]
  cases h : HMap.find? (HMap.ofList ([] : List (TyIdentifier × LMonoTy))) x with
  | none => rfl
  | some v => exact absurd (HMap.mem_keys_ofList _ x (HMap.find?_mem_keys _ h)) (by simp)

/-- `subst` over a single empty scope is the identity. -/
private theorem subst_ofScopes_nilScope (mty : LMonoTy) :
    LMonoTy.subst (Strata.Util.HMaps.ofScopes ([[]] : List (List (TyIdentifier × LMonoTy)))) mty = mty := by
  induction mty with
  | ftvar x => rw [LMonoTy.subst_unfold]; simp only [find?_ofScopes_nilScope]
  | bitvec n => rw [LMonoTy.subst_bitvec]
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map]
    congr 1
    rw [List.map_congr_left ih]; exact List.map_id_fun' ▸ rfl

/-- Value-mapping the single instantiation scope through `subst S` commutes with
    `find?`: the specialisation of `find?_mapValues` for the concrete
    `ofScopes [zip ids (map ftvar fts)]` store used by `instantiate`. -/
private theorem find?_instScope_mapValues (S : Subst)
    (ids freshtvs : List TyIdentifier) (v : TyIdentifier) :
    HMaps.find? (Strata.Util.HMaps.ofScopes
        [List.zip ids (List.map (fun w => LMonoTy.subst S (.ftvar w)) freshtvs)]) v =
      (HMaps.find? (Strata.Util.HMaps.ofScopes
        [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) v).map (LMonoTy.subst S) := by
  simp only [Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil]
  rw [HMaps.find?_single_scope, HMaps.find?_single_scope]
  have h_zip : List.zip ids (List.map (fun w => LMonoTy.subst S (.ftvar w)) freshtvs) =
      (List.zip ids (List.map LMonoTy.ftvar freshtvs)).map
        (fun p => (p.1, LMonoTy.subst S p.2)) := by
    have h_comp : (List.map (fun w => LMonoTy.subst S (.ftvar w)) freshtvs) =
        List.map (LMonoTy.subst S) (List.map LMonoTy.ftvar freshtvs) := by
      rw [List.map_map]; rfl
    rw [h_comp, List.zip_map_right]
    rfl
  rw [h_zip]
  exact HMap.find?_ofList_map_snd _ (LMonoTy.subst S) v

/-- The core composition: applying `S` after the inner instantiation
    store equals applying the store whose values are pre-mapped through
    `subst S`, provided every free var of `mty` outside the instantiation `ids`
    is not a key of `S` (so `S` cannot touch anything the inner store leaves
    alone). Proved via `subst_ext` on `find?`-agreement — no list `subst`. -/
private theorem subst_compose_instScope (S : Subst)
    (ids freshtvs : List TyIdentifier)
    (h_len : ids.length = freshtvs.length) (mty : LMonoTy)
    (h_extra : ∀ v, v ∈ LMonoTy.freeVars mty → v ∉ ids → v ∉ HMaps.keys S) :
    LMonoTy.subst S (LMonoTy.subst (Strata.Util.HMaps.ofScopes
        [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) mty) =
    LMonoTy.subst (Strata.Util.HMaps.ofScopes
        [List.zip ids (List.map (fun v => LMonoTy.subst S (.ftvar v)) freshtvs)]) mty := by
  induction mty with
  | ftvar x =>
    -- find? in the inner store: either some value, or none (x not a key).
    cases h_find : HMaps.find? (Strata.Util.HMaps.ofScopes
        [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) x with
    | some val =>
      -- Inner store maps x ↦ val; the pre-mapped store maps x ↦ subst S val.
      rw [LMonoTy.subst_ftvar_eq _ x val h_find,
          LMonoTy.subst_ftvar_eq _ x (LMonoTy.subst S val)
            (by rw [find?_instScope_mapValues, h_find]; rfl)]
    | none =>
      -- x is not a key of the inner store, so it is not in `ids`; hence not a key
      -- of S (by h_extra), so both sides leave `ftvar x` unchanged.
      have h_inner : LMonoTy.subst (Strata.Util.HMaps.ofScopes
          [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) (.ftvar x) = .ftvar x := by
        rw [LMonoTy.subst_unfold]; simp only [h_find]
      have h_mapped : HMaps.find? (Strata.Util.HMaps.ofScopes
          [List.zip ids (List.map (fun v => LMonoTy.subst S (.ftvar v)) freshtvs)]) x = none := by
        rw [find?_instScope_mapValues, h_find]; rfl
      rw [h_inner]
      have h_rhs : LMonoTy.subst (Strata.Util.HMaps.ofScopes
          [List.zip ids (List.map (fun v => LMonoTy.subst S (.ftvar v)) freshtvs)]) (.ftvar x)
          = .ftvar x := by
        rw [LMonoTy.subst_unfold]; simp only [h_mapped]
      rw [h_rhs]
      -- x not a key of inner store ⇒ x ∉ ids.
      have h_x_not_id : x ∉ ids := by
        intro h_id
        have h_key : x ∈ (List.zip ids (List.map LMonoTy.ftvar freshtvs)).map Prod.fst := by
          rw [List.map_fst_zip (by simp [h_len])]; exact h_id
        obtain ⟨w, hw⟩ := HMap.find?_ofList_of_mem_keys _ x h_key
        rw [show HMaps.find? (Strata.Util.HMaps.ofScopes
          [List.zip ids (List.map LMonoTy.ftvar freshtvs)]) x =
            HMap.find? (HMap.ofList (List.zip ids (List.map LMonoTy.ftvar freshtvs))) x from by
          simp only [Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil,
            HMaps.find?_single_scope]] at h_find
        rw [hw] at h_find; exact absurd h_find (by simp)
      have h_x_not_key : x ∉ HMaps.keys S :=
        h_extra x (by simp [LMonoTy.freeVars]) h_x_not_id
      exact LMonoTy.subst_no_relevant_keys S (.ftvar x)
        (fun w hw => by simp only [LMonoTy.freeVars, List.mem_singleton] at hw; subst hw; exact h_x_not_key)
  | bitvec n => rw [LMonoTy.subst_bitvec, LMonoTy.subst_bitvec, LMonoTy.subst_bitvec]
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons, LMonoTy.subst_tcons,
        LMonoTys.subst_eq_map, LMonoTys.subst_eq_map, LMonoTys.subst_eq_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact ih a ha (fun v hv hni => h_extra v (by
      simp only [LMonoTy.freeVars]; exact LMonoTys.freeVars_mem_subset ha hv) hni)

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
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
  elim_err h  -- context lookup failed
  rename_i ty h_find
  elim_err h  -- instantiateWithCheck failed
  rename_i v1 h_inst
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
      elim_err h_inst
      rename_i v_ra h_ra; obtain ⟨mty_ra, Env_ra⟩ := v_ra; dsimp at h_inst h_ra
      elim_errs h_inst
      simp at h_inst
      obtain ⟨h_mty, h_env⟩ := h_inst; subst h_mty; subst h_env
      -- Decompose resolveAliases to get instantiate + resolveAliases
      simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
      elim_err h_ra
      rename_i v_inst h_lty_inst; obtain ⟨mty_inst, genEnv'⟩ := v_inst
      simp at h_ra h_lty_inst
      have h_find_S := TContext_types_subst_find
        Env.context.types S x ty h_find
      have h_tvar_S := HasType.tvar (C := C) (TContext.subst Env.context S) m x
        (LTy.subst S ty) h_find_S
      have h_nodup := h_bvnd x ty h_find
      have h_bv_fresh_ty := h_bvf x ty h_find
      have ⟨mty', h_inst_S⟩ := LTy_subst_instantiate S ty
        Env.genEnv mty_inst genEnv' h_lty_inst
      have h_bv_eq := LTy_subst_boundVars S ty
      have h_nodup_S : (LTy.subst S ty).boundVars.Nodup := h_bv_eq ▸ h_nodup
      have h_bv_fresh_S : ∀ v, v ∈ (LTy.subst S ty).boundVars →
          ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
        rw [h_bv_eq]; exact h_bv_fresh_ty
      have h_mono_S := HasType_LTy_instantiate C (TContext.subst Env.context S)
        (.fvar m x none) (LTy.subst S ty) mty'
        Env.genEnv genEnv' h_tvar_S h_inst_S h_nodup_S h_bv_fresh_S
      have h_ctx_inst := LTy.instantiate_context ty Env.genEnv mty_inst genEnv' h_lty_inst
      have h_aliases_subst : (TContext.subst Env.context S).aliases = Env.context.aliases :=
        TContext.subst_aliases Env.context S
      have h_aw_subst : TContext.AliasesWF (TContext.subst Env.context S) := by
        rw [TContext.AliasesWF]; rw [h_aliases_subst]; exact h_aw
      have h_aliases_env : Env.context.aliases =
          ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context.aliases := by
        simp [TEnv.context]; rw [h_ctx_inst]
      have h_ae := resolveAliases_aliasEquiv (Γ := Env.context) mty_inst
        ({Env with genEnv := genEnv'} : TEnv T.IDMeta) mty_ra Env_ra h_ra
        h_aliases_env h_aw
      have h_ae_S := AliasEquiv_subst Env.context.aliases mty_inst mty_ra S h_ae
        (fun a ha => h_aw a ha)
      cases ty with
      | forAll xs body =>
      cases xs with
      | nil =>
        simp [LTy.instantiate] at h_lty_inst
        obtain ⟨h1, _⟩ := h_lty_inst; subst h1
        simp [LTy.subst, LTy.subst.go, LTy.instantiate] at h_inst_S
        obtain ⟨h2, _⟩ := h_inst_S; subst h2
        exact HasType.talias (TContext.subst Env.context S) _ _ _
          (h_aliases_subst ▸ h_ae_S) h_mono_S
      | cons x_bv rest =>
        have h_go_irrel := polyKeysFresh_go_body_irrel S Env.context
          x (x_bv :: rest) body h_fresh_ctx h_find (List.cons_ne_nil _ _)
        have h_subst_ty_eq : LTy.subst S (.forAll (x_bv :: rest) body) =
            .forAll (x_bv :: rest) body := by
          simp [LTy.subst, h_go_irrel]
        rw [h_subst_ty_eq] at h_tvar_S
        have h_mono := HasType_LTy_instantiate C (TContext.subst Env.context S)
          (.fvar m x none) (.forAll (x_bv :: rest) body) mty_inst
          Env.genEnv genEnv' h_tvar_S h_lty_inst h_nodup h_bv_fresh_ty
        have h_aliases_S_eq : (TContext.subst Env.context S).aliases =
            ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context.aliases := by
          rw [h_aliases_subst]; simp [TEnv.context]; rw [h_ctx_inst]
        have h_typed := HasType_resolveAliases C (TContext.subst Env.context S)
          (.fvar m x none) mty_inst mty_ra
          {Env with genEnv := genEnv'} Env_ra h_mono h_ra h_aliases_S_eq h_aw_subst
        exact HasType_subst_fresh_all C (TContext.subst Env.context S)
          (.fvar m x none) mty_ra S h_typed
          (fun a ha_key _ => TContext.isFresh_subst_of_key Env.context S a ha_key h_wf_S)
          h_wf_S
  · -- Case fty = some fty_val
    rename_i fty_val
    elim_err h  -- LMonoTy.instantiateWithCheck failed
    rename_i v2 h_inst2
    obtain ⟨fty_inst, Env2⟩ := v2
    simp at h h_inst2
    elim_err h  -- unify failed (via mapError)
    rename_i S_info h_unify_raw
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
      elim_err h_inst
      rename_i v_ra h_ra; obtain ⟨mty_ra, Env_ra⟩ := v_ra; dsimp at h_inst h_ra
      elim_errs h_inst
      simp at h_inst
      obtain ⟨h_mty_eq, h_env_eq⟩ := h_inst; subst h_mty_eq; subst h_env_eq
      -- Decompose resolveAliases into instantiate + LMonoTy.resolveAliases
      simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
      elim_err h_ra
      rename_i v_inst h_lty_inst; obtain ⟨mty_inst, genEnv'⟩ := v_inst
      simp at h_ra h_lty_inst
      -- Context chain
      have h_ctx_inst := LTy.instantiate_context ty Env.genEnv mty_inst genEnv' h_lty_inst
      have h_ra_ctx : ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context = Env.context := by
        simp [TEnv.context]; exact h_ctx_inst
      have h_env_ra_ctx : Env_ra.context = Env.context := by
        rw [LMonoTy.resolveAliases_context _ _ _ _ h_ra]; exact h_ra_ctx
      have h_aliases_eq : Env.context.aliases =
          ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context.aliases := by
        simp [TEnv.context]; rw [h_ctx_inst]
      -- AliasEquiv from resolveAliases: mty_inst ~ mty_ra
      have h_ae := resolveAliases_aliasEquiv (Γ := Env.context) mty_inst
        {Env with genEnv := genEnv'} mty_ra Env_ra h_ra h_aliases_eq h_aw
      -- Under S: subst S mty_inst ~ subst S mty_ra
      have h_ae_S := AliasEquiv_subst Env.context.aliases mty_inst mty_ra S h_ae
        (fun a ha => h_aw a ha)
      -- AnnotCompat: decompose h_inst2 to get substitution structure.
      have ⟨mty_fty_ie, Env_fty_ie, Env_fty_ra, h_fty_ie, h_fty_ra⟩ :=
        LMonoTy.instantiateWithCheck_decompose fty_val C Env_ra fty_inst Env2 h_inst2
      have ⟨freshtvs_fty, _, h_gen_fty, h_fty_result, _⟩ :=
        instantiateEnv_decompose _ _ _ _ _ h_fty_ie
      -- `instantiateEnv` produces `subst (ofScopes [zip fv (map ftvar fts)]) fty_val`.
      have h_fty_eq : mty_fty_ie = LMonoTy.subst (Strata.Util.HMaps.ofScopes
          [List.zip (LMonoTy.freeVars fty_val) (List.map LMonoTy.ftvar freshtvs_fty)]) fty_val := by
        have h := h_fty_result
        rw [LMonoTys.subst_eq_map] at h
        simpa using h
      -- AliasEquiv from resolveAliases on annotation
      have h_fty_ie_ctx := LMonoTys.instantiateEnv_context _ _ Env_ra _ _ h_fty_ie
      have h_ae_fty : AliasEquiv Env.context.aliases
          (LMonoTy.subst (Strata.Util.HMaps.ofScopes
            [List.zip (LMonoTy.freeVars fty_val) (List.map LMonoTy.ftvar freshtvs_fty)]) fty_val)
          fty_inst := by
        have h_ctx_chain : Env_fty_ie.context.aliases = Env.context.aliases := by
          rw [h_fty_ie_ctx, h_env_ra_ctx]
        rw [← h_fty_eq]
        exact h_ctx_chain ▸ resolveAliases_aliasEquiv (Γ := Env_fty_ie.context) mty_fty_ie Env_fty_ie
          fty_inst Env_fty_ra h_fty_ra rfl (by rw [h_fty_ie_ctx, h_env_ra_ctx]; exact h_aw)
      -- Apply S to annotation AliasEquiv
      have h_ae_fty_S := AliasEquiv_subst Env.context.aliases _ _ S h_ae_fty
        (fun a ha => h_aw a ha)
      -- Unification + absorption: subst S fty_inst = subst S mty_ra
      have h_eq_abs : LMonoTy.subst S fty_inst = LMonoTy.subst S mty_ra := by
        have h_eq := unify_makes_equal fty_inst mty_ra Env2.stateSubstInfo S_info h_unify
        have h_congr := congrArg (LMonoTy.subst S) h_eq
        rw [LMonoTy.subst_absorbs S S_info.subst fty_inst h_abs_S,
            LMonoTy.subst_absorbs S S_info.subst mty_ra h_abs_S] at h_congr
        exact h_congr
      rw [h_eq_abs] at h_ae_fty_S
      -- Compose substitutions: subst S ∘ inner-store = value-mapped store.
      have h_fty_len : (LMonoTy.freeVars fty_val).length = freshtvs_fty.length :=
        (TGenEnv.genTyVars_length _ _ _ _ h_gen_fty).symm
      rw [subst_compose_instScope S _ freshtvs_fty h_fty_len fty_val
          (fun v hv hni => absurd hv hni)] at h_ae_fty_S
      -- Bridge to subst S mty_inst via symm of h_ae_S
      have h_ae_fty_mty : AliasEquiv Env.context.aliases
          (LMonoTy.subst (Strata.Util.HMaps.ofScopes
            [List.zip (LMonoTy.freeVars fty_val)
              (List.map (fun v => LMonoTy.subst S (.ftvar v)) freshtvs_fty)]) fty_val)
          (LMonoTy.subst S mty_inst) :=
        .trans h_ae_fty_S (AliasEquiv.symm h_ae_S)
      -- Build the AnnotCompat witness: the single scope IS the SubstOne.
      have h_annot : AnnotCompat Env.context.aliases fty_val (LMonoTy.subst S mty_inst) := by
        refine ⟨HMap.ofList (List.zip (LMonoTy.freeVars fty_val)
          (List.map (fun v => LMonoTy.subst S (.ftvar v)) freshtvs_fty)), ?_⟩
        show AliasEquiv Env.context.aliases (LMonoTy.subst (Strata.Util.HMaps.ofScopes
          [List.zip (LMonoTy.freeVars fty_val)
            (List.map (fun v => LMonoTy.subst S (.ftvar v)) freshtvs_fty)]) fty_val) _
        exact h_ae_fty_mty
      -- Case split on ty's bound vars for openFull construction
      have h_aliases_subst : (TContext.subst Env.context S).aliases = Env.context.aliases :=
        TContext.subst_aliases Env.context S
      have h_find_S := TContext_types_subst_find
        Env.context.types S x ty h_find
      cases ty with
      | forAll vars body =>
      simp [LTy.boundVars] at h_bvnd h_bvf
      cases vars with
      | nil =>
        -- Monomorphic case: mty_inst = body
        simp [LTy.instantiate] at h_lty_inst
        obtain ⟨h_eq_inst, _⟩ := h_lty_inst; subst h_eq_inst
        have h_open : LTy.openFull (LTy.subst S (.forAll [] body)) [] =
            LMonoTy.subst S body := by
          have h_bv : (LTy.subst S (.forAll [] body)).boundVars = [] := by
            rw [LTy_subst_boundVars]; simp [LTy.boundVars]
          have h_tm : (LTy.subst S (.forAll [] body)).toMonoTypeUnsafe = LMonoTy.subst S body := by
            simp [LTy.subst, LTy.subst.go, LTy.toMonoTypeUnsafe]
          rw [LTy.openFull, h_bv, h_tm]
          -- ofScopes [zip [] []] = [empty]; subst over the empty scope is identity.
          simp only [List.zip, List.zipWith]
          exact subst_ofScopes_nilScope (LMonoTy.subst S body)
        have h_bv_subst : (LTy.subst S (.forAll [] body)).boundVars = [] := by
          rw [LTy_subst_boundVars]; simp [LTy.boundVars]
        rw [← h_aliases_subst] at h_annot h_ae_S
        exact HasType.talias (TContext.subst Env.context S) _ _ _ h_ae_S
          (HasType.tvar_annotated (C := C) (TContext.subst Env.context S) m x
            (LTy.subst S (.forAll [] body)) (LMonoTy.subst S body) [] fty_val
            h_find_S (by simp [h_bv_subst]) h_open h_annot)
      | cons x' xs' =>
        -- Polymorphic case
        simp only [LTy.instantiate, Bind.bind, Except.bind] at h_lty_inst
        elim_err h_lty_inst
        rename_i v_gen h_gen'; obtain ⟨ftvs, gE⟩ := v_gen
        simp at h_lty_inst h_gen'
        obtain ⟨h_eq_inst, _⟩ := h_lty_inst; subst h_eq_inst
        have h_len := TGenEnv.genTyVars_length _ _ _ _ h_gen'
        have h_go_irrel := polyKeysFresh_go_body_irrel S Env.context
          x (x' :: xs') body h_fresh_ctx h_find (List.cons_ne_nil _ _)
        have h_subst_ty : LTy.subst S (.forAll (x' :: xs') body) =
            .forAll (x' :: xs') body := by
          simp [LTy.subst, h_go_irrel]
        have h_extra : ∀ v, v ∈ LMonoTy.freeVars body → v ∉ (x' :: xs') →
            v ∉ HMaps.keys S := by
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
        -- H composition: subst S ∘ (inner instantiation store) = value-mapped store.
        have h_compose := subst_compose_instScope S (x' :: xs') ftvs
          h_len.symm body h_extra
        -- `mty_inst = subst (ofScopes [zip (x'::xs') (map ftvar ftvs)]) body`.
        have h_open : LTy.openFull (LTy.subst S (.forAll (x' :: xs') body))
            (List.map (fun tv => LMonoTy.subst S (.ftvar tv)) ftvs) =
            LMonoTy.subst S (LMonoTy.subst (Strata.Util.HMaps.ofScopes
              [List.zip (x' :: xs') (List.map LMonoTy.ftvar ftvs)]) body) := by
          rw [h_subst_ty]
          simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe]
          rw [h_compose]
        have h_bv_subst : (LTy.subst S (.forAll (x' :: xs') body)).boundVars =
            x' :: xs' := by
          rw [LTy_subst_boundVars]; simp [LTy.boundVars]
        rw [← h_aliases_subst] at h_annot h_ae_S
        exact HasType.talias (TContext.subst Env.context S) _ _ _ h_ae_S
          (HasType.tvar_annotated (C := C) (TContext.subst Env.context S) m x
            (LTy.subst S (.forAll (x' :: xs') body))
            (LMonoTy.subst S (LMonoTy.subst (Strata.Util.HMaps.ofScopes
              [List.zip (x' :: xs') (List.map LMonoTy.ftvar ftvs)]) body))
            (List.map (fun tv => LMonoTy.subst S (.ftvar tv)) ftvs) fty_val h_find_S
            (by simp [h_bv_subst]; exact h_len)
            h_open h_annot)

/-! ### `WellScoped` and its propagation through `varOpen` / `typeBoundVar` -/

/-- An expression is well-scoped w.r.t. a context: all its free variable
    identifiers appear in the context's `knownVars`.
    This is the standard precondition for type-checking: every free variable
    reference must be bound in the context.
    Propagates through `varOpen`: if `WellScoped e Γ`, then
    `WellScoped (varOpen 0 (xv, some xty) e) (extend Γ xv)`. -/
@[expose] def WellScoped (e : LExpr T.mono) (Γ : TContext T.IDMeta) : Prop :=
  ∀ x ∈ LExpr.freeVars e, x.1 ∈ TContext.knownVars Γ

omit [ToString T.IDMeta] [DecidableEq T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat T.IDMeta]
  [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] [Hashable T.IDMeta] in
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

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat T.IDMeta]
  [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
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

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- The bound variable produced by `typeBoundVar` is fresh: it is not among the
    context's known variables. -/
theorem typeBoundVar_xv_not_in_knownVars
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env')) :
    xv ∉ TContext.knownVars Env.context := by
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v_gen h_gen; obtain ⟨xv_raw, Env_g⟩ := v_gen
  have h_fresh := liftGenEnv_genVar_fresh Env xv_raw Env_g h_gen
  revert h; cases bty with
  | some bty_val =>
    simp only []; intro h; elim_err h
    rename_i v_ic _; obtain ⟨_, _⟩ := v_ic
    simp at h; obtain ⟨h_xv, _, _⟩ := h; subst h_xv; exact h_fresh
  | none =>
    simp; intro h; elim_err h
    rename_i v_tg _; obtain ⟨_, _⟩ := v_tg
    simp at h; obtain ⟨h_xv, _, _⟩ := h; subst h_xv; exact h_fresh

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata]  in
/-- A variable fresh for a well-scoped expression's context does not occur in the
    expression's variables. -/
theorem WellScoped_fresh_not_in_getVars
    (e : LExpr T.mono) (Γ : TContext T.IDMeta) (xv : T.Identifier)
    (h_ws : WellScoped e Γ) (h_fresh : xv ∉ TContext.knownVars Γ) :
    xv ∉ LExpr.getVars e := by
  intro h_mem
  have h_eq := freeVars_map_fst_eq_getVars e
  rw [← h_eq] at h_mem
  simp only [List.mem_map] at h_mem
  obtain ⟨⟨xv', ty'⟩, h_in, h_fst⟩ := h_mem
  simp at h_fst; subst h_fst
  exact h_fresh (h_ws ⟨xv', ty'⟩ h_in)

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `typeBoundVar` only extends `knownVars`. Since `knownVars = types.keys`,
    membership is `find?`-preservation via `typeBoundVar_preserves_find`. -/
private theorem typeBoundVar_knownVars_mono
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env'))
    (v : T.Identifier) (hv : v ∈ TContext.knownVars Env.context) :
    v ∈ TContext.knownVars Env'.context := by
  simp only [TContext.knownVars] at hv ⊢
  obtain ⟨vty, h_find⟩ := (HMaps.mem_keys_iff_find? Env.context.types v).mp hv
  by_cases h_eq : v = xv
  · subst h_eq
    exact HMaps.find?_mem_keys Env'.context.types
      (typeBoundVar_adds_to_context C Env bty v xty Env' h)
  · exact HMaps.find?_mem_keys Env'.context.types
      (typeBoundVar_preserves_find C Env bty xv xty Env' h v vty h_eq h_find)

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `typeBoundVar` makes `xv` a member of `knownVars`. -/
private theorem typeBoundVar_xv_in_knownVars
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env')) :
    xv ∈ TContext.knownVars Env'.context :=
  HMaps.find?_mem_keys Env'.context.types
    (typeBoundVar_adds_to_context C Env bty xv xty Env' h)

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- WellScoped for varOpen after typeBoundVar: combines `WellScoped_varOpen`
    with `typeBoundVar_knownVars_mono` and `typeBoundVar_xv_in_knownVars`. -/
private theorem WellScoped_varOpen_typeBoundVar
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
    (body : LExpr T.mono)
    (h_tbv : typeBoundVar C Env bty = .ok (xv, xty, Env1))
    (h_ws_body : WellScoped body Env.context) :
    WellScoped (LExpr.varOpen 0 (xv, some xty) body) Env1.context :=
  WellScoped_varOpen body Env.context Env1.context xv xty h_ws_body
    (typeBoundVar_knownVars_mono C Env bty xv xty Env1 h_tbv)
    (typeBoundVar_xv_in_knownVars C Env bty xv xty Env1 h_tbv)



/-! ### `resolveAux_HasType` — the induction core (`resolve_HasType` chain) -/

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat T.IDMeta] [Hashable T.IDMeta]
  [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `varCloseT` preserves `toLMonoTy` (representation-independent; only changes
    fvars to bvars without affecting the root metadata). -/
theorem varCloseT_toLMonoTy (k : Nat) (x : T.Identifier) (e : LExprT T.mono) :
    (LExpr.varCloseT k x e).toLMonoTy = e.toLMonoTy := by
  cases e with
  | const _ _ => rfl
  | bvar _ _ => rfl
  | fvar _ y _ => simp [LExpr.varCloseT]; split <;> simp [toLMonoTy]
  | op _ _ _ => rfl
  | app _ _ _ => rfl
  | abs _ _ _ _ => rfl
  | quant _ _ _ _ _ _ => rfl
  | ite _ _ _ _ => rfl
  | eq _ _ _ => rfl

omit [ToString T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta]
  [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `WellScoped` transports across context equivalence (reads `Γ` only through
    `knownVars = types.keys`, which `Equiv` preserves). -/
private theorem WellScoped_Equiv_knownVars {Γ Γ' : TContext T.IDMeta} (h : Γ.Equiv Γ')
    {e : LExpr T.mono} (h_ws : WellScoped e Γ) : WellScoped e Γ' := by
  intro x hx
  have h_mem := h_ws x hx
  simp only [TContext.knownVars] at h_mem ⊢
  obtain ⟨v, hv⟩ := (HMaps.mem_keys_iff_find? Γ.types x.1).mp h_mem
  exact HMaps.find?_mem_keys Γ'.types (by rw [← h.find? x.1]; exact hv)

omit [ToString T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta]
  [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `polyKeysFresh` transports across context equivalence (reads `Γ` only through
    `Γ.types.find?`). -/
private theorem polyKeysFresh_Equiv {Γ Γ' : TContext T.IDMeta} (h : Γ.Equiv Γ')
    {S : Subst} (h_pf : Subst.polyKeysFresh (T := T) S Γ) :
    Subst.polyKeysFresh (T := T) S Γ' := by
  intro a ha x ty h_find h_bv
  exact h_pf a ha x ty (by rw [h.find? x]; exact h_find) h_bv


theorem resolveAux_HasType :
    ∀ (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T)
      (Env Env' : TEnv T.IDMeta),
      resolveAux C Env e = .ok (et, Env') →
      TEnvWF Env →
      Env.context.types ≠ [] →
      FactoryWF C.functions →
      WellScoped e Env.context →
      Env'.context.Equiv Env.context ∧
      ∀ (S : Subst), Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        Subst.polyKeysFresh (T := T) S Env.context →
        HasType C (TContext.subst Env.context S) e
          (.forAll [] (LMonoTy.subst S et.toLMonoTy)) := by
  intro e et C Env Env' h_res h_envwf h_ne h_fwf h_ws
  revert h_ws
  apply resolveAux_ind
    (P := fun e et C Env Env' => WellScoped e Env.context →
      Env'.context.Equiv Env.context ∧
      ∀ (S : Subst), Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        Subst.polyKeysFresh (T := T) S Env.context →
        HasType C (TContext.subst Env.context S) e
          (.forAll [] (LMonoTy.subst S et.toLMonoTy)))
    (e := e) (et := et) (C := C) (Env := Env) (Env' := Env')
    (h_res := h_res) (h_envwf := h_envwf) (h_ne := h_ne) (h_fwf := h_fwf)
  case h_const =>
    intro m c et C Env Env' h h_envwf h_ne h_fwf _
    have h_aw := h_envwf.aliasesWF
    simp [resolveAux, inferConst] at h
    elim_err h
    rename_i h_known
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
  case h_op =>
    intro m o oty et C Env Env' h h_envwf h_ne h_fwf h_ws
    have h_aw := h_envwf.aliasesWF
    -- Decompose resolveAux for .op
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_err h  -- function not found
    rename_i func h_find
    elim_err h  -- func.type error
    rename_i type_val h_type
    elim_err h  -- instantiateWithCheck error
    rename_i v1 h_inst; obtain ⟨ty_inst, Env1⟩ := v1; dsimp at h h_inst
    cases oty with
    | none =>
      simp at h; obtain ⟨h_et, h_env⟩ := h
      constructor
      · -- Context preservation
        rw [← h_env]
        exact TContext.Equiv.of_eq (LTy_instantiateWithCheck_context type_val C Env ty_inst Env1 h_inst)
      · -- Typing under arbitrary absorbing S
        intro S h_abs_S h_wf_S _
        rw [← h_et]; simp [toLMonoTy]
        have h_func_mem : func ∈ C.functions.toArray := Factory.getElem?_is_some_implies_mem h_find
        have h_func_wf : LFuncWF func := h_fwf.lfuncs_wf func h_func_mem
        have h_top := HasType.top (TContext.subst Env.context S) m func o type_val h_find h_type
        have h_ty_closed := LFunc.type_freeVars_eq_nil func type_val h_type h_func_wf
        have h_bv_eq := LFunc.type_boundVars_eq_typeArgs func type_val h_type
        have h_nodup : (LTy.boundVars type_val).Nodup := h_bv_eq ▸ h_func_wf.typeArgs_nodup
        have h_bv_fresh : ∀ v, v ∈ LTy.boundVars type_val →
            ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
          rw [h_bv_eq]; intro v hv _ _ h_eq
          exact h_func_wf.typeArgs_no_gen_prefix v hv
            (h_eq ▸ (by rw [String.toList_append]; exact isPrefixOf_append_self _ _))
        simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h_inst
        elim_err h_inst
        rename_i v_ra h_ra; obtain ⟨mty_ra, Env_ra⟩ := v_ra; dsimp at h_inst h_ra
        elim_errs h_inst
        simp at h_inst; obtain ⟨h_mty, h_env⟩ := h_inst
        subst h_mty; subst h_env
        simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
        elim_err h_ra
        rename_i v_inst h_lty_inst; obtain ⟨mty_inst, genEnv'⟩ := v_inst
        simp at h_ra h_lty_inst
        have h_ctx_inst := LTy.instantiate_context type_val Env.genEnv mty_inst genEnv' h_lty_inst
        have h_mono := HasType_LTy_instantiate C (TContext.subst Env.context S) (.op m o none) type_val mty_inst
          Env.genEnv genEnv' h_top h_lty_inst h_nodup h_bv_fresh
        -- Alias resolution: resolveAliases preserves HasType via talias
        have h_ra_ctx : ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context = Env.context := by
          simp [TEnv.context]; exact h_ctx_inst
        have h_aliases_subst : (TContext.subst Env.context S).aliases = Env.context.aliases :=
          TContext.subst_aliases Env.context S
        have h_aliases_eq : (TContext.subst Env.context S).aliases =
          ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context.aliases := by
          rw [h_aliases_subst]; simp [TEnv.context]; rw [h_ctx_inst]
        have h_aw_subst : TContext.AliasesWF (TContext.subst Env.context S) := by
          rw [TContext.AliasesWF]; rw [h_aliases_subst]; exact h_aw
        have h_typed := HasType_resolveAliases C (TContext.subst Env.context S) (.op m o none) mty_inst mty_ra
          {Env with genEnv := genEnv'} Env_ra h_mono h_ra h_aliases_eq h_aw_subst
        exact HasType_subst_fresh_all C (TContext.subst Env.context S) (.op m o none) mty_ra S h_typed
          (fun a h_key _ => TContext.isFresh_subst_of_key Env.context S a h_key h_wf_S)
          h_wf_S
    | some oty_val =>
      simp only [Except.mapError] at h
      elim_err h
      rename_i v2 h_inst2; obtain ⟨oty_inst, Env2⟩ := v2; dsimp at h h_inst2
      elim_err h
      rename_i v3 h_mapError
      simp at h; obtain ⟨h_et, h_env⟩ := h
      constructor
      · -- Context preservation
        rw [← h_env]; simp [TEnv.updateSubst, TEnv.context]
        have h1 := LTy_instantiateWithCheck_context type_val C Env ty_inst Env1 h_inst
        have h2 := LMonoTy_instantiateWithCheck_context oty_val C Env1 oty_inst Env2 h_inst2
        simp [TEnv.context] at h1 h2
        exact TContext.Equiv.of_eq (by rw [h2, h1])
      · -- Typing under arbitrary absorbing S
        intro S h_abs_S h_wf_S _
        rw [← h_et]; simp [toLMonoTy]
        rw [← h_env] at h_abs_S; simp [TEnv.updateSubst] at h_abs_S
        -- Extract unify hypothesis from mapError wrapper
        have h_unify := unify_of_mapError h_mapError
        -- Closed type facts
        have h_func_mem : func ∈ C.functions.toArray := Factory.getElem?_is_some_implies_mem h_find
        have h_func_wf : LFuncWF func := h_fwf.lfuncs_wf func h_func_mem
        have h_ty_closed := LFunc.type_freeVars_eq_nil func type_val h_type h_func_wf
        have h_bv_eq := LFunc.type_boundVars_eq_typeArgs func type_val h_type
        -- Decompose instantiateWithCheck for type_val
        simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h_inst
        elim_err h_inst
        rename_i v_ra h_ra; obtain ⟨mty_ra, Env_ra⟩ := v_ra; dsimp at h_inst h_ra
        elim_errs h_inst
        simp at h_inst
        obtain ⟨h_mty_eq, h_env_eq⟩ := h_inst; subst h_mty_eq; subst h_env_eq
        -- Decompose resolveAliases into instantiate + LMonoTy.resolveAliases
        simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
        elim_err h_ra
        rename_i v_inst h_lty_inst; obtain ⟨mty_inst, genEnv'⟩ := v_inst
        simp at h_ra h_lty_inst
        -- Context chain
        have h_ctx_inst := LTy.instantiate_context type_val Env.genEnv mty_inst genEnv' h_lty_inst
        have h_ra_ctx : ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context = Env.context := by
          simp [TEnv.context]; exact h_ctx_inst
        have h_aliases_eq : Env.context.aliases =
            ({Env with genEnv := genEnv'} : TEnv T.IDMeta).context.aliases := by
          simp [TEnv.context]; rw [h_ctx_inst]
        -- AliasEquiv from resolveAliases: mty_inst ~ mty_ra
        have h_ae := resolveAliases_aliasEquiv (Γ := Env.context) mty_inst {Env with genEnv := genEnv'}
          mty_ra Env_ra h_ra h_aliases_eq h_aw
        -- Under S: subst S mty_inst ~ subst S mty_ra
        have h_ae_S := AliasEquiv_subst Env.context.aliases mty_inst mty_ra S h_ae
          (fun a ha => h_aw a ha)
        have h_env_ra_ctx : Env_ra.context = Env.context := by
          rw [LMonoTy.resolveAliases_context _ _ _ _ h_ra]; exact h_ra_ctx
        -- AnnotCompat: decompose h_inst2 to get substitution structure
        have ⟨mty_fty_ie, Env_fty_ie, Env_fty_ra, h_fty_ie, h_fty_ra⟩ :=
          LMonoTy.instantiateWithCheck_decompose oty_val C Env_ra oty_inst Env2 h_inst2
        have ⟨freshtvs_fty, _, h_gen_fty, h_fty_result, _⟩ :=
          instantiateEnv_decompose _ _ _ _ _ h_fty_ie
        have h_fty_eq : mty_fty_ie = LMonoTy.subst (Strata.Util.HMaps.ofScopes
            [List.zip (LMonoTy.freeVars oty_val) (List.map LMonoTy.ftvar freshtvs_fty)]) oty_val := by
          have h := h_fty_result
          rw [LMonoTys.subst_eq_map] at h
          simpa using h
        have h_fty_ie_ctx := LMonoTys.instantiateEnv_context _ _ Env_ra _ _ h_fty_ie
        have h_ae_fty : AliasEquiv Env.context.aliases
            (LMonoTy.subst (Strata.Util.HMaps.ofScopes
              [List.zip (LMonoTy.freeVars oty_val) (List.map LMonoTy.ftvar freshtvs_fty)]) oty_val)
            oty_inst := by
          have h_ctx_chain : Env_fty_ie.context.aliases = Env.context.aliases := by
            rw [h_fty_ie_ctx, h_env_ra_ctx]
          rw [← h_fty_eq]
          exact h_ctx_chain ▸ resolveAliases_aliasEquiv (Γ := Env_fty_ie.context) mty_fty_ie Env_fty_ie oty_inst Env_fty_ra
            h_fty_ra rfl (by rw [h_fty_ie_ctx, h_env_ra_ctx]; exact h_aw)
        have h_ae_fty_S := AliasEquiv_subst Env.context.aliases _ _ S h_ae_fty
          (fun a ha => h_aw a ha)
        -- Unification + absorption: subst S oty_inst = subst S mty_ra
        have h_eq_abs : LMonoTy.subst S oty_inst = LMonoTy.subst S mty_ra := by
          have h_eq := unify_makes_equal mty_ra oty_inst Env2.stateSubstInfo v3 h_unify
          have h_congr := congrArg (LMonoTy.subst S) h_eq
          rw [LMonoTy.subst_absorbs S v3.subst mty_ra h_abs_S,
              LMonoTy.subst_absorbs S v3.subst oty_inst h_abs_S] at h_congr
          exact h_congr.symm
        rw [h_eq_abs] at h_ae_fty_S
        have h_fty_len : (LMonoTy.freeVars oty_val).length = freshtvs_fty.length :=
          (TGenEnv.genTyVars_length _ _ _ _ h_gen_fty).symm
        rw [subst_compose_instScope S _ freshtvs_fty h_fty_len oty_val
            (fun v hv hni => absurd hv hni)] at h_ae_fty_S
        have h_ae_fty_mty : AliasEquiv Env.context.aliases
            (LMonoTy.subst (Strata.Util.HMaps.ofScopes
              [List.zip (LMonoTy.freeVars oty_val)
                (List.map (fun v => LMonoTy.subst S (.ftvar v)) freshtvs_fty)]) oty_val)
            (LMonoTy.subst S mty_inst) :=
          .trans h_ae_fty_S (AliasEquiv.symm h_ae_S)
        -- Build the AnnotCompat witness: the single scope IS the SubstOne.
        have h_annot : AnnotCompat Env.context.aliases oty_val (LMonoTy.subst S mty_inst) := by
          refine ⟨HMap.ofList (List.zip (LMonoTy.freeVars oty_val)
            (List.map (fun v => LMonoTy.subst S (.ftvar v)) freshtvs_fty)), ?_⟩
          show AliasEquiv Env.context.aliases (LMonoTy.subst (Strata.Util.HMaps.ofScopes
            [List.zip (LMonoTy.freeVars oty_val)
              (List.map (fun v => LMonoTy.subst S (.ftvar v)) freshtvs_fty)]) oty_val) _
          exact h_ae_fty_mty
        -- Case split on type_val's bound vars for openFull construction
        cases type_val with
        | forAll vars body =>
        simp [LTy.freeVars] at h_ty_closed
        cases vars with
        | nil =>
          -- Monomorphic case: mty_inst = body
          simp [LTy.instantiate] at h_lty_inst
          obtain ⟨h_eq_inst, _⟩ := h_lty_inst; subst h_eq_inst
          have h_body_fv_nil : LMonoTy.freeVars body = [] := by
            simp only [List.removeAll, List.filter_eq_nil_iff] at h_ty_closed
            match h_fv : LMonoTy.freeVars body with
            | [] => rfl
            | a :: _ => exfalso; have h_a := h_ty_closed a (by simp [h_fv])
                        simp at h_a
          have h_subst_body : LMonoTy.subst S body = body :=
            LMonoTy.subst_no_relevant_keys S body
              (fun x hx => by simp [h_body_fv_nil] at hx)
          rw [h_subst_body] at h_annot h_ae_S
          have h_open : LTy.openFull (.forAll [] body) [] = body := by
            simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe, List.zip_nil_left]
            exact subst_ofScopes_nilScope body
          have h_aliases_subst : (TContext.subst Env.context S).aliases = Env.context.aliases :=
            TContext.subst_aliases Env.context S
          rw [← h_aliases_subst] at h_annot h_ae_S
          exact HasType.talias (TContext.subst Env.context S) _ _ _ h_ae_S
            (HasType.top_annotated (TContext.subst Env.context S) m func o (.forAll [] body) body [] oty_val
              h_find h_type (by simp [LTy.boundVars]) h_open h_annot)
        | cons x' xs' =>
          -- Polymorphic case
          simp only [LTy.instantiate, Bind.bind, Except.bind] at h_lty_inst
          elim_err h_lty_inst
          rename_i v_gen h_gen'; obtain ⟨ftvs, gE⟩ := v_gen
          simp at h_lty_inst h_gen'
          obtain ⟨h_eq_inst, _⟩ := h_lty_inst; subst h_eq_inst
          have h_body_cl : ∀ tv, tv ∈ LMonoTy.freeVars body → tv ∈ (x' :: xs') := by
            intro tv htv
            simp only [List.removeAll, List.filter_eq_nil_iff] at h_ty_closed
            have h_tv := h_ty_closed tv htv
            simp only [List.elem_eq_mem, Bool.not_eq_true', decide_eq_false_iff_not,
                        Decidable.not_not] at h_tv
            exact h_tv
          have h_len := TGenEnv.genTyVars_length _ _ _ _ h_gen'
          -- H composition: subst S ∘ (inner store) = value-mapped store (all fv ∈ bound vars).
          have h_compose := subst_compose_instScope S (x' :: xs') ftvs h_len.symm body
            (fun v hv hni => absurd (h_body_cl v hv) hni)
          rw [h_compose] at h_annot h_ae_S
          -- openFull produces exactly that value-mapped store applied to `body`.
          have h_open : LTy.openFull (.forAll (x' :: xs') body)
              (List.map (fun tv => LMonoTy.subst S (.ftvar tv)) ftvs) =
              LMonoTy.subst (Strata.Util.HMaps.ofScopes [List.zip (x' :: xs')
                (List.map (fun v => LMonoTy.subst S (.ftvar v)) ftvs)]) body := by
            simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe]
          rw [← h_open] at h_annot h_ae_S
          have h_aliases_subst : (TContext.subst Env.context S).aliases = Env.context.aliases :=
            TContext.subst_aliases Env.context S
          rw [← h_aliases_subst] at h_annot h_ae_S
          exact HasType.talias (TContext.subst Env.context S) _ _ _ h_ae_S
            (HasType.top_annotated (TContext.subst Env.context S) m func o (.forAll (x' :: xs') body)
              (LTy.openFull (.forAll (x' :: xs') body) (List.map (fun tv => LMonoTy.subst S (.ftvar tv)) ftvs))
              (List.map (fun tv => LMonoTy.subst S (.ftvar tv)) ftvs) oty_val
              h_find h_type (by simp [LTy.boundVars]; exact h_len) rfl h_annot)
  case h_fvar =>
    intro m x fty et C Env Env' h h_envwf h_ne h_fwf _
    have h_aw := h_envwf.aliasesWF
    simp only [resolveAux, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_infer
    obtain ⟨ty_res, Env_res⟩ := v1
    simp at h
    obtain ⟨h_et, h_env'⟩ := h
    rw [← h_et, ← h_env']
    simp [toLMonoTy]
    have ⟨h_ctx_pres, h_base_ty⟩ := inferFVar_HasType C Env x fty ty_res Env_res m
      h_infer h_envwf.boundVarsNodup h_envwf.boundVarsFresh h_envwf.aliasesWF
    constructor
    · exact TContext.Equiv.of_eq h_ctx_pres
    · intro S h_abs_S h_wf_S h_poly_fresh
      exact h_base_ty S h_abs_S h_wf_S h_poly_fresh
  case h_app =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 fresh_name Env_gen substInfo
      h_res h_res1 h_res2 h_genTyVar h_unify h_et h_subeq h_abs_rem_Env1 h_abs_rem_Env2
      h_e1t_no_fresh h_e2t_no_fresh h_unify_eq
      h_envwf h_ne h_fwf h_envwf1 h_ctx1 h_envwf2 h_ctx2 h_ih1 h_ih2 h_ws
    have h_aw := h_envwf.aliasesWF
    subst h_et
    have h_ws1 : WellScoped e1 Env.context :=
      fun x hx => h_ws x (by simp [LExpr.freeVars, List.mem_append]; left; exact hx)
    have ⟨_, h_ty1⟩ := h_ih1 h_ws1
    have h_ws2 : WellScoped e2 Env1.context :=
      WellScoped_Equiv_knownVars h_ctx1.symm
        (fun x hx => h_ws x (by simp [LExpr.freeVars, List.mem_append]; right; exact hx))
    have ⟨_, h_ty2⟩ := h_ih2 h_ws2
    constructor
    · -- Context preservation, from resolveAux_properties on the app-level result
      exact (resolveAux_properties (.app m e1 e2) _ C Env Env' h_res h_ne h_aw h_fwf
        h_envwf.substFreshForGen h_envwf.ctxFreshForGen h_envwf.boundVarsFresh).context
    · -- Typing under arbitrary absorbing S
      intro S h_abs_S h_wf_S h_poly_fresh
      simp [toLMonoTy]
      rw [h_subeq] at h_abs_S
      have h_abs_S_Env1 : Subst.absorbs S Env1.stateSubstInfo.subst :=
        Subst.absorbs_trans Env1.stateSubstInfo.subst (HMaps.remove substInfo.subst fresh_name) S
          h_abs_rem_Env1 h_abs_S
      have h_abs_S_Env2 : Subst.absorbs S Env2.stateSubstInfo.subst :=
        Subst.absorbs_trans Env2.stateSubstInfo.subst (HMaps.remove substInfo.subst fresh_name) S
          h_abs_rem_Env2 h_abs_S
      have h_ty1_S := h_ty1 S h_abs_S_Env1 h_wf_S h_poly_fresh
      have h_ty2_S := HasType_Equiv (h_ty2 S h_abs_S_Env2 h_wf_S
        (polyKeysFresh_Equiv h_ctx1.symm h_poly_fresh)) (TContext.Equiv.subst h_ctx1 S)
      -- subst substInfo x = subst (remove substInfo fresh) x when fresh ∉ freeVars x
      have h_subst_e1t : LMonoTy.subst S (LMonoTy.subst substInfo.subst e1t.toLMonoTy) =
          LMonoTy.subst S e1t.toLMonoTy := by
        rw [← LMonoTy.subst_remove_not_fv substInfo.subst fresh_name e1t.toLMonoTy h_e1t_no_fresh]
        exact LMonoTy.subst_absorbs S (HMaps.remove substInfo.subst fresh_name) e1t.toLMonoTy h_abs_S
      have h_subst_e2t : LMonoTy.subst S (LMonoTy.subst substInfo.subst e2t.toLMonoTy) =
          LMonoTy.subst S e2t.toLMonoTy := by
        rw [← LMonoTy.subst_remove_not_fv substInfo.subst fresh_name e2t.toLMonoTy h_e2t_no_fresh]
        exact LMonoTy.subst_absorbs S (HMaps.remove substInfo.subst fresh_name) e2t.toLMonoTy h_abs_S
      -- Apply subst S to h_unify_eq
      have h_eq_S : LMonoTy.subst S e1t.toLMonoTy =
          LMonoTy.tcons "arrow"
            [LMonoTy.subst S e2t.toLMonoTy,
             LMonoTy.subst S (LMonoTy.subst substInfo.subst (.ftvar fresh_name))] := by
        have h := congrArg (LMonoTy.subst S) h_unify_eq
        rw [h_subst_e1t] at h
        rw [LMonoTy.subst_tcons_pair substInfo.subst "arrow" e2t.toLMonoTy (.ftvar fresh_name)] at h
        rw [LMonoTy.subst_tcons_pair S "arrow" (LMonoTy.subst substInfo.subst e2t.toLMonoTy)
            (LMonoTy.subst substInfo.subst (.ftvar fresh_name))] at h
        rw [h_subst_e2t] at h
        exact h
      rw [h_eq_S] at h_ty1_S
      exact HasType.tapp (TContext.subst Env.context S) m e1 e2
        (.forAll [] (LMonoTy.subst S (LMonoTy.subst substInfo.subst (.ftvar fresh_name))))
        (.forAll [] (LMonoTy.subst S e2t.toLMonoTy))
        (by simp [LTy.isMonoType, LTy.boundVars])
        (by simp [LTy.isMonoType, LTy.boundVars])
        (by simp [LTy.toMonoType]; exact h_ty1_S)
        h_ty2_S
  case h_abs =>
    intro m pn bty e_body et C Env Env' xv xty Env1 et_body Env2
      h_res h_tbv h_res_body h_et h_env' h_envwf h_ne h_fwf h_envwf1 h_ne1 h_aliases_eq h_ih h_ws
    have h_aw := h_envwf.aliasesWF
    have h_per_scope := typeBoundVar_xv_fresh_in_context C Env bty xv xty Env1 h_tbv
    have h_xv_fresh_maps : HMaps.find? Env.context.types xv = none := by
      have h_gen : ∀ (types : HMaps (Identifier T.IDMeta) LTy),
          (∀ mm, mm ∈ types → HMap.find? mm xv = none) → HMaps.find? types xv = none := by
        intro types h_all
        induction types with
        | nil => rfl
        | cons scope rest ih =>
          simp only [HMaps.find?]
          rw [h_all scope (by simp)]
          exact ih (fun mm hmm => h_all mm (by simp [hmm]))
      exact h_gen _ h_per_scope
    have h_xv_not_known : xv ∉ TContext.knownVars Env.context := by
      simp only [TContext.knownVars]
      intro h_kv
      obtain ⟨w, hw⟩ := (HMaps.mem_keys_iff_find? Env.context.types xv).mp h_kv
      rw [h_xv_fresh_maps] at hw; exact absurd hw (by simp)
    have h_ctx_bridge : Env1.context =
        { Env.context with types := Env.context.types.addInNewest (HMap.single xv (.forAll [] xty)) } := by
      have h_types := typeBoundVar_types_addInNewest C Env bty xv xty Env1 h_tbv
      have h_al := typeBoundVar_aliases_eq C Env bty xv xty Env1 h_tbv
      cases hc : Env1.context with
      | mk t1 a1 =>
        rw [hc] at h_types h_al
        simp only [] at h_types h_al
        subst h_types; subst h_al; rfl
    have h_ws_body : WellScoped e_body Env.context :=
      fun x hx => h_ws x (by simp [LExpr.freeVars]; exact hx)
    have h_ws_open := WellScoped_varOpen_typeBoundVar C Env bty xv xty Env1
      e_body h_tbv h_ws_body
    have ⟨h_ctx_body, h_ty_body⟩ := h_ih h_ws_open
    subst h_env'
    constructor
    · -- Context preservation up to Equiv
      exact eraseFromContext_typeBoundVar_equiv C Env bty xv xty Env1 h_tbv Env2 h_ctx_body h_ne
    · -- Typing under arbitrary absorbing S
      intro S h_abs_S h_wf_S h_poly_fresh
      have h_et_ty : et.toLMonoTy = LMonoTy.subst Env2.stateSubstInfo.subst
          (.tcons "arrow" [xty, et_body.toLMonoTy]) := by
        subst h_et
        change (LMonoTy.subst Env2.stateSubstInfo.subst
          (.tcons "arrow" [xty, (LExpr.varCloseT 0 xv et_body).toLMonoTy]))
          = LMonoTy.subst Env2.stateSubstInfo.subst (.tcons "arrow" [xty, et_body.toLMonoTy])
        rw [varCloseT_toLMonoTy]
      rw [h_et_ty]
      have h_abs_Env2 : Subst.absorbs S Env2.stateSubstInfo.subst := by
        simp [TEnv.eraseFromContext, TEnv.updateContext] at h_abs_S
        exact h_abs_S
      have h_poly_fresh_ext : Subst.polyKeysFresh (T := T) S Env1.context :=
        polyKeysFresh_typeBoundVar S C Env bty xv xty Env1 h_tbv h_poly_fresh
      have h_body_S := h_ty_body S h_abs_Env2 h_wf_S h_poly_fresh_ext
      rw [LMonoTy.subst_absorbs S Env2.stateSubstInfo.subst
        (.tcons "arrow" [xty, et_body.toLMonoTy]) h_abs_Env2]
      rw [LMonoTy.subst_tcons_pair S "arrow" xty et_body.toLMonoTy]
      -- Bridge: Env1.context.subst S ≈ (Env.context.subst S) with xv ↦ subst S (forAll [] xty)
      have h_ctx_subst_equiv : (Env1.context.subst S).Equiv
          { Env.context.subst S with types :=
            (Env.context.subst S).types.insert xv (LTy.subst S (.forAll [] xty)) } := by
        rw [h_ctx_bridge]
        exact TContext.subst_addInNewest_single_equiv_insert Env.context S xv (.forAll [] xty)
          h_ne h_xv_fresh_maps
      have h_lty_subst : LTy.subst S (.forAll [] xty) = .forAll [] (LMonoTy.subst S xty) := by
        simp [LTy.subst, LTy.subst.go]
      rw [h_lty_subst] at h_ctx_subst_equiv
      have h_body_S' := HasType_Equiv h_body_S h_ctx_subst_equiv
      have h_tabs := HasType.tabs (TContext.subst Env.context S) m pn (xv, some xty)
        (.forAll [] (LMonoTy.subst S xty))
        e_body (.forAll [] (LMonoTy.subst S et_body.toLMonoTy)) bty
        (by intro h_mem
            have h_in_ctx := h_ws (xv, some xty) (by simp [LExpr.freeVars]; exact h_mem)
            exact h_xv_not_known h_in_ctx)
        (by simp [LTy.isMonoType, LTy.boundVars])
        (by simp [LTy.isMonoType, LTy.boundVars])
        (by exact h_body_S')
        (by cases bty with
            | none => exact Or.inl rfl
            | some bty_val =>
              right; exact ⟨bty_val, rfl,
                (TContext.subst_aliases Env.context S) ▸
                AnnotCompat_subst S
                  (typeBoundVar_AnnotCompat C Env bty_val xv xty Env1 h_tbv h_aw)
                  (fun a ha => h_aw a ha)⟩)
      simp [LTy.toMonoType] at h_tabs
      exact h_tabs
  case h_quant =>
    intro m qk pn bty tr e_body et C Env Env' xv xty Env1 et_body Env2 triggersT Env3 substInfo
      h_res h_tbv h_res_body h_res_tr h_unify h_et h_env' h_abs32 h_envwf h_ne h_fwf h_envwf1 h_ne1 h_aliases_eq
      h_envwf2 h_ctx2 h_ih_body h_ih_tr h_ws
    have h_aw := h_envwf.aliasesWF
    have h_per_scope := typeBoundVar_xv_fresh_in_context C Env bty xv xty Env1 h_tbv
    have h_xv_fresh_maps : HMaps.find? Env.context.types xv = none := by
      have h_gen : ∀ (types : HMaps (Identifier T.IDMeta) LTy),
          (∀ mm, mm ∈ types → HMap.find? mm xv = none) → HMaps.find? types xv = none := by
        intro types h_all
        induction types with
        | nil => rfl
        | cons scope rest ih =>
          simp only [HMaps.find?]
          rw [h_all scope (by simp)]
          exact ih (fun mm hmm => h_all mm (by simp [hmm]))
      exact h_gen _ h_per_scope
    have h_xv_not_known : xv ∉ TContext.knownVars Env.context := by
      simp only [TContext.knownVars]
      intro h_kv
      obtain ⟨w, hw⟩ := (HMaps.mem_keys_iff_find? Env.context.types xv).mp h_kv
      rw [h_xv_fresh_maps] at hw; exact absurd hw (by simp)
    have h_ctx_bridge : Env1.context =
        { Env.context with types := Env.context.types.addInNewest (HMap.single xv (.forAll [] xty)) } := by
      have h_types := typeBoundVar_types_addInNewest C Env bty xv xty Env1 h_tbv
      have h_al := typeBoundVar_aliases_eq C Env bty xv xty Env1 h_tbv
      cases hc : Env1.context with
      | mk t1 a1 =>
        rw [hc] at h_types h_al
        simp only [] at h_types h_al
        subst h_types; subst h_al; rfl
    have h_ws_open_body : WellScoped (varOpen 0 (xv, some xty) e_body) Env1.context :=
      WellScoped_varOpen_typeBoundVar C Env bty xv xty Env1 e_body h_tbv
        (fun x hx => h_ws x (by simp [LExpr.freeVars, List.mem_append]; right; exact hx))
    have ⟨h_ctx_body, h_ty_body⟩ := h_ih_body h_ws_open_body
    have h_ws_tr : WellScoped (varOpen 0 (xv, some xty) tr) Env1.context :=
      WellScoped_varOpen_typeBoundVar C Env bty xv xty Env1 tr h_tbv
        (fun x hx => h_ws x (by simp [LExpr.freeVars, List.mem_append]; left; exact hx))
    have ⟨h_ctx_tr, h_ty_tr⟩ := h_ih_tr (WellScoped_Equiv_knownVars h_ctx2.symm h_ws_tr)
    subst h_env'
    have h_updSubst_ctx : (Env3.updateSubst substInfo).context = Env3.context := by
      simp [TEnv.updateSubst, TEnv.context]
    constructor
    · -- Context preservation: eraseFromContext (updateSubst Env3) xv → Env.context
      exact eraseFromContext_typeBoundVar_equiv C Env bty xv xty Env1 h_tbv (Env3.updateSubst substInfo)
        (TContext.Equiv.of_eq h_updSubst_ctx |>.trans (h_ctx_tr.trans h_ctx2)) h_ne
    · -- Typing: quant result type is bool, subst S bool = bool
      intro S h_abs_S h_wf_S h_poly_fresh
      subst h_et; simp [toLMonoTy, LMonoTy.subst_bool]
      -- S absorbs substInfo (eraseFromContext/updateSubst set the subst to substInfo)
      have h_abs_S_sub : Subst.absorbs S substInfo.subst := by
        simp [TEnv.eraseFromContext, TEnv.updateContext, TEnv.updateSubst] at h_abs_S
        exact h_abs_S
      have h_abs_S_Env3 : Subst.absorbs S Env3.stateSubstInfo.subst :=
        Subst.absorbs_trans Env3.stateSubstInfo.subst substInfo.subst S
          (Constraints.unify_absorbs _ _ _ h_unify) h_abs_S_sub
      have h_abs_S_Env2 : Subst.absorbs S Env2.stateSubstInfo.subst :=
        Subst.absorbs_trans Env2.stateSubstInfo.subst Env3.stateSubstInfo.subst S
          h_abs32 h_abs_S_Env3
      have h_poly_fresh_ext : Subst.polyKeysFresh (T := T) S Env1.context :=
        polyKeysFresh_typeBoundVar S C Env bty xv xty Env1 h_tbv h_poly_fresh
      have h_body_S := h_ty_body S h_abs_S_Env2 h_wf_S h_poly_fresh_ext
      have h_body_bool : LMonoTy.subst S et_body.toLMonoTy = LMonoTy.bool := by
        have h_eq := unify_makes_equal et_body.toLMonoTy LMonoTy.bool
          Env3.stateSubstInfo substInfo h_unify
        have h := congrArg (LMonoTy.subst S) h_eq
        rw [LMonoTy.subst_absorbs S substInfo.subst _ h_abs_S_sub,
            LMonoTy.subst_absorbs S substInfo.subst _ h_abs_S_sub,
            LMonoTy.subst_bool] at h
        exact h
      rw [h_body_bool] at h_body_S
      have h_tr_S := HasType_Equiv (h_ty_tr S h_abs_S_Env3 h_wf_S
        (polyKeysFresh_Equiv h_ctx2.symm h_poly_fresh_ext)) (TContext.Equiv.subst h_ctx2 S)
      -- Bridge: Env1.context.subst S ≈ inserted substituted context
      have h_ctx_subst_equiv : (Env1.context.subst S).Equiv
          { Env.context.subst S with types :=
            (Env.context.subst S).types.insert xv (LTy.subst S (.forAll [] xty)) } := by
        rw [h_ctx_bridge]
        exact TContext.subst_addInNewest_single_equiv_insert Env.context S xv (.forAll [] xty)
          h_ne h_xv_fresh_maps
      have h_lty_subst : LTy.subst S (.forAll [] xty) = .forAll [] (LMonoTy.subst S xty) := by
        simp [LTy.subst, LTy.subst.go]
      rw [h_lty_subst] at h_ctx_subst_equiv
      have h_body_S' := HasType_Equiv h_body_S h_ctx_subst_equiv
      have h_tr_S' := HasType_Equiv h_tr_S h_ctx_subst_equiv
      have h_tquant := HasType.tquant (TContext.subst Env.context S) m qk pn tr
        (.forAll [] (LMonoTy.subst S (triggersT.toLMonoTy)))
        (xv, some xty) (.forAll [] (LMonoTy.subst S xty)) e_body bty
        (by intro h_mem
            have h_in_ctx := h_ws (xv, some xty) (by
              simp [LExpr.freeVars, List.mem_append]; right; exact h_mem)
            exact h_xv_not_known h_in_ctx)
        (by simp [LTy.isMonoType, LTy.boundVars])
        (by exact h_body_S')
        (by exact h_tr_S')
        (by cases bty with
            | none => exact Or.inl rfl
            | some bty_val =>
              right; exact ⟨bty_val, rfl,
                (TContext.subst_aliases Env.context S) ▸
                AnnotCompat_subst S
                  (typeBoundVar_AnnotCompat C Env bty_val xv xty Env1 h_tbv h_aw)
                  (fun a ha => h_aw a ha)⟩)
      simp at h_tquant
      exact h_tquant
  case h_eq =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 substInfo
      h_res h_res1 h_res2 h_unify h_et h_subeq h_abs1 h_abs2 h_envwf h_ne h_fwf
      h_envwf1 h_ctx1 h_envwf2 h_ctx2 h_ih1 h_ih2 h_ws
    have h_aw := h_envwf.aliasesWF
    have h_ne1 := h_ctx1.symm.types_ne_nil h_ne
    have h_ws1 : WellScoped e1 Env.context :=
      fun x hx => h_ws x (by simp [LExpr.freeVars, List.mem_append]; left; exact hx)
    have ⟨_, h_ty1⟩ := h_ih1 h_ws1
    have h_ws2 : WellScoped e2 Env1.context :=
      WellScoped_Equiv_knownVars h_ctx1.symm
        (fun x hx => h_ws x (by simp [LExpr.freeVars, List.mem_append]; right; exact hx))
    have ⟨_, h_ty2⟩ := h_ih2 h_ws2
    subst h_et
    constructor
    · -- Context preservation
      exact (resolveAux_properties (.eq m e1 e2) _ C Env Env' h_res h_ne h_aw h_fwf
        h_envwf.substFreshForGen h_envwf.ctxFreshForGen h_envwf.boundVarsFresh).context
    · intro S h_abs_S h_wf_S h_poly_fresh
      simp [toLMonoTy]
      rw [LMonoTy.subst_bool]
      rw [h_subeq] at h_abs_S
      have h_abs_unify := Constraints.unify_absorbs [(e1t.toLMonoTy, e2t.toLMonoTy)]
        Env2.stateSubstInfo substInfo h_unify
      have h_abs_S_Env2 : Subst.absorbs S Env2.stateSubstInfo.subst :=
        Subst.absorbs_trans Env2.stateSubstInfo.subst substInfo.subst S h_abs_unify h_abs_S
      have h_abs_S_Env1 : Subst.absorbs S Env1.stateSubstInfo.subst :=
        Subst.absorbs_trans Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst S h_abs2 h_abs_S_Env2
      have h_ty1_S := h_ty1 S h_abs_S_Env1 h_wf_S h_poly_fresh
      have h_ty2_S := HasType_Equiv (h_ty2 S h_abs_S_Env2 h_wf_S
        (polyKeysFresh_Equiv h_ctx1.symm h_poly_fresh)) (TContext.Equiv.subst h_ctx1 S)
      have h_eq := unify_makes_equal e1t.toLMonoTy e2t.toLMonoTy
        Env2.stateSubstInfo substInfo h_unify
      have h_eq_S : LMonoTy.subst S e1t.toLMonoTy = LMonoTy.subst S e2t.toLMonoTy := by
        have h := congrArg (LMonoTy.subst S) h_eq
        rw [LMonoTy.subst_absorbs S substInfo.subst _ h_abs_S,
            LMonoTy.subst_absorbs S substInfo.subst _ h_abs_S] at h
        exact h
      rw [h_eq_S] at h_ty1_S
      exact HasType.teq (TContext.subst Env.context S) m e1 e2
        (.forAll [] (LMonoTy.subst S e2t.toLMonoTy))
        h_ty1_S h_ty2_S
  case h_ite =>
    intro m c t e et C Env Env' ct Env1 tht Env2 elt Env3 substInfo
      h_res h_res_c h_res_t h_res_e h_unify h_et h_subeq h_abs_th2 h_abs_el3 h_envwf h_ne h_fwf
      h_envwf1 h_ctx1 h_envwf2 h_ctx2 h_envwf3 h_ctx3 h_ih_c h_ih_t h_ih_e h_ws
    have h_aw := h_envwf.aliasesWF
    have h_ws_c : WellScoped c Env.context := by
      intro x hx; apply h_ws; simp only [WellScoped, LExpr.freeVars] at h_ws ⊢
      exact List.mem_append_left _ (List.mem_append_left _ hx)
    have ⟨_, h_ty_c⟩ := h_ih_c h_ws_c
    have h_ws_t : WellScoped t Env1.context :=
      WellScoped_Equiv_knownVars h_ctx1.symm (by
        intro x hx; apply h_ws; simp only [LExpr.freeVars]
        exact List.mem_append_left _ (List.mem_append_right _ hx))
    have ⟨_, h_ty_t⟩ := h_ih_t h_ws_t
    have h_ws_e : WellScoped e Env2.context :=
      WellScoped_Equiv_knownVars h_ctx2.symm (by
        intro x hx; apply h_ws; simp only [LExpr.freeVars]
        exact List.mem_append_right _ hx)
    have ⟨_, h_ty_e⟩ := h_ih_e h_ws_e
    subst h_et
    constructor
    · -- Context preservation
      exact (resolveAux_properties (.ite m c t e) _ C Env Env' h_res h_ne h_aw h_fwf
        h_envwf.substFreshForGen h_envwf.ctxFreshForGen h_envwf.boundVarsFresh).context
    · intro S h_abs_S h_wf_S h_poly_fresh
      simp [toLMonoTy]
      rw [h_subeq] at h_abs_S
      have h_abs_unify := Constraints.unify_absorbs
        [(ct.toLMonoTy, LMonoTy.bool), (tht.toLMonoTy, elt.toLMonoTy)]
        Env3.stateSubstInfo substInfo h_unify
      have h_abs_S_Env3 : Subst.absorbs S Env3.stateSubstInfo.subst :=
        Subst.absorbs_trans Env3.stateSubstInfo.subst substInfo.subst S h_abs_unify h_abs_S
      have h_abs_S_Env2 : Subst.absorbs S Env2.stateSubstInfo.subst :=
        Subst.absorbs_trans Env2.stateSubstInfo.subst Env3.stateSubstInfo.subst S h_abs_el3 h_abs_S_Env3
      have h_abs_S_Env1 : Subst.absorbs S Env1.stateSubstInfo.subst :=
        Subst.absorbs_trans Env1.stateSubstInfo.subst Env2.stateSubstInfo.subst S h_abs_th2 h_abs_S_Env2
      have h_ty_c_S := h_ty_c S h_abs_S_Env1 h_wf_S h_poly_fresh
      have h_ty_t_S := HasType_Equiv (h_ty_t S h_abs_S_Env2 h_wf_S
        (polyKeysFresh_Equiv h_ctx1.symm h_poly_fresh)) (TContext.Equiv.subst h_ctx1 S)
      have h_ty_e_S := HasType_Equiv (h_ty_e S h_abs_S_Env3 h_wf_S
        (polyKeysFresh_Equiv h_ctx2.symm h_poly_fresh)) (TContext.Equiv.subst h_ctx2 S)
      have ⟨h_eq_bool, h_eq_te⟩ := unify_makes_equal₂
        ct.toLMonoTy LMonoTy.bool tht.toLMonoTy elt.toLMonoTy
        Env3.stateSubstInfo substInfo h_unify
      have h_eq_bool_S : LMonoTy.subst S ct.toLMonoTy = LMonoTy.bool := by
        have h := congrArg (LMonoTy.subst S) h_eq_bool
        rw [LMonoTy.subst_absorbs S substInfo.subst _ h_abs_S,
            LMonoTy.subst_absorbs S substInfo.subst _ h_abs_S,
            LMonoTy.subst_bool] at h
        exact h
      have h_eq_te_S : LMonoTy.subst S tht.toLMonoTy = LMonoTy.subst S elt.toLMonoTy := by
        have h := congrArg (LMonoTy.subst S) h_eq_te
        rw [LMonoTy.subst_absorbs S substInfo.subst _ h_abs_S,
            LMonoTy.subst_absorbs S substInfo.subst _ h_abs_S] at h
        exact h
      rw [h_eq_bool_S] at h_ty_c_S
      rw [← h_eq_te_S] at h_ty_e_S
      exact HasType.tif (TContext.subst Env.context S) m c t e
        (.forAll [] (LMonoTy.subst S tht.toLMonoTy))
        h_ty_c_S h_ty_t_S h_ty_e_S



/-! ### `resolve_HasType` — top-level soundness wrappers -/

omit [ToString T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta]
  [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `HasType` transfers from `{types := [HMap.empty], aliases}` to
    `{types := [], aliases}`. Both contexts have `find? = none` for all variables
    and `insert` gives the same results, so all `HasType` constructors behave
    identically. -/
private theorem HasType_transfer_empty_scope
    (C : LContext T) (aliases : List TypeAlias) (e : LExpr T.mono) (ty : LTy)
    (h : HasType C { types := [HMap.empty], aliases := aliases } e ty) :
    HasType C { types := [], aliases := aliases } e ty := by
  have h_insert_eq : ∀ (x : T.Identifier) (v : LTy),
      HMaps.insert ([HMap.empty] : HMaps T.Identifier LTy) x v =
      HMaps.insert ([] : HMaps T.Identifier LTy) x v := by
    intro x v
    simp [HMaps.insert, HMaps.find?, HMap.find?_empty, HMaps.newest, HMaps.pop, HMaps.push]
  generalize hΓ_eq : ({ types := [HMap.empty], aliases := aliases } : TContext T.IDMeta) = Γ' at h
  induction h with
  | tbool_const _ m b h_known => exact HasType.tbool_const _ m b h_known
  | tint_const _ m n h_known => exact HasType.tint_const _ m n h_known
  | treal_const _ m r h_known => exact HasType.treal_const _ m r h_known
  | tstr_const _ m s h_known => exact HasType.tstr_const _ m s h_known
  | tbitvec_const _ m n b h_known => exact HasType.tbitvec_const _ m n b h_known
  | tvar _ m x ty h_find =>
    subst hΓ_eq; simp [HMaps.find?, HMap.find?_empty] at h_find
  | tvar_annotated _ m x ty_o ty_s tys ann h_find h_len h_open h_compat =>
    subst hΓ_eq; simp [HMaps.find?, HMap.find?_empty] at h_find
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
    simp [HMaps.find?] at h_find_x
  | tif _ m c e1 e2 ty h_c h_e1 h_e2 ih_c ih_e1 ih_e2 =>
    exact HasType.tif _ m c e1 e2 ty (ih_c hΓ_eq) (ih_e1 hΓ_eq) (ih_e2 hΓ_eq)
  | teq _ m e1 e2 ty h_e1 h_e2 ih1 ih2 =>
    exact HasType.teq _ m e1 e2 ty (ih1 hΓ_eq) (ih2 hΓ_eq)
  | tquant _ m k _name tr tr_ty x x_ty e o h_fresh hx h_body h_tr h_annot ih_body ih_tr =>
    subst hΓ_eq
    rw [h_insert_eq] at h_body h_tr
    exact HasType.tquant _ m k _ tr tr_ty x x_ty e o h_fresh hx h_body h_tr h_annot
  | top _ m f op ty h_find h_type => exact HasType.top _ m f op ty h_find h_type
  | top_annotated _ m f op ty_o ty_s tys ann h_find h_type h_len h_open h_compat =>
    subst hΓ_eq
    exact HasType.top_annotated _ m f op ty_o ty_s tys ann h_find h_type h_len h_open h_compat
  | talias _ e mty mty' h_equiv h_e ih =>
    subst hΓ_eq
    exact HasType.talias _ e mty mty' h_equiv (ih rfl)

omit [ToString T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta]
  [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `checkContextTypesClosed` is equivalent to: every value in `types.values` is
    closed. Stated over `values` (not `find?`) so it transports across `Equiv`,
    which preserves `values` membership even for shadowed entries. -/
private theorem checkContextTypesClosed_iff_values (Env : TEnv T.IDMeta) :
    checkContextTypesClosed Env ↔
    ∀ ty, ty ∈ Env.context.types.values → LTy.freeVars ty = [] := by
  simp only [checkContextTypesClosed, List.all_eq_true]
  constructor
  · intro h ty h_mem
    obtain ⟨scope, h_scope, h_ty⟩ := (HMaps.mem_values_iff_exists_scope _ ty).mp h_mem
    obtain ⟨k, hk⟩ := (HMap.mem_values_iff_find? scope ty).mp h_ty
    have := HMap.all_of_find? (h scope h_scope) hk
    simpa using this
  · intro h scope h_scope
    show HMap.all scope _ = true
    rw [HMap.all, Std.HashMap.all_eq_true_iff_forall_mem_getElem]
    intro k h_mem
    simp only [beq_iff_eq]
    have h_val : scope.rep[k]'h_mem ∈ Env.context.types.values := by
      rw [HMaps.mem_values_iff_exists_scope]
      refine ⟨scope, h_scope, ?_⟩
      rw [HMap.mem_values_iff_find?]
      exact ⟨k, by simp only [HMap.find?, Std.HashMap.get?_eq_getElem?];
                   exact Std.HashMap.getElem?_eq_some_getElem h_mem⟩
    exact h _ h_val

omit [ToString T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta]
  [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Derive the find?-based closedness condition from `checkContextTypesClosed`. -/
private theorem ctx_closed_of_check (Env : TEnv T.IDMeta)
    (h : checkContextTypesClosed Env) :
    ∀ y ty, Env.context.types.find? y = some ty → LTy.freeVars ty = [] :=
  fun _ ty h_find =>
    (checkContextTypesClosed_iff_values Env).mp h ty
      (HMaps.find?_mem_values Env.context.types h_find)

omit [ToString T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta]
  [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `checkContextTypesClosed` is preserved when context is unchanged up to Equiv
    (`Equiv` preserves `values` membership). -/
private theorem checkContextTypesClosed_of_ctx_eq {Env Env' : TEnv T.IDMeta}
    (h : checkContextTypesClosed Env) (h_ctx : Env'.context.Equiv Env.context) :
    checkContextTypesClosed Env' := by
  rw [checkContextTypesClosed_iff_values] at h ⊢
  intro ty h_mem
  exact h ty ((h_ctx.1.mem_values ty).mp h_mem)

omit [ToString T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta]
  [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- When all context types are closed, `allKeysFresh` holds for any substitution
    (`isFresh` is vacuously true). -/
theorem Subst.allKeysFresh_of_ctx_closed
    {S : Subst} {Γ : TContext T.IDMeta}
    (h_ctx_closed : ∀ y ty, Γ.types.find? y = some ty → LTy.freeVars ty = []) :
    Subst.allKeysFresh (T := T) S Γ := by
  intro a _ x ty hf
  simp [h_ctx_closed x ty hf]

/-- Core resolve soundness: if `LExpr.resolve` succeeds, the result is well-typed
    (universally over absorbing substitutions), idempotent, and preserves `TEnvWF`.
    No `checkContextTypesClosed` or `allKeysFresh` preconditions needed. -/
theorem resolve_HasType_core :
    ∀ (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
      (Env : TEnv T.IDMeta) Env',
      e.resolve C Env = .ok ⟨e_typed, Env'⟩ →
      TEnvWF Env →
      FactoryWF C.functions →
      WellScoped e Env.context →
      (∀ S, Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        Subst.polyKeysFresh (T := T) S Env.context →
        HasType C (TContext.subst Env.context S) e (.forAll [] (LMonoTy.subst S e_typed.toLMonoTy))) ∧
      LMonoTy.subst Env'.stateSubstInfo.subst e_typed.toLMonoTy = e_typed.toLMonoTy ∧
      TEnvWF Env' := by
  intro e e_typed C Env Env' h h_envwf h_fwf h_ws
  unfold LExpr.resolve at h
  simp only [Bind.bind, Except.bind] at h
  cases h_empty : Env.context.types.isEmpty with
  | true =>
    simp only [h_empty, if_true] at h
    elim_err h
    rename_i v h_aux
    obtain ⟨et, Env_r⟩ := v
    simp at h
    obtain ⟨h_typed, h_env'⟩ := h
    -- Env.context.types = [] (isEmpty true)
    have h_types_nil : Env.context.types = [] := by
      cases ht : Env.context.types with
      | nil => rfl
      | cons _ _ => rw [ht] at h_empty; simp [HMaps.isEmpty] at h_empty
    let Env_upd := Env.updateContext { Env.context with types := [HMap.empty] }
    have h_upd_ne : Env_upd.context.types ≠ [] := by
      simp [Env_upd, TEnv.updateContext, TEnv.context]
    have h_upd_ctx_eq : Env_upd.context =
        { types := [HMap.empty], aliases := Env.context.aliases } := by
      simp [Env_upd, TEnv.updateContext, TEnv.context]
    have h_envwf_upd : TEnvWF Env_upd := {
      aliasesWF := by
        simp only [h_upd_ctx_eq]; exact h_envwf.aliasesWF
      substFreshForGen := by
        simp only [Env_upd, TEnv.updateContext]; exact h_envwf.substFreshForGen
      ctxFreshForGen := by
        simp only [h_upd_ctx_eq, ContextFreshForGen, TContext.knownTypeVars,
          HMaps.values, HMap.values_empty, List.flatMap_nil, List.append_nil,
          List.not_mem_nil, false_implies, implies_true]
      boundVarsNodup := by
        intro y ty h_f
        rw [h_upd_ctx_eq] at h_f
        simp [HMaps.find?, HMap.find?_empty] at h_f
      boundVarsFresh := by
        intro y ty h_f
        rw [h_upd_ctx_eq] at h_f
        simp [HMaps.find?, HMap.find?_empty] at h_f
    }
    have h_ws_upd : WellScoped e Env_upd.context := by
      have h_kv_eq : Env_upd.context.knownVars = Env.context.knownVars := by
        simp only [TContext.knownVars, h_upd_ctx_eq, h_types_nil,
          HMaps.keys, HMap.keys_empty, List.append_nil]
      unfold WellScoped at h_ws ⊢
      rw [h_kv_eq]; exact h_ws
    have h_aux' : resolveAux C Env_upd e = .ok (et, Env_r) := by
      simp only [Env_upd, TEnv.updateContext] at h_aux ⊢; exact h_aux
    subst h_env'
    have ⟨h_ctx_upd, h_hastype⟩ := resolveAux_HasType e et C Env_upd Env_r h_aux'
      h_envwf_upd h_upd_ne h_fwf h_ws_upd
    have h_envwf' := TEnvWF.of_resolveAux e et C Env_upd Env_r h_aux' h_envwf_upd h_upd_ne h_fwf h_ctx_upd
    have h_idem : LMonoTy.subst Env_r.stateSubstInfo.subst e_typed.toLMonoTy = e_typed.toLMonoTy := by
      rw [← h_typed, applySubstT_toLMonoTy]
      exact LMonoTy.subst_idempotent Env_r.stateSubstInfo.subst Env_r.stateSubstInfo.isWF (et.toLMonoTy)
    refine ⟨fun S h_abs h_wf h_pkf => ?_, h_idem, h_envwf'⟩
    rw [← h_typed, applySubstT_toLMonoTy, LMonoTy.subst_absorbs S Env_r.stateSubstInfo.subst _ h_abs]
    -- polyKeysFresh on the empty context lifts to Env_upd.context
    have h_pkf_upd : Subst.polyKeysFresh (T := T) S Env_upd.context := by
      intro a ha x ty hf _
      rw [h_upd_ctx_eq] at hf; simp [HMaps.find?, HMap.find?_empty] at hf
    have h_ht := h_hastype S h_abs h_wf h_pkf_upd
    have h_ctx_empty : Env.context = { types := [], aliases := Env.context.aliases } := by
      cases hc : Env.context with
      | mk t a =>
        rw [hc] at h_types_nil; simp only at h_types_nil; rw [h_types_nil]
    -- TContext.subst on both empty contexts is the identity (types stay empty/[HMap.empty])
    have h_ctx_subst_id : TContext.subst Env.context S = Env.context := by
      rw [h_ctx_empty]
      simp only [TContext.subst, TContext.types.subst, HMaps.mapValues, List.map_nil]
    have h_upd_subst_equiv : (TContext.subst Env_upd.context S).Equiv
        { types := [HMap.empty], aliases := Env.context.aliases } := by
      refine ⟨?_, by rw [TContext.subst_aliases, h_upd_ctx_eq]⟩
      rw [h_upd_ctx_eq]
      -- mapValues (subst S) [HMap.empty] ≈ [HMap.empty] (both find? = none per scope)
      simp only [TContext.subst, TContext.types.subst, HMaps.mapValues, List.map_cons,
        List.map_nil]
      refine ⟨fun k => ?_, True.intro⟩
      rw [HMap.find?_mapValues, HMap.find?_empty]; rfl
    have h_ht' := HasType_Equiv h_ht h_upd_subst_equiv
    rw [h_ctx_subst_id]
    have h_result := HasType_transfer_empty_scope C Env.context.aliases e _ h_ht'
    rw [h_ctx_empty]; exact h_result
  | false =>
    rw [if_neg (by simp [h_empty])] at h
    elim_err h
    rename_i v h_aux
    obtain ⟨et, Env_r⟩ := v
    simp at h
    obtain ⟨h_typed, h_env'⟩ := h
    subst h_env'
    have h_ne : Env.context.types ≠ [] := by
      cases ht : Env.context.types with
      | nil => rw [ht] at h_empty; simp [HMaps.isEmpty] at h_empty
      | cons _ _ => exact List.cons_ne_nil _ _
    have ⟨h_ctx_pres, h_hastype⟩ := resolveAux_HasType e et C Env Env_r h_aux h_envwf h_ne h_fwf h_ws
    have h_envwf' := TEnvWF.of_resolveAux e et C Env Env_r h_aux h_envwf h_ne h_fwf h_ctx_pres
    have h_idem : LMonoTy.subst Env_r.stateSubstInfo.subst e_typed.toLMonoTy = e_typed.toLMonoTy := by
      rw [← h_typed, applySubstT_toLMonoTy]
      exact LMonoTy.subst_idempotent Env_r.stateSubstInfo.subst Env_r.stateSubstInfo.isWF (et.toLMonoTy)
    refine ⟨fun S h_abs h_wf h_pkf => ?_, h_idem, h_envwf'⟩
    rw [← h_typed, applySubstT_toLMonoTy]
    have h_ht := h_hastype S h_abs h_wf h_pkf
    rw [LMonoTy.subst_absorbs S Env_r.stateSubstInfo.subst _ h_abs]
    exact h_ht

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
theorem resolve_preserves_context
    (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = .ok ⟨e_typed, Env'⟩)
    (h_envwf : TEnvWF Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions) :
    Env'.context.Equiv Env.context := by
  unfold LExpr.resolve at h
  simp only [Bind.bind, Except.bind] at h
  have h_ne' : Env.context.types.isEmpty = false := by
    cases ht : Env.context.types with
    | nil => exact absurd ht h_ne
    | cons _ _ => simp [HMaps.isEmpty]
  rw [if_neg (by simp [h_ne'])] at h
  elim_err h
  rename_i v h_aux
  obtain ⟨et, Env_r⟩ := v
  simp at h
  obtain ⟨_, h_env'⟩ := h
  subst h_env'
  exact (resolveAux_properties e et C Env Env_r h_aux h_ne
    h_envwf.aliasesWF h_fwf h_envwf.substFreshForGen h_envwf.ctxFreshForGen
    h_envwf.boundVarsFresh).context

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- `resolve` produces a substitution that absorbs the input substitution. -/
theorem resolve_absorbs
    (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = .ok ⟨e_typed, Env'⟩)
    (h_envwf : TEnvWF Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  unfold LExpr.resolve at h
  simp only [Bind.bind, Except.bind] at h
  cases h_types : Env.context.types with
  | nil => exact absurd h_types h_ne
  | cons hd tl =>
    simp [HMaps.isEmpty, h_types] at h
    elim_err h
    rename_i v h_aux
    obtain ⟨et, Env_r⟩ := v
    simp at h
    obtain ⟨_, h_env'⟩ := h
    subst h_env'
    have h_props := resolveAux_properties e et C Env Env_r h_aux
      (by rw [h_types]; exact List.cons_ne_nil _ _)
      h_envwf.aliasesWF h_fwf h_envwf.substFreshForGen h_envwf.ctxFreshForGen
      h_envwf.boundVarsFresh
    exact h_props.absorbs

omit [ToString T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/--
For a bare input free variable (`fvar m x none`, as emitted for inout call
arguments), `resolve` returns a typed expression whose monotype is alias-
equivalent to the (monomorphic) context type of `x`, under any substitution that
absorbs the final environment's substitution. The `resolve`-level wrapper of
`inferFVar_none_find_aliasEquiv`, serving both soundness theorems. -/
theorem resolve_fvar_none_find_aliasEquiv
    (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (m : T.mono.base.Metadata) (x : Identifier T.IDMeta) (et : LExprT T.mono)
    (h : (LExpr.fvar m x none).resolve C Env = .ok (et, Env'))
    (h_wf : TEnvWF Env) (h_ne : Env.context.types ≠ []) (_h_fwf : FactoryWF C.functions)
    (h_mono : ∀ y t, Env.context.types.find? y = some t → LTy.boundVars t = []) :
    ∃ mty_ctx, Env.context.types.find? x = some (.forAll [] mty_ctx) ∧
      ∀ S, Subst.absorbs S Env'.stateSubstInfo.subst →
        AliasEquiv Env.context.aliases (LMonoTy.subst S mty_ctx)
          (LMonoTy.subst S et.toLMonoTy) := by
  unfold LExpr.resolve at h
  simp only [Bind.bind, Except.bind] at h
  cases h_types : Env.context.types with
  | nil => exact absurd h_types h_ne
  | cons hd tl =>
    simp [HMaps.isEmpty, h_types] at h
    elim_err h
    rename_i v h_aux
    obtain ⟨et_aux, Env_r⟩ := v
    simp at h
    obtain ⟨h_typed, h_env'⟩ := h
    subst h_env'
    -- `resolveAux` fvar case: `inferFVar` then re-tag.
    simp only [resolveAux, Bind.bind, Except.bind] at h_aux
    elim_err h_aux
    rename_i v_if h_inf
    obtain ⟨ty, Env_inf⟩ := v_if
    simp at h_aux
    obtain ⟨h_et_aux, h_env_r⟩ := h_aux
    -- Extract the alias-equivalence fact from the `inferFVar` call.
    have h_ae := inferFVar_none_find_aliasEquiv C Env Env_inf x ty h_inf h_mono
      h_wf.aliasesWF
    obtain ⟨mty_ctx, h_find, h_ae_S⟩ := h_ae
    rw [h_types] at h_find
    refine ⟨mty_ctx, h_find, ?_⟩
    intro S h_abs_S
    -- `et.toLMonoTy = subst Env_r.subst ty`, and `absorbs S Env_r.subst` collapses it.
    have h_et_ty : et.toLMonoTy = LMonoTy.subst Env_r.stateSubstInfo.subst ty := by
      rw [← h_typed, applySubstT_toLMonoTy, ← h_et_aux]
      simp [LExpr.toLMonoTy]
    rw [h_et_ty, LMonoTy.subst_absorbs S Env_r.stateSubstInfo.subst ty h_abs_S]
    exact h_ae_S S

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

    This builds on `resolve_HasType_core` (which proves the universally-quantified
    typing conclusion under the minimal preconditions). Here we additionally derive
    the composability postconditions `checkContextTypesClosed Env'` and
    `allKeysFresh Env'.subst Env'.context`, then specialize the universal typing
    conclusion to the final substitution `Env'.stateSubstInfo.subst`.

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
      checkContextTypesClosed Env →
      HasType C (TContext.subst Env.context Env'.stateSubstInfo.subst) e (.forAll [] e_typed.toLMonoTy) ∧
      TEnvWF Env' ∧
      checkContextTypesClosed Env' ∧
      Subst.allKeysFresh Env'.stateSubstInfo.subst Env'.context := by
  intro e e_typed C Env Env' h h_envwf h_fwf h_ws h_all_fresh h_check
  have ⟨h_ht, h_idem, h_envwf'⟩ := resolve_HasType_core e e_typed C Env Env' h h_envwf h_fwf h_ws
  have h_ctx_closed : ∀ y ty, Env.context.types.find? y = some ty → LTy.freeVars ty = [] :=
    ctx_closed_of_check Env h_check
  -- Derive the composability postconditions by unfolding `resolve`.
  have ⟨h_check', h_fresh'⟩ : checkContextTypesClosed Env' ∧
      Subst.allKeysFresh (T := T) Env'.stateSubstInfo.subst Env'.context := by
    unfold LExpr.resolve at h
    simp only [Bind.bind, Except.bind] at h
    cases h_empty : Env.context.types.isEmpty with
    | true =>
      simp only [h_empty, if_true] at h
      elim_err h
      rename_i v h_aux
      obtain ⟨et, Env_r⟩ := v
      simp at h
      obtain ⟨h_typed, h_env'⟩ := h
      subst h_env'
      have h_types_nil : Env.context.types = [] := by
        cases ht : Env.context.types with
        | nil => rfl
        | cons _ _ => rw [ht] at h_empty; simp [HMaps.isEmpty] at h_empty
      let Env_upd := Env.updateContext { Env.context with types := [HMap.empty] }
      have h_upd_ctx_eq : Env_upd.context =
          { types := [HMap.empty], aliases := Env.context.aliases } := by
        simp [Env_upd, TEnv.updateContext, TEnv.context]
      have h_aux' : resolveAux C Env_upd e = .ok (et, Env_r) := by
        simp only [Env_upd, TEnv.updateContext] at h_aux ⊢; exact h_aux
      have h_upd_ne : Env_upd.context.types ≠ [] := by
        simp [Env_upd, TEnv.updateContext, TEnv.context]
      have h_envwf_upd : TEnvWF Env_upd := {
        aliasesWF := by simp only [h_upd_ctx_eq]; exact h_envwf.aliasesWF
        substFreshForGen := by simp only [Env_upd, TEnv.updateContext]; exact h_envwf.substFreshForGen
        ctxFreshForGen := by
          simp only [h_upd_ctx_eq, ContextFreshForGen, TContext.knownTypeVars,
            HMaps.values, HMap.values_empty, List.flatMap_nil, List.append_nil,
            List.not_mem_nil, false_implies, implies_true]
        boundVarsNodup := by
          intro y ty h_f; rw [h_upd_ctx_eq] at h_f; simp [HMaps.find?, HMap.find?_empty] at h_f
        boundVarsFresh := by
          intro y ty h_f; rw [h_upd_ctx_eq] at h_f; simp [HMaps.find?, HMap.find?_empty] at h_f
      }
      have h_ws_upd : WellScoped e Env_upd.context := by
        have h_kv_eq : Env_upd.context.knownVars = Env.context.knownVars := by
          simp only [TContext.knownVars, h_upd_ctx_eq, h_types_nil,
            HMaps.keys, HMap.keys_empty, List.append_nil]
        unfold WellScoped at h_ws ⊢; rw [h_kv_eq]; exact h_ws
      have ⟨h_ctx_upd, _⟩ := resolveAux_HasType e et C Env_upd Env_r h_aux'
        h_envwf_upd h_upd_ne h_fwf h_ws_upd
      have h_check_upd : checkContextTypesClosed Env_upd := by
        rw [checkContextTypesClosed_iff_values]
        intro ty h_mem
        rw [h_upd_ctx_eq] at h_mem
        simp [HMaps.values, HMap.values_empty] at h_mem
      have h_check' : checkContextTypesClosed Env_r :=
        checkContextTypesClosed_of_ctx_eq h_check_upd h_ctx_upd
      have h_all_fresh' : Subst.allKeysFresh (T := T) Env_r.stateSubstInfo.subst Env_r.context := by
        apply Subst.allKeysFresh_of_ctx_closed
        exact ctx_closed_of_check Env_r h_check'
      exact ⟨h_check', h_all_fresh'⟩
    | false =>
      rw [if_neg (by simp [h_empty])] at h
      elim_err h
      rename_i v h_aux
      obtain ⟨et, Env_r⟩ := v
      simp at h
      obtain ⟨h_typed, h_env'⟩ := h
      subst h_env'
      have h_ne : Env.context.types ≠ [] := by
        cases ht : Env.context.types with
        | nil => rw [ht] at h_empty; simp [HMaps.isEmpty] at h_empty
        | cons _ _ => exact List.cons_ne_nil _ _
      have ⟨h_ctx_pres, _⟩ := resolveAux_HasType e et C Env Env_r h_aux h_envwf h_ne h_fwf h_ws
      have h_check' : checkContextTypesClosed Env_r :=
        checkContextTypesClosed_of_ctx_eq h_check h_ctx_pres
      have h_all_fresh' : Subst.allKeysFresh (T := T) Env_r.stateSubstInfo.subst Env_r.context := by
        apply Subst.allKeysFresh_of_ctx_closed
        exact ctx_closed_of_check Env_r h_check'
      exact ⟨h_check', h_all_fresh'⟩
  refine ⟨?_, h_envwf', h_check', h_fresh'⟩
  have h_akf : Subst.allKeysFresh (T := T) Env'.stateSubstInfo.subst Env.context :=
    Subst.allKeysFresh_of_ctx_closed h_ctx_closed
  have h_hastype := h_ht Env'.stateSubstInfo.subst
    (Subst.absorbs_refl _ Env'.stateSubstInfo.isWF) Env'.stateSubstInfo.isWF
    (Subst.allKeysFresh_implies_polyKeysFresh _ _ h_akf)
  rw [h_idem] at h_hastype
  exact h_hastype



end Proofs

---------------------------------------------------------------------

section Tests

-- Examples of typing derivations using the `HasType` relation.

open LExpr.SyntaxMono LTy.Syntax

macro "solveKnownNames" : tactic =>  `(tactic | simp[KnownTypes.containsName, LTy.toKnownType!, makeKnownTypes, KnownTypes.default, LContext.default])

macro "findOfScopes" : tactic =>
  `(tactic | simp [HMaps.ofScopes, HMaps.find?, HMap.ofList, HMap.find?])

example : LExpr.HasType (T := ⟨Unit, Unit⟩) LContext.default {} esM[#true] t[bool] := by
  apply LExpr.HasType.tbool_const; solveKnownNames

example : LExpr.HasType (T := ⟨Unit, Unit⟩) LContext.default {} esM[#-1] t[int] := by
  apply LExpr.HasType.tint_const; solveKnownNames

example : LExpr.HasType (T := ⟨Unit, Unit⟩) LContext.default { types := HMaps.ofScopes [[(⟨"x", ()⟩, t[∀a. %a])]]} esM[x] t[int] := by
  have h_tinst := @LExpr.HasType.tinst (T := ⟨Unit, Unit⟩) _ _ LContext.default { types := HMaps.ofScopes [[("x", t[∀a. %a])]]} esM[x] t[∀a. %a] t[int] "a" mty[int]
  have h_tvar := @LExpr.HasType.tvar (T := ⟨Unit, Unit⟩) _ _ LContext.default { types := HMaps.ofScopes [[("x", t[∀a. %a])]]} () "x" t[∀a. %a]
  apply h_tinst; apply h_tvar; findOfScopes
  simp [LTy.open, List.removeAll, Subst.singleton, HMaps.find?,
        HMap.find?_single_self, LMonoTy.subst_unfold]

example : LExpr.HasType (T := ⟨Unit, Unit⟩) LContext.default { types := HMaps.ofScopes [[(⟨"m", ()⟩, t[∀a. %a → int])]]}
                        esM[(m #true)]
                        t[int] := by
  apply LExpr.HasType.tapp (T := ⟨Unit, Unit⟩) _ _ _ _ _ t[bool]
  · simp
    apply LExpr.HasType.tinst (T := ⟨Unit, Unit⟩) _ _ t[∀a. %a → int] t[bool → int] "a" mty[bool]
    · apply LExpr.HasType.tvar (T := ⟨Unit, Unit⟩)
      findOfScopes
    · simp [LTy.open, List.removeAll, Subst.singleton, HMaps.find?,
            HMap.find?_single_self, LMonoTy.subst_unfold]
  · apply LExpr.HasType.tbool_const
    solveKnownNames
  · simp +ground
  · simp +ground

example : LExpr.HasType (T := ⟨Unit, Unit⟩) {} {} esM[λ %0] t[∀a. %a → %a] := by
  have h_tabs := @LExpr.HasType.tabs (T := ⟨Unit, Unit⟩) _ _ {} {} () "" ("a", none) t[%a] esM[%0] t[%a] none
  simp at h_tabs
  have h_tvar' : LExpr.HasType (T := ⟨Unit, Unit⟩) {} { types := HMaps.insert ({} : HMaps _ _) "a" t[%a] } esM[a] t[%a] := by
    apply LExpr.HasType.tvar; rw [HMaps.find?_insert_self]
  specialize (h_tabs (by unfold fresh; unfold LExpr.freeVars; simp only [List.not_mem_nil,
    not_false_eq_true]) rfl rfl h_tvar')
  simp [LTy.toMonoType] at h_tabs
  have h_tgen := @LExpr.HasType.tgen (T := ⟨Unit, Unit⟩) _ _ {} {} esM[λ %0] "a"
                 t[%a → %a]
                 h_tabs
  simp [TContext.isFresh, HMaps.find?] at h_tgen
  assumption
  done

def idFactory : LFunc ⟨Unit, Unit⟩ := {name := "id", typeArgs := ["a"],  inputs := [⟨"x", .ftvar "a"⟩], output := .ftvar "a"}

example : LExpr.HasType (LContext.default.addFactoryFunction idFactory) {} (.op () ⟨"id", ()⟩ none) t[∀a. %a → %a] := by
  apply (LExpr.HasType.top _ _ idFactory)
  · simp only [LContext.default, Lambda.LContext.addFactoryFunction]
    simp [Lambda.Factory.push_mem_match, idFactory]
  · rfl

example : LExpr.HasType (LContext.default.addFactoryFunction idFactory) {} (.op () ⟨"id", ()⟩ mty[int → int]) t[int → int] := by
  apply (LExpr.HasType.top_annotated _ _ idFactory _ t[∀a. %a → %a] _ [.int]) <;> try rfl
  · simp only [LContext.default, Lambda.LContext.addFactoryFunction]
    simp [Lambda.Factory.push_mem_match, idFactory]
  · simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe, List.zip, List.zipWith]
    rw [LMonoTy.subst_tcons]
    have h_find_a : HMaps.find? (Strata.Util.HMaps.ofScopes [[("a", LMonoTy.int)]]) "a"
        = some LMonoTy.int := by findOfScopes
    simp only [LMonoTys.subst_eq_map, List.map_cons, List.map_nil,
      LMonoTy.subst_ftvar_eq _ "a" LMonoTy.int h_find_a]
    rfl
  · exact AnnotCompat.of_eq

end Tests

---------------------------------------------------------------------
end LExpr
end -- public section
end Lambda
