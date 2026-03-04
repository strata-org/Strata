/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprTypeSpec

/-!
## Typed Denotational Semantics for Lambda

A variant of `DenotationalSemantics.lean` where the denotation function takes
the target monotype as a parameter and directly returns `denoteLMonoTyT ctx mty`,
rather than returning a sigma type `(mty : LMonoTy) × denoteLMonoTyT ctx mty`.

This assumes type information is available at each subexpression. We skip the
`app` case (since the argument type is not stored in the AST), and the `none`
cases for `abs` and `quant`.
-/

namespace Lambda
open Strata
open Std (ToFormat Format format)

/-! ## Type Substitutions -/

abbrev TySubstT := List (TyIdentifier × LMonoTy)

def applyTySubstT : TySubstT → LMonoTy → LMonoTy
  | σ, .ftvar x => (σ.lookup x).getD (.ftvar x)
  | _, .bitvec n => .bitvec n
  | σ, .tcons name args => .tcons name (args.map (applyTySubstT σ))

theorem applyTySubstT_id (ty: LMonoTy):
  applyTySubstT [] ty = ty := by
  induction ty <;> simp[applyTySubstT]
  rw [@List.map_congr_left _ _ _ _ id]
  . apply List.map_id
  . assumption

/-- Composing two applyTySubstT applications into one. -/
theorem applyTySubstT_comp (σ₁ σ₂ : TySubstT) (ty : LMonoTy) :
    applyTySubstT σ₂ (applyTySubstT σ₁ ty) =
    applyTySubstT (σ₁.map (fun (k, v) => (k, applyTySubstT σ₂ v)) ++ σ₂) ty := by
  induction ty with
  | ftvar x =>
    simp [applyTySubstT]
    induction σ₁ with
    | nil => simp [List.lookup, applyTySubstT]
    | cons hd tl ih =>
      simp [List.lookup, List.map]
      split <;> simp_all
  | bitvec n => simp [applyTySubstT]
  | tcons name args ih =>
    simp only [applyTySubstT]
    congr 1
    rw[List.map_map]
    apply List.map_congr_left
    intros a ha
    grind

theorem List_lookup_map_find [DecidableEq α] (x: α) (l: List (α × β)):
  List.lookup x l = Map.find? l x := by
  induction l
  case nil => simp[Map.find?]
  case cons h t IH =>
    simp[Map.find?, List.lookup]
    grind

theorem List_lookup_maps_find [DecidableEq α] (x: α) (l: List (α × β)):
  List.lookup x l = Maps.find? [l] x := by
  unfold Maps.find?
  rw[List_lookup_map_find]
  split <;> (try simp[Maps.find?]) <;> assumption

theorem List_lookup_maps_find' [DecidableEq α] (x: α) (l: List (List (α × β))):
  Maps.find? l x = List.lookup x (List.flatten l)  := by
  induction l
  case nil => simp[Maps.find?]
  case cons h t IH =>
    simp[Maps.find?, List.lookup_append]
    rw[List_lookup_map_find]
    split
    . rename_i heq; rw[heq]
      apply IH
    . rename_i heq; rw[heq]
      rfl

theorem List_map_find [DecidableEq α] (x: α) (l: List (α × β)) y:
  (List.lookup x l).getD y =
  match Map.find? l x with
  | some z => z
  | none => y := by
  rw[List_lookup_map_find]
  rfl

theorem List_maps_find [DecidableEq α] (x: α) (l: List (α × β)) y:
  (List.lookup x l).getD y =
  match Maps.find? [l] x with
  | some z => z
  | none => y := by
  rw[List_lookup_maps_find]
  rfl


theorem applyTySubstT_subst σ ty:
  applyTySubstT σ ty = LMonoTy.subst [σ] ty := by
  have Hemp: Subst.hasEmptyScopes [σ] = (List.isEmpty σ) := by
    cases σ<;> rfl
  cases he: (List.isEmpty σ)
  case true =>
    unfold LMonoTy.subst
    rw[Hemp, he]; simp
    have : σ = [] := by grind
    subst_vars
    apply applyTySubstT_id
  case false =>
    rw[he] at Hemp
    induction ty <;> simp[applyTySubstT, LMonoTy.subst, Hemp]
    case ftvar f =>
      rw [List_maps_find f σ (LMonoTy.ftvar f)]
      grind
    case tcons name args ih =>
      rw[LMonoTys.subst_eq_substLogic ]
      induction args
      case nil =>
        simp[LMonoTys.substLogic]
      case cons h t IH =>
        simp[LMonoTys.substLogic, Hemp]
        constructor
        . apply ih; grind
        . apply IH
          intros ty hty; apply ih; grind


-- theorem applyTySubstT_openFull vars tys ty:
--   tys.length = vars.length →
--   openFull


--  tys.length = ty_o.boundVars.length
-- σ : TySubstT := ty_o.boundVars.zip tys
-- ⊢ openFull ty_o tys = applyTySubstT σ ty_o.toMonoTypeUnsafe

-- tys.length = ty_o.boundVars.length
-- σ : TySubstT := ty_o.boundVars.zip tys
-- ⊢ openFull ty_o tys = instantiateSchemeT ty_o σ


theorem LMonoTy_subst_nil (mty : LMonoTy) : LMonoTy.subst [[]] mty = mty := by
  unfold LMonoTy.subst; simp [Subst.hasEmptyScopes, Map.isEmpty]

@[simp] theorem LTy_forAll_nil_toMonoTypeUnsafe (mty : LMonoTy) :
    (LTy.forAll [] mty).toMonoTypeUnsafe = mty := by rfl
def instantiateSchemeT (ty : LTy) (σ : TySubstT) : LMonoTy :=
  applyTySubstT σ ty.toMonoTypeUnsafe

/-! ## Monomorphic Typing Relation -/

namespace LExpr
open LTy

variable {T : LExprParams} [DecidableEq T.IDMeta]

inductive HasTypeT {T : LExprParams} [DecidableEq T.IDMeta] (C : LContext T) :
    TContext T.IDMeta → LExpr T.mono → LMonoTy → Prop where

  | tbool_const : ∀ Γ m b,
      C.knownTypes.containsName "bool" →
      HasTypeT C Γ (.boolConst m b) .bool

  | tint_const : ∀ Γ m n,
      C.knownTypes.containsName "int" →
      HasTypeT C Γ (.intConst m n) .int

  | treal_const : ∀ Γ m r,
      C.knownTypes.containsName "real" →
      HasTypeT C Γ (.realConst m r) .real

  | tstr_const : ∀ Γ m s,
      C.knownTypes.containsName "string" →
      HasTypeT C Γ (.strConst m s) .string

  | tbitvec_const : ∀ Γ m n b,
      C.knownTypes.containsName "bitvec" →
      HasTypeT C Γ (.bitvecConst m n b) (.bitvec n)

  | tvar : ∀ Γ m x o ty_scheme σ,
      Γ.types.find? x = some ty_scheme →
      HasTypeT C Γ (.fvar m x o) (instantiateSchemeT ty_scheme σ)

  | tabs : ∀ Γ m x x_mty e e_mty o,
      LExpr.fresh x e →
      HasTypeT C { Γ with types := Γ.types.insert x.fst (.forAll [] x_mty) }
        (LExpr.varOpen 0 x e) e_mty →
      o = none ∨ o = some x_mty →
      HasTypeT C Γ (.abs m o e) (.arrow x_mty e_mty)

  | tapp : ∀ Γ m e1 e2 t1 t2,
      HasTypeT C Γ e1 (.arrow t2 t1) →
      HasTypeT C Γ e2 t2 →
      HasTypeT C Γ (.app m e1 e2) t1

  | tif : ∀ Γ m c e1 e2 mty,
      HasTypeT C Γ c .bool →
      HasTypeT C Γ e1 mty →
      HasTypeT C Γ e2 mty →
      HasTypeT C Γ (.ite m c e1 e2) mty

  | teq : ∀ Γ m e1 e2 mty,
      HasTypeT C Γ e1 mty →
      HasTypeT C Γ e2 mty →
      HasTypeT C Γ (.eq m e1 e2) .bool

  | tquant : ∀ Γ m k tr tr_mty x x_mty e o,
      LExpr.fresh x e →
      HasTypeT C { Γ with types := Γ.types.insert x.fst (.forAll [] x_mty) }
        (LExpr.varOpen 0 x e) .bool →
      HasTypeT C { Γ with types := Γ.types.insert x.fst (.forAll [] x_mty) }
        (LExpr.varOpen 0 x tr) tr_mty →
      o = none ∨ o = some x_mty →
      HasTypeT C Γ (.quant m k o tr e) .bool

  | top : ∀ Γ m f op o ty_scheme σ,
      C.functions.find? (fun fn => fn.name == op) = some f →
      f.type = .ok ty_scheme →
      HasTypeT C Γ (.op m op o) (instantiateSchemeT ty_scheme σ)

/-!
## `HasType` implies `HasTypeT`

Because there is no let-polymorphism, every `HasType C Γ e ty` derivation
can be translated to `HasTypeT C Γ e ty.toMonoTypeUnsafe`. The key idea is
that a type substitution (from `tgen`/`tinst` chains) corresponds to the
`σ` parameter in `instantiateSchemeT` used by `HasTypeT`.
-/

-- /-- HasTypeT is closed under monotype substitution: substituting a type variable
--     in the result type can be absorbed by adjusting the σ in each tvar/top rule. -/
-- theorem HasTypeT_mono_subst {C : LContext T} {Γ : TContext T.IDMeta}
--     {e : LExpr T.mono} {mty : LMonoTy}
--     (h : HasTypeT C Γ e mty) (x : TyIdentifier) (xty : LMonoTy) :
--     HasTypeT C Γ e (LMonoTy.subst [[(x, xty)]] mty) := by
--   induction h with
--   | tbool_const Γ m b hk =>
--     unfold LMonoTy.subst
--     simp[Subst.hasEmptyScopes, Map.isEmpty]
--     rw[LMonoTys.subst_eq_substLogic]
--     simp[LMonoTys.substLogic]
--     constructor
--     assumption
--   | tint_const Γ m n hk =>
--     unfold LMonoTy.subst
--     simp[Subst.hasEmptyScopes, Map.isEmpty]
--     rw[LMonoTys.subst_eq_substLogic]
--     simp[LMonoTys.substLogic]
--     constructor
--     assumption
--   | treal_const Γ m r hk =>
--     unfold LMonoTy.subst
--     simp[Subst.hasEmptyScopes, Map.isEmpty]
--     rw[LMonoTys.subst_eq_substLogic]
--     simp[LMonoTys.substLogic]
--     constructor
--     assumption
--   | tstr_const Γ m s hk =>
--     unfold LMonoTy.subst
--     simp[Subst.hasEmptyScopes, Map.isEmpty]
--     rw[LMonoTys.subst_eq_substLogic]
--     simp[LMonoTys.substLogic]
--     constructor
--     assumption
--   | tbitvec_const Γ m n b hk =>
--     unfold LMonoTy.subst
--     simp[Subst.hasEmptyScopes, Map.isEmpty]
--     constructor
--     assumption
--   | tvar Γ m x' ty_scheme σ hfind =>
--     unfold instantiateSchemeT
--     rw[←applyTySubstT_subst, applyTySubstT_comp]
--     apply HasTypeT.tvar; assumption
--   | tvar_annotated Γ m x' ty_scheme σ mty' hfind hmty =>
--     subst hmty
--     unfold instantiateSchemeT
--     rw[←applyTySubstT_subst, applyTySubstT_comp]
--     apply HasTypeT.tvar_annotated _ _ _ ty_scheme
--     · exact hfind
--     · rfl
--   | tabs Γ m x' x_mty e e_mty o hfresh hbody ho ih =>
--     sorry
--   | tapp Γ m e1 e2 t1 t2 h1 h2 ih1 ih2 =>
--     sorry
--   | tif Γ m c e1 e2 mty' hc h1 h2 ihc ih1 ih2 =>
--     simp [LMonoTy.subst, LMonoTy.bool, LMonoTys.subst] at ihc
--     exact .tif _ _ _ _ _ _ ihc ih1 ih2
--   | teq Γ m e1 e2 mty' h1 h2 ih1 ih2 =>
--     simp [LMonoTy.subst, LMonoTy.bool, LMonoTys.subst]
--     exact .teq _ _ _ _ _ ih1 ih2
--   | tquant Γ m k tr tr_mty x' x_mty e o hfresh hbody htr ho ih_body ih_tr =>
--     simp [LMonoTy.subst, LMonoTy.bool, LMonoTys.subst]
--     exact .tquant _ _ _ _ _ _ _ _ hfresh ih_body ih_tr ho
--   | top Γ m f op ty_scheme σ hfind htype =>
--     exact .top _ _ f _ ty_scheme (σ.map (fun (k,v) => (k, LMonoTy.subst [[(x, xty)]] v)) ++ [(x, xty)]) hfind htype
--   | top_annotated Γ m f op ty_scheme σ mty' hfind htype hmty =>
--     exact .top_annotated _ _ f _ ty_scheme (σ.map (fun (k,v) => (k, LMonoTy.subst [[(x, xty)]] v)) ++ [(x, xty)]) _ hfind htype sorry

-- /-- Opening a type variable in an LTy preserves HasTypeT. -/
-- theorem HasTypeT_open_mono {C : LContext T} {Γ : TContext T.IDMeta}
--     {e : LExpr T.mono} {ty : LTy} {x : TyIdentifier} {xty : LMonoTy}
--     (h : HasTypeT C Γ e ty.toMonoTypeUnsafe) :
--     HasTypeT C Γ e (LTy.open x xty ty).toMonoTypeUnsafe := by
--   unfold LTy.open
--   cases ty with
--   | forAll vars lty =>
--     simp [LTy.toMonoTypeUnsafe] at *
--     split
--     · exact HasTypeT_mono_subst h x xty
--     · exact h

-- @[simp] theorem applyTySubstT_tcons_nil (σ : TySubstT) (name : String) :
--     applyTySubstT σ (.tcons name []) = .tcons name [] := by
--   simp [applyTySubstT]

-- theorem HasTypeT_mono_subst {C : LContext T} {Γ : TContext T.IDMeta}
--     {e : LExpr T.mono} {mty : LMonoTy}
--     (h : HasTypeT C Γ e mty) (x : TyIdentifier) (xty : LMonoTy) :
--     HasTypeT C Γ e (LMonoTy.subst [[(x, xty)]] mty) := by
--   induction h with
--   | tbool_const Γ m b hk =>
--     unfold LMonoTy.subst; simp [Subst.hasEmptyScopes, Map.isEmpty]
--     rw [LMonoTys.subst_eq_substLogic]; simp [LMonoTys.substLogic]
--     exact .tbool_const _ _ _ hk
--   | tint_const Γ m n hk =>
--     unfold LMonoTy.subst; simp [Subst.hasEmptyScopes, Map.isEmpty]
--     rw [LMonoTys.subst_eq_substLogic]; simp [LMonoTys.substLogic]
--     exact .tint_const _ _ _ hk
--   | treal_const Γ m r hk =>
--     unfold LMonoTy.subst; simp [Subst.hasEmptyScopes, Map.isEmpty]
--     rw [LMonoTys.subst_eq_substLogic]; simp [LMonoTys.substLogic]
--     exact .treal_const _ _ _ hk
--   | tstr_const Γ m s hk =>
--     unfold LMonoTy.subst; simp [Subst.hasEmptyScopes, Map.isEmpty]
--     rw [LMonoTys.subst_eq_substLogic]; simp [LMonoTys.substLogic]
--     exact .tstr_const _ _ _ hk
--   | tbitvec_const Γ m n b hk =>
--     unfold LMonoTy.subst; simp [Subst.hasEmptyScopes, Map.isEmpty]
--     exact .tbitvec_const _ _ _ _ hk
--   | tvar Γ m x' o ty_scheme σ hfind =>
--     unfold instantiateSchemeT
--     rw [← applyTySubstT_subst, applyTySubstT_comp]
--     exact .tvar _ _ _ _ ty_scheme _ hfind
--   | tabs Γ m x' x_mty e e_mty o hfresh hbody ho ih =>
--     unfold LMonoTy.arrow LMonoTy.subst
--     simp [Subst.hasEmptyScopes, Map.isEmpty]
--     rw [LMonoTys.subst_eq_substLogic]
--     simp [LMonoTys.substLogic]
--     simp[Subst.hasEmptyScopes, Map.isEmpty]
--     exact .tabs _ _ _ _ _ _ _ hfresh ih ho
--   | tapp Γ m e1 e2 t1 t2 h1 h2 ih1 ih2 =>
--     have : LMonoTy.subst [[(x, xty)]] (.arrow t2 t1) = .arrow (LMonoTy.subst [[(x, xty)]] t2) (LMonoTy.subst [[(x, xty)]] t1) := by
--       unfold LMonoTy.arrow LMonoTy.subst
--       simp [Subst.hasEmptyScopes, Map.isEmpty]
--       rw [LMonoTys.subst_eq_substLogic]; simp [LMonoTys.substLogic]
--     exact .tapp _ _ _ _ _ _ (this ▸ ih1) ih2
--   | tif Γ m c e1 e2 mty' hc h1 h2 ihc ih1 ih2 =>
--     unfold LMonoTy.subst at ihc
--     simp [Subst.hasEmptyScopes, Map.isEmpty] at ihc
--     rw [LMonoTys.subst_eq_substLogic] at ihc; simp [LMonoTys.substLogic] at ihc
--     unfold LMonoTy.subst; simp [Subst.hasEmptyScopes, Map.isEmpty]
--     rw [LMonoTys.subst_eq_substLogic]; simp [LMonoTys.substLogic]
--     exact .tif _ _ _ _ _ _ ihc ih1 ih2
--   | teq Γ m e1 e2 mty' h1 h2 ih1 ih2 =>
--     unfold LMonoTy.subst; simp [Subst.hasEmptyScopes, Map.isEmpty]
--     rw [LMonoTys.subst_eq_substLogic]; simp [LMonoTys.substLogic]
--     exact .teq _ _ _ _ _ ih1 ih2
--   | tquant Γ m k tr tr_mty x' x_mty e o hfresh hbody htr ho ih_body ih_tr =>
--     unfold LMonoTy.subst at ih_body
--     simp [Subst.hasEmptyScopes, Map.isEmpty] at ih_body
--     rw [LMonoTys.subst_eq_substLogic] at ih_body; simp [LMonoTys.substLogic] at ih_body
--     unfold LMonoTy.subst; simp [Subst.hasEmptyScopes, Map.isEmpty]
--     rw [LMonoTys.subst_eq_substLogic]; simp [LMonoTys.substLogic]
--     exact .tquant _ _ _ _ _ _ _ _ hfresh ih_body ih_tr ho
--   | top Γ m f op o ty_scheme σ hfind htype =>
--     unfold instantiateSchemeT
--     rw [← applyTySubstT_subst, applyTySubstT_comp]
--     exact .top _ _ f _ _ ty_scheme _ hfind htype

-- theorem HasTypeT_open_mono {C : LContext T} {Γ : TContext T.IDMeta}
--     {e : LExpr T.mono} {ty : LTy} {x : TyIdentifier} {xty : LMonoTy}
--     (h : HasTypeT C Γ e ty.toMonoTypeUnsafe) :
--     HasTypeT C Γ e (LTy.open x xty ty).toMonoTypeUnsafe := by
--   unfold LTy.open
--   cases ty with
--   | forAll vars lty =>
--     simp [LTy.toMonoTypeUnsafe] at *
--     split
--     · exact HasTypeT_mono_subst h x xty
--     · exact h

-- theorem HasType_implies_HasTypeT (C : LContext T) (Γ : TContext T.IDMeta)
--     (e : LExpr T.mono) (ty : LTy)
--     (h : LExpr.HasType C Γ e ty) :
--     HasTypeT C Γ e ty.toMonoTypeUnsafe := by
--     induction h <;> try solve | (constructor <;> assumption)
--     case tvar Γ' m' x' ty' Hfind =>
--       have Hty := (@HasTypeT.tvar _ _ C Γ' m' x' none ty' [] Hfind)
--       unfold instantiateSchemeT at Hty
--       rw[applyTySubstT_id] at Hty
--       exact Hty
--     case tvar_annotated Γ' m' x' ty_o ty_s tys Hfind Hlen Hopen =>
--       simp[LTy.toMonoTypeUnsafe]
--       let σ : TySubstT := List.zip ty_o.boundVars tys
--       have Hty : ty_s = instantiateSchemeT ty_o σ := by
--         subst_vars; unfold instantiateSchemeT LTy.openFull; rw [applyTySubstT_subst]
--       rw [Hty]
--       apply HasTypeT.tvar
--       apply Hfind
--     case tabs Γ m x x_ty e e_ty o Hfresh hx he Hty Ho IH =>
--       simp[LTy.toMonoTypeUnsafe]
--       apply HasTypeT.tabs <;> try assumption
--       have he': e_ty.toMonoTypeUnsafe = e_ty.toMonoType he := by rfl
--       rw[←he']
--       have Hx : x_ty = (LTy.forAll [] (x_ty.toMonoType hx)) := by
--         cases x_ty; simp[LTy.isMonoType, LTy.boundVars] at hx
--         subst_vars; rfl
--       rw[Hx] at IH
--       exact IH
--     case tinst Γ e ty e_ty x x_ty Hty Hopen IH =>
--       subst_vars
--       exact HasTypeT_open_mono IH
--     case tgen Γ e a ty Hty Hinfv IH =>
--       unfold LTy.close; cases a; simp[LTy.toMonoTypeUnsafe] at *; assumption
--     case tquant Γ m k tr tr_ty x x_ty e o Hfresh hx Hbody Htr Ho IH_body IH_tr =>
--       simp[LTy.toMonoTypeUnsafe]
--       apply HasTypeT.tquant <;> try assumption
--       . have Hx : x_ty = (LTy.forAll [] (x_ty.toMonoType hx)) := by
--           cases x_ty; simp[LTy.isMonoType, LTy.boundVars] at hx
--           subst_vars; rfl
--         rw[Hx] at IH_body
--         exact IH_body
--       . have Hx : x_ty = (LTy.forAll [] (x_ty.toMonoType hx)) := by
--           cases x_ty; simp[LTy.isMonoType, LTy.boundVars] at hx
--           subst_vars; rfl
--         rw[Hx] at IH_tr
--         exact IH_tr
--     case top Γ' m' f op ty' Hfind Htype =>
--       have Hty := (@HasTypeT.top _ _ C Γ' m' f op none ty' [] Hfind Htype)
--       unfold instantiateSchemeT at Hty
--       rw[applyTySubstT_id] at Hty
--       exact Hty
--     case top_annotated Γ' m' f op ty_o ty_s tys Hfind Htype Hlen Hopen =>
--       simp[LTy.toMonoTypeUnsafe]
--       let σ : TySubstT := List.zip ty_o.boundVars tys
--       have Hty : ty_s = instantiateSchemeT ty_o σ := by
--         subst_vars; unfold instantiateSchemeT LTy.openFull; rw [applyTySubstT_subst]
--       rw [Hty]
--       apply HasTypeT.top
--       apply Hfind
--       apply Htype


/-!
## Generalized proof: carry σ, substitute only monotype context entries

The key insight: `tabs`/`tquant` only add monotype schemes `forAll [] mty`,
while polymorphic schemes come from the initial context. By substituting σ
only into monotype entries, `tvar_annotated` sees the original polymorphic
scheme (no commutation problem), while `tabs` gets the substituted monotype
(context matches).
-/

/-- Apply a `TySubstT` to a single `LTy`, but only if it is a monotype scheme. -/
def applyTySubstTLTy (σ : TySubstT) (ty : LTy) : LTy :=
  match ty with
  | .forAll [] mty => .forAll [] (applyTySubstT σ mty)
  | other => other

/-- Apply a `TySubstT` to every type in a `Maps`, only substituting monotype entries. -/
def monoSubstMaps (σ : TySubstT) : Maps (Identifier T.IDMeta) LTy → Maps (Identifier T.IDMeta) LTy
  | [] => []
  | m :: rest => m.map (fun (k, ty) => (k, applyTySubstTLTy σ ty)) :: monoSubstMaps σ rest

/-- Apply a `TySubstT` to a `TContext`, only substituting monotype entries. -/
def monoSubstCtx (σ : TySubstT) (Γ : TContext T.IDMeta) : TContext T.IDMeta :=
  { Γ with types := monoSubstMaps σ Γ.types }

omit [DecidableEq T.IDMeta] in
@[simp] theorem applyTySubstTLTy_nil (ty : LTy) : applyTySubstTLTy [] ty = ty := by
  cases ty with | forAll vars mty =>
  simp [applyTySubstTLTy]; split <;> simp_all [applyTySubstT_id]

omit [DecidableEq T.IDMeta] in
@[simp] theorem monoSubstMaps_nil :
    monoSubstMaps (T := T) [] types = types := by
  induction types with
  | nil => simp [monoSubstMaps]
  | cons m rest ih =>
    simp only [monoSubstMaps, ih]; congr 1
    rw [@List.map_congr_left _ _ _ _ id]
    · simp
    · intro nty _; rcases nty with ⟨n, ty⟩; simp [id, applyTySubstTLTy_nil]

omit [DecidableEq T.IDMeta] in
@[simp] theorem monoSubstCtx_nil :
    monoSubstCtx (T := T) [] Γ = Γ := by
  simp [monoSubstCtx]

-- Mono entries are substituted
theorem monoSubstMaps_find_mono (σ : TySubstT) (types : Maps (Identifier T.IDMeta) LTy)
    (x : Identifier T.IDMeta) (mty : LMonoTy) :
    types.find? x = some (.forAll [] mty) →
    (monoSubstMaps σ types).find? x = some (.forAll [] (applyTySubstT σ mty)) := by
  sorry

-- Poly entries are unchanged
theorem monoSubstMaps_find_poly (σ : TySubstT) (types : Maps (Identifier T.IDMeta) LTy)
    (x : Identifier T.IDMeta) (ty : LTy) (h : ty.boundVars ≠ []) :
    types.find? x = some ty →
    (monoSubstMaps σ types).find? x = some ty := by
  sorry

-- Insert a mono entry into a monoSubst'd context
theorem monoSubstMaps_insert (σ : TySubstT) (types : Maps (Identifier T.IDMeta) LTy)
    (x : Identifier T.IDMeta) (mty : LMonoTy) :
    monoSubstMaps σ (types.insert x (.forAll [] mty)) =
    (monoSubstMaps σ types).insert x (.forAll [] (applyTySubstT σ mty)) := by
  sorry

theorem HasType_implies_HasTypeT' (C : LContext T) (Γ : TContext T.IDMeta)
    (e : LExpr T.mono) (ty : LTy) (σ : TySubstT)
    (h : LExpr.HasType C Γ e ty) :
    HasTypeT C (monoSubstCtx σ Γ) e (applyTySubstT σ ty.toMonoTypeUnsafe) := by
    induction h generalizing σ with
    | tbool_const Γ' m b hk =>
      simp [LTy.toMonoTypeUnsafe, LMonoTy.bool, applyTySubstT]
      exact .tbool_const _ _ _ hk
    | tint_const Γ' m n hk =>
      simp [LTy.toMonoTypeUnsafe, LMonoTy.int, applyTySubstT]
      exact .tint_const _ _ _ hk
    | treal_const Γ' m r hk =>
      simp [LTy.toMonoTypeUnsafe, LMonoTy.real, applyTySubstT]
      exact .treal_const _ _ _ hk
    | tstr_const Γ' m s hk =>
      simp [LTy.toMonoTypeUnsafe, LMonoTy.string, applyTySubstT]
      exact .tstr_const _ _ _ hk
    | tbitvec_const Γ' m n b hk =>
      simp [LTy.toMonoTypeUnsafe, LMonoTy.bitvec, applyTySubstT]
      exact .tbitvec_const _ _ _ _ hk
    | tvar Γ' m x' ty' Hfind =>
      cases ty' with | forAll vars mty =>
      simp [LTy.toMonoTypeUnsafe]
      cases vars with
      | nil =>
        have Hfind' := monoSubstMaps_find_mono σ Γ'.types x' mty Hfind
        have Hty := @HasTypeT.tvar _ _ C (monoSubstCtx σ Γ') m x' none (.forAll [] (applyTySubstT σ mty)) [] Hfind'
        unfold instantiateSchemeT at Hty; rw [applyTySubstT_id] at Hty; exact Hty
      | cons v vs =>
        have Hfind' := monoSubstMaps_find_poly σ Γ'.types x' (.forAll (v :: vs) mty) (by simp [LTy.boundVars]) Hfind
        have Hty := @HasTypeT.tvar _ _ C (monoSubstCtx σ Γ') m x' none (.forAll (v :: vs) mty) σ Hfind'
        unfold instantiateSchemeT at Hty; exact Hty
    | tvar_annotated Γ' m x' ty_o ty_s tys Hfind Hlen Hopen =>
      simp [LTy.toMonoTypeUnsafe]
      cases ty_o with | forAll vars mty =>
      cases vars with
      | nil =>
        -- mono scheme: substituted in context
        have Hfind' := monoSubstMaps_find_mono σ Γ'.types x' mty Hfind
        -- tys = [] since boundVars = []
        simp [LTy.boundVars] at Hlen; simp [Hlen] at Hopen
        -- ty_s = openFull (forAll [] mty) [] = LMonoTy.subst [[]] mty = mty
        have Hopen' : ty_s = mty := by
          simp [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe] at Hopen
          rw [←Hopen]; exact LMonoTy_subst_nil mty
        subst Hopen'
        have Hty := @HasTypeT.tvar _ _ C (monoSubstCtx σ Γ') m x' (some ty_s) (.forAll [] (applyTySubstT σ ty_s)) [] Hfind'
        unfold instantiateSchemeT at Hty; rw [applyTySubstT_id] at Hty;
        rw[LTy_forAll_nil_toMonoTypeUnsafe] at Hty
        exact Hty
      | cons v vs =>
        -- poly scheme: unchanged in context
        have Hfind' := monoSubstMaps_find_poly σ Γ'.types x' (.forAll (v :: vs) mty) (by simp [LTy.boundVars]) Hfind
        let σ' : TySubstT := List.zip (v :: vs) tys
        have Hgoal : applyTySubstT σ ty_s = instantiateSchemeT (.forAll (v :: vs) mty) (σ'.map (fun (k, t) => (k, applyTySubstT σ t)) ++ σ) := by
          subst_vars
          unfold instantiateSchemeT LTy.openFull LTy.toMonoTypeUnsafe LTy.boundVars
          simp only [← applyTySubstT_subst]
          rw [← applyTySubstT_comp]
        rw [Hgoal]
        exact .tvar _ _ _ _ _ _ Hfind'
    | tabs Γ' m x x_ty e e_ty o Hfresh hx he Hty Ho IH =>
      sorry
    | tapp Γ' m e1 e2 t1 t2 h1 h2 Hty1 Hty2 IH1 IH2 =>
      simp only [LTy.toMonoTypeUnsafe, LMonoTy.arrow, LTy.toMonoType, applyTySubstT] at IH1 ⊢
      exact .tapp _ _ _ _ _ _ (IH1 σ) (IH2 σ)
    | tinst Γ' e ty' e_ty x x_ty Hty Hopen IH =>
      sorry
    | tgen Γ' e a ty' Hty Hfresh Hinfv IH =>
      unfold LTy.close; cases ty' with | forAll vars lty =>
      simp [LTy.toMonoTypeUnsafe] at *; exact IH σ
    | tif Γ' m c e1 e2 ty' Hc H1 H2 IHc IH1 IH2 =>
      have IHc' := IHc σ
      simp [LTy.toMonoTypeUnsafe, LMonoTy.bool, applyTySubstT] at IHc'
      exact .tif _ _ _ _ _ _ IHc' (IH1 σ) (IH2 σ)
    | teq Γ' m e1 e2 ty' H1 H2 IH1 IH2 =>
      simp only [LTy.toMonoTypeUnsafe, LMonoTy.bool, applyTySubstT]
      exact .teq _ _ _ _ _ (IH1 σ) (IH2 σ)
    | tquant Γ' m k tr tr_ty x x_ty e o Hfresh hx Hbody Htr Ho IH_body IH_tr =>
      sorry
    | top Γ' m' f op ty' Hfind Htype =>
      sorry
    | top_annotated Γ' m' f op ty_o ty_s tys Hfind Htype Hlen Hopen =>
      sorry

/-- The original theorem as a corollary. -/
theorem HasType_implies_HasTypeT₂ (C : LContext T) (Γ : TContext T.IDMeta)
    (e : LExpr T.mono) (ty : LTy)
    (h : LExpr.HasType C Γ e ty) :
    HasTypeT C Γ e ty.toMonoTypeUnsafe := by
  have H := HasType_implies_HasTypeT' C Γ e ty [] h
  simp at H; rw [applyTySubstT_id] at H; exact H

/-! ## Arrow decomposition -/

def asArrowT (mty : LMonoTy) : Option (LMonoTy × LMonoTy) :=
  match mty with
  | .tcons "arrow" [t1, t2] => some (t1, t2)
  | _ => none

theorem asArrowT_some {mty t1 t2 : LMonoTy} (h : asArrowT mty = some (t1, t2)) :
    mty = .arrow t1 t2 := by
  simp only [asArrowT] at h; split at h <;> simp_all; rfl

theorem asArrowT_arrow {t1 t2 : LMonoTy}: asArrowT (t1.arrow t2) = some (t1, t2)
  := by rfl

theorem asArrowT_none {mty : LMonoTy} (h : asArrowT mty = none) :
    ∀ t1 t2, mty ≠ .arrow t1 t2 := by
  intro t1 t2; unfold LMonoTy.arrow; simp only [asArrowT] at h; split at h <;> simp_all

/-! ## Denotation of Monotypes -/

abbrev TypeContextT.{u} := List (TyIdentifier × Type u)

def denoteLMonoTyT.{u} : TypeContextT.{u} → LMonoTy → Type u
  | _, .tcons "bool" [] => ULift Bool
  | _, .tcons "int" [] => ULift Int
  | _, .tcons "string" [] => ULift String
  | _, .tcons "real" [] => ULift Rat
  | _, .bitvec n => ULift (BitVec n)
  | ctx, .tcons "arrow" [t1, t2] => denoteLMonoTyT ctx t1 → denoteLMonoTyT ctx t2
  | ctx, .ftvar x => (ctx.lookup x).getD (ULift Empty)
  | _, .tcons _ _ => ULift Empty

/-! ## Valuation -/

abbrev ValuationT.{u} (ctx : TypeContextT.{u}) :=
  (name : String) → (mty : LMonoTy) → denoteLMonoTyT ctx mty

/-- Extend a valuation with a new binding. When the name and type match,
    return the given value; otherwise fall through to the old valuation. -/
def updateVal {ctx : TypeContextT} (val : ValuationT ctx)
    (name : String) (mty : LMonoTy) (v : denoteLMonoTyT ctx mty) :
    ValuationT ctx :=
  fun n mty' =>
    if name == n then
      if h : mty = mty' then h ▸ v else val n mty'
    else val n mty'

/-- Semantic interpretation of operators. Maps operator name and monotype to a value. -/
abbrev OpInterpretation.{u} (ctx : TypeContextT.{u}) :=
  (name : String) → (mty : LMonoTy) → denoteLMonoTyT ctx mty

/-! ## Relational Denotation (`DenotesT`) -/

inductive DenotesT {T : LExprParams} [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    (C : LContext T) (ctx : TypeContextT)
    (interp : OpInterpretation ctx) :
    ValuationT ctx → LExpr T.mono → (mty : LMonoTy) → denoteLMonoTyT ctx mty → Prop where

  | dbool : ∀ val m b,
      DenotesT C ctx interp val (.boolConst m b) .bool ⟨b⟩

  | dint : ∀ val m i,
      DenotesT C ctx interp val (.intConst m i) .int ⟨i⟩

  | dstr : ∀ val m s,
      DenotesT C ctx interp val (.strConst m s) .string ⟨s⟩

  | dbitvec : ∀ val m n bv,
      DenotesT C ctx interp val (.bitvecConst m n bv) (.bitvec n) ⟨bv⟩

  | dreal : ∀ val m r,
      DenotesT C ctx interp val (.realConst m r) .real ⟨r⟩

  | dite_true : ∀ val m c t e mty (vc : denoteLMonoTyT ctx .bool) (vt : denoteLMonoTyT ctx mty),
      DenotesT C ctx interp val c .bool vc →
      vc.down = true →
      DenotesT C ctx interp val t mty vt →
      DenotesT C ctx interp val (.ite m c t e) mty vt

  | dite_false : ∀ val m c t e mty (vc : denoteLMonoTyT ctx .bool) (ve : denoteLMonoTyT ctx mty),
      DenotesT C ctx interp val c .bool vc →
      vc.down = false →
      DenotesT C ctx interp val e mty ve →
      DenotesT C ctx interp val (.ite m c t e) mty ve

  -- | dapp : ∀ val m e1 e2 t1 t2
  --     (vf : denoteLMonoTyT ctx (.arrow t2 t1)) (va : denoteLMonoTyT ctx t2),
  --     DenotesT C ctx interp val e1 (.arrow t2 t1) vf →
  --     DenotesT C ctx interp val e2 t2 va →
  --     DenotesT C ctx interp val (.app m e1 e2) t1 (vf va)

  | dabs : ∀ val m x_mty e_mty e (y : IdentT LMonoTy T.IDMeta)
      (f : denoteLMonoTyT ctx x_mty → denoteLMonoTyT ctx e_mty),
      LExpr.fresh y e →
      y.snd.isSome = true →
      (∀ a, DenotesT C ctx interp (updateVal val y.fst.name x_mty a) (LExpr.varOpen 0 y e) e_mty (f a)) →
      DenotesT C ctx interp val (.abs m (some x_mty) e) (.arrow x_mty e_mty) f

  | dquant_all : ∀ val m x_mty tr e (y : IdentT LMonoTy T.IDMeta)
      (bodyBool : denoteLMonoTyT ctx x_mty → Bool),
      LExpr.fresh y e →
      y.snd.isSome = true →
      (∀ d, DenotesT C ctx interp (updateVal val y.fst.name x_mty d) (LExpr.varOpen 0 y e) .bool ⟨bodyBool d⟩) →
      (∀ d, bodyBool d = true) →
      DenotesT C ctx interp val (.quant m .all (some x_mty) tr e) .bool ⟨true⟩

  | dquant_all_false : ∀ val m x_mty tr e (y : IdentT LMonoTy T.IDMeta)
      (bodyBool : denoteLMonoTyT ctx x_mty → Bool),
      LExpr.fresh y e →
      y.snd.isSome = true →
      (∀ d, DenotesT C ctx interp (updateVal val y.fst.name x_mty d) (LExpr.varOpen 0 y e) .bool ⟨bodyBool d⟩) →
      ¬(∀ d, bodyBool d = true) →
      DenotesT C ctx interp val (.quant m .all (some x_mty) tr e) .bool ⟨false⟩

  | dquant_exist : ∀ val m x_mty tr e (y : IdentT LMonoTy T.IDMeta)
      (bodyBool : denoteLMonoTyT ctx x_mty → Bool),
      LExpr.fresh y e →
      y.snd.isSome = true →
      (∀ d, DenotesT C ctx interp (updateVal val y.fst.name x_mty d) (LExpr.varOpen 0 y e) .bool ⟨bodyBool d⟩) →
      (∃ d, bodyBool d = true) →
      DenotesT C ctx interp val (.quant m .exist (some x_mty) tr e) .bool ⟨true⟩

  | dquant_exist_false : ∀ val m x_mty tr e (y : IdentT LMonoTy T.IDMeta)
      (bodyBool : denoteLMonoTyT ctx x_mty → Bool),
      LExpr.fresh y e →
      y.snd.isSome = true →
      (∀ d, DenotesT C ctx interp (updateVal val y.fst.name x_mty d) (LExpr.varOpen 0 y e) .bool ⟨bodyBool d⟩) →
      ¬(∃ d, bodyBool d = true) →
      DenotesT C ctx interp val (.quant m .exist (some x_mty) tr e) .bool ⟨false⟩

  | dfvar : ∀ val m (name : Identifier T.IDMeta) ann mty,
      DenotesT C ctx interp val (.fvar m name ann) mty (val name.name mty)

  | dop : ∀ val m (name : Identifier T.IDMeta) args mty,
      DenotesT C ctx interp val (.op m name args) mty (interp name.name mty)

/-! ## Type-recovery lemmas -/

theorem HasTypeT.boolConst_ty {C : LContext T} {Γ m b mty}
    (h : HasTypeT C Γ (.boolConst m b) mty) : mty = .bool := by
  cases h; rfl

theorem HasTypeT.intConst_ty {C : LContext T} {Γ m n mty}
    (h : HasTypeT C Γ (.intConst m n) mty) : mty = .int := by
  cases h; rfl

theorem HasTypeT.realConst_ty {C : LContext T} {Γ m r mty}
    (h : HasTypeT C Γ (.realConst m r) mty) : mty = .real := by
  cases h; rfl

theorem HasTypeT.strConst_ty {C : LContext T} {Γ m s mty}
    (h : HasTypeT C Γ (.strConst m s) mty) : mty = .string := by
  cases h; rfl

theorem HasTypeT.bitvecConst_ty {C : LContext T} {Γ m n bv mty}
    (h : HasTypeT C Γ (.bitvecConst m n bv) mty) : mty = .bitvec n := by
  cases h; rfl

theorem HasTypeT.ite_cond {C : LContext T} {Γ m} {c t e : LExpr T.mono} {mty}
    (h : HasTypeT C Γ (.ite m c t e) mty) : HasTypeT C Γ c .bool := by
  cases h; assumption

theorem HasTypeT.ite_then {C : LContext T} {Γ m} {c t e : LExpr T.mono} {mty}
    (h : HasTypeT C Γ (.ite m c t e) mty) : HasTypeT C Γ t mty := by
  cases h; assumption

theorem HasTypeT.ite_else {C : LContext T} {Γ m} {c t e : LExpr T.mono} {mty}
    (h : HasTypeT C Γ (.ite m c t e) mty) : HasTypeT C Γ e mty := by
  cases h; assumption

theorem HasTypeT.eq_ty {C : LContext T} {Γ m} {e1 e2 : LExpr T.mono} {mty}
    (h : HasTypeT C Γ (.eq m e1 e2) mty) : mty = .bool := by
  cases h; rfl

theorem HasTypeT.eq_lhs {C : LContext T} {Γ m} {e1 e2 : LExpr T.mono} {mty}
    (h : HasTypeT C Γ (.eq m e1 e2) mty) : ∃ mty', HasTypeT C Γ e1 mty' := by
  cases h; exact ⟨_, ‹_›⟩

theorem HasTypeT.eq_rhs {C : LContext T} {Γ m} {e1 e2 : LExpr T.mono} {mty}
    (h : HasTypeT C Γ (.eq m e1 e2) mty) : ∃ mty', HasTypeT C Γ e2 mty' := by
  cases h; exact ⟨_, ‹_›⟩

theorem HasTypeT.quant_ty {C : LContext T} {Γ m k o} {tr e : LExpr T.mono} {mty}
    (h : HasTypeT C Γ (.quant m k o tr e) mty) : mty = .bool := by
  cases h; rfl

theorem HasTypeT.abs_asArrow {C : LContext T} {Γ m o} {e : LExpr T.mono} {mty}
    (h : HasTypeT C Γ (.abs m o e) mty) : asArrowT mty ≠ none := by
  cases h with
  | tabs _ _ _ x_mty _ e_mty _ _ _ => simp [asArrowT, LMonoTy.arrow]

/-- Generate `n` distinct candidate names: `_x0`, `_x1`, ... -/
private def candidates [Inhabited T.IDMeta] (n : Nat) (ty : LMonoTy) : List (IdentT LMonoTy T.IDMeta) :=
  (List.range n).map fun i => (⟨s!"_x{i}", default⟩, some ty)

/-- Compute a fresh `IdentT` for an expression by pigeonhole:
    generate `|freeVars| + 1` candidates; at least one has a name not among
    the free variable names. -/
def findFresh [Inhabited T.IDMeta] [DecidableEq T.IDMeta] (e : LExpr T.mono) (ty : LMonoTy) :
    IdentT LMonoTy T.IDMeta :=
  let fvNames := (LExpr.freeVars e).map Prod.fst
  let cands := candidates (fvNames.length + 1) ty
  match cands.find? (fun c => c.fst ∉ fvNames) with
  | some y => y
  | none => (⟨"_unreachable", default⟩, some ty)  -- unreachable by pigeonhole

theorem findFresh_fresh [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    (e : LExpr T.mono) (ty : LMonoTy) : LExpr.fresh (findFresh e ty) e := by
  sorry

theorem findFresh_isSome [Inhabited T.IDMeta]
    (e : LExpr T.mono) (ty : LMonoTy) : (findFresh e ty).snd.isSome = true := by
  simp only [findFresh, candidates]
  split
  . rename_i Hfind
    have Hex := List.exists_of_mem_map (List.mem_of_find?_eq_some Hfind)
    rcases Hex with ⟨a, ⟨ a1, a2⟩ ⟩
    subst_vars; rfl
  . rfl

/-! ## Renaming lemma -/

theorem HasTypeT.rename_fresh
    {C : LContext T} {Γ : TContext T.IDMeta}
    {e : LExpr T.mono} {mty x_mty : LMonoTy}
    {x y : IdentT LMonoTy T.IDMeta}
    (hfx : LExpr.fresh x e) (hfy : LExpr.fresh y e)
    (h : HasTypeT C { Γ with types := Γ.types.insert x.fst (.forAll [] x_mty) }
      (LExpr.varOpen 0 x e) mty) :
    HasTypeT C { Γ with types := Γ.types.insert y.fst (.forAll [] x_mty) }
      (LExpr.varOpen 0 y e) mty := by sorry


theorem HasTypeT.abs_body
    {C : LContext T} {Γ m} {e : LExpr T.mono} {x_mty : LMonoTy} {mty : LMonoTy}
    {t1 t2 : LMonoTy}
    (h : HasTypeT C Γ (.abs m (some x_mty) e) mty)
    (harr : asArrowT mty = some (t1, t2))
    (y : IdentT LMonoTy T.IDMeta) (hfy : LExpr.fresh y e) :
    HasTypeT C { Γ with types := Γ.types.insert y.fst (.forAll [] t1) }
      (LExpr.varOpen 0 y e) t2 := by
  cases h with
  | tabs _ _ x' _ _ e_mty' _ hfresh hbody ho =>
    have heq := asArrowT_some harr
    simp only [LMonoTy.arrow] at heq; cases heq
    exact HasTypeT.rename_fresh hfresh hfy hbody

theorem HasTypeT.abs_x_mty {C : LContext T} {Γ m} {e : LExpr T.mono}
    {x_mty : LMonoTy} {mty : LMonoTy} {t1 t2 : LMonoTy}
    (h : HasTypeT C Γ (.abs m (some x_mty) e) mty)
    (harr : asArrowT mty = some (t1, t2)) : x_mty = t1 := by
  cases h with
  | tabs _ _ _ x_mty' _ e_mty' _ _ _ ho =>
    have := asArrowT_some harr
    simp only [LMonoTy.arrow] at this
    cases this
    cases ho <;> grind

theorem HasTypeT.quant_body
    {C : LContext T} {Γ m k} {x_mty : LMonoTy} {tr e : LExpr T.mono} {mty}
    (h : HasTypeT C Γ (.quant m k (some x_mty) tr e) mty)
    (y : IdentT LMonoTy T.IDMeta) (hfy : LExpr.fresh y e) :
    HasTypeT C { Γ with types := Γ.types.insert y.fst (.forAll [] x_mty) }
      (LExpr.varOpen 0 y e) .bool := by
  have := h.quant_ty; subst this
  cases h
  case tquant tr_mty x x_mty' Hopt Htr Hfresh  Hbody =>
    cases Hopt
    · grind
    · rename_i Hopt; cases Hopt
      exact (HasTypeT.rename_fresh Hfresh hfy Hbody)

/-! ## Typed denotation function

Match only on the expression. Use type-recovery lemmas to obtain type
equalities, and `asArrowT` to decompose arrow types in data context.
-/

inductive annotated {T : LExprParams} : LExpr T.mono → Prop where
  | ann_const : ∀ m c, annotated (.const m c)
  | ann_fvar : ∀ m name ty, annotated (.fvar m name (some ty))
  | ann_bvar : ∀ m x, annotated (.bvar m x)
  | ann_op : ∀ m name ty, annotated (.op m name (some ty))
  | ann_abs : ∀ m ty e, annotated e → annotated (.abs m (some ty) e)
  | ann_quant : ∀ m k ty tr e, annotated tr → annotated e → annotated (.quant m k (some ty) tr e)
  | ann_ite : ∀ m c t e, annotated c → annotated t → annotated e → annotated (.ite m c t e)
  -- | ann_eq : ∀ m e1 e2, annotated e1 → annotated e2 → annotated (.eq m e1 e2)
  -- | ann_app : ∀ m e1 e2, annotated e1 → annotated e2 → annotated (.app m e1 e2)

theorem annotated.ite_cond {T : LExprParams} {m} {c t e : LExpr T.mono} (h : annotated (.ite m c t e)) : annotated c := by cases h; assumption
theorem annotated.ite_then {T : LExprParams} {m} {c t e : LExpr T.mono} (h : annotated (.ite m c t e)) : annotated t := by cases h; assumption
theorem annotated.ite_else {T : LExprParams} {m} {c t e : LExpr T.mono} (h : annotated (.ite m c t e)) : annotated e := by cases h; assumption
theorem annotated.abs_body {T : LExprParams} {m} {ty : T.mono.TypeType} {e : LExpr T.mono} (h : annotated (.abs m (some ty) e)) : annotated e := by cases h; assumption
theorem annotated.quant_body {T : LExprParams} {m} {k} {ty : T.mono.TypeType} {tr e : LExpr T.mono} (h : annotated (.quant m k (some ty) tr e)) : annotated e := by cases h; assumption

theorem annotated_varOpen {T : LExprParams} [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    {e : LExpr T.mono} {x' : IdentT LMonoTy T.IDMeta} {k : Nat}
    (he : annotated e) (hx : x'.snd.isSome = true) :
    annotated (LExpr.varOpen k x' e) := by
  induction he generalizing k with
  | ann_const => unfold LExpr.varOpen LExpr.substK; exact .ann_const _ _
  | ann_fvar => unfold LExpr.varOpen LExpr.substK; exact .ann_fvar _ _ _
  | ann_bvar m x =>
    unfold LExpr.varOpen LExpr.substK
    split
    · cases x' with | mk fst snd =>
      cases snd with
      | some ty => exact .ann_fvar _ _ _
      | none => simp at hx
    · exact .ann_bvar _ _
  | ann_op => unfold LExpr.varOpen LExpr.substK; exact .ann_op _ _ _
  | ann_abs _ _ _ _ ih =>
    show annotated (LExpr.varOpen k x' (.abs _ _ _))
    unfold LExpr.varOpen LExpr.substK; exact .ann_abs _ _ _ ih
  | ann_quant _ _ _ _ _ _ _ ih_tr ih_e =>
    show annotated (LExpr.varOpen k x' (.quant _ _ _ _ _))
    unfold LExpr.varOpen LExpr.substK; exact .ann_quant _ _ _ _ _ ih_tr ih_e
  | ann_ite _ _ _ _ _ _ _ ih_c ih_t ih_e =>
    show annotated (LExpr.varOpen k x' (.ite _ _ _ _))
    unfold LExpr.varOpen LExpr.substK; exact .ann_ite _ _ _ _ ih_c ih_t ih_e
  -- | ann_eq _ _ _ _ _ ih1 ih2 =>
  --   show annotated (LExpr.varOpen k x' (.eq _ _ _))
  --   unfold LExpr.varOpen LExpr.substK; exact .ann_eq _ _ _ ih1 ih2
  -- | ann_app _ _ _ _ _ ih1 ih2 =>
  --   show annotated (LExpr.varOpen k x' (.app _ _ _))
  --   unfold LExpr.varOpen LExpr.substK; exact .ann_app _ _ _ ih1 ih2

noncomputable def denoteLExprT
    {T : LExprParams}
    [Inhabited T.IDMeta]
    [DecidableEq T.IDMeta]
    (C : LContext T)
    (Γ : TContext T.IDMeta)
    (ctx : TypeContextT)
    (interp : OpInterpretation ctx)
    (val : ValuationT ctx) :
    (e : LExpr T.mono) →
    (mty : LMonoTy) →
    HasTypeT C Γ e mty →
    annotated e →
    denoteLMonoTyT ctx mty

  | .boolConst _ b, mty, hwt, _ =>
    hwt.boolConst_ty ▸ (⟨b⟩ : denoteLMonoTyT ctx .bool)

  | .intConst _ i, mty, hwt, _ =>
    hwt.intConst_ty ▸ (⟨i⟩ : denoteLMonoTyT ctx .int)

  | .strConst _ s, mty, hwt, _ =>
    hwt.strConst_ty ▸ (⟨s⟩ : denoteLMonoTyT ctx .string)

  | .bitvecConst _ n bv, mty, hwt, _ =>
    hwt.bitvecConst_ty ▸ (⟨bv⟩ : denoteLMonoTyT ctx (.bitvec n))

  | .realConst _ r, mty, hwt, _ =>
    hwt.realConst_ty ▸ (⟨r⟩ : denoteLMonoTyT ctx .real)

  | .ite _ c t e, mty, hwt, ha =>
    let vc := denoteLExprT C Γ ctx interp val c .bool hwt.ite_cond ha.ite_cond
    let vt := denoteLExprT C Γ ctx interp val t mty hwt.ite_then ha.ite_then
    let ve := denoteLExprT C Γ ctx interp val e mty hwt.ite_else ha.ite_else
    if vc.down then vt else ve

  | .abs _ (some x_mty) e, mty, hwt, ha =>
    match harr : asArrowT mty with
    | some (t1, t2) =>
      let heq := asArrowT_some harr
      -- have hx : x_mty = t1 := by
      --   cases hwt
      --   simp[asArrowT] at harr

      -- let hx := hwt.abs_x_mty harr
      let y := findFresh e t1
      heq ▸
        let Γ' := { Γ with types := Γ.types.insert y.fst (.forAll [] t1) }
        (fun (a : denoteLMonoTyT ctx t1) =>
          let val' := updateVal val y.fst.name t1 a
          denoteLExprT C Γ' ctx interp val' (LExpr.varOpen 0 y e) t2
            (hwt.abs_body harr y (findFresh_fresh e t1))
            (annotated_varOpen ha.abs_body (findFresh_isSome e t1))
        : denoteLMonoTyT ctx (.arrow t1 t2))
    | none => absurd harr hwt.abs_asArrow

  | .abs _ none _, _, _, ha => nomatch ha

  | .quant _ k (some x_mty) _tr e, mty, hwt, ha =>
    hwt.quant_ty ▸
      let y := findFresh e x_mty
      let Γ' := { Γ with types := Γ.types.insert y.fst (.forAll [] x_mty) }
      let bodyBool := fun (d : denoteLMonoTyT ctx x_mty) =>
        let val' := updateVal val y.fst.name x_mty d
        (denoteLExprT C Γ' ctx interp val' (LExpr.varOpen 0 y e) .bool
          (hwt.quant_body y (findFresh_fresh e x_mty))
          (annotated_varOpen ha.quant_body (findFresh_isSome e x_mty))).down
      let result : Bool := match k with
        | .all   => if (Classical.propDecidable (∀ d, bodyBool d = true)).decide then true else false
        | .exist => if (Classical.propDecidable (∃ d, bodyBool d = true)).decide then true else false
      (⟨result⟩ : denoteLMonoTyT ctx .bool)

  | .quant _ _ none _ _, _, _, ha => nomatch ha
  | .app _ _ _, _, _, ha => nomatch ha
  | .eq _ _ _, _, _, ha => nomatch ha

  | .fvar _ name _, mty, _, _ => val name.name mty

  | .bvar _ _, _, hwt, _ => nomatch hwt

  | .op _ name _, mty, _, _ => interp name.name mty

termination_by e => e.sizeOf
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rw [LExpr.varOpen_sizeOf]; omega)

/-! ## Equivalence theorems -/

/-
Theorem: denoteLExprT is sound w.r.t. DenotesT.

  If denoteLExprT C Γ ctx val interp e mty h = v, then DenotesT C ctx e mty v.

Proof: By induction on e, constructing the DenotesT derivation.
-/
set_option pp.proofs true
theorem denoteLExprT_sound
    {T : LExprParams} [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    {C : LContext T} {Γ : TContext T.IDMeta} {ctx : TypeContextT}
    (interp : OpInterpretation ctx)
    (val : ValuationT ctx)
    (e : LExpr T.mono)
    (mty : LMonoTy)
    (h : HasTypeT C Γ e mty)
    (ha : annotated e) :
    DenotesT C ctx interp val e mty (denoteLExprT C Γ ctx interp val e mty h ha) := by
  fun_induction denoteLExprT C Γ ctx interp val e mty h ha
  case case1 Γ' val' m b mty' ha1 ha2 hty' hty => -- boolConst
    have heq := hty.boolConst_ty
    subst heq
    exact .dbool val' m b
  case case2 Γ' val' m i mty' ha1 ha2 hty' hwt => -- intConst
    have heq := hwt.intConst_ty; subst heq
    exact .dint val' m i
  case case3 Γ' val' m s mty' ha1 ha2 hty' hwt => -- strConst
    have heq := hwt.strConst_ty; subst heq
    exact .dstr val' m s
  case case4 Γ' val' m n bv mty' ha1 ha2 hty' hwt => -- bitvecConst
    have heq := hwt.bitvecConst_ty; subst heq
    exact .dbitvec val' m n bv
  case case5 Γ' val' m r bv mty' ha1 ha2 hwt =>
    have heq := hwt.realConst_ty; subst heq
    exact .dreal val' m r
  case case6 Γ' val' m c t e mty' hty ha1 d1 d2 hcond ha2 hwt ih_c ih_t ih_e => -- ite true
    cases hc : (denoteLExprT C Γ' ctx interp val' c .bool (HasTypeT.ite_cond hty) (annotated.ite_cond ha1)).down with
    | true => exact .dite_true val' m c t e mty' _ _ ih_c hc ih_t
    | false => unfold d1 at hcond; rw[hcond] at hc; contradiction
  case case7 Γ' val' m c t e mty' hty ha1 d1 d2 hcond ha2 hwt ih_c ih_t ih_e => -- ite false
    simp [] at *
    cases hc : (denoteLExprT C Γ' ctx interp val' c .bool (HasTypeT.ite_cond hty) (annotated.ite_cond ha1)).down with
    | true => unfold d1 at hcond; rw[hcond] at hc; contradiction
    | false => exact .dite_false val' m c t e mty' _ _ ih_c hc ih_e
  case case8 _ _ Γ' val' m' x_mty e' _ t1 t2 y ha2 hty1 hty2 _ ih => -- abs some, asArrow
    have hx := hty1.abs_x_mty hty2; subst hx
    exact .dabs val' m' _ t2 e' y _ (findFresh_fresh e' _) (findFresh_isSome e' _) (fun a => ih a)
  case case9 Γ' val' m k x_mty tr e' mty' hwt ha1 ha2 y ih_body => -- quant some
    have hmty := hwt.quant_ty; subst hmty
    have hfresh := findFresh_fresh e' x_mty
    have ha: (varOpen 0 (e'.findFresh x_mty) e').annotated := by
      refine annotated_varOpen (annotated.quant_body ha1) (findFresh_isSome _ _)
    cases k with
    | all =>
      by_cases hall : ∀ d, (denoteLExprT C _ ctx interp (updateVal val' (findFresh e' x_mty).fst.name x_mty d)
        (LExpr.varOpen 0 (findFresh e' _) e') .bool (hwt.quant_body (findFresh e' _) hfresh) ha).down = true
      · simp [hall]
        exact .dquant_all val' m x_mty tr e' (findFresh e' _) _ hfresh (findFresh_isSome _ _) (fun d => ih_body d) hall
      · simp [hall]
        exact .dquant_all_false val' m x_mty tr e' (findFresh e' _) _ hfresh (findFresh_isSome _ _) (fun d => ih_body d) hall
    | exist =>
      by_cases hex : ∃ d, (denoteLExprT C _ ctx interp (updateVal val' (findFresh e' x_mty).fst.name x_mty d)
        (LExpr.varOpen 0 (findFresh e' _) e') .bool (hwt.quant_body (findFresh e' _) hfresh) ha).down = true
      · simp [hex]
        exact .dquant_exist val' m x_mty tr e' (findFresh e' _) _ hfresh (findFresh_isSome _ _) (fun d => ih_body d) hex
      · simp [hex]
        exact .dquant_exist_false val' m x_mty tr e' (findFresh e' _) _ hfresh (findFresh_isSome _ _) (fun d => ih_body d) hex
  case case10 mty Γ' val' m' name ty mty hty1 ha1 ha2 hty2 =>
    exact (DenotesT.dfvar val' m' name ty mty)
  case case11 mty Γ' val' m' name ty mty hty1 ha1 ha2 hty2 =>
    exact (DenotesT.dop val' m' name ty mty)

/-- Renaming lemma for denoteLExprT: the denotation of `varOpen 0 x e` is the same
    as `varOpen 0 y e` (under correspondingly updated valuations), provided both
    `x` and `y` are fresh for `e`. This is the semantic α-equivalence lemma. -/
theorem denoteLExprT_rename_fresh
    {T : LExprParams} [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    {C : LContext T} {ctx : TypeContextT}
    (interp : OpInterpretation ctx)
    (val : ValuationT ctx)
    {e : LExpr T.mono} {mty x_mty : LMonoTy}
    {x y : IdentT LMonoTy T.IDMeta}
    (hfx : LExpr.fresh x e) (hfy : LExpr.fresh y e)
    {Γx : TContext T.IDMeta} {Γy : TContext T.IDMeta}
    (hx : HasTypeT C Γx (LExpr.varOpen 0 x e) mty)
    (hy : HasTypeT C Γy (LExpr.varOpen 0 y e) mty)
    (hax : annotated (LExpr.varOpen 0 x e))
    (hay : annotated (LExpr.varOpen 0 y e))
    (a : denoteLMonoTyT ctx x_mty) :
    denoteLExprT C Γy ctx interp (updateVal val y.fst.name x_mty a)
      (LExpr.varOpen 0 y e) mty hy hay =
    denoteLExprT C Γx ctx interp (updateVal val x.fst.name x_mty a)
      (LExpr.varOpen 0 x e) mty hx hax := by
  sorry

/-
Theorem: DenotesT is complete w.r.t. denoteLExprT.

  If DenotesT C ctx e mty v, then denoteLExprT returns v.

Proof: By induction on the DenotesT derivation.
-/
set_option pp.proofs true in
theorem denotesT_complete
    {T : LExprParams} [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    {C : LContext T} {Γ : TContext T.IDMeta} {ctx : TypeContextT}
    (interp : OpInterpretation ctx)
    (val : ValuationT ctx)
    {e : LExpr T.mono} {mty : LMonoTy} {v : denoteLMonoTyT ctx mty}
    (hd : DenotesT C ctx interp val e mty v)
    (h : HasTypeT C Γ e mty)
    (ha : annotated e) :
    denoteLExprT C Γ ctx interp val e mty h ha = v := by
    induction hd generalizing Γ <;> try solve | unfold denoteLExprT; rfl
    case dite_true val m c t e mty vc vt hd1 hcond hd2 ih1 ih2 =>
      unfold denoteLExprT; simp only[]
      rw[ih1 (HasTypeT.ite_cond h), hcond]; simp; apply ih2 (HasTypeT.ite_then h)
    case dite_false val m c t e mty vc vt hd1 hcond hd2 ih1 ih2 =>
      unfold denoteLExprT; simp only[]
      rw[ih1 (HasTypeT.ite_cond h), hcond]; simp; apply ih2 (HasTypeT.ite_else h)
    case dabs val m x_mty e_mty e y f hfresh hyann a ih =>
      unfold denoteLExprT;
      split
      . simp; apply funext; intros x
        rename_i t1 t2 heq
        have heq' : x_mty = t1 ∧ e_mty = t2 := by
          cases heq; grind
        cases heq'; subst_vars
        simp only[]
        have ha_body := ha.abs_body
        have ha_vo_ff := annotated_varOpen (k := 0) ha_body (findFresh_isSome e t1)
        have ha_vo_y := annotated_varOpen (k := 0) ha_body hyann
        rw [denoteLExprT_rename_fresh interp val hfresh (findFresh_fresh e t1)
            (HasTypeT.rename_fresh (findFresh_fresh e t1) hfresh (h.abs_body (asArrowT_arrow) (findFresh e t1) (findFresh_fresh e t1)))
            (HasTypeT.rename_fresh hfresh (findFresh_fresh e t1) _)
            ha_vo_y ha_vo_ff]
        . apply ih _ _ ha_vo_y
        . cases h
          apply (HasTypeT.rename_fresh) <;> assumption
      . contradiction
    case dquant_all val' m' x_mty tr e y bodyBool hfresh hyann hdenotes htrue ih =>
      unfold denoteLExprT; simp only []
      congr 1
      have ha_body := ha.quant_body
      have hfresh' := findFresh_fresh e x_mty
      have ha_vo_ff := annotated_varOpen (k := 0) ha_body (findFresh_isSome e x_mty)
      have ha_vo_y := annotated_varOpen (k := 0) ha_body hyann
      have hbody_eq : ∀ d,
          (denoteLExprT C _ ctx interp (updateVal val' (findFresh e x_mty).fst.name x_mty d)
            (LExpr.varOpen 0 (findFresh e x_mty) e) .bool
            (h.quant_body (findFresh e x_mty) hfresh') ha_vo_ff).down = bodyBool d := by
        intro d
        have hty_y : HasTypeT C { Γ with types := Γ.types.insert y.fst (.forAll [] x_mty) }
            (LExpr.varOpen 0 y e) .bool :=
          HasTypeT.rename_fresh hfresh' hfresh (h.quant_body (findFresh e x_mty) hfresh')
        have hrename := denoteLExprT_rename_fresh interp val' hfresh hfresh'
            hty_y (h.quant_body (findFresh e x_mty) hfresh') ha_vo_y ha_vo_ff d
        have hih := ih d hty_y ha_vo_y
        simp [hrename, hih]
      have hall : ∀ d, (denoteLExprT C _ ctx interp
          (updateVal val' (findFresh e x_mty).fst.name x_mty d)
          (LExpr.varOpen 0 (findFresh e x_mty) e) .bool
          (h.quant_body (findFresh e x_mty) hfresh') ha_vo_ff).down = true := by
        intro d; rw [hbody_eq d]; exact htrue d
      simp [hall]
    case dquant_all_false val' m' x_mty tr e y bodyBool hfresh hyann hdenotes hntrue ih =>
      unfold denoteLExprT; simp only []
      congr 1
      have ha_body := ha.quant_body
      have hfresh' := findFresh_fresh e x_mty
      have ha_vo_ff := annotated_varOpen (k := 0) ha_body (findFresh_isSome e x_mty)
      have ha_vo_y := annotated_varOpen (k := 0) ha_body hyann
      have hbody_eq : ∀ d,
          (denoteLExprT C _ ctx interp (updateVal val' (findFresh e x_mty).fst.name x_mty d)
            (LExpr.varOpen 0 (findFresh e x_mty) e) .bool
            (h.quant_body (findFresh e x_mty) hfresh') ha_vo_ff).down = bodyBool d := by
        intro d
        have hty_y : HasTypeT C { Γ with types := Γ.types.insert y.fst (.forAll [] x_mty) }
            (LExpr.varOpen 0 y e) .bool :=
          HasTypeT.rename_fresh hfresh' hfresh (h.quant_body (findFresh e x_mty) hfresh')
        have hrename := denoteLExprT_rename_fresh interp val' hfresh hfresh'
            hty_y (h.quant_body (findFresh e x_mty) hfresh') ha_vo_y ha_vo_ff d
        have hih := ih d hty_y ha_vo_y
        simp [hrename, hih]
      have hnall : ¬∀ d, (denoteLExprT C _ ctx interp
          (updateVal val' (findFresh e x_mty).fst.name x_mty d)
          (LExpr.varOpen 0 (findFresh e x_mty) e) .bool
          (h.quant_body (findFresh e x_mty) hfresh') ha_vo_ff).down = true := by
        rwa [show (∀ d, _ = true) ↔ (∀ d, bodyBool d = true) from
          ⟨fun h d => by rw [← hbody_eq d]; exact h d,
           fun h d => by rw [hbody_eq d]; exact h d⟩]
      simp [hnall]
    case dquant_exist val' m' x_mty tr e y bodyBool hfresh hyann hdenotes hex ih =>
      unfold denoteLExprT; simp only []
      congr 1
      have ha_body := ha.quant_body
      have hfresh' := findFresh_fresh e x_mty
      have ha_vo_ff := annotated_varOpen (k := 0) ha_body (findFresh_isSome e x_mty)
      have ha_vo_y := annotated_varOpen (k := 0) ha_body hyann
      have hbody_eq : ∀ d,
          (denoteLExprT C _ ctx interp (updateVal val' (findFresh e x_mty).fst.name x_mty d)
            (LExpr.varOpen 0 (findFresh e x_mty) e) .bool
            (h.quant_body (findFresh e x_mty) hfresh') ha_vo_ff).down = bodyBool d := by
        intro d
        have hty_y : HasTypeT C { Γ with types := Γ.types.insert y.fst (.forAll [] x_mty) }
            (LExpr.varOpen 0 y e) .bool :=
          HasTypeT.rename_fresh hfresh' hfresh (h.quant_body (findFresh e x_mty) hfresh')
        have hrename := denoteLExprT_rename_fresh interp val' hfresh hfresh'
            hty_y (h.quant_body (findFresh e x_mty) hfresh') ha_vo_y ha_vo_ff d
        have hih := ih d hty_y ha_vo_y
        simp [hrename, hih]
      have hexf : ∃ d, (denoteLExprT C _ ctx interp
          (updateVal val' (findFresh e x_mty).fst.name x_mty d)
          (LExpr.varOpen 0 (findFresh e x_mty) e) .bool
          (h.quant_body (findFresh e x_mty) hfresh') ha_vo_ff).down = true := by
        obtain ⟨d, hd⟩ := hex
        exact ⟨d, by rw [hbody_eq d]; exact hd⟩
      simp [hexf]
    case dquant_exist_false val' m' x_mty tr e y bodyBool hfresh hyann hdenotes hnex ih =>
      unfold denoteLExprT; simp only []
      congr 1
      have ha_body := ha.quant_body
      have hfresh' := findFresh_fresh e x_mty
      have ha_vo_ff := annotated_varOpen (k := 0) ha_body (findFresh_isSome e x_mty)
      have ha_vo_y := annotated_varOpen (k := 0) ha_body hyann
      have hbody_eq : ∀ d,
          (denoteLExprT C _ ctx interp (updateVal val' (findFresh e x_mty).fst.name x_mty d)
            (LExpr.varOpen 0 (findFresh e x_mty) e) .bool
            (h.quant_body (findFresh e x_mty) hfresh') ha_vo_ff).down = bodyBool d := by
        intro d
        have hty_y : HasTypeT C { Γ with types := Γ.types.insert y.fst (.forAll [] x_mty) }
            (LExpr.varOpen 0 y e) .bool :=
          HasTypeT.rename_fresh hfresh' hfresh (h.quant_body (findFresh e x_mty) hfresh')
        have hrename := denoteLExprT_rename_fresh interp val' hfresh hfresh'
            hty_y (h.quant_body (findFresh e x_mty) hfresh') ha_vo_y ha_vo_ff d
        have hih := ih d hty_y ha_vo_y
        simp [hrename, hih]
      have hnexf : ¬∃ d, (denoteLExprT C _ ctx interp
          (updateVal val' (findFresh e x_mty).fst.name x_mty d)
          (LExpr.varOpen 0 (findFresh e x_mty) e) .bool
          (h.quant_body (findFresh e x_mty) hfresh') ha_vo_ff).down = true := by
        rwa [show (∃ d, _ = true) ↔ (∃ d, bodyBool d = true) from
          ⟨fun ⟨d, hd⟩ => ⟨d, by rw [← hbody_eq d]; exact hd⟩,
           fun ⟨d, hd⟩ => ⟨d, by rw [hbody_eq d]; exact hd⟩⟩]
      simp [hnexf]


/-- An operator interpretation is consistent with a context if:
    for every function with a body, evaluating the body equals the interpretation,
    and for every function with a concreteEvalFunction, it agrees with the interpretation. -/
def OpInterpretation.Consistent {T : LExprParams} [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    (C : LContext T) (ctx : TypeContextT) (interp : OpInterpretation ctx) : Prop :=
  ∀ f ∈ C.functions, ∀ (mty : LMonoTy) (Γ : TContext T.IDMeta) (val : ValuationT ctx),
    -- If the function has a body, its denotation equals the interpretation
    (∀ (body : LExpr T.mono) (_h_body : f.body = some body)
       (hty : HasTypeT C Γ body mty) (ha : annotated body),
       denoteLExprT C Γ ctx interp val body mty hty ha = interp f.name.name mty) ∧
    -- If the function has a concrete evaluator, it is consistent with the interpretation
    (∀ (ev : T.mono.base.Metadata → List (LExpr T.mono) → Option (LExpr T.mono))
       (_h_ev : f.concreteEval = some ev)
       (m : T.mono.base.Metadata) (args : List (LExpr T.mono)) (result : LExpr T.mono)
       (_h_res : ev m args = some result)
       (hty : HasTypeT C Γ result mty) (ha : annotated result),
       denoteLExprT C Γ ctx interp val result mty hty ha = interp f.name.name mty)

def ValidT.{u} {T : LExprParams} [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono)
    (h : HasTypeT C Γ e .bool) (ha : annotated e) : Prop :=
  ∀ (ctx : TypeContextT.{u}) (interp : OpInterpretation ctx) (val : ValuationT ctx),
    interp.Consistent C ctx →
    (denoteLExprT C Γ ctx interp val e .bool h ha).down = true

end LExpr
end Lambda
