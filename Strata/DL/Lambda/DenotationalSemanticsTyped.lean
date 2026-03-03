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

  | tvar : ∀ Γ m x ty_scheme σ,
      Γ.types.find? x = some ty_scheme →
      HasTypeT C Γ (.fvar m x none) (instantiateSchemeT ty_scheme σ)

  | tvar_annotated : ∀ Γ m x ty_scheme σ mty,
      Γ.types.find? x = some ty_scheme →
      mty = instantiateSchemeT ty_scheme σ →
      HasTypeT C Γ (.fvar m x (some mty)) mty

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

  | top : ∀ Γ m f op ty_scheme σ,
      C.functions.find? (fun fn => fn.name == op) = some f →
      f.type = .ok ty_scheme →
      HasTypeT C Γ (.op m op none) (instantiateSchemeT ty_scheme σ)

  | top_annotated : ∀ Γ m f op ty_scheme σ mty,
      C.functions.find? (fun fn => fn.name == op) = some f →
      f.type = .ok ty_scheme →
      mty = instantiateSchemeT ty_scheme σ →
      HasTypeT C Γ (.op m op (some mty)) mty

/-! ## Arrow decomposition -/

def asArrowT (mty : LMonoTy) : Option (LMonoTy × LMonoTy) :=
  match mty with
  | .tcons "arrow" [t1, t2] => some (t1, t2)
  | _ => none

theorem asArrowT_some {mty t1 t2 : LMonoTy} (h : asArrowT mty = some (t1, t2)) :
    mty = .arrow t1 t2 := by
  simp only [asArrowT] at h; split at h <;> simp_all; rfl

theorem asArrowT_none {mty : LMonoTy} (h : asArrowT mty = none) :
    ∀ t1 t2, mty ≠ .arrow t1 t2 := by
  intro t1 t2; unfold LMonoTy.arrow; simp only [asArrowT] at h; split at h <;> simp_all

/-! ## Denotation of Monotypes -/

abbrev TypeContextT.{u} := List (TyIdentifier × Type u)

def denoteLMonoTyT.{u} : TypeContextT.{u} → LMonoTy → Type u
  | _, .tcons "bool" [] => ULift Bool
  | _, .tcons "int" [] => ULift Int
  | _, .tcons "string" [] => ULift String
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

/-- An operator interpretation is consistent with a context if:
    for every function with a body, evaluating the body equals the interpretation,
    and for every function with a concreteEvalFunction, it agrees with the interpretation. -/
def OpInterpretation.Consistent {T : LExprParams} [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    (_C : LContext T) (_ctx : TypeContextT) (_interp : OpInterpretation _ctx) : Prop :=
  sorry

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

  | dapp : ∀ val m e1 e2 t1 t2
      (vf : denoteLMonoTyT ctx (.arrow t2 t1)) (va : denoteLMonoTyT ctx t2),
      DenotesT C ctx interp val e1 (.arrow t2 t1) vf →
      DenotesT C ctx interp val e2 t2 va →
      DenotesT C ctx interp val (.app m e1 e2) t1 (vf va)

  | dabs : ∀ val m x_mty e_mty e (y : IdentT LMonoTy T.IDMeta)
      (f : denoteLMonoTyT ctx x_mty → denoteLMonoTyT ctx e_mty),
      LExpr.fresh y e →
      (∀ a, DenotesT C ctx interp (updateVal val y.fst.name x_mty a) (LExpr.varOpen 0 y e) e_mty (f a)) →
      DenotesT C ctx interp val (.abs m (some x_mty) e) (.arrow x_mty e_mty) f

  | dquant_all : ∀ val m x_mty tr e (y : IdentT LMonoTy T.IDMeta)
      (bodyBool : denoteLMonoTyT ctx x_mty → Bool),
      LExpr.fresh y e →
      (∀ d, DenotesT C ctx interp (updateVal val y.fst.name x_mty d) (LExpr.varOpen 0 y e) .bool ⟨bodyBool d⟩) →
      (∀ d, bodyBool d = true) →
      DenotesT C ctx interp val (.quant m .all (some x_mty) tr e) .bool ⟨true⟩

  | dquant_all_false : ∀ val m x_mty tr e (y : IdentT LMonoTy T.IDMeta)
      (bodyBool : denoteLMonoTyT ctx x_mty → Bool),
      LExpr.fresh y e →
      (∀ d, DenotesT C ctx interp (updateVal val y.fst.name x_mty d) (LExpr.varOpen 0 y e) .bool ⟨bodyBool d⟩) →
      ¬(∀ d, bodyBool d = true) →
      DenotesT C ctx interp val (.quant m .all (some x_mty) tr e) .bool ⟨false⟩

  | dquant_exist : ∀ val m x_mty tr e (y : IdentT LMonoTy T.IDMeta)
      (bodyBool : denoteLMonoTyT ctx x_mty → Bool),
      LExpr.fresh y e →
      (∀ d, DenotesT C ctx interp (updateVal val y.fst.name x_mty d) (LExpr.varOpen 0 y e) .bool ⟨bodyBool d⟩) →
      (∃ d, bodyBool d = true) →
      DenotesT C ctx interp val (.quant m .exist (some x_mty) tr e) .bool ⟨true⟩

  | dquant_exist_false : ∀ val m x_mty tr e (y : IdentT LMonoTy T.IDMeta)
      (bodyBool : denoteLMonoTyT ctx x_mty → Bool),
      LExpr.fresh y e →
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
private def candidates [Inhabited T.IDMeta] (n : Nat) : List (IdentT LMonoTy T.IDMeta) :=
  (List.range n).map fun i => (⟨s!"_x{i}", default⟩, none)

/-- Compute a fresh `IdentT` for an expression by pigeonhole:
    generate `|freeVars| + 1` candidates; at least one has a name not among
    the free variable names. -/
def findFresh [Inhabited T.IDMeta] [DecidableEq T.IDMeta] (e : LExpr T.mono) :
    IdentT LMonoTy T.IDMeta :=
  let fvNames := (LExpr.freeVars e).map Prod.fst
  let cands := candidates (fvNames.length + 1)
  match cands.find? (fun c => c.fst ∉ fvNames) with
  | some y => y
  | none => (⟨"_unreachable", default⟩, none)  -- unreachable by pigeonhole

theorem findFresh_fresh [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    (e : LExpr T.mono) : LExpr.fresh (findFresh e) e := by
  sorry

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
    (hx : x_mty = t1)
    (y : IdentT LMonoTy T.IDMeta) (hfy : LExpr.fresh y e) :
    HasTypeT C { Γ with types := Γ.types.insert y.fst (.forAll [] t1) }
      (LExpr.varOpen 0 y e) t2 := by
  subst hx
  cases h with
  | tabs _ _ x' _ _ e_mty' _ hfresh hbody ho =>
    have heq := asArrowT_some harr
    simp only [LMonoTy.arrow] at heq; cases heq
    rcases ho with h | h <;> simp_all
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
  case tquant tr_mty x x_mty Hopt Hty' Hfresh Hty =>
    cases Hopt; grind
    rename_i Hopt; cases Hopt;
    exact (HasTypeT.rename_fresh Hfresh hfy Hty)

/-! ## Typed denotation function

Match only on the expression. Use type-recovery lemmas to obtain type
equalities, and `asArrowT` to decompose arrow types in data context.
-/

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
    denoteLMonoTyT ctx mty

  | .boolConst _ b, mty, hwt =>
    hwt.boolConst_ty ▸ (⟨b⟩ : denoteLMonoTyT ctx .bool)

  | .intConst _ i, mty, hwt =>
    hwt.intConst_ty ▸ (⟨i⟩ : denoteLMonoTyT ctx .int)

  | .strConst _ s, mty, hwt =>
    hwt.strConst_ty ▸ (⟨s⟩ : denoteLMonoTyT ctx .string)

  | .bitvecConst _ n bv, mty, hwt =>
    hwt.bitvecConst_ty ▸ (⟨bv⟩ : denoteLMonoTyT ctx (.bitvec n))

  | .realConst _ _, _, _ => sorry

  | .ite _ c t e, mty, hwt =>
    let vc := denoteLExprT C Γ ctx interp val c .bool hwt.ite_cond
    let vt := denoteLExprT C Γ ctx interp val t mty hwt.ite_then
    let ve := denoteLExprT C Γ ctx interp val e mty hwt.ite_else
    if vc.down then vt else ve

  | .eq _ e1 e2, mty, hwt =>
    -- To compute equality we'd need DecidableEq on denoteLMonoTyT for the
    -- sub-expression type, which we don't have in general.
    hwt.eq_ty ▸ (sorry : denoteLMonoTyT ctx .bool)

  | .abs _ (some x_mty) e, mty, hwt =>
    match harr : asArrowT mty with
    | some (t1, t2) =>
      let heq := asArrowT_some harr
      let hx := hwt.abs_x_mty harr
      let y := findFresh e
      heq ▸
        let Γ' := { Γ with types := Γ.types.insert y.fst (.forAll [] t1) }
        (fun (a : denoteLMonoTyT ctx t1) =>
          let val' := updateVal val y.fst.name t1 a
          denoteLExprT C Γ' ctx interp val' (LExpr.varOpen 0 y e) t2
            (hwt.abs_body harr hx y (findFresh_fresh e))
        : denoteLMonoTyT ctx (.arrow t1 t2))
    | none => absurd harr hwt.abs_asArrow

  | .abs _ none _, _, _ => sorry

  | .quant _ k (some x_mty) _tr e, mty, hwt =>
    hwt.quant_ty ▸
      let y := findFresh e
      let Γ' := { Γ with types := Γ.types.insert y.fst (.forAll [] x_mty) }
      let bodyBool := fun (d : denoteLMonoTyT ctx x_mty) =>
        let val' := updateVal val y.fst.name x_mty d
        (denoteLExprT C Γ' ctx interp val' (LExpr.varOpen 0 y e) .bool
          (hwt.quant_body y (findFresh_fresh e))).down
      let result : Bool := match k with
        | .all   => if (Classical.propDecidable (∀ d, bodyBool d = true)).decide then true else false
        | .exist => if (Classical.propDecidable (∃ d, bodyBool d = true)).decide then true else false
      (⟨result⟩ : denoteLMonoTyT ctx .bool)

  | .quant _ _ none _ _, _, _ => sorry
  | .app _ _ _, _, _ => sorry

  | .fvar _ name _, mty, _ => val name.name mty

  | .bvar _ _, _, hwt => nomatch hwt

  | .op _ name _, mty, _ => interp name.name mty

termination_by e => e.sizeOf
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rw [LExpr.varOpen_sizeOf]; omega)

/-! ## Equivalence theorems -/

inductive annotated {T : LExprParams} : LExpr T.mono → Prop where
  | ann_const : ∀ m c, annotated (.const m c)
  | ann_fvar : ∀ m name ty, annotated (.fvar m name (some ty))
  | ann_bvar : ∀ m x, annotated (.bvar m x)
  | ann_op : ∀ m name ty, annotated (.op m name (some ty))
  | ann_abs : ∀ m ty e, annotated e → annotated (.abs m (some ty) e)
  | ann_quant : ∀ m k ty tr e, annotated tr → annotated e → annotated (.quant m k (some ty) tr e)
  | ann_ite : ∀ m c t e, annotated c → annotated t → annotated e → annotated (.ite m c t e)
  | ann_eq : ∀ m e1 e2, annotated e1 → annotated e2 → annotated (.eq m e1 e2)
  | ann_app : ∀ m e1 e2, annotated e1 → annotated e2 → annotated (.app m e1 e2)

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
  | ann_eq _ _ _ _ _ ih1 ih2 =>
    show annotated (LExpr.varOpen k x' (.eq _ _ _))
    unfold LExpr.varOpen LExpr.substK; exact .ann_eq _ _ _ ih1 ih2
  | ann_app _ _ _ _ _ ih1 ih2 =>
    show annotated (LExpr.varOpen k x' (.app _ _ _))
    unfold LExpr.varOpen LExpr.substK; exact .ann_app _ _ _ ih1 ih2

/-
Theorem: denoteLExprT is sound w.r.t. DenotesT.

  If denoteLExprT C Γ ctx val interp e mty h = v, then DenotesT C ctx e mty v.

Proof: By induction on e, constructing the DenotesT derivation.
-/
theorem denoteLExprT_sound
    {T : LExprParams} [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    {C : LContext T} {Γ : TContext T.IDMeta} {ctx : TypeContextT}
    (interp : OpInterpretation ctx)
    (val : ValuationT ctx)
    (e : LExpr T.mono)
    (mty : LMonoTy)
    (h : HasTypeT C Γ e mty) :
    DenotesT C ctx interp val e mty (denoteLExprT C Γ ctx interp val e mty h) := by
  fun_induction denoteLExprT C Γ ctx interp val e mty h
  case case1 Γ' val' m b mty' hty' hty => -- boolConst
    have heq := hty.boolConst_ty
    subst heq
    exact .dbool val' m b
  case case2 Γ' val' m i mty' hty' hwt => -- intConst
    have heq := hwt.intConst_ty; subst heq
    exact .dint val' m i
  case case3 Γ' val' m s mty' hty' hwt => -- strConst
    have heq := hwt.strConst_ty; subst heq
    exact .dstr val' m s
  case case4 Γ' val' m n bv mty' hty' hwt => -- bitvecConst
    have heq := hwt.bitvecConst_ty; subst heq
    exact .dbitvec val' m n bv
  · -- realConst
    sorry
  case case6 Γ' val' m c t e mty' hty d1 d2 hcond hwt ih_c ih_t ih_e => -- ite true
    simp [denoteLExprT] at *
    cases hc : (denoteLExprT C Γ' ctx interp val' c .bool hwt.ite_cond).down with
    | true => exact .dite_true val' m c t e mty' _ _ ih_c hc ih_t
    | false => unfold d1 at hcond; rw[hcond] at hc; contradiction
  case case7 Γ' val' m c t e mty' hty d1 d2 hcond hwt ih_c ih_t ih_e => -- ite false
    simp [denoteLExprT] at *
    cases hc : (denoteLExprT C Γ' ctx interp val' c .bool hwt.ite_cond).down with
    | true => unfold d1 at hcond; rw[hcond] at hc; contradiction
    | false => exact .dite_false val' m c t e mty' _ _ ih_c hc ih_e
  · -- eq
    sorry
  case case9 Γ' val' m' e' ty1 ty2 y harr hty1 hty2 ih => -- abs some, asArrow
    -- simp only []
    exact .dabs val' m' ty1 ty2 e' y _ (findFresh_fresh e') (fun a => ih a)
  . -- abs none
    sorry
  case case11 Γ' val' m k x_mty tr e' mty' hwt y ih_body => -- quant some
    have hmty := hwt.quant_ty; subst hmty
    have hfresh := findFresh_fresh e'
    cases k with
    | all =>
      by_cases hall : ∀ d, (denoteLExprT C _ ctx interp (updateVal val' (findFresh e').fst.name x_mty d)
        (LExpr.varOpen 0 (findFresh e') e') .bool (hwt.quant_body (findFresh e') hfresh)).down = true
      · simp [hall]
        exact .dquant_all val' m x_mty tr e' (findFresh e') _ hfresh (fun d => ih_body d) hall
      · simp [hall]
        exact .dquant_all_false val' m x_mty tr e' (findFresh e') _ hfresh (fun d => ih_body d) hall
    | exist =>
      by_cases hex : ∃ d, (denoteLExprT C _ ctx interp (updateVal val' (findFresh e').fst.name x_mty d)
        (LExpr.varOpen 0 (findFresh e') e') .bool (hwt.quant_body (findFresh e') hfresh)).down = true
      · simp [hex]
        exact .dquant_exist val' m x_mty tr e' (findFresh e') _ hfresh (fun d => ih_body d) hex
      · simp [hex]
        exact .dquant_exist_false val' m x_mty tr e' (findFresh e') _ hfresh (fun d => ih_body d) hex
  · -- quant none
    sorry
  · -- app
    sorry
  case case14 mty Γ' val' m' name ty mty hty1 hty2 =>
    exact (DenotesT.dfvar val' m' name ty mty)
  case case15 mty Γ' val' m' name ty mty hty1 hty2 =>
    exact (DenotesT.dop val' m' name ty mty)

/-
Theorem: DenotesT is complete w.r.t. denoteLExprT.

  If DenotesT C ctx e mty v, then denoteLExprT returns v.

Proof: By induction on the DenotesT derivation.
-/
theorem denotesT_complete
    {T : LExprParams} [Inhabited T.IDMeta] [DecidableEq T.IDMeta]
    {C : LContext T} {Γ : TContext T.IDMeta} {ctx : TypeContextT}
    (interp : OpInterpretation ctx)
    (val : ValuationT ctx)
    {e : LExpr T.mono} {mty : LMonoTy} {v : denoteLMonoTyT ctx mty}
    (hd : DenotesT C ctx interp val e mty v)
    (h : HasTypeT C Γ e mty) :
    denoteLExprT C Γ ctx val interp e mty h = v := by
  sorry

end LExpr
end Lambda
