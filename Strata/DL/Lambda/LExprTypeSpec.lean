/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.LExprWF

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

variable {Identifier : Type} [DecidableEq Identifier]

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
      .forAll (vars.removeAll [x]) (LMonoTy.subst S lty)
    else
      ty

/--
Typing relation for `LExpr`s.

(TODO) Add the introduction and elimination rules for `.tcons`.
-/
inductive HasType {Identifier : Type} [DecidableEq Identifier]:
  (TContext Identifier) → (LExpr LMonoTy Identifier) → LTy → Prop where
  | tmdata : ∀ Γ info e ty, HasType Γ e ty →
                            HasType Γ (.mdata info e) ty

  | tbool_const_t : ∀ Γ, HasType Γ (.const "true" none)
                         (.forAll [] (.tcons "bool" []))
  | tbool_const_f : ∀ Γ, HasType Γ (.const "false" none)
                        (.forAll [] (.tcons "bool" []))
  | tint_const : ∀ Γ, n.isInt → HasType Γ (.const n none)
                                (.forAll [] (.tcons "int" []))

  | tvar : ∀ Γ x ty, Γ.types.find? x = some ty → HasType Γ (.fvar x none) ty

  | tabs : ∀ Γ x x_ty e e_ty,
            LExpr.fresh x e →
            (hx : LTy.isMonoType x_ty) →
            (he : LTy.isMonoType e_ty) →
            HasType { Γ with types := Γ.types.insert x.fst x_ty} (LExpr.varOpen 0 x e) e_ty →
            HasType Γ (.abs .none e)
                      (.forAll [] (.tcons "arrow" [(LTy.toMonoType x_ty hx),
                                                   (LTy.toMonoType e_ty he)]))

--  | tcons_intro : ∀ Γ C args targs,
--                  args.length == targs.length →
--                  ∀ et ∈ (List.zip args targs), HasType Γ et.fst et.snd →
--                  HasType Γ (.app (.const C) args) (.tcons C targs)

--  | tcons_elim :
--                HasType Γ (.app (.const C) args) (.tcons C targs) →
--                (h : i < targs.length) →
--                HasType Γ (.proj i args) (List.get targs i h)

  | tapp : ∀ Γ e1 e2 t1 t2,
            (h1 : LTy.isMonoType t1) →
            (h2 : LTy.isMonoType t2) →
            HasType Γ e1 (.forAll [] (.tcons "arrow" [(LTy.toMonoType t2 h2),
                                                     (LTy.toMonoType t1 h1)])) →
            HasType Γ e2 t2 →
            HasType Γ (.app e1 e2) t1

  -- `ty` is more general than `e_ty`, so we can instantiate `ty` with `e_ty`.
  | tinst : ∀ Γ e ty e_ty x x_ty,
           HasType Γ e ty →
           e_ty = LTy.open x x_ty ty →
           HasType Γ e e_ty

  -- The generalization rule will let us do things like the following:
  -- `(·ftvar "a") → (.ftvar "a")` (or `a → a`) will be generalized to
  -- `(.btvar 0) → (.btvar 0)` (or `∀a. a → a`), assuming `a` is not in the
  -- context.
  | tgen : ∀ Γ e a ty,
           HasType Γ e ty →
           TContext.isFresh a Γ →
           HasType Γ e (LTy.close a ty)

  | tif : ∀ Γ c e1 e2 ty,
          HasType Γ c (.forAll [] (.tcons "bool" [])) →
          HasType Γ e1 ty →
          HasType Γ e2 ty →
          HasType Γ (.ite c e1 e2) ty

  | teq : ∀ Γ e1 e2 ty,
          HasType Γ e1 ty →
          HasType Γ e2 ty →
          HasType Γ (.eq e1 e2) (.forAll [] (.tcons "bool" []))

/--
If `LExpr e` is well-typed, then it is well-formed, i.e., contains no dangling
bound variables.
-/
theorem HasType.regularity (h : HasType (Identifier:=Identifier) Γ e ty) :
  LExpr.WF e := by
  open LExpr in
  induction h
  case tbool_const_t => simp [WF, lcAt]
  case tbool_const_f => simp [WF, lcAt]
  case tint_const => simp [WF, lcAt]
  case tvar => simp [WF, lcAt]
  case tmdata => simp_all [WF, lcAt]
  case tabs T x x_ty e e_ty hx h_x_mono h_e_mono ht ih =>
    simp_all [WF]
    have := @lcAt_varOpen_abs (Identifier:=Identifier) _ x e 0 0
    simp_all
  case tapp => simp_all [WF, lcAt]
  case tif => simp_all [WF, lcAt]
  case teq => simp_all [WF, lcAt]
  case tgen => simp_all
  case tinst => simp_all
  done

---------------------------------------------------------------------

section Tests

-- Examples of typing derivations using the `HasType` relation.

open LExpr.SyntaxMono LTy.Syntax

example : LExpr.HasType {} esM[#true] t[bool] := by
  apply LExpr.HasType.tbool_const_t

example : LExpr.HasType {} esM[#-1] t[int] := by
  apply LExpr.HasType.tint_const
  simp +ground

example : LExpr.HasType { types := [[("x", t[∀a. %a])]]} esM[x] t[int] := by
  have h_tinst := @LExpr.HasType.tinst (Identifier := String) _ { types := [[("x", t[∀a. %a])]]} esM[x] t[∀a. %a] t[int] "a" mty[int]
  have h_tvar := @LExpr.HasType.tvar (Identifier := String) _ { types := [[("x", t[∀a. %a])]]} "x" t[∀a. %a]
  simp +ground at h_tvar
  simp [h_tvar] at h_tinst
  simp +ground at h_tinst
  simp [Map.isEmpty, Bool.decEq] at h_tinst
  assumption

example : LExpr.HasType { types := [[("m", t[∀a. %a → int])]]}
                        esM[(m #true)]
                        t[int] := by
  apply LExpr.HasType.tapp _ _ _ _ t[bool] <;> (try simp +ground)
  <;> try apply LExpr.HasType.tbool_const_t
  apply LExpr.HasType.tinst _ _ t[∀a. %a → int] t[bool → int] "a" mty[bool]
  · apply LExpr.HasType.tvar
    simp +ground
  · simp +ground
    simp [Map.isEmpty, Bool.decEq]
  done

example : LExpr.HasType {} esM[λ %0] t[∀a. %a → %a] := by
  have h_tabs := @LExpr.HasType.tabs (Identifier := String) _ {} ("a", none) t[%a] esM[%0] t[%a]
  simp +ground at h_tabs
  have h_tvar := @LExpr.HasType.tvar (Identifier := String) _ { types := [[("a", t[%a])]] }
                 "a" t[%a]
  simp [Maps.find?, Map.find?] at h_tvar
  simp [h_tvar, LTy.toMonoType] at h_tabs
  have h_tgen := @LExpr.HasType.tgen (Identifier := String) _ {} esM[λ %0] "a"
                 t[%a → %a]
                 h_tabs
  simp +ground [Maps.find?] at h_tgen
  assumption
  done

end Tests

---------------------------------------------------------------------
end LExpr
end Lambda
