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
Typing relation for `LExpr`s.
-/
inductive HasType {IDMeta : Type} [DecidableEq IDMeta] (C: LContext IDMeta):
  (TContext IDMeta) → (LExpr LMonoTy IDMeta) → LTy → Prop where
  | tmdata : ∀ Γ info e ty, HasType C Γ e ty →
                            HasType C Γ (.mdata info e) ty

  | tbool_const : ∀ Γ b,
            C.knownTypes.containsName "bool" →
            HasType C Γ (.boolConst b) (.forAll [] .bool)
  | tint_const : ∀ Γ n,
            C.knownTypes.containsName "int" →
            HasType C Γ (.intConst n) (.forAll [] .int)
  | treal_const : ∀ Γ r,
            C.knownTypes.containsName "real" →
            HasType C Γ (.realConst r) (.forAll [] .real)
  | tstr_const : ∀ Γ s,
            C.knownTypes.containsName "string" →
            HasType C Γ (.strConst s) (.forAll [] .string)
  | tbitvec_const : ∀ Γ n b,
            C.knownTypes.containsName "bitvec" →
            HasType C Γ (.bitvecConst n b) (.forAll [] (.bitvec n))

  | tvar : ∀ Γ x ty, Γ.types.find? x = some ty → HasType C Γ (.fvar x none) ty

  /-
  For an annotated free variable (or operator, see `top_annotated`), it must be
  the case that the claimed type `ty_s` is an instantiation of the general type
  `ty_o`. It suffices to show the existence of a list `tys` that, when
  substituted for the bound variables in `ty_o`, results in `ty_s`.
  -/
  | tvar_annotated : ∀ Γ x ty_o ty_s tys,
            Γ.types.find? x = some ty_o →
            tys.length = ty_o.boundVars.length →
            LTy.openFull ty_o tys = ty_s →
            HasType C Γ (.fvar x (some ty_s)) (.forAll [] ty_s)

  | tabs : ∀ Γ x x_ty e e_ty o,
            LExpr.fresh x e →
            (hx : LTy.isMonoType x_ty) →
            (he : LTy.isMonoType e_ty) →
            HasType C { Γ with types := Γ.types.insert x.fst x_ty} (LExpr.varOpen 0 x e) e_ty →
            o = none ∨ o = some (x_ty.toMonoType hx) →
            HasType C Γ (.abs o e)
                      (.forAll [] (.tcons "arrow" [(LTy.toMonoType x_ty hx),
                                                   (LTy.toMonoType e_ty he)]))

  | tapp : ∀ Γ e1 e2 t1 t2,
            (h1 : LTy.isMonoType t1) →
            (h2 : LTy.isMonoType t2) →
            HasType C Γ e1 (.forAll [] (.tcons "arrow" [(LTy.toMonoType t2 h2),
                                                     (LTy.toMonoType t1 h1)])) →
            HasType C Γ e2 t2 →
            HasType C Γ (.app e1 e2) t1

  -- `ty` is more general than `e_ty`, so we can instantiate `ty` with `e_ty`.
  | tinst : ∀ Γ e ty e_ty x x_ty,
            HasType C Γ e ty →
            e_ty = LTy.open x x_ty ty →
            HasType C Γ e e_ty

  -- The generalization rule will let us do things like the following:
  -- `(·ftvar "a") → (.ftvar "a")` (or `a → a`) will be generalized to
  -- `(.btvar 0) → (.btvar 0)` (or `∀a. a → a`), assuming `a` is not in the
  -- context.
  | tgen : ∀ Γ e a ty,
            HasType C Γ e ty →
            TContext.isFresh a Γ →
            HasType C Γ e (LTy.close a ty)

  | tif : ∀ Γ c e1 e2 ty,
            HasType C Γ c (.forAll [] .bool) →
            HasType C Γ e1 ty →
            HasType C Γ e2 ty →
            HasType C Γ (.ite c e1 e2) ty

  | teq : ∀ Γ e1 e2 ty,
            HasType C Γ e1 ty →
            HasType C Γ e2 ty →
            HasType C Γ (.eq e1 e2) (.forAll [] .bool)

  | tquant: ∀ Γ k tr tr_ty x x_ty e o,
            LExpr.fresh x e →
            (hx : LTy.isMonoType x_ty) →
            HasType C { Γ with types := Γ.types.insert x.fst x_ty} (LExpr.varOpen 0 x e) (.forAll [] .bool) →
            HasType C {Γ with types := Γ.types.insert x.fst x_ty} (LExpr.varOpen 0 x tr) tr_ty →
            o = none ∨ o = some (x_ty.toMonoType hx) →
            HasType C Γ (.quant k o tr e) (.forAll [] .bool)
  | top: ∀ Γ f op ty,
            C.functions.find? (fun fn => fn.name == op) = some f →
            f.type = .ok ty →
            HasType C Γ (.op op none) ty
  /-
  See comments in `tvar_annotated`.
  -/
  | top_annotated: ∀ Γ f op ty_o ty_s tys,
            C.functions.find? (fun fn => fn.name == op) = some f →
            f.type = .ok ty_o →
            tys.length = ty_o.boundVars.length →
            LTy.openFull ty_o tys = ty_s →
            HasType C Γ (.op op (some ty_s)) (.forAll [] ty_s)

/--
If `LExpr e` is well-typed, then it is well-formed, i.e., contains no dangling
bound variables.
-/
theorem HasType.regularity (h : HasType (IDMeta:=IDMeta) C Γ e ty) :
  LExpr.WF e := by
  open LExpr in
  induction h <;> try (solve | simp_all[WF, lcAt])
  case tabs T x x_ty e e_ty hx h_x_mono h_e_mono ht ih =>
    simp_all [WF]
    exact lcAt_varOpen_abs ih (by simp)
  case tquant T k tr tr_ty x x_ty e o h_x_mono hx htr ih ihtr =>
    simp_all [WF]
    exact lcAt_varOpen_quant ih (by omega) ihtr
  done

---------------------------------------------------------------------

section Tests

-- Examples of typing derivations using the `HasType` relation.

open LExpr.SyntaxMono LTy.Syntax

macro "solveKnownNames" : tactic =>  `(tactic | simp[KnownTypes.containsName, LTy.toKnownType!, makeKnownTypes, KnownTypes.default, LContext.default])

example : LExpr.HasType LContext.default {} esM[#true] t[bool] := by
  apply LExpr.HasType.tbool_const; solveKnownNames

example : LExpr.HasType LContext.default {} esM[#-1] t[int] := by
  apply LExpr.HasType.tint_const; solveKnownNames

example : LExpr.HasType LContext.default { types := [[("x", t[∀a. %a])]]} esM[x] t[int] := by
  have h_tinst := @LExpr.HasType.tinst (IDMeta := Unit) _ LContext.default { types := [[("x", t[∀a. %a])]]} esM[x] t[∀a. %a] t[int] "a" mty[int]
  have h_tvar := @LExpr.HasType.tvar (IDMeta := Unit) _ LContext.default { types := [[("x", t[∀a. %a])]]} "x" t[∀a. %a]
  apply h_tinst; apply h_tvar; rfl
  simp +ground; rfl

example : LExpr.HasType LContext.default { types := [[("m", t[∀a. %a → int])]]}
                        esM[(m #true)]
                        t[int] := by
  apply LExpr.HasType.tapp _ _ _ _ t[bool] <;> (try simp +ground)
  <;> try apply LExpr.HasType.tbool_const <;> simp[KnownTypes.containsName]
  apply LExpr.HasType.tinst _ _ t[∀a. %a → int] t[bool → int] "a" mty[bool]
  · apply LExpr.HasType.tvar
    simp +ground
  · simp +ground
    exact rfl
  solveKnownNames
  done

example : LExpr.HasType {} {} esM[λ %0] t[∀a. %a → %a] := by
  have h_tabs := @LExpr.HasType.tabs (IDMeta := Unit) _ {} {} ("a", none) t[%a] esM[%0] t[%a] none
  simp at h_tabs
  have h_tvar := @LExpr.HasType.tvar (IDMeta := Unit) _ {} { types := [[("a", t[%a])]] }
                 "a" t[%a]
  simp [Maps.find?, Map.find?] at h_tvar
  specialize (h_tabs rfl rfl rfl h_tvar)
  simp [LTy.toMonoType] at h_tabs
  have h_tgen := @LExpr.HasType.tgen (IDMeta := Unit) _ {} {} esM[λ %0] "a"
                 t[%a → %a]
                 h_tabs
  simp[TContext.isFresh, Maps.find?] at h_tgen
  assumption
  done

def idFactory : LFunc Unit := {name := "id", typeArgs := ["a"],  inputs := [⟨"x", .ftvar "a"⟩], output := .ftvar "a"}

example : LExpr.HasType (LContext.default.addFactoryFunction idFactory) {} (.op ⟨"id", ()⟩ none) t[∀a. %a → %a] := by
  apply (LExpr.HasType.top _ idFactory) <;> rfl

example : LExpr.HasType (LContext.default.addFactoryFunction idFactory) {} (.op ⟨"id", ()⟩ mty[int → int]) t[int → int] := by
  apply (LExpr.HasType.top_annotated _ idFactory _ t[∀a. %a → %a] _ [.int]) <;> try rfl
  simp only[LTy.openFull, LTy.toMonoTypeUnsafe, List.zip, LTy.boundVars];
  unfold LMonoTy.subst ;
  simp[Subst.hasEmptyScopes, Map.isEmpty, LMonoTys.subst, LMonoTys.subst.substAux, LMonoTy.subst, Maps.find?, Map.find?, LMonoTy.int]

end Tests

---------------------------------------------------------------------
end LExpr
end Lambda
