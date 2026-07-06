/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Identifiers
public import Strata.Languages.Core.CoreOp
public import Strata.DL.Imperative.HasVars
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.LState
public import Strata.DL.Lambda.LExprEval
public import Strata.DL.Lambda.IntBoolFactory

namespace Core
open Std (ToFormat Format format)
---------------------------------------------------------------------

public section

open Imperative

@[expose] abbrev ExpressionMetadata := Unit

@[expose]
abbrev Expression : PureExpr :=
   { Ident := CoreIdent,
     EqIdent := inferInstanceAs (DecidableEq (Lambda.Identifier Unit))
     Expr := Lambda.LExpr ⟨⟨ExpressionMetadata, Unit⟩, Lambda.LMonoTy⟩,
     Ty := Lambda.LTy,
     ExprMetadata := ExpressionMetadata,
     TyEnv := @Lambda.TEnv Unit,
     TyContext := @Lambda.LContext ⟨ExpressionMetadata, Unit⟩,
     Factory := Lambda.Factory CoreLParams,
     eval := Lambda.LExpr.evalFully }

instance : HasFvars Expression where
  getFvars := Lambda.LExpr.LExpr.getVars

instance : HasOps Expression where
  getOps := Lambda.LExpr.getOps

instance : Inhabited Expression.Expr where
  default := .intConst () 0

/-- Build an `LExpr.op` node from a structured `CoreOp`. -/
def coreOpExpr (op : CoreOp) (ty : Option Lambda.LMonoTy := none) : Expression.Expr :=
  .op () op.toString ty

instance : HasVal Core.Expression where
  value := fun f e => Lambda.LExpr.isCanonicalValue f e = true

instance : HasFvar Core.Expression where
  mkFvar := (.fvar () · none)
  getFvar
  | .fvar _ v _ => some v
  | _ => none

instance : HasSubstFvar Core.Expression where
  substFvar := Lambda.LExpr.substFvar
  substFvars := Lambda.LExpr.substFvars

instance : HasIdent Core.Expression where
  ident s := ⟨s, ()⟩

@[expose, match_pattern]
def Core.true : Core.Expression.Expr := .boolConst () Bool.true
@[expose, match_pattern]
def Core.false : Core.Expression.Expr := .boolConst () Bool.false

/-- Syntactic check for integer numeral literals in Core. -/
def Core.isNumeral : Core.Expression.Expr → Bool
  | .const _ (.intConst _) => Bool.true
  | _ => Bool.false

instance : HasBool Core.Expression where
  tt := Core.true
  ff := Core.false
  tt_is_not_ff := by unfold Core.true Core.false; unfold Lambda.LExpr.boolConst; simp
  boolTy := .forAll [] (.tcons "bool" [])
  boolIsVal := fun f => by
    simp only [HasVal.value]
    exact ⟨by show Lambda.LExpr.isCanonicalValue f Core.true = true
              simp [Core.true, Lambda.LExpr.boolConst, Lambda.LExpr.isCanonicalValue],
           by show Lambda.LExpr.isCanonicalValue f Core.false = true
              simp [Core.false, Lambda.LExpr.boolConst, Lambda.LExpr.isCanonicalValue]⟩

instance : HasInt Core.Expression where
  zero        := .intConst () 0
  intTy       := .forAll [] (.tcons "int" [])
  isNumeral   := Core.isNumeral
  numeralIsValue f n hn := by
    simp only [HasVal.value]
    cases n with
    | const m c =>
      cases c with
      | intConst _ => simp [Lambda.LExpr.isCanonicalValue]
      | _ => simp [Core.isNumeral] at hn
    | _ => simp [Core.isNumeral] at hn
  zeroIsNumeral := by
    show Core.isNumeral (.intConst () 0) = Bool.true
    rfl
  numeralHasNoFvars n hn := by
    cases n with
    | const _ c => cases c <;> first | rfl | simp [Core.isNumeral] at hn
    | _ => simp [Core.isNumeral] at hn

instance : HasIntOps Core.Expression where
  eq    e1 e2 := .eq () e1 e2
  lt    e1 e2 := .app () (.app () (@Lambda.intLtFunc CoreLParams _).opExpr e1) e2

instance : HasBoolOps Core.Expression where
  not
  | Core.true => Core.false
  | Core.false => Core.true
  | e => Lambda.LExpr.app () (Lambda.boolNotFunc (T:=CoreLParams)).opExpr e
  and e1 e2 := Lambda.LExpr.app () (Lambda.LExpr.app ()
    (Lambda.boolAndFunc (T:=CoreLParams)).opExpr e1) e2
  imp e1 e2 := Lambda.LExpr.app () (Lambda.LExpr.app ()
    (Lambda.boolImpliesFunc (T:=CoreLParams)).opExpr e1) e2

---------------------------------------------------------------------

end

end Core
