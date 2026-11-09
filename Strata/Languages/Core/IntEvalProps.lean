/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core.InstWellFormedSemanticsEval
public import Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import all Strata.Languages.Core.Factory

/-! # Integer operator interpretation properties

Key results:
- `Core.intGe_opInterp` identifies `Int.Ge` with integer comparison;
- `Core.intAdd_opInterp` and `Core.intMul_opInterp` identify built-in arithmetic;
- `Core.intAdd_opInterp_of_lookup`, `Core.intSub_opInterp_of_lookup`,
  `Core.intMul_opInterp_of_lookup`, and `Core.intGt_opInterp_of_lookup` provide
  the corresponding facts for factories extending `Core.Factory`;
- `Core.denote_intAdd_of_lookup`, `Core.denote_intSub_of_lookup`,
  `Core.denote_intMul_of_lookup`, and `Core.denote_intGt_of_lookup` lift them
  to the denotation of an operator applied to two integer-valued arguments;
- `Core.eval_intAdd`, `eval_intSub`, `eval_intMul`, `eval_intLt`, `eval_intLe`,
  `eval_intGt` and `eval_intGe` (instances of `Core.eval_app2_op`) give Core's evaluation of an
  operator applied to two integers, with `eval_const`, `eval_intConst`, `eval_boolConst`,
  `eval_fvar` and `eval_fvar_int` for its leaves and `eval_eq_true`/`eval_eq_false` for equalities.
-/

public section

namespace Core

open _root_.Lambda

/-- An integer operation built by `binaryOp` from `op : Int → Int → Int` keeps `op` as its
    interpretation in any factory that resolves `name` to it. -/
private theorem intArith_opInterp_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory) (name : String) (op : Int → Int → Int)
    (hlookup : factory[name]? = some
      (Lambda.binaryOp (T := CoreLParams) (InValTy := Int) (OutValTy := Int) ⟨name, ()⟩ op).func)
    (a b : Int) :
    (model.opInterp name (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) = op a b :=
  (opInterp_of_concreteEval model hlookup rfl (args := [.intConst () a, .intConst () b])
    (res := .intConst () (op a b)) rfl (fun _ => .int) (fun _ s =>
      @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s))
    (.cons .const (.cons .const .nil)) .const).symm

/-- An integer comparison built by `binaryOp` from `op : Int → Int → Bool` keeps `op` as its
    interpretation in any factory that resolves `name` to it. -/
private theorem intCmp_opInterp_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory) (name : String) (op : Int → Int → Bool)
    (hlookup : factory[name]? = some
      (Lambda.binaryOp (T := CoreLParams) (InValTy := Int) (OutValTy := Bool) ⟨name, ()⟩ op).func)
    (a b : Int) :
    (model.opInterp name (Lambda.LSort.mkArrow .bool [.int, .int]) a b : Bool) = op a b :=
  (opInterp_of_concreteEval model hlookup rfl (args := [.intConst () a, .intConst () b])
    (res := .boolConst () (op a b)) rfl (fun _ => .int) (fun _ s =>
      @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s))
    (.cons .const (.cons .const .nil)) .const).symm

/-- `Int.Ge`'s interpretation at `int, int → bool` is `≥` in every consistent model. -/
theorem intGe_opInterp (model : Lambda.Interp Core.Factory) (a b : Int) :
    (model.opInterp "Int.Ge"
        (Lambda.LSort.mkArrow .bool [.int, .int]) a b : Bool)
      = decide (a ≥ b) :=
  intCmp_opInterp_of_lookup model "Int.Ge" _ Core.coreFactory_intGe a b

/-- `Int.Add`'s interpretation at `int, int → int` is `+` in every consistent model. -/
theorem intAdd_opInterp (model : Lambda.Interp Core.Factory) (a b : Int) :
    (model.opInterp "Int.Add"
        (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int)
      = a + b :=
  intArith_opInterp_of_lookup model "Int.Add" _ Core.coreFactory_intAdd a b

/-- `Int.Mul`'s interpretation at `int, int → int` is `*` in every consistent model. -/
theorem intMul_opInterp (model : Lambda.Interp Core.Factory) (a b : Int) :
    (model.opInterp "Int.Mul"
        (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int)
      = a * b :=
  intArith_opInterp_of_lookup model "Int.Mul" _ Core.coreFactory_intMul a b

/-- `Int.Add` keeps its standard interpretation in any factory that resolves
    it to Core's built-in addition function. -/
theorem intAdd_opInterp_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Add"]? = some (Lambda.intAddFunc (T := CoreLParams)).func)
    (a b : Int) :
    (model.opInterp "Int.Add"
        (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) = a + b :=
  intArith_opInterp_of_lookup model "Int.Add" _ hlookup a b

/-- `Int.Sub` keeps its standard interpretation in any factory that resolves
    it to Core's built-in subtraction function. -/
theorem intSub_opInterp_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Sub"]? = some (Lambda.intSubFunc (T := CoreLParams)).func)
    (a b : Int) :
    (model.opInterp "Int.Sub"
        (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) = a - b :=
  intArith_opInterp_of_lookup model "Int.Sub" _ hlookup a b

/-- `Int.Mul` keeps its standard interpretation in any factory that resolves
    it to Core's built-in multiplication function. -/
theorem intMul_opInterp_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Mul"]? = some (Lambda.intMulFunc (T := CoreLParams)).func)
    (a b : Int) :
    (model.opInterp "Int.Mul"
        (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) = a * b :=
  intArith_opInterp_of_lookup model "Int.Mul" _ hlookup a b

/-- `Int.Gt` has integer greater-than semantics in any factory that resolves it
    to Core's built-in comparison function. -/
theorem intGt_opInterp_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Gt"]? = some (Lambda.intGtFunc (T := CoreLParams)).func)
    (a b : Int) :
    (model.opInterp "Int.Gt"
        (Lambda.LSort.mkArrow .bool [.int, .int]) a b : Bool) = decide (a > b) :=
  intCmp_opInterp_of_lookup model "Int.Gt" _ hlookup a b

/-- `Int.Lt` has integer less-than semantics in any factory that resolves it
    to Core's built-in comparison function. -/
theorem intLt_opInterp_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Lt"]? = some (Lambda.intLtFunc (T := CoreLParams)).func)
    (a b : Int) :
    (model.opInterp "Int.Lt"
        (Lambda.LSort.mkArrow .bool [.int, .int]) a b : Bool) = decide (a < b) :=
  intCmp_opInterp_of_lookup model "Int.Lt" _ hlookup a b

/-- `Int.Le` has integer less-or-equal semantics in any factory that resolves it
    to Core's built-in comparison function. -/
theorem intLe_opInterp_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Le"]? = some (Lambda.intLeFunc (T := CoreLParams)).func)
    (a b : Int) :
    (model.opInterp "Int.Le"
        (Lambda.LSort.mkArrow .bool [.int, .int]) a b : Bool) = decide (a ≤ b) :=
  intCmp_opInterp_of_lookup model "Int.Le" _ hlookup a b

/-- `Int.Ge` has integer greater-or-equal semantics in any factory that resolves it
    to Core's built-in comparison function. -/
theorem intGe_opInterp_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Ge"]? = some (Lambda.intGeFunc (T := CoreLParams)).func)
    (a b : Int) :
    (model.opInterp "Int.Ge"
        (Lambda.LSort.mkArrow .bool [.int, .int]) a b : Bool) = decide (a ≥ b) :=
  intCmp_opInterp_of_lookup model "Int.Ge" _ hlookup a b

/-- In any factory that resolves `Int.Add` to Core's built-in addition,
    `int.add(e₁, e₂)` denotes `a + b` when `e₁` and `e₂` denote `a` and `b`. -/
theorem denote_intAdd_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Add"]? = some (Lambda.intAddFunc (T := CoreLParams)).func)
    (fv : Lambda.FreeVarVal CoreLParams model.tcInterp) (vt : Lambda.TyVarVal)
    {Δ : List Lambda.LMonoTy} (bv : Lambda.BVarVal model.tcInterp vt Δ)
    {e₁ e₂ : Expression.Expr} {a b : Int}
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.app () intAddOp e₁) e₂) .int)
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .int) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .int)
    (hv₁ : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁ = a)
    (hv₂ : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂ = b) :
    Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
      (.app () (.app () intAddOp e₁) e₂) .int h = a + b := by
  have hop : Lambda.LExpr.HasTypeA (T := CoreLParams) Δ intAddOp
      (.arrow .int (.arrow .int .int)) := .op
  have happ : Lambda.LExpr.HasTypeA Δ (.app () intAddOp e₁) (.arrow .int .int) :=
    .app hop h₁
  rw [Lambda.denote_app bv happ h₂ h, Lambda.denote_app bv hop h₁ happ, hv₁, hv₂]
  simp only [intAddOp, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr,
    Lambda.LFuncDefined.opExpr] at hop ⊢
  rw [Lambda.denote_op]
  exact intAdd_opInterp_of_lookup model hlookup a b

/-- In any factory that resolves `Int.Sub` to Core's built-in subtraction,
    `int.sub(e₁, e₂)` denotes `a - b` when `e₁` and `e₂` denote `a` and `b`. -/
theorem denote_intSub_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Sub"]? = some (Lambda.intSubFunc (T := CoreLParams)).func)
    (fv : Lambda.FreeVarVal CoreLParams model.tcInterp) (vt : Lambda.TyVarVal)
    {Δ : List Lambda.LMonoTy} (bv : Lambda.BVarVal model.tcInterp vt Δ)
    {e₁ e₂ : Expression.Expr} {a b : Int}
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.app () intSubOp e₁) e₂) .int)
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .int) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .int)
    (hv₁ : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁ = a)
    (hv₂ : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂ = b) :
    Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
      (.app () (.app () intSubOp e₁) e₂) .int h = a - b := by
  have hop : Lambda.LExpr.HasTypeA (T := CoreLParams) Δ intSubOp
      (.arrow .int (.arrow .int .int)) := .op
  have happ : Lambda.LExpr.HasTypeA Δ (.app () intSubOp e₁) (.arrow .int .int) :=
    .app hop h₁
  rw [Lambda.denote_app bv happ h₂ h, Lambda.denote_app bv hop h₁ happ, hv₁, hv₂]
  simp only [intSubOp, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr,
    Lambda.LFuncDefined.opExpr] at hop ⊢
  rw [Lambda.denote_op]
  exact intSub_opInterp_of_lookup model hlookup a b

/-- In any factory that resolves `Int.Mul` to Core's built-in multiplication,
    `int.mul(e₁, e₂)` denotes `a * b` when `e₁` and `e₂` denote `a` and `b`. -/
theorem denote_intMul_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Mul"]? = some (Lambda.intMulFunc (T := CoreLParams)).func)
    (fv : Lambda.FreeVarVal CoreLParams model.tcInterp) (vt : Lambda.TyVarVal)
    {Δ : List Lambda.LMonoTy} (bv : Lambda.BVarVal model.tcInterp vt Δ)
    {e₁ e₂ : Expression.Expr} {a b : Int}
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.app () intMulOp e₁) e₂) .int)
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .int) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .int)
    (hv₁ : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁ = a)
    (hv₂ : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂ = b) :
    Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
      (.app () (.app () intMulOp e₁) e₂) .int h = a * b := by
  have hop : Lambda.LExpr.HasTypeA (T := CoreLParams) Δ intMulOp
      (.arrow .int (.arrow .int .int)) := .op
  have happ : Lambda.LExpr.HasTypeA Δ (.app () intMulOp e₁) (.arrow .int .int) :=
    .app hop h₁
  rw [Lambda.denote_app bv happ h₂ h, Lambda.denote_app bv hop h₁ happ, hv₁, hv₂]
  simp only [intMulOp, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr,
    Lambda.LFuncDefined.opExpr] at hop ⊢
  rw [Lambda.denote_op]
  exact intMul_opInterp_of_lookup model hlookup a b

/-- In any factory that resolves `Int.Gt` to Core's built-in comparison,
    `int.gt(e₁, e₂)` denotes `decide (a > b)` when `e₁` and `e₂` denote `a`
    and `b`. -/
theorem denote_intGt_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Int.Gt"]? = some (Lambda.intGtFunc (T := CoreLParams)).func)
    (fv : Lambda.FreeVarVal CoreLParams model.tcInterp) (vt : Lambda.TyVarVal)
    {Δ : List Lambda.LMonoTy} (bv : Lambda.BVarVal model.tcInterp vt Δ)
    {e₁ e₂ : Expression.Expr} {a b : Int}
    (h : Lambda.LExpr.HasTypeA Δ (.app () (.app () intGtOp e₁) e₂) .bool)
    (h₁ : Lambda.LExpr.HasTypeA Δ e₁ .int) (h₂ : Lambda.LExpr.HasTypeA Δ e₂ .int)
    (hv₁ : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₁ .int h₁ = a)
    (hv₂ : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv e₂ .int h₂ = b) :
    (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt bv
      (.app () (.app () intGtOp e₁) e₂) .bool h : Bool) = decide (a > b) := by
  have hop : Lambda.LExpr.HasTypeA (T := CoreLParams) Δ intGtOp
      (.arrow .int (.arrow .int .bool)) := .op
  have happ : Lambda.LExpr.HasTypeA Δ (.app () intGtOp e₁) (.arrow .int .bool) :=
    .app hop h₁
  rw [Lambda.denote_app bv happ h₂ h, Lambda.denote_app bv hop h₁ happ, hv₁, hv₂]
  simp only [intGtOp, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr,
    Lambda.LFuncDefined.opExpr] at hop ⊢
  rw [Lambda.denote_op]
  exact intGt_opInterp_of_lookup model hlookup a b

/-! ## Evaluation of integer operators

Core's evaluator (`Expression.eval`) is denotational, so an integer operator applied
to integer-valued arguments evaluates to its interpretation in the model of the
runtime factory, which is the standard operation whenever the factory resolves the
operator to Core's built-in function. -/

/-- An integer literal evaluates to its integer. -/
theorem eval_intConst (f : Expression.Factory) {m : ExpressionMetadata} (σ : CoreStore) (n : Int) :
    Expression.eval f σ (.intConst m n) = some (SemValue.ofInt f.model.tcInterp n) :=
  LExpr.denoteEval_intConst

/-- A Boolean literal evaluates to its Boolean. -/
theorem eval_boolConst (f : Expression.Factory)
    {m : ExpressionMetadata} (σ : CoreStore) (b : Bool) :
    Expression.eval f σ (.boolConst m b) = some (SemValue.ofBool f.model.tcInterp b) :=
  LExpr.denoteEval_boolConst

/-- A literal evaluates to its value. -/
theorem eval_const (f : Expression.Factory) {m : ExpressionMetadata} (σ : CoreStore) (c : LConst) :
    Expression.eval f σ (.const m c) = some (SemValue.ofConst f.model.tcInterp c) :=
  LExpr.denoteEval_const

/-- An equality of two expressions with the same value evaluates to `true`. -/
theorem eval_eq_true (f : Expression.Factory)
    {m : ExpressionMetadata} {σ : CoreStore} {a b : Expression.Expr}
    {v : Expression.Val} (ha : Expression.eval f σ a = some v)
    (hb : Expression.eval f σ b = some v) :
    Expression.eval f σ (.eq m a b) = some (SemValue.ofBool f.model.tcInterp true) :=
  LExpr.denoteEval_eq_true ha hb

/-- An equality of two expressions with distinct values of the same sort evaluates to
    `false`. -/
theorem eval_eq_false (f : Expression.Factory)
    {m : ExpressionMetadata} {σ : CoreStore} {a b : Expression.Expr}
    {va vb : Expression.Val} (ha : Expression.eval f σ a = some va)
    (hb : Expression.eval f σ b = some vb) (hs : va.sort = vb.sort) (hne : va ≠ vb) :
    Expression.eval f σ (.eq m a b) = some (SemValue.ofBool f.model.tcInterp false) :=
  LExpr.denoteEval_eq_false ha hb hs hne

/-- A conditional whose condition evaluates to a Boolean and whose branches evaluate to
    values of the same sort evaluates to the selected branch's value. -/
theorem eval_ite (f : Expression.Factory)
    {m : ExpressionMetadata} {σ : CoreStore} {c t e : Expression.Expr}
    {b : Bool} {vt ve : Expression.Val}
    (hc : Expression.eval f σ c = some (SemValue.ofBool f.model.tcInterp b))
    (ht : Expression.eval f σ t = some vt) (he : Expression.eval f σ e = some ve)
    (hs : vt.sort = ve.sort) :
    Expression.eval f σ (.ite m c t e) = some (if b then vt else ve) :=
  (LExpr.denoteEval_ite_iff (T := CoreLParams)).mpr ⟨b, vt, ve, hc, ht, he, hs, rfl⟩

/-- A free variable bound to a value of the factory evaluates to it. -/
theorem eval_fvar (f : Expression.Factory) {m : ExpressionMetadata} {σ : CoreStore} {x : CoreIdent}
    {ty : Option LMonoTy} {v : Expression.Val} (hx : σ x = some v)
    (hv : v.tc = f.model.tcInterp) :
    Expression.eval f σ (.fvar m x ty) = some v :=
  LExpr.denoteEval_fvar hx hv

/-- A free variable bound to an integer of the factory evaluates to it. -/
theorem eval_fvar_int (f : Expression.Factory)
    {m : ExpressionMetadata} {σ : CoreStore} {x : CoreIdent}
    {ty : Option LMonoTy} {n : Int} (hx : σ x = some (SemValue.ofInt f.model.tcInterp n)) :
    Expression.eval f σ (.fvar m x ty) = some (SemValue.ofInt f.model.tcInterp n) :=
  LExpr.denoteEval_fvar hx rfl

/-- `Int.Add` applied to two integers evaluates to `a + b` when the factory resolves
    it to Core's built-in function. -/
theorem eval_intAdd {f : Expression.Factory} {m m' : ExpressionMetadata}
    (hlookup : f.factory["Int.Add"]? = some (Lambda.intAddFunc (T := CoreLParams)).func)
    {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    (hx : Expression.eval f σ x = some (SemValue.ofInt f.model.tcInterp a))
    (hy : Expression.eval f σ y = some (SemValue.ofInt f.model.tcInterp b)) :
    Expression.eval f σ (.app m (.app m' intAddOp x) y) =
      some (SemValue.ofInt f.model.tcInterp (a + b)) :=
  eval_app2_op "Int.Add" (c := .int) rfl rfl rfl hx hy
      (intAdd_opInterp_of_lookup f.model hlookup a b)

/-- `Int.Sub` applied to two integers evaluates to `a - b` when the factory resolves
    it to Core's built-in function. -/
theorem eval_intSub {f : Expression.Factory} {m m' : ExpressionMetadata}
    (hlookup : f.factory["Int.Sub"]? = some (Lambda.intSubFunc (T := CoreLParams)).func)
    {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    (hx : Expression.eval f σ x = some (SemValue.ofInt f.model.tcInterp a))
    (hy : Expression.eval f σ y = some (SemValue.ofInt f.model.tcInterp b)) :
    Expression.eval f σ (.app m (.app m' intSubOp x) y) =
      some (SemValue.ofInt f.model.tcInterp (a - b)) :=
  eval_app2_op "Int.Sub" (c := .int) rfl rfl rfl hx hy
      (intSub_opInterp_of_lookup f.model hlookup a b)

/-- `Int.Mul` applied to two integers evaluates to `a * b` when the factory resolves
    it to Core's built-in function. -/
theorem eval_intMul {f : Expression.Factory} {m m' : ExpressionMetadata}
    (hlookup : f.factory["Int.Mul"]? = some (Lambda.intMulFunc (T := CoreLParams)).func)
    {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    (hx : Expression.eval f σ x = some (SemValue.ofInt f.model.tcInterp a))
    (hy : Expression.eval f σ y = some (SemValue.ofInt f.model.tcInterp b)) :
    Expression.eval f σ (.app m (.app m' intMulOp x) y) =
      some (SemValue.ofInt f.model.tcInterp (a * b)) :=
  eval_app2_op "Int.Mul" (c := .int) rfl rfl rfl hx hy
      (intMul_opInterp_of_lookup f.model hlookup a b)

/-- `Int.Lt` applied to two integers evaluates to `decide (a < b)` when the factory resolves
    it to Core's built-in function. -/
theorem eval_intLt {f : Expression.Factory} {m m' : ExpressionMetadata}
    (hlookup : f.factory["Int.Lt"]? = some (Lambda.intLtFunc (T := CoreLParams)).func)
    {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    (hx : Expression.eval f σ x = some (SemValue.ofInt f.model.tcInterp a))
    (hy : Expression.eval f σ y = some (SemValue.ofInt f.model.tcInterp b)) :
    Expression.eval f σ (.app m (.app m' intLtOp x) y) =
      some (SemValue.ofBool f.model.tcInterp (decide (a < b))) :=
  eval_app2_op "Int.Lt" (c := .bool) rfl rfl rfl hx hy
      (intLt_opInterp_of_lookup f.model hlookup a b)

/-- `Int.Le` applied to two integers evaluates to `decide (a ≤ b)` when the factory resolves
    it to Core's built-in function. -/
theorem eval_intLe {f : Expression.Factory} {m m' : ExpressionMetadata}
    (hlookup : f.factory["Int.Le"]? = some (Lambda.intLeFunc (T := CoreLParams)).func)
    {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    (hx : Expression.eval f σ x = some (SemValue.ofInt f.model.tcInterp a))
    (hy : Expression.eval f σ y = some (SemValue.ofInt f.model.tcInterp b)) :
    Expression.eval f σ (.app m (.app m' intLeOp x) y) =
      some (SemValue.ofBool f.model.tcInterp (decide (a ≤ b))) :=
  eval_app2_op "Int.Le" (c := .bool) rfl rfl rfl hx hy
      (intLe_opInterp_of_lookup f.model hlookup a b)

/-- `Int.Gt` applied to two integers evaluates to `decide (a > b)` when the factory resolves
    it to Core's built-in function. -/
theorem eval_intGt {f : Expression.Factory} {m m' : ExpressionMetadata}
    (hlookup : f.factory["Int.Gt"]? = some (Lambda.intGtFunc (T := CoreLParams)).func)
    {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    (hx : Expression.eval f σ x = some (SemValue.ofInt f.model.tcInterp a))
    (hy : Expression.eval f σ y = some (SemValue.ofInt f.model.tcInterp b)) :
    Expression.eval f σ (.app m (.app m' intGtOp x) y) =
      some (SemValue.ofBool f.model.tcInterp (decide (a > b))) :=
  eval_app2_op "Int.Gt" (c := .bool) rfl rfl rfl hx hy
      (intGt_opInterp_of_lookup f.model hlookup a b)

/-- `Int.Ge` applied to two integers evaluates to `decide (a ≥ b)` when the factory resolves
    it to Core's built-in function. -/
theorem eval_intGe {f : Expression.Factory} {m m' : ExpressionMetadata}
    (hlookup : f.factory["Int.Ge"]? = some (Lambda.intGeFunc (T := CoreLParams)).func)
    {σ : CoreStore} {x y : Expression.Expr} {a b : Int}
    (hx : Expression.eval f σ x = some (SemValue.ofInt f.model.tcInterp a))
    (hy : Expression.eval f σ y = some (SemValue.ofInt f.model.tcInterp b)) :
    Expression.eval f σ (.app m (.app m' intGeOp x) y) =
      some (SemValue.ofBool f.model.tcInterp (decide (a ≥ b))) :=
  eval_app2_op "Int.Ge" (c := .bool) rfl rfl rfl hx hy
      (intGe_opInterp_of_lookup f.model hlookup a b)

end Core

end -- public section
