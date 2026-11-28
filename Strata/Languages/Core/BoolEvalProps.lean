/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core.InstWellFormedSemanticsEval
public import Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import all Strata.Languages.Core.Factory

/-! # Boolean connective interpretation properties

Core builds `Bool.And`, `Bool.Or` and `Bool.Implies` as short-circuit operators and `Bool.Not`
as a unary one, each with a concrete evaluator. A model consistent with a factory that
resolves them to Core's built-ins interprets them as `&&`, `||`, implication and `!`, and an
expression applying one to Boolean values evaluates to the Boolean the connective gives.

Key results:
- `Core.boolAnd_opInterp_of_lookup`, `Core.boolOr_opInterp_of_lookup` and
  `Core.boolImplies_opInterp_of_lookup` give the interpretations (`Bool.Not`'s is
  `Core.boolNot_opInterp_of_lookup`);
- `Core.eval_boolAnd`, `Core.eval_boolOr`, `Core.eval_boolImplies` and `Core.eval_boolNot`
  (instances of `Core.eval_app2_op` and `Core.eval_app1_op`) give Core's evaluation.
-/

public section

namespace Core

open _root_.Lambda

/-- In every consistent interpretation of a factory that resolves `Bool.And` to Core's built-in
    conjunction, `Bool.And` is interpreted as `&&`. -/
theorem boolAnd_opInterp_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Bool.And"]? = some (Lambda.boolAndFunc (T := CoreLParams)).func)
    (p q : Bool) :
    (model.opInterp "Bool.And" (Lambda.LSort.mkArrow .bool [.bool, .bool]) p q : Bool) =
      (p && q) := by
  have heval : (Lambda.boolAndFunc (T := CoreLParams)).func.concreteEval.bind
      (fun ce => ce coreLoc (some ((Lambda.boolAndFunc (T := CoreLParams)).func.instTy Lambda.Subst.empty))
        [.boolConst coreLoc p, .boolConst coreLoc q]) = some (.boolConst coreLoc (p && q)) := by
    cases p <;> rfl
  exact (opInterp_of_concreteEval model hlookup rfl heval (fun _ => .int) (fun _ s =>
      @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s))
    (.cons (.const rfl) (.cons (.const rfl) .nil)) (.const rfl)).symm

/-- In every consistent interpretation of a factory that resolves `Bool.Or` to Core's built-in
    disjunction, `Bool.Or` is interpreted as `||`. -/
theorem boolOr_opInterp_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Bool.Or"]? = some (Lambda.boolOrFunc (T := CoreLParams)).func)
    (p q : Bool) :
    (model.opInterp "Bool.Or" (Lambda.LSort.mkArrow .bool [.bool, .bool]) p q : Bool) =
      (p || q) := by
  have heval : (Lambda.boolOrFunc (T := CoreLParams)).func.concreteEval.bind
      (fun ce => ce coreLoc (some ((Lambda.boolOrFunc (T := CoreLParams)).func.instTy Lambda.Subst.empty))
        [.boolConst coreLoc p, .boolConst coreLoc q]) = some (.boolConst coreLoc (p || q)) := by
    cases p <;> rfl
  exact (opInterp_of_concreteEval model hlookup rfl heval (fun _ => .int) (fun _ s =>
      @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s))
    (.cons (.const rfl) (.cons (.const rfl) .nil)) (.const rfl)).symm

/-- In every consistent interpretation of a factory that resolves `Bool.Implies` to Core's
    built-in implication, `Bool.Implies` is interpreted as `!p || q`. -/
theorem boolImplies_opInterp_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Bool.Implies"]? = some (Lambda.boolImpliesFunc (T := CoreLParams)).func)
    (p q : Bool) :
    (model.opInterp "Bool.Implies" (Lambda.LSort.mkArrow .bool [.bool, .bool]) p q : Bool) =
      (!p || q) := by
  have heval : (Lambda.boolImpliesFunc (T := CoreLParams)).func.concreteEval.bind
      (fun ce => ce coreLoc (some ((Lambda.boolImpliesFunc (T := CoreLParams)).func.instTy Lambda.Subst.empty))
        [.boolConst coreLoc p, .boolConst coreLoc q]) = some (.boolConst coreLoc (!p || q)) := by
    cases p <;> rfl
  exact (opInterp_of_concreteEval model hlookup rfl heval (fun _ => .int) (fun _ s =>
      @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s))
    (.cons (.const rfl) (.cons (.const rfl) .nil)) (.const rfl)).symm

/-- `a && b` evaluates to the conjunction of the Booleans its operands evaluate to. -/
theorem eval_boolAnd {f : Expression.Factory} {m m' : ExpressionMetadata}
    (hlookup : f.factory["Bool.And"]? = some (Lambda.boolAndFunc (T := CoreLParams)).func)
    {σ : CoreStore} {x y : Expression.Expr} {p q : Bool}
    (hx : Expression.eval f σ x = some (SemValue.ofBool f.model.tcInterp p))
    (hy : Expression.eval f σ y = some (SemValue.ofBool f.model.tcInterp q)) :
    Expression.eval f σ (.app m (.app m' boolAndOp x) y) =
      some (SemValue.ofBool f.model.tcInterp (p && q)) :=
  eval_app2_op "Bool.And" (c := .bool) rfl rfl rfl hx hy
    (boolAnd_opInterp_of_lookup f.model hlookup p q)

/-- `a || b` evaluates to the disjunction of the Booleans its operands evaluate to. -/
theorem eval_boolOr {f : Expression.Factory} {m m' : ExpressionMetadata}
    (hlookup : f.factory["Bool.Or"]? = some (Lambda.boolOrFunc (T := CoreLParams)).func)
    {σ : CoreStore} {x y : Expression.Expr} {p q : Bool}
    (hx : Expression.eval f σ x = some (SemValue.ofBool f.model.tcInterp p))
    (hy : Expression.eval f σ y = some (SemValue.ofBool f.model.tcInterp q)) :
    Expression.eval f σ (.app m (.app m' boolOrOp x) y) =
      some (SemValue.ofBool f.model.tcInterp (p || q)) :=
  eval_app2_op "Bool.Or" (c := .bool) rfl rfl rfl hx hy
    (boolOr_opInterp_of_lookup f.model hlookup p q)

/-- `a ==> b` evaluates to the implication between the Booleans its operands evaluate to. -/
theorem eval_boolImplies {f : Expression.Factory} {m m' : ExpressionMetadata}
    (hlookup : f.factory["Bool.Implies"]? =
      some (Lambda.boolImpliesFunc (T := CoreLParams)).func)
    {σ : CoreStore} {x y : Expression.Expr} {p q : Bool}
    (hx : Expression.eval f σ x = some (SemValue.ofBool f.model.tcInterp p))
    (hy : Expression.eval f σ y = some (SemValue.ofBool f.model.tcInterp q)) :
    Expression.eval f σ (.app m (.app m' boolImpliesOp x) y) =
      some (SemValue.ofBool f.model.tcInterp (!p || q)) :=
  eval_app2_op "Bool.Implies" (c := .bool) rfl rfl rfl hx hy
    (boolImplies_opInterp_of_lookup f.model hlookup p q)

/-- `!a` evaluates to the negation of the Boolean its operand evaluates to. -/
theorem eval_boolNot {f : Expression.Factory} {m : ExpressionMetadata}
    (hlookup : f.factory["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func)
    {σ : CoreStore} {x : Expression.Expr} {p : Bool}
    (hx : Expression.eval f σ x = some (SemValue.ofBool f.model.tcInterp p)) :
    Expression.eval f σ (.app m boolNotOp x) = some (SemValue.ofBool f.model.tcInterp (!p)) :=
  eval_app1_op "Bool.Not" (c := .bool) rfl rfl hx (boolNot_opInterp_of_lookup f.model hlookup p)

end Core

end -- public section
