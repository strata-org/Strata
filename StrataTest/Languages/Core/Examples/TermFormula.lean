/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Term/Formula Deep Embedding

A deep embedding of first-order logic over integers where terms and formulas
are mutually recursive:

- **Terms**: integer literals, addition, negation, if-then-else (guarded by a formula)
- **Formulas**: equality, less-than, less-equal, not, and, or, implies

`eval` and `holds` are mutually recursive: `eval` returns int, `holds` returns bool.
-/

namespace Strata.TermFormulaTest

def termFormulaPgm : Program :=
#strata
program Core;

  datatype Term {
    Lit(val: int),
    Add(lhs: Term, rhs: Term),
    Neg(inner: Term),
    Ite(cond: Formula, thn: Term, els: Term)
  }
  datatype Formula {
    Eq(eqL: Term, eqR: Term),
    Lt(ltL: Term, ltR: Term),
    Le(leL: Term, leR: Term),
    FNot(inner: Formula),
    FAnd(andL: Formula, andR: Formula),
    FOr(orL: Formula, orR: Formula),
    FImplies(ante: Formula, cons: Formula)
  };

rec function eval (@[cases] t : Term) : int
  {
    if Term..isLit(t) then Term..val(t)
    else if Term..isAdd(t) then eval(Term..lhs(t)) + eval(Term..rhs(t))
    else if Term..isNeg(t) then 0 - eval(Term..inner(t))
    else if holds(Term..cond(t)) then eval(Term..thn(t))
    else eval(Term..els(t))
  }
function holds (@[cases] f : Formula) : bool
  {
    if Formula..isEq(f) then eval(Formula..eqL(f)) == eval(Formula..eqR(f))
    else if Formula..isLt(f) then eval(Formula..ltL(f)) < eval(Formula..ltR(f))
    else if Formula..isLe(f) then eval(Formula..leL(f)) <= eval(Formula..leR(f))
    else if Formula..isFNot(f) then !holds(Formula..inner(f))
    else if Formula..isFAnd(f) then holds(Formula..andL(f)) && holds(Formula..andR(f))
    else if Formula..isFOr(f) then holds(Formula..orL(f)) || holds(Formula..orR(f))
    else if Formula..isFImplies(f) then !holds(Formula..ante(f)) || holds(Formula..cons(f))
    else false
  };

// --- Concrete evaluation tests ---

procedure TestEval()
spec { ensures true; }
{
  assert [add_neg]: eval(Add(Lit(3), Neg(Lit(2)))) == 1;
  assert [lit]: eval(Lit(42)) == 42;
  assert [neg_neg]: eval(Neg(Neg(Lit(5)))) == 5;
};

procedure TestIte()
spec { ensures true; }
{
  assert [ite_true]: eval(Ite(Lt(Lit(3), Lit(5)), Lit(10), Lit(20))) == 10;
  assert [ite_false]: eval(Ite(Lt(Lit(5), Lit(3)), Lit(10), Lit(20))) == 20;
};

procedure TestFormula()
spec { ensures true; }
{
  assert [eq_true]: holds(Eq(Lit(3), Add(Lit(1), Lit(2))));
  assert [eq_false]: !holds(Eq(Lit(3), Lit(4)));
  assert [lt_true]: holds(Lt(Lit(2), Lit(3)));
  assert [le_refl]: holds(Le(Lit(5), Lit(5)));
  assert [not_false]: holds(FNot(Lt(Lit(5), Lit(3))));
  assert [and_true]: holds(FAnd(Le(Lit(0), Lit(1)), Le(Lit(1), Lit(2))));
  assert [or_left]: holds(FOr(Lt(Lit(0), Lit(1)), Lt(Lit(5), Lit(3))));
  assert [implies_vacuous]: holds(FImplies(Lt(Lit(5), Lit(3)), Eq(Lit(0), Lit(1))));
};

// --- Symbolic reasoning ---

// For any term t, eval(Add(t, Neg(t))) == 0
procedure AddNegCancel(t : Term)
spec {
  ensures [cancel]: eval(Add(t, Neg(t))) == 0;
}
{
};

// Double negation: eval(Neg(Neg(t))) == eval(t)
procedure DoubleNeg(t : Term)
spec {
  ensures [double_neg]: eval(Neg(Neg(t))) == eval(t);
}
{
};

// Ite with a true condition evaluates to the then-branch
procedure IteTrueBranch(t1 : Term, t2 : Term, phi : Formula)
spec {
  requires holds(phi);
  ensures [ite_then]: eval(Ite(phi, t1, t2)) == eval(t1);
}
{
};

// Ite with a false condition evaluates to the else-branch
procedure IteFalseBranch(t1 : Term, t2 : Term, phi : Formula)
spec {
  requires !holds(phi);
  ensures [ite_else]: eval(Ite(phi, t1, t2)) == eval(t2);
}
{
};

// holds(FNot(FNot(f))) <==> holds(f)
procedure DoubleNegFormula(f : Formula)
spec {
  ensures [dneg_formula]: holds(FNot(FNot(f))) == holds(f);
}
{
};

// De Morgan: not(and(p,q)) <==> or(not p, not q)
procedure DeMorgan(p : Formula, q : Formula)
spec {
  ensures [demorgan]: holds(FNot(FAnd(p, q))) == holds(FOr(FNot(p), FNot(q)));
}
{
};

// Eq is reflexive
procedure EqRefl(t : Term)
spec {
  ensures [eq_refl]: holds(Eq(t, t));
}
{
};
#end

/--
info: true
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram termFormulaPgm) |>.snd |>.isEmpty

/--
info:
Obligation: eval_body_calls_Term..val_0
Property: assert
Result: ✅ pass

Obligation: eval_body_calls_Term..lhs_1
Property: assert
Result: ✅ pass

Obligation: eval_body_calls_Term..rhs_2
Property: assert
Result: ✅ pass

Obligation: eval_body_calls_Term..inner_3
Property: assert
Result: ✅ pass

Obligation: eval_body_calls_Term..cond_4
Property: assert
Result: ✅ pass

Obligation: eval_body_calls_Term..thn_5
Property: assert
Result: ✅ pass

Obligation: eval_body_calls_Term..els_6
Property: assert
Result: ✅ pass

Obligation: holds_body_calls_Formula..eqL_0
Property: assert
Result: ✅ pass

Obligation: holds_body_calls_Formula..eqR_1
Property: assert
Result: ✅ pass

Obligation: holds_body_calls_Formula..ltL_2
Property: assert
Result: ✅ pass

Obligation: holds_body_calls_Formula..ltR_3
Property: assert
Result: ✅ pass

Obligation: holds_body_calls_Formula..leL_4
Property: assert
Result: ✅ pass

Obligation: holds_body_calls_Formula..leR_5
Property: assert
Result: ✅ pass

Obligation: holds_body_calls_Formula..inner_6
Property: assert
Result: ✅ pass

Obligation: holds_body_calls_Formula..andL_7
Property: assert
Result: ✅ pass

Obligation: holds_body_calls_Formula..andR_8
Property: assert
Result: ✅ pass

Obligation: holds_body_calls_Formula..orL_9
Property: assert
Result: ✅ pass

Obligation: holds_body_calls_Formula..orR_10
Property: assert
Result: ✅ pass

Obligation: holds_body_calls_Formula..ante_11
Property: assert
Result: ✅ pass

Obligation: holds_body_calls_Formula..cons_12
Property: assert
Result: ✅ pass

Obligation: eval_terminates_0
Property: assert
Result: ✅ pass

Obligation: eval_terminates_1
Property: assert
Result: ✅ pass

Obligation: eval_terminates_2
Property: assert
Result: ✅ pass

Obligation: eval_terminates_3
Property: assert
Result: ✅ pass

Obligation: eval_terminates_4
Property: assert
Result: ✅ pass

Obligation: eval_terminates_5
Property: assert
Result: ✅ pass

Obligation: holds_terminates_0
Property: assert
Result: ✅ pass

Obligation: holds_terminates_1
Property: assert
Result: ✅ pass

Obligation: holds_terminates_2
Property: assert
Result: ✅ pass

Obligation: holds_terminates_3
Property: assert
Result: ✅ pass

Obligation: holds_terminates_4
Property: assert
Result: ✅ pass

Obligation: holds_terminates_5
Property: assert
Result: ✅ pass

Obligation: holds_terminates_6
Property: assert
Result: ✅ pass

Obligation: holds_terminates_7
Property: assert
Result: ✅ pass

Obligation: holds_terminates_8
Property: assert
Result: ✅ pass

Obligation: holds_terminates_9
Property: assert
Result: ✅ pass

Obligation: holds_terminates_10
Property: assert
Result: ✅ pass

Obligation: holds_terminates_11
Property: assert
Result: ✅ pass

Obligation: holds_terminates_12
Property: assert
Result: ✅ pass

Obligation: add_neg
Property: assert
Result: ✅ pass

Obligation: lit
Property: assert
Result: ✅ pass

Obligation: neg_neg
Property: assert
Result: ✅ pass

Obligation: TestEval_ensures_0
Property: assert
Result: ✅ pass

Obligation: ite_true
Property: assert
Result: ✅ pass

Obligation: ite_false
Property: assert
Result: ✅ pass

Obligation: TestIte_ensures_0
Property: assert
Result: ✅ pass

Obligation: eq_true
Property: assert
Result: ✅ pass

Obligation: eq_false
Property: assert
Result: ✅ pass

Obligation: lt_true
Property: assert
Result: ✅ pass

Obligation: le_refl
Property: assert
Result: ✅ pass

Obligation: not_false
Property: assert
Result: ✅ pass

Obligation: and_true
Property: assert
Result: ✅ pass

Obligation: or_left
Property: assert
Result: ✅ pass

Obligation: implies_vacuous
Property: assert
Result: ✅ pass

Obligation: TestFormula_ensures_0
Property: assert
Result: ✅ pass

Obligation: cancel
Property: assert
Result: ✅ pass

Obligation: double_neg
Property: assert
Result: ✅ pass

Obligation: ite_then
Property: assert
Result: ✅ pass

Obligation: ite_else
Property: assert
Result: ✅ pass

Obligation: dneg_formula
Property: assert
Result: ✅ pass

Obligation: demorgan
Property: assert
Result: ✅ pass

Obligation: eq_refl
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify termFormulaPgm (options := .quiet)

end Strata.TermFormulaTest
