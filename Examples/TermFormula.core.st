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

procedure TestEval() returns ()
spec { ensures true; }
{
  assert [add_neg]: eval(Add(Lit(3), Neg(Lit(2)))) == 1;
  assert [lit]: eval(Lit(42)) == 42;
  assert [neg_neg]: eval(Neg(Neg(Lit(5)))) == 5;
};

procedure TestIte() returns ()
spec { ensures true; }
{
  assert [ite_true]: eval(Ite(Lt(Lit(3), Lit(5)), Lit(10), Lit(20))) == 10;
  assert [ite_false]: eval(Ite(Lt(Lit(5), Lit(3)), Lit(10), Lit(20))) == 20;
};

procedure TestFormula() returns ()
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
procedure AddNegCancel(t : Term) returns ()
spec {
  ensures [cancel]: eval(Add(t, Neg(t))) == 0;
}
{
};


// Double negation: eval(Neg(Neg(t))) == eval(t)
procedure DoubleNeg(t : Term) returns ()
spec {
  ensures [double_neg]: eval(Neg(Neg(t))) == eval(t);
}
{
};


// Ite with a true condition evaluates to the then-branch
procedure IteTrueBranch(t1 : Term, t2 : Term, phi : Formula) returns ()
spec {
  requires holds(phi);
  ensures [ite_then]: eval(Ite(phi, t1, t2)) == eval(t1);
}
{
};


// Ite with a false condition evaluates to the else-branch
procedure IteFalseBranch(t1 : Term, t2 : Term, phi : Formula) returns ()
spec {
  requires !holds(phi);
  ensures [ite_else]: eval(Ite(phi, t1, t2)) == eval(t2);
}
{
};


// holds(FNot(FNot(f))) <==> holds(f)
procedure DoubleNegFormula(f : Formula) returns ()
spec {
  ensures [dneg_formula]: holds(FNot(FNot(f))) == holds(f);
}
{
};


// De Morgan: not(and(p,q)) <==> or(not p, not q)
procedure DeMorgan(p : Formula, q : Formula) returns ()
spec {
  ensures [demorgan]: holds(FNot(FAnd(p, q))) == holds(FOr(FNot(p), FNot(q)));
}
{
};


// Eq is reflexive
procedure EqRefl(t : Term) returns ()
spec {
  ensures [eq_refl]: holds(Eq(t, t));
}
{
};