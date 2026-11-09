/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
---------------------------------------------------------------------
namespace Strata.AbstractedLemmasTest

/-! # Lemmas checked without the function they are about

The termination and well-formedness lemmas of a function hold whatever the
function returns: each function of its recursive block becomes a universally
quantified variable of the function's type. They are declared before the function, so its
definition is not in scope when they are checked.
-/

/-! `loop` does not terminate, and its recursive axiom
`loop(Cons(h, t)) == loop(Cons(h, t)) + 1` is contradictory. Its termination
lemma is stated without `loop`, so that axiom cannot prove it, and it is not
proved. The solver does not prove it even with the axiom in scope, so the test
pins the guarantee, not a verdict the axiom would flip. -/

def nonTerminatingPgm :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function loop (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else int.add(loop(xs), 1)
};
#end

/--
info:
Obligation: loop_terminates_0
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify nonTerminatingPgm (options := .quiet)

/-! The division in `bad`'s body is well-formed only when `bad(IntList..tl(xs))`
is not `0`, which nothing guarantees. The check fails, although `bad`'s
contradictory axiom would prove it if it were in scope. -/

def wfNeedsAbstractionPgm :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function bad (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0
  else int.add(bad(xs), int.add(1, int.mul(0, int.safeDiv(1, bad(IntList..tl(xs))))))
};
#end

/--
info:
Obligation: bad_terminates_0
Property: assert
Result: ❓ unknown

Obligation: bad_terminates_1
Property: assert
Result: ✅ pass

Obligation: bad_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: bad_body_calls_Int.SafeDiv_1
Property: division by zero check
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify wfNeedsAbstractionPgm (options := .quiet)

/-! The well-formedness lemma of `sumTo` states the division's precondition for
any result of the recursive call, and holds because the divisor is the input. -/

def wfAbstractedPassesPgm :=
#strata
program Core;

rec function sumTo (n : int) : int
  decreases n
{
  if int.le(n, 0) then 0 else int.add(int.safeDiv(sumTo(int.sub(n, 1)), n), n)
};
#end

/--
info:
Obligation: sumTo_terminates_0
Property: assert
Result: ✅ pass

Obligation: sumTo_terminates_1
Property: assert
Result: ✅ pass

Obligation: sumTo_body_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify wfAbstractedPassesPgm (options := .quiet)

/-! Abstracting calls loses the facts that unfolding the function on a
specific argument would give. The division in `cnt`'s body is well-formed
since `cnt(Nil())` is `1`, but its well-formedness lemma does not see `cnt`'s
definition and fails. Its termination lemma passes: the rank of `Nil()`, a
constructor without recursive fields, is `0`, and `xs`, not `Nil()`, has a
rank of at least `1`. -/

def unfoldingLostPgm :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function cnt (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 1 else int.safeDiv(10, cnt(Nil()))
};
#end

/--
info:
Obligation: cnt_terminates_0
Property: assert
Result: ✅ pass

Obligation: cnt_body_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify unfoldingLostPgm (options := .quiet)

/-! The rank `0` of a constructor without recursive fields proves only calls
on it from a caller that is not that constructor. When `xs` may be `Nil()`,
the call `f(Nil())` does not decrease, and its termination lemma is not
proved: the rank of `xs` is at least `1` only when `xs` is not `Nil()`. The
solver cannot refute the lemma either, since `adtRank` is uninterpreted. -/

def rankZeroSelfCallPgm :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function f (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then f(Nil()) else 0
};
#end

/--
info:
Obligation: f_terminates_0
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify rankZeroSelfCallPgm (options := .quiet)

/-! The same holds across a block: `f(Nil())` calls `g(Nil())`, which calls
`f(Nil())`, so neither call decreases. -/

def rankZeroMutualCallPgm :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function f (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then g(Nil()) else 0
}
function g (@[cases] ys : IntList) : int
{
  if IntList..isNil(ys) then f(Nil()) else 0
};
#end

/--
info:
Obligation: f_terminates_0
Property: assert
Result: ❓ unknown

Obligation: g_terminates_0
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify rankZeroMutualCallPgm (options := .quiet)

/-! A decreasing argument with a bound variable is rejected, even a
constructor without recursive fields such as `Leaf(y)`, whose rank is `0`
whatever `y` is. Here the call does not decrease, since `t` may be a leaf, and
`f`'s definition is contradictory. An unproved termination lemma would not stop
that definition from being assumed, so `bogus` would pass; rejecting the call
keeps the program from being verified at all. -/

def rankZeroBoundArgPgm :=
#strata
program Core;

datatype Tree { Leaf(v: int), Node(l: Tree) };

rec function f (@[cases] t : Tree, k : int) : bool
{
  !(forall y : int :: if y == int.add(k, 1) then f(Leaf(y), k) else true)
};

procedure P()
{
  assert [bogus]: f(Leaf(1), 0) && !(f(Leaf(1), 0));
};
#end

/-- error: termination checking 'f': decreasing argument contains a bound variable -/
#guard_msgs in
#eval Core.verify rankZeroBoundArgPgm (options := .quiet)

/-! Without a guard, the call on `Leaf(y)` is rejected too. -/

def rankZeroBoundArgNoGuardPgm :=
#strata
program Core;

datatype Tree { Leaf(v: int), Node(l: Tree) };

rec function f (@[cases] t : Tree, k : int) : bool
{
  !(forall y : int :: f(Leaf(y), k))
};
#end

/-- error: termination checking 'f': decreasing argument contains a bound variable -/
#guard_msgs in
#eval Core.verify rankZeroBoundArgNoGuardPgm (options := .quiet)

/-! A call on `Leaf(y)` under a binder of `y` is rejected even from a caller
that is a node, where it decreases: the rank of `Leaf(y)` is `0`, and a node's
rank is at least `1`. Quantifying the call's obligation over `y` would accept
it. -/

def rankZeroBoundArgFromNodePgm :=
#strata
program Core;

datatype Tree { Leaf(v: int), Node(l: Tree) };

rec function f (@[cases] t : Tree, k : int) : bool
{
  if Tree..isNode(t) then !(forall y : int :: f(Leaf(y), k)) else true
};
#end

/-- error: termination checking 'f': decreasing argument contains a bound variable -/
#guard_msgs in
#eval Core.verify rankZeroBoundArgFromNodePgm (options := .quiet)

/-! A constructor with a recursive field does not get the rank `0`, so a call
on `Node(y)` under a binder of `y` keeps the rank `adtRank(Node(y))`, which
depends on `y`, and is rejected. The call does not decrease: `y` may be `t`. -/

def recursiveConstrBoundArgPgm :=
#strata
program Core;

datatype T { Leaf(x : int), Node(l : T) };

rec function f (@[cases] t : T) : bool
{
  !(forall y : T :: f(Node(y)))
};
#end

/-- error: termination checking 'f': decreasing argument contains a bound variable -/
#guard_msgs in
#eval Core.verify recursiveConstrBoundArgPgm (options := .quiet)

/-! A field could only contain the datatype inside another datatype if nested
datatypes were allowed. They are not: the type checker rejects `Wrap`. Here
termination checking rejects the call first. -/

def nestedConstrBoundArgPgm :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };
datatype T { Leaf(x : int), Wrap(ls : MyList T) };

rec function f (@[cases] t : T) : bool
{
  !(forall y : MyList T :: f(Wrap(y)))
};
#end

/-- error: termination checking 'f': decreasing argument contains a bound variable -/
#guard_msgs in
#eval Core.verify nestedConstrBoundArgPgm (options := .quiet)

/-! A condition under a binder of the body is not a hypothesis of the
termination lemma, since the lemma's binders would capture its bound variable.
Here `y == k + 1` would read as `k == k + 1` and make the lemma vacuous. The
lemma is not proved, rightly: `f(Leaf(0), 0)` calls `f` on `Tree..l(Leaf(0))`,
whose rank is not known to be smaller. -/

def boundGuardPgm :=
#strata
program Core;

datatype Tree { Leaf(v: int), Node(l: Tree) };

rec function f (@[cases] t : Tree, k : int) : bool
{
  !(forall y : int :: if y == int.add(k, 1) then f(Tree..l(t), k) else true)
};
#end

/--
info:
Obligation: f_terminates_0
Property: assert
Result: ❓ unknown

Obligation: f_body_calls_Tree..l_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify boundGuardPgm (options := .quiet)

/-! The same guard over a call on `t` itself, which does not decrease: the
termination lemma is not proved. Without leaving the guard out, its `y` would be
captured as `k`, and the lemma would hold vacuously. `bogus` still passes, from
`g`'s contradictory definition: an unproved termination lemma does not stop a
function's definition from being assumed.

TODO: assume a function's definition only once its termination lemmas are
proved, so that `bogus` is not proved. -/

def boundGuardNoDecreasePgm :=
#strata
program Core;

datatype Tree { Leaf(v: int), Node(l: Tree) };

rec function g (@[cases] t : Tree, k : int) : bool
{
  !(forall y : int :: if y == int.add(k, 1) then g(t, k) else true)
};

procedure P()
{
  assert [bogus]: g(Leaf(1), 0) && !(g(Leaf(1), 0));
};
#end

/--
info:
Obligation: g_terminates_0
Property: assert
Result: ❓ unknown

Obligation: bogus
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify boundGuardNoDecreasePgm (options := .quiet)

/-! Only the conjuncts of a condition that mention a binder of the body are
left out: `Tree..isNode(t)` stays a hypothesis, so the call on `Tree..l(t)`
decreases. -/

def mixedBoundGuardPgm :=
#strata
program Core;

datatype Tree { Leaf(v: int), Node(l: Tree) };

rec function f (@[cases] t : Tree, k : int) : bool
{
  !(forall y : int :: if Tree..isNode(t) && int.gt(y, 0) then f(Tree..l(t), k) else true)
};
#end

/--
info:
Obligation: f_terminates_0
Property: assert
Result: ✅ pass

Obligation: f_body_calls_Tree..l_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify mixedBoundGuardPgm (options := .quiet)

/-! The else branch of a mixed condition assumes `!(Tree..isNode(t) && y > 0)`,
which mentions `y` and is left out whole: it does not imply `isNode(t)` or its
negation. Here the call on `t` itself does not decrease, and its termination
lemma is not proved. -/

def mixedBoundGuardElsePgm :=
#strata
program Core;

datatype Tree { Leaf(v: int), Node(l: Tree) };

rec function f (@[cases] t : Tree, k : int) : bool
{
  !(forall y : int :: if Tree..isNode(t) && int.gt(y, 0) then true else f(t, k))
};
#end

/--
info:
Obligation: f_terminates_0
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify mixedBoundGuardElsePgm (options := .quiet)

/-! A negated mixed condition is not split either: `isNode(t)` is not a
hypothesis of the call on `Tree..l(t)`, whose termination lemma is not
proved. -/

def negatedMixedBoundGuardPgm :=
#strata
program Core;

datatype Tree { Leaf(v: int), Node(l: Tree) };

rec function f (@[cases] t : Tree, k : int) : bool
{
  !(forall y : int :: if !(Tree..isNode(t) && int.gt(y, 0)) then f(Tree..l(t), k) else true)
};
#end

/--
info:
Obligation: f_terminates_0
Property: assert
Result: ❓ unknown

Obligation: f_body_calls_Tree..l_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify negatedMixedBoundGuardPgm (options := .quiet)

/-! A lemma declared before a function is checked without it. -/

def lemmaBeforeFunctionPgm :=
#strata
program Core;

lemma [square_nonneg] (x : int): int.ge(int.mul(x, x), 0);

function square (x : int) : int { int.mul(x, x) }

procedure P(x : int)
{
  assert [uses_square]: int.ge(square(x), 0);
};
#end

/--
info:
Obligation: square_nonneg
Property: assert
Result: ✅ pass

Obligation: uses_square
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify lemmaBeforeFunctionPgm (options := .quiet)

/-! In a call to a polymorphic function of the block, the function becomes a
variable `pid_fn` of its type, applied to the call's arguments, so type checking
infers the call's type even when nothing else constrains it, as for the two
sides of `pid(MyList..tl(xs)) == pid(MyList..tl(xs))`. The last `MyList..tl`
check fails, rightly: for `xs == Cons(h, Nil())`, `pid(MyList..tl(xs))` is
`Nil()`. -/

def polymorphicCallsPgm :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

rec function pid<a>(@[cases] xs : MyList a) : MyList a
{
  if MyList..isNil(xs) then xs
  else if pid(MyList..tl(xs)) == pid(MyList..tl(xs)) then MyList..tl(pid(MyList..tl(xs)))
  else xs
};

procedure P(xs : MyList int)
{
  assert [same]: pid(xs) == pid(xs);
};
#end

/--
info:
Obligation: pid_terminates_0
Property: assert
Result: ✅ pass

Obligation: pid_terminates_1
Property: assert
Result: ✅ pass

Obligation: pid_terminates_2
Property: assert
Result: ✅ pass

Obligation: pid_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass

Obligation: pid_body_calls_MyList..tl_1
Property: assert
Result: ✅ pass

Obligation: pid_body_calls_MyList..tl_2
Property: assert
Result: ✅ pass

Obligation: pid_body_calls_MyList..tl_3
Property: assert
Result: ❌ fail

Obligation: same
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify polymorphicCallsPgm (options := .quiet)

/-! In `h`'s body, the first recursive call's second argument is the bound
variable `z`. It is a hypothesis of the second call's termination lemma, where
`h` becomes a variable `h_fn` of type `IntList -> int -> int`, like every
monomorphic function of the block: the lemma quantifies over every function of
that type. -/

def boundArgumentPgm :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function h (@[cases] xs : IntList, y : int) : int
{
  if IntList..isNil(xs) then 0
  else if (forall z : int :: int.ge(h(IntList..tl(xs), z), 0)) then h(IntList..tl(xs), y) else 2
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: h_terminates_0
Property: assert
Obligation:
(forall x : IntList ::  { IntList..adtRank(x) }
  int.ge(IntList..adtRank(x), 0)) ==> (forall hd : int :: forall tl : IntList ::  { IntList..adtRank(Cons(hd, tl)) }
  int.lt(IntList..adtRank(tl), IntList..adtRank(Cons(hd, tl)))) ==> (forall x : IntList ::  { IntList..adtRank(x) }
  !(IntList..isNil(x)) ==> int.ge(IntList..adtRank(x), 1)) ==> !(IntList..isNil(xs@1)) ==> int.lt(IntList..adtRank(IntList..tl(xs@1)), IntList..adtRank(xs@1))

Label: h_terminates_1
Property: assert
Obligation:
(forall x : IntList ::  { IntList..adtRank(x) }
  int.ge(IntList..adtRank(x), 0)) ==> (forall hd : int :: forall tl : IntList ::  { IntList..adtRank(Cons(hd, tl)) }
  int.lt(IntList..adtRank(tl), IntList..adtRank(Cons(hd, tl)))) ==> (forall x : IntList ::  { IntList..adtRank(x) }
  !(IntList..isNil(x)) ==> int.ge(IntList..adtRank(x), 1)) ==> (forall z : int :: int.ge(h_fn@1(IntList..tl(xs@2), z), 0)) ==> !(IntList..isNil(xs@2)) ==> int.lt(IntList..adtRank(IntList..tl(xs@2)), IntList..adtRank(xs@2))

Label: h_body_calls_IntList..tl_0
Property: assert
Obligation:
!(IntList..isNil(xs@3)) ==> IntList..isCons(xs@3)

Label: h_body_calls_IntList..tl_1
Property: assert
Obligation:
(forall z : int :: int.ge(h_fn@2(IntList..tl(xs@4), z), 0)) ==> !(IntList..isNil(xs@4)) ==> IntList..isCons(xs@4)

---
info:
Obligation: h_terminates_0
Property: assert
Result: ✅ pass

Obligation: h_terminates_1
Property: assert
Result: ✅ pass

Obligation: h_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: h_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify boundArgumentPgm (options := .default)

/-! The repeated call `bad2(m)` in `P` gets a CSE definition shared by every
obligation of the program. Each obligation is sent only the CSE definitions it
uses, so `bad2_terminates_0` does not see `bad2`'s contradictory axiom through
it, and neither does `unrelated`, a false goal that only the solver decides.
`vac2` mentions `bad2` and passes from that axiom, which is why
`bad2_terminates_0` must not pass. Batch and incremental solving agree. -/

def cseSharedCallPgm :=
#strata
program Core;

datatype MyNat { Zero(), Succ(pred: MyNat) };

rec function bad2 (@[cases] n : MyNat) : int
{
  if MyNat..isZero(n) then 0 else int.add(bad2(n), 1)
};

procedure P(m : MyNat)
{
  assert [vac2]: int.lt(bad2(m), bad2(m));
};

procedure Unrelated(z : int)
{
  assert [unrelated]: int.lt(z, z);
};
#end

/--
info:
Obligation: bad2_terminates_0
Property: assert
Result: ❓ unknown

Obligation: vac2
Property: assert
Result: ✅ pass

Obligation: unrelated
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify cseSharedCallPgm (options := .quiet)

/--
info:
Obligation: bad2_terminates_0
Property: assert
Result: ❓ unknown

Obligation: vac2
Property: assert
Result: ✅ pass

Obligation: unrelated
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify cseSharedCallPgm (options := { Core.VerifyOptions.quiet with incremental := true })

/-! A monomorphic function `f` calls the polymorphic `g` of its block at type
`int`, and uses the result as a list of integers. In `f`'s lemmas, `g` becomes
a variable applied to `MyList..tl(xs)`, so type checking infers the call's
instantiation from its argument. The two occurrences of `g(MyList..tl(xs))` get
different variables, since identical polymorphic calls may stand at different
instantiations, so the `MyList..isCons` test does not guard `MyList..hd`, and
`f_body_calls_MyList..hd_2` fails. `g_terminates_0`, for
the call `f(Nil())` in `g`, passes: the rank of `Nil()` is `0`, at whatever
element type. -/

def polymorphicCallFromMonomorphicPgm :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

rec function f (@[cases] xs : MyList int) : int
{
  if MyList..isNil(xs) then 0
  else if MyList..isCons(g(MyList..tl(xs))) then int.add(MyList..hd(g(MyList..tl(xs))), f(MyList..tl(xs)))
  else f(MyList..tl(xs))
}
function g<b> (@[cases] ys : MyList b) : MyList b
{
  if MyList..isNil(ys) then ys else if int.lt(f(Nil()), 0) then ys else g(MyList..tl(ys))
};
#end

/--
info:
Obligation: f_terminates_0
Property: assert
Result: ✅ pass

Obligation: f_terminates_1
Property: assert
Result: ✅ pass

Obligation: f_terminates_2
Property: assert
Result: ✅ pass

Obligation: f_terminates_3
Property: assert
Result: ✅ pass

Obligation: g_terminates_0
Property: assert
Result: ✅ pass

Obligation: g_terminates_1
Property: assert
Result: ✅ pass

Obligation: f_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass

Obligation: f_body_calls_MyList..tl_1
Property: assert
Result: ✅ pass

Obligation: f_body_calls_MyList..hd_2
Property: assert
Result: ❌ fail

Obligation: f_body_calls_MyList..tl_3
Property: assert
Result: ✅ pass

Obligation: f_body_calls_MyList..tl_4
Property: assert
Result: ✅ pass

Obligation: g_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify polymorphicCallFromMonomorphicPgm (options := .quiet)

/-! The two identical calls `g(Nil())` stand at different instantiations,
`MyList int` and `MyList bool`, so they get different variables. In the
termination lemmas for these calls, nothing fixes the element type of the
measure's `Nil()`. The lemmas pass all the same, since the rank of `Nil()`, a
constructor without recursive fields, is `0` at every element type. -/

def polymorphicCallsAtTwoTypesPgm :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

rec function f (@[cases] xs : MyList int) : int
{
  if MyList..isNil(xs) then 0
  else if g(Nil()) == Cons(1, Nil()) then (if g(Nil()) == Cons(true, Nil()) then f(MyList..tl(xs)) else 1)
  else 2
}
function g<b> (@[cases] ys : MyList b) : MyList b
{
  if MyList..isNil(ys) then ys else if int.lt(f(Nil()), 0) then ys else g(MyList..tl(ys))
};
#end

/--
info:
Obligation: f_terminates_0
Property: assert
Result: ✅ pass

Obligation: f_terminates_1
Property: assert
Result: ✅ pass

Obligation: f_terminates_2
Property: assert
Result: ✅ pass

Obligation: g_terminates_0
Property: assert
Result: ✅ pass

Obligation: g_terminates_1
Property: assert
Result: ✅ pass

Obligation: f_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass

Obligation: g_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify polymorphicCallsAtTwoTypesPgm (options := .quiet)

/-! `g`'s type parameter appears only in its output, so nothing fixes it in
`f`'s lemmas: it becomes a fresh opaque type. -/

def outputOnlyTypeParamPgm :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

rec function f (@[cases] xs : MyList int) : int
{
  if MyList..isNil(xs) then 0
  else if MyList..isCons(g(MyList..tl(xs))) then int.add(MyList..hd(g(MyList..tl(xs))), f(MyList..tl(xs)))
  else f(MyList..tl(xs))
}
function g<b> (@[cases] ys : MyList int) : MyList b
{
  if MyList..isNil(ys) then Nil() else if int.lt(f(Nil()), 0) then Nil() else g(MyList..tl(ys))
};
#end

/--
info:
Obligation: f_terminates_0
Property: assert
Result: ✅ pass

Obligation: f_terminates_1
Property: assert
Result: ✅ pass

Obligation: f_terminates_2
Property: assert
Result: ✅ pass

Obligation: f_terminates_3
Property: assert
Result: ✅ pass

Obligation: g_terminates_0
Property: assert
Result: ✅ pass

Obligation: g_terminates_1
Property: assert
Result: ✅ pass

Obligation: f_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass

Obligation: f_body_calls_MyList..tl_1
Property: assert
Result: ✅ pass

Obligation: f_body_calls_MyList..hd_2
Property: assert
Result: ❌ fail

Obligation: f_body_calls_MyList..tl_3
Property: assert
Result: ✅ pass

Obligation: f_body_calls_MyList..tl_4
Property: assert
Result: ✅ pass

Obligation: g_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify outputOnlyTypeParamPgm (options := .quiet)

/-! `r2` becomes one variable `r2_fn` for both of its calls, so the lemma keeps
that they agree on equal arguments: `r2(int.sub(n, 1))` and
`r2(int.add(int.sub(n, 2), 1))` are equal, and the division is well-formed. -/

def congruencePgm :=
#strata
program Core;

rec function r2 (n : int) : int
  decreases n
{
  if int.le(n, 0) then 1
  else if int.gt(r2(int.sub(n, 1)), 0) then int.safeDiv(10, r2(int.add(int.sub(n, 2), 1)))
  else 1
};
#end

/--
info:
Obligation: r2_terminates_0
Property: assert
Result: ✅ pass

Obligation: r2_terminates_1
Property: assert
Result: ✅ pass

Obligation: r2_terminates_2
Property: assert
Result: ✅ pass

Obligation: r2_terminates_3
Property: assert
Result: ✅ pass

Obligation: r2_body_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify congruencePgm (options := .quiet)

/-! A failing well-formedness check that mentions a call still reports its
counterexample: the variable `r_fn` standing for `r` is left out of it, since
a function has no value SMT-LIB can print. -/

def counterexampleWithCallPgm :=
#strata
program Core;

rec function r (n : int) : int
  decreases n
{
  if int.le(n, 0) then 1 else int.safeDiv(10, r(int.sub(n, 1)))
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: r_terminates_0
Property: assert
Obligation:
!(int.le(n@1, 0)) ==> int.le(0, int.sub(n@1, 1))

Label: r_terminates_1
Property: assert
Obligation:
!(int.le(n@2, 0)) ==> int.lt(int.sub(n@2, 1), n@2)

Label: r_body_calls_Int.SafeDiv_0
Property: division by zero check
Obligation:
!(int.le(n@3, 0)) ==> !(r_fn@1(int.sub(n@3, 1)) == 0)

---
info:
Obligation: r_terminates_0
Property: assert
Result: ✅ pass

Obligation: r_terminates_1
Property: assert
Result: ✅ pass

Obligation: r_body_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❌ fail
Model:
(n@3, 1)
-/
#guard_msgs in
#eval Core.verify counterexampleWithCallPgm

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: r_terminates_0
Property: assert
Obligation:
!(int.le(n@1, 0)) ==> int.le(0, int.sub(n@1, 1))

Label: r_terminates_1
Property: assert
Obligation:
!(int.le(n@2, 0)) ==> int.lt(int.sub(n@2, 1), n@2)

Label: r_body_calls_Int.SafeDiv_0
Property: division by zero check
Obligation:
!(int.le(n@3, 0)) ==> !(r_fn@1(int.sub(n@3, 1)) == 0)

---
info:
Obligation: r_terminates_0
Property: assert
Result: ✅ pass

Obligation: r_terminates_1
Property: assert
Result: ✅ pass

Obligation: r_body_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❌ fail
Model:
(n@3, 1)
-/
#guard_msgs in
#eval Core.verify counterexampleWithCallPgm (options := { Core.VerifyOptions.default with incremental := true })

/-! A valid lemma that is not proved yet. The division by `plen(MyList..tl(xs))`
is guarded by `plen(MyList..tl(xs)) > 0`, but the two calls to the polymorphic
`plen` get separate variables, so they are not known to agree and
`plen_body_calls_Int.SafeDiv_2` fails. Sharing one variable per type
instantiation of `plen` should make it pass. -/

def polymorphicCallsNotSharedPgm :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

rec function plen<a> (@[cases] xs : MyList a) : int
{
  if MyList..isNil(xs) then 0
  else if int.gt(plen(MyList..tl(xs)), 0) then int.safeDiv(10, plen(MyList..tl(xs)))
  else 1
};
#end

/--
info:
Obligation: plen_terminates_0
Property: assert
Result: ✅ pass

Obligation: plen_terminates_1
Property: assert
Result: ✅ pass

Obligation: plen_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass

Obligation: plen_body_calls_MyList..tl_1
Property: assert
Result: ✅ pass

Obligation: plen_body_calls_Int.SafeDiv_2
Property: division by zero check
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify polymorphicCallsNotSharedPgm (options := .quiet)

end Strata.AbstractedLemmasTest
