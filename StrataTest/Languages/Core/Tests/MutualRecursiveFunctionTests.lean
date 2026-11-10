/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)

/-!
# Mutual Recursive Function Verification Tests

Tests mutually recursive functions (isEven/isOdd) over algebraic datatypes,
verifying parsing, translation, axiom-based SMT encoding, and end-to-end
verification.
-/

namespace Strata.MutualRecursiveFunctionTest

def mutualRecPgm : Program :=
#strata
program Core;

datatype MyNat { Zero(), Succ(pred: MyNat) };

rec function isEven (@[cases] n : MyNat) : bool
{
  if MyNat..isZero(n) then true else isOdd(MyNat..pred(n))
}
function isOdd (@[cases] n : MyNat) : bool
{
  if MyNat..isZero(n) then false else isEven(MyNat..pred(n))
};

procedure TestMutual()
spec {
  ensures true;
}
{
  assert [zeroEven]: isEven(Zero()) == true;
  assert [zeroNotOdd]: isOdd(Zero()) == false;
  assert [oneOdd]: isOdd(Succ(Zero())) == true;
  assert [oneNotEven]: isEven(Succ(Zero())) == false;
};
#end

/--
info: true
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram mutualRecPgm) |>.snd |>.isEmpty

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: isEven_terminates_0
Property: assert
Obligation:
(forall x : MyNat ::  { MyNat..adtRank(x) }
  int.ge(MyNat..adtRank(x), 0)) ==> (forall pred : MyNat ::  { MyNat..adtRank(Succ(pred)) }
  int.lt(MyNat..adtRank(pred), MyNat..adtRank(Succ(pred)))) ==> (forall x : MyNat ::  { MyNat..adtRank(x) }
  !(MyNat..isZero(x)) ==> int.ge(MyNat..adtRank(x), 1)) ==> !(MyNat..isZero(n@1)) ==> int.lt(MyNat..adtRank(MyNat..pred(n@1)), MyNat..adtRank(n@1))

Label: isOdd_terminates_0
Property: assert
Obligation:
(forall x : MyNat ::  { MyNat..adtRank(x) }
  int.ge(MyNat..adtRank(x), 0)) ==> (forall pred : MyNat ::  { MyNat..adtRank(Succ(pred)) }
  int.lt(MyNat..adtRank(pred), MyNat..adtRank(Succ(pred)))) ==> (forall x : MyNat ::  { MyNat..adtRank(x) }
  !(MyNat..isZero(x)) ==> int.ge(MyNat..adtRank(x), 1)) ==> !(MyNat..isZero(n@2)) ==> int.lt(MyNat..adtRank(MyNat..pred(n@2)), MyNat..adtRank(n@2))

Label: isEven_body_calls_MyNat..pred_0
Property: assert
Obligation:
!(MyNat..isZero(n@3)) ==> MyNat..isSucc(n@3)

Label: isOdd_body_calls_MyNat..pred_0
Property: assert
Obligation:
!(MyNat..isZero(n@4)) ==> MyNat..isSucc(n@4)

Label: zeroEven
Property: assert
Obligation:
true

Label: zeroNotOdd
Property: assert
Obligation:
true

Label: oneOdd
Property: assert
Obligation:
true

Label: oneNotEven
Property: assert
Obligation:
true

Label: TestMutual_ensures_0
Property: assert
Obligation:
true

---
info:
Obligation: isEven_terminates_0
Property: assert
Result: ✅ pass

Obligation: isOdd_terminates_0
Property: assert
Result: ✅ pass

Obligation: isEven_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: isOdd_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: zeroEven
Property: assert
Result: ✅ pass

Obligation: zeroNotOdd
Property: assert
Result: ✅ pass

Obligation: oneOdd
Property: assert
Result: ✅ pass

Obligation: oneNotEven
Property: assert
Result: ✅ pass

Obligation: TestMutual_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify mutualRecPgm (options := .default)

end Strata.MutualRecursiveFunctionTest

---------------------------------------------------------------------

namespace Strata.MutualRecursiveRoseTreeTest

def roseTreePgm : Program :=
#strata
program Core;

datatype RoseTree { Leaf(val: int), Node(children: RoseList) }
datatype RoseList { RNil(), RCons(hd: RoseTree, tl: RoseList) };

rec function treeSize (@[cases] t : RoseTree) : int
{
  if RoseTree..isLeaf(t) then 1 else listSize(RoseTree..children(t))
}
function listSize (@[cases] xs : RoseList) : int
{
  if RoseList..isRNil(xs) then 0 else int.add(treeSize(RoseList..hd(xs)), listSize(RoseList..tl(xs)))
};

procedure TestRoseTreeGround()
spec {
  ensures true;
}
{
  assert [leafSize]: treeSize(Leaf(42)) == 1;
  assert [singleChild]: treeSize(Node(RCons(Leaf(1), RNil()))) == 1;
  assert [twoChildren]: treeSize(Node(RCons(Leaf(1), RCons(Leaf(2), RNil())))) == 2;
};

procedure TestRoseTreeHavoc()
spec {
  ensures true;
}
{
  var t : RoseTree;
  var xs : RoseList;

  havoc t;
  assume RoseTree..isLeaf(t);
  assert [havocLeafSize]: treeSize(t) == 1;

  havoc xs;
  assume RoseList..isRNil(xs);
  assert [havocEmptyList]: listSize(xs) == 0;

  havoc xs;
  assume xs == RCons(Leaf(5), RCons(Leaf(7), RNil()));
  assert [havocTwoLeaves]: listSize(xs) == 2;
};
#end

/--
info: true
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram roseTreePgm) |>.snd |>.isEmpty

/--
info:
Obligation: treeSize_terminates_0
Property: assert
Result: ✅ pass

Obligation: listSize_terminates_0
Property: assert
Result: ✅ pass

Obligation: listSize_terminates_1
Property: assert
Result: ✅ pass

Obligation: treeSize_body_calls_RoseTree..children_0
Property: assert
Result: ✅ pass

Obligation: listSize_body_calls_RoseList..hd_0
Property: assert
Result: ✅ pass

Obligation: listSize_body_calls_RoseList..tl_1
Property: assert
Result: ✅ pass

Obligation: leafSize
Property: assert
Result: ✅ pass

Obligation: singleChild
Property: assert
Result: ✅ pass

Obligation: twoChildren
Property: assert
Result: ✅ pass

Obligation: TestRoseTreeGround_ensures_0
Property: assert
Result: ✅ pass

Obligation: havocLeafSize
Property: assert
Result: ✅ pass

Obligation: havocEmptyList
Property: assert
Result: ✅ pass

Obligation: havocTwoLeaves
Property: assert
Result: ✅ pass

Obligation: TestRoseTreeHavoc_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify roseTreePgm (options := .quiet)

end Strata.MutualRecursiveRoseTreeTest

---------------------------------------------------------------------

namespace Strata.MutualRecursivePrecondTest

def mutualPrecondPgm : Program :=
#strata
program Core;

datatype MyNat { Zero(), Succ(pred: MyNat) };

rec function isEven (@[cases] n : MyNat) : bool
{
  if MyNat..isZero(n) then true else isOdd(MyNat..pred(n))
}
function isOdd (@[cases] n : MyNat) : bool
{
  if MyNat..isZero(n) then false else isEven(MyNat..pred(n))
};

rec function evenHalf (@[cases] n : MyNat) : int
  requires isEven(n);
{
  if MyNat..isZero(n) then 0 else int.add(1, oddHalf(MyNat..pred(n)))
}
function oddHalf (@[cases] n : MyNat) : int
  requires isOdd(n);
{
  evenHalf(MyNat..pred(n))
};

procedure TestHalfGround()
spec {
  ensures true;
}
{
  assert [half0]: evenHalf(Zero()) == 0;
  assert [half2]: evenHalf(Succ(Succ(Zero()))) == 1;
  assert [half1]: oddHalf(Succ(Zero())) == 0;
  assert [half3]: oddHalf(Succ(Succ(Succ(Zero())))) == 1;
};

procedure TestHalfHavoc()
spec {
  ensures true;
}
{
  var n : MyNat;
  havoc n;
  assume isEven(n);
  assume MyNat..isZero(n);
  assert [havocEvenZero]: evenHalf(n) == 0;
};
#end

/--
info: true
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram mutualPrecondPgm) |>.snd |>.isEmpty

/--
info:
Obligation: isEven_terminates_0
Property: assert
Result: ✅ pass

Obligation: isOdd_terminates_0
Property: assert
Result: ✅ pass

Obligation: isEven_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: isOdd_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: evenHalf_terminates_0
Property: assert
Result: ✅ pass

Obligation: oddHalf_terminates_0
Property: assert
Result: ✅ pass

Obligation: evenHalf_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: evenHalf_body_calls_oddHalf_1
Property: assert
Result: ✅ pass

Obligation: oddHalf_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: oddHalf_body_calls_evenHalf_1
Property: assert
Result: ✅ pass

Obligation: assert_half0_calls_evenHalf_0
Property: assert
Result: ✅ pass

Obligation: half0
Property: assert
Result: ✅ pass

Obligation: assert_half2_calls_evenHalf_0
Property: assert
Result: ✅ pass

Obligation: half2
Property: assert
Result: ✅ pass

Obligation: assert_half1_calls_oddHalf_0
Property: assert
Result: ✅ pass

Obligation: half1
Property: assert
Result: ✅ pass

Obligation: assert_half3_calls_oddHalf_0
Property: assert
Result: ✅ pass

Obligation: half3
Property: assert
Result: ✅ pass

Obligation: TestHalfGround_ensures_0
Property: assert
Result: ✅ pass

Obligation: assert_havocEvenZero_calls_evenHalf_0
Property: assert
Result: ✅ pass

Obligation: havocEvenZero
Property: assert
Result: ✅ pass

Obligation: TestHalfHavoc_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify mutualPrecondPgm (options := .quiet)

end Strata.MutualRecursivePrecondTest

---------------------------------------------------------------------

namespace Strata.PolyMutualStructTest

/-!
Mutually recursive polymorphic functions with a structural (`@[cases]`)
measure, used at a ground type so the block reaches the verifier.
-/

def polyMutualStructPgm : Program :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

rec function evenLen<a>(@[cases] xs : MyList a) : bool
{
  if MyList..isNil(xs) then true else oddLen(MyList..tl(xs))
}
function oddLen<a>(@[cases] xs : MyList a) : bool
{
  if MyList..isNil(xs) then false else evenLen(MyList..tl(xs))
};

procedure TestPolyMutual(out r : bool)
spec {
  ensures true;
}
{
  var xs : MyList int;
  xs := Cons(1, Cons(2, Nil()));
  r := evenLen(xs);
};
#end

/--
info: true
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram polyMutualStructPgm) |>.snd |>.isEmpty

/--
info:
Obligation: evenLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: oddLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: evenLen_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass

Obligation: oddLen_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass

Obligation: TestPolyMutual_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify polyMutualStructPgm (options := .quiet)

end Strata.PolyMutualStructTest


/-! ## Mutual functions that order their type parameters differently

The termination lemma of a call into another function of the block annotates
the callee's measure with the callee's own type-parameter names, read in the
caller's scope. When the two functions order their type parameters
differently, a well-typed block is rejected by the type checking of that
lemma. The error below is that bug, not the intended behavior: once it is
fixed, this block verifies. -/

namespace Strata.SwappedTypeParamsTest

def swappedStructPgm : Program :=
#strata
program Core;
datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };
rec function g<p, q> (@[cases] xs : MyList p, y : q) : q
{ if MyList..isNil(xs) then y else g2(MyList..tl(xs), y) }
function g2<q, p> (@[cases] xs : MyList q, y : p) : p
{ if MyList..isNil(xs) then y else g(MyList..tl(xs), y) };
#end

/--
error: ❌ Type checking error.
Impossible to unify (arrow (MyList $__ty40) int) with (arrow (MyList $__opaque_g_terminates_0_p_0) $__ty45).
First mismatch: $__opaque_g_terminates_0_q_1 with $__opaque_g_terminates_0_p_0.
-/
#guard_msgs in
#eval Core.verify swappedStructPgm (options := .quiet)

/-! The same bug cannot make a termination obligation easier from source: a
measure cannot name the instance of a type parameter that the swap gets wrong.
The obligations below are those of the matching order, and every block whose
measure does not decrease is rejected. A front end that builds Core directly
with explicit instance annotations is not covered by these tests. -/

/-! A measure that does not decrease, with type parameters used nowhere. -/

def swappedUnusedPgm : Program :=
#strata
program Core;
rec function g<p, q> (x : int) : int
  decreases x
{ g2(x) }
function g2<q, p> (x : int) : int
  decreases x
{ g(x) };
#end

/--
info:
Obligation: g_terminates_0
Property: assert
Result: ❌ fail

Obligation: g_terminates_1
Property: assert
Result: ❌ fail

Obligation: g2_terminates_0
Property: assert
Result: ❌ fail

Obligation: g2_terminates_1
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify swappedUnusedPgm (options := .quiet)

/-! A measure through a function whose type parameter is phantom: its instance
is not fixed by its arguments, so it cannot depend on `p` or `q`. -/

def swappedPhantomPgm : Program :=
#strata
program Core;
function c<t> () : int;
rec function g<p, q> (x : int) : int
  decreases int.add(x, c())
{ g2(x) }
function g2<q, p> (x : int) : int
  decreases int.add(x, c())
{ g(x) };
#end

/--
info:
Obligation: g_terminates_0
Property: assert
Result: ❌ fail

Obligation: g_terminates_1
Property: assert
Result: ❌ fail

Obligation: g2_terminates_0
Property: assert
Result: ❌ fail

Obligation: g2_terminates_1
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify swappedPhantomPgm (options := .quiet)

/-! The same with two phantom measures and an axiom relating them at matching
instances: the call back with a larger argument does not decrease, so the
block is rejected. -/

def swappedLinkedPgm : Program :=
#strata
program Core;
function m1<a, b> (n : int) : int;
function m2<a, b> (n : int) : int;
axiom [link]: forall n : int :: int.lt(m2(n), m1(n));
rec function g<p, q> (x : int) : int
  decreases m1(x)
{ g2(x) }
function g2<q, p> (x : int) : int
  decreases m2(x)
{ g(int.add(x, 1)) };
#end

/--
info:
Obligation: g_terminates_0
Property: assert
Result: ❓ unknown

Obligation: g_terminates_1
Property: assert
Result: ✅ pass

Obligation: g2_terminates_0
Property: assert
Result: ❓ unknown

Obligation: g2_terminates_1
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify swappedLinkedPgm (options := .quiet)

/-! A measure that depends on a type parameter through a quantifier is rejected
outright: a measure may not contain bound variables. -/

def swappedQuantifiedPgm : Program :=
#strata
program Core;
rec function g<p, q> (x : int) : int
  decreases (if (forall w : q, v : q :: w == v) then 1 else 0)
{ g2(x) }
function g2<q, p> (x : int) : int
  decreases (if (forall w : p, v : p :: w == v) then 0 else 1)
{ g(x) };
#end

/--
error: termination checking 'g': decreasing argument contains a bound variable
-/
#guard_msgs in
#eval Core.verify swappedQuantifiedPgm (options := .quiet)

end Strata.SwappedTypeParamsTest

end
