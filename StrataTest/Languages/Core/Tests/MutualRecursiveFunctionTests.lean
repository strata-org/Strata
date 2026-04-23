/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

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

/-- info: [Strata.Core] Type checking succeeded.


VCs:
Label: isEven_body_calls_MyNat..pred_0
Property: assert
Obligation:
!(MyNat..isZero($__n0)) ==> MyNat..isSucc($__n0)

Label: isOdd_body_calls_MyNat..pred_0
Property: assert
Obligation:
!(MyNat..isZero($__n1)) ==> MyNat..isSucc($__n1)

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
info: Obligation: isEven_body_calls_MyNat..pred_0
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
Result: ✅ pass-/
#guard_msgs in
#eval verify mutualRecPgm (options := .default)

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
  if RoseList..isRNil(xs) then 0 else treeSize(RoseList..hd(xs)) + listSize(RoseList..tl(xs))
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
info: Obligation: treeSize_body_calls_RoseTree..children_0
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
#eval verify roseTreePgm (options := .quiet)

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
  if MyNat..isZero(n) then 0 else 1 + oddHalf(MyNat..pred(n))
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
Obligation: isEven_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: isOdd_body_calls_MyNat..pred_0
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
#eval verify mutualPrecondPgm (options := .quiet)

end Strata.MutualRecursivePrecondTest
