/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Termination Checking Integration Tests

Tests termination checking for recursive functions over algebraic datatypes.
The TermCheck pipeline phase generates `D..dtRank` UF declarations, per-constructor
axioms, and `$$term` procedures that assert `dtRank` decreases at each recursive
call site.
-/

namespace Strata.TerminationCheckTest

---------------------------------------------------------------------
-- Test 1: listLen — basic structural recursion (full VCs shown)
---------------------------------------------------------------------

def listLenTermPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};

procedure TestListLen() returns ()
spec {
  ensures true;
}
{
  assert [nilLen]: listLen(Nil()) == 0;
  assert [oneLen]: listLen(Cons(1, Nil())) == 1;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listLenTermPgm) |>.snd |>.isEmpty

/-- info: [Strata.Core] Type checking succeeded.


VCs:
Label: listLen_terminates_0
Property: assert
Assumptions:
IntList..dtRank_0: forall __q0 : IntList ::  { IntList..dtRank(__q0) }
  IntList..dtRank(__q0) >= 0
IntList..dtRank_1: forall __q0 : int :: forall __q1 : IntList ::  { IntList..dtRank(Cons(__q0, __q1)) }
  IntList..dtRank(__q1) < IntList..dtRank(Cons(__q0, __q1))
Obligation:
!(IntList..isNil($__xs0)) ==> IntList..dtRank(IntList..tl($__xs0)) < IntList..dtRank($__xs0)

Label: listLen_body_calls_IntList..tl_0
Property: assert
Obligation:
!(IntList..isNil($__xs1)) ==> IntList..isCons($__xs1)

Label: nilLen
Property: assert
Obligation:
true

Label: oneLen
Property: assert
Obligation:
true

Label: TestListLen_ensures_0
Property: assert
Obligation:
true

---
info:
Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: nilLen
Property: assert
Result: ✅ pass

Obligation: oneLen
Property: assert
Result: ✅ pass

Obligation: TestListLen_ensures_0
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval verify listLenTermPgm (options := .default)

---------------------------------------------------------------------
-- Test 2: contains — recursion on non-first parameter
---------------------------------------------------------------------

def containsTermPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function contains (key : int, @[cases] xs : IntList) : bool
{
  if IntList..isNil(xs) then false
  else if IntList..hd(xs) == key then true
  else contains(key, IntList..tl(xs))
};
#end

/-- info:
Obligation: contains_terminates_0
Property: assert
Result: ✅ pass

Obligation: contains_body_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: contains_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval verify containsTermPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 3: non-terminating — f(xs) = f(xs) (should fail)
---------------------------------------------------------------------

def nonTermPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function bad (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else bad(xs)
};
#end

/-- info:
Obligation: bad_terminates_0
Property: assert
Result: ❓ unknown -/
#guard_msgs in
#eval verify nonTermPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 4: non-terminating — wrong direction f(xs) = f(Cons(1, xs))
---------------------------------------------------------------------

def wrongDirPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function bad (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else bad(Cons(1, xs))
};
#end

/-- info:
Obligation: bad_terminates_0
Property: assert
Result: ❓ unknown -/
#guard_msgs in
#eval verify wrongDirPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 5: multiple recursive calls in branches — both must decrease
---------------------------------------------------------------------

def multiBranchPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function sumList (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0
  else if IntList..isNil(IntList..tl(xs)) then IntList..hd(xs)
  else IntList..hd(xs) + sumList(IntList..tl(xs))
};
#end

/-- info:
Obligation: sumList_terminates_0
Property: assert
Result: ✅ pass

Obligation: sumList_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: sumList_body_calls_IntList..hd_1
Property: assert
Result: ✅ pass

Obligation: sumList_body_calls_IntList..hd_2
Property: assert
Result: ✅ pass

Obligation: sumList_body_calls_IntList..tl_3
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval verify multiBranchPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 6: mutual recursion — isEven/isOdd over MyNat
---------------------------------------------------------------------

def mutualTermPgm : Program :=
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

procedure TestMutual() returns ()
spec {
  ensures true;
}
{
  assert [zeroEven]: isEven(Zero()) == true;
  assert [oneOdd]: isOdd(Succ(Zero())) == true;
};
#end

/-- info:
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

Obligation: oneOdd
Property: assert
Result: ✅ pass

Obligation: TestMutual_ensures_0
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval verify mutualTermPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 7: two recFuncBlocks using the same datatype (no duplicate dtRank)
---------------------------------------------------------------------

def sharedDtPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};

rec function listSum (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else IntList..hd(xs) + listSum(IntList..tl(xs))
};

procedure Test() returns ()
spec {
  ensures true;
}
{
  assert [lenNil]: listLen(Nil()) == 0;
  assert [sumNil]: listSum(Nil()) == 0;
};
#end

/-- info:
Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: listSum_terminates_0
Property: assert
Result: ✅ pass

Obligation: listSum_body_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: listSum_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass

Obligation: lenNil
Property: assert
Result: ✅ pass

Obligation: sumNil
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval verify sharedDtPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 8: multiple recursive calls per branch — Tree with Branch and Chain
-- Branch(left, right) has two recursive fields → two termination obligations
-- Chain(head, tail) has one recursive field → one termination obligation
---------------------------------------------------------------------

def treeSizePgm : Program :=
#strata
program Core;

datatype Tree { Leaf(val: int), Branch(left: Tree, right: Tree), Chain(head: int, tail: Tree) };

rec function treeSize (@[cases] t : Tree) : int
{
  if Tree..isLeaf(t) then 1
  else if Tree..isBranch(t) then treeSize(Tree..left(t)) + treeSize(Tree..right(t))
  else 1 + treeSize(Tree..tail(t))
};

procedure TestTreeSize() returns ()
spec {
  ensures true;
}
{
  assert [leaf]: treeSize(Leaf(42)) == 1;
  assert [branch]: treeSize(Branch(Leaf(1), Leaf(2))) == 2;
  assert [chain]: treeSize(Chain(0, Leaf(1))) == 2;
};
#end

/-- info: [Strata.Core] Type checking succeeded.


VCs:
Label: treeSize_terminates_0
Property: assert
Assumptions:
Tree..dtRank_0: forall __q0 : Tree ::  { Tree..dtRank(__q0) }
  Tree..dtRank(__q0) >= 0
Tree..dtRank_1: forall __q0 : Tree :: forall __q1 : Tree ::  { Tree..dtRank(Branch(__q0, __q1)) }
  Tree..dtRank(__q0) < Tree..dtRank(Branch(__q0, __q1))
Tree..dtRank_2: forall __q0 : Tree :: forall __q1 : Tree ::  { Tree..dtRank(Branch(__q0, __q1)) }
  Tree..dtRank(__q1) < Tree..dtRank(Branch(__q0, __q1))
Tree..dtRank_3: forall __q0 : int :: forall __q1 : Tree ::  { Tree..dtRank(Chain(__q0, __q1)) }
  Tree..dtRank(__q1) < Tree..dtRank(Chain(__q0, __q1))
Obligation:
Tree..isBranch($__t0) ==> !(Tree..isLeaf($__t0)) ==> Tree..dtRank(Tree..left($__t0)) < Tree..dtRank($__t0)

Label: treeSize_terminates_1
Property: assert
Assumptions:
Tree..dtRank_0: forall __q0 : Tree ::  { Tree..dtRank(__q0) }
  Tree..dtRank(__q0) >= 0
Tree..dtRank_1: forall __q0 : Tree :: forall __q1 : Tree ::  { Tree..dtRank(Branch(__q0, __q1)) }
  Tree..dtRank(__q0) < Tree..dtRank(Branch(__q0, __q1))
Tree..dtRank_2: forall __q0 : Tree :: forall __q1 : Tree ::  { Tree..dtRank(Branch(__q0, __q1)) }
  Tree..dtRank(__q1) < Tree..dtRank(Branch(__q0, __q1))
Tree..dtRank_3: forall __q0 : int :: forall __q1 : Tree ::  { Tree..dtRank(Chain(__q0, __q1)) }
  Tree..dtRank(__q1) < Tree..dtRank(Chain(__q0, __q1))
Obligation:
Tree..isBranch($__t0) ==> !(Tree..isLeaf($__t0)) ==> Tree..dtRank(Tree..right($__t0)) < Tree..dtRank($__t0)

Label: treeSize_terminates_2
Property: assert
Assumptions:
Tree..dtRank_0: forall __q0 : Tree ::  { Tree..dtRank(__q0) }
  Tree..dtRank(__q0) >= 0
Tree..dtRank_1: forall __q0 : Tree :: forall __q1 : Tree ::  { Tree..dtRank(Branch(__q0, __q1)) }
  Tree..dtRank(__q0) < Tree..dtRank(Branch(__q0, __q1))
Tree..dtRank_2: forall __q0 : Tree :: forall __q1 : Tree ::  { Tree..dtRank(Branch(__q0, __q1)) }
  Tree..dtRank(__q1) < Tree..dtRank(Branch(__q0, __q1))
Tree..dtRank_3: forall __q0 : int :: forall __q1 : Tree ::  { Tree..dtRank(Chain(__q0, __q1)) }
  Tree..dtRank(__q1) < Tree..dtRank(Chain(__q0, __q1))
Obligation:
!(Tree..isBranch($__t0)) ==> !(Tree..isLeaf($__t0)) ==> Tree..dtRank(Tree..tail($__t0)) < Tree..dtRank($__t0)

Label: treeSize_body_calls_Tree..left_0
Property: assert
Obligation:
Tree..isBranch($__t1) ==> !(Tree..isLeaf($__t1)) ==> Tree..isBranch($__t1)

Label: treeSize_body_calls_Tree..right_1
Property: assert
Obligation:
Tree..isBranch($__t1) ==> !(Tree..isLeaf($__t1)) ==> Tree..isBranch($__t1)

Label: treeSize_body_calls_Tree..tail_2
Property: assert
Obligation:
!(Tree..isBranch($__t1)) ==> !(Tree..isLeaf($__t1)) ==> Tree..isChain($__t1)

Label: leaf
Property: assert
Obligation:
true

Label: branch
Property: assert
Obligation:
true

Label: chain
Property: assert
Obligation:
true

Label: TestTreeSize_ensures_0
Property: assert
Obligation:
true

---
info:
Obligation: treeSize_terminates_0
Property: assert
Result: ✅ pass

Obligation: treeSize_terminates_1
Property: assert
Result: ✅ pass

Obligation: treeSize_terminates_2
Property: assert
Result: ✅ pass

Obligation: treeSize_body_calls_Tree..left_0
Property: assert
Result: ✅ pass

Obligation: treeSize_body_calls_Tree..right_1
Property: assert
Result: ✅ pass

Obligation: treeSize_body_calls_Tree..tail_2
Property: assert
Result: ✅ pass

Obligation: leaf
Property: assert
Result: ✅ pass

Obligation: branch
Property: assert
Result: ✅ pass

Obligation: chain
Property: assert
Result: ✅ pass

Obligation: TestTreeSize_ensures_0
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval verify treeSizePgm (options := .default)

end Strata.TerminationCheckTest
