/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Termination Checking Tests

Tests termination checking for recursive functions over algebraic datatypes.
-/

namespace Strata.TerminationCheckTest

---------------------------------------------------------------------
-- Test 1: listLen — basic structural recursion
---------------------------------------------------------------------

def listLenTermPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};

procedure TestListLen() spec {
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
Label: listLen_body_calls_IntList..tl_0
Property: assert
Obligation:
!(IntList..isNil(xs@1)) ==> IntList..isCons(xs@1)

Label: listLen_terminates_0
Property: assert
Assumptions:
IntList..adtRank_0: forall __q0 : IntList ::  { IntList..adtRank(__q0) }
  IntList..adtRank(__q0) >= 0
IntList..adtRank_1: forall __q0 : int :: forall __q1 : IntList ::  { IntList..adtRank(Cons(__q0, __q1)) }
  IntList..adtRank(__q1) < IntList..adtRank(Cons(__q0, __q1))
Obligation:
!(IntList..isNil(xs@2)) ==> IntList..adtRank(IntList..tl(xs@2)) < IntList..adtRank(xs@2)

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
Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: listLen_terminates_0
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
Obligation: contains_body_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: contains_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass

Obligation: contains_terminates_0
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
Result: ✅ pass

Obligation: sumList_terminates_0
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

procedure TestMutual() spec {
  ensures true;
}
{
  assert [zeroEven]: isEven(Zero()) == true;
  assert [oneOdd]: isOdd(Succ(Zero())) == true;
};
#end

/-- info:
Obligation: isEven_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: isOdd_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: isEven_terminates_0
Property: assert
Result: ✅ pass

Obligation: isOdd_terminates_0
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

procedure Test() spec {
  ensures true;
}
{
  assert [lenNil]: listLen(Nil()) == 0;
  assert [sumNil]: listSum(Nil()) == 0;
};
#end

/-- info: [Strata.Core] Type checking succeeded.


VCs:
Label: listLen_body_calls_IntList..tl_0
Property: assert
Obligation:
!(IntList..isNil(xs@1)) ==> IntList..isCons(xs@1)

Label: listLen_terminates_0
Property: assert
Assumptions:
IntList..adtRank_0: forall __q0 : IntList ::  { IntList..adtRank(__q0) }
  IntList..adtRank(__q0) >= 0
IntList..adtRank_1: forall __q0 : int :: forall __q1 : IntList ::  { IntList..adtRank(Cons(__q0, __q1)) }
  IntList..adtRank(__q1) < IntList..adtRank(Cons(__q0, __q1))
Obligation:
!(IntList..isNil(xs@2)) ==> IntList..adtRank(IntList..tl(xs@2)) < IntList..adtRank(xs@2)

Label: listSum_body_calls_IntList..hd_0
Property: assert
Obligation:
!(IntList..isNil(xs@3)) ==> IntList..isCons(xs@3)

Label: listSum_body_calls_IntList..tl_1
Property: assert
Obligation:
!(IntList..isNil(xs@3)) ==> IntList..isCons(xs@3)

Label: listSum_terminates_0
Property: assert
Assumptions:
IntList..adtRank_0: forall __q0 : IntList ::  { IntList..adtRank(__q0) }
  IntList..adtRank(__q0) >= 0
IntList..adtRank_1: forall __q0 : int :: forall __q1 : IntList ::  { IntList..adtRank(Cons(__q0, __q1)) }
  IntList..adtRank(__q1) < IntList..adtRank(Cons(__q0, __q1))
Obligation:
!(IntList..isNil(xs@4)) ==> IntList..adtRank(IntList..tl(xs@4)) < IntList..adtRank(xs@4)

Label: lenNil
Property: assert
Obligation:
true

Label: sumNil
Property: assert
Obligation:
true

Label: Test_ensures_0
Property: assert
Obligation:
true

---
info:
Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: listSum_body_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: listSum_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass

Obligation: listSum_terminates_0
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
#eval verify sharedDtPgm (options := .default)

---------------------------------------------------------------------
-- Test 8: multiple recursive calls per branch — Tree with Branch and Chain
-- Branch(left, right) has two recursive fields
-- Chain(head, tail) has one recursive field
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

procedure TestTreeSize() spec {
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
Label: treeSize_body_calls_Tree..left_0
Property: assert
Obligation:
Tree..isBranch(t@1) ==> !(Tree..isLeaf(t@1)) ==> Tree..isBranch(t@1)

Label: treeSize_body_calls_Tree..right_1
Property: assert
Obligation:
Tree..isBranch(t@1) ==> !(Tree..isLeaf(t@1)) ==> Tree..isBranch(t@1)

Label: treeSize_body_calls_Tree..tail_2
Property: assert
Obligation:
!(Tree..isBranch(t@1)) ==> !(Tree..isLeaf(t@1)) ==> Tree..isChain(t@1)

Label: treeSize_terminates_0
Property: assert
Assumptions:
Tree..adtRank_0: forall __q0 : Tree ::  { Tree..adtRank(__q0) }
  Tree..adtRank(__q0) >= 0
Tree..adtRank_1: forall __q0 : Tree :: forall __q1 : Tree ::  { Tree..adtRank(Branch(__q0, __q1)) }
  Tree..adtRank(__q0) < Tree..adtRank(Branch(__q0, __q1))
Tree..adtRank_2: forall __q0 : Tree :: forall __q1 : Tree ::  { Tree..adtRank(Branch(__q0, __q1)) }
  Tree..adtRank(__q1) < Tree..adtRank(Branch(__q0, __q1))
Tree..adtRank_3: forall __q0 : int :: forall __q1 : Tree ::  { Tree..adtRank(Chain(__q0, __q1)) }
  Tree..adtRank(__q1) < Tree..adtRank(Chain(__q0, __q1))
Obligation:
Tree..isBranch(t@2) ==> !(Tree..isLeaf(t@2)) ==> Tree..adtRank(Tree..left(t@2)) < Tree..adtRank(t@2)

Label: treeSize_terminates_1
Property: assert
Assumptions:
Tree..adtRank_0: forall __q0 : Tree ::  { Tree..adtRank(__q0) }
  Tree..adtRank(__q0) >= 0
Tree..adtRank_1: forall __q0 : Tree :: forall __q1 : Tree ::  { Tree..adtRank(Branch(__q0, __q1)) }
  Tree..adtRank(__q0) < Tree..adtRank(Branch(__q0, __q1))
Tree..adtRank_2: forall __q0 : Tree :: forall __q1 : Tree ::  { Tree..adtRank(Branch(__q0, __q1)) }
  Tree..adtRank(__q1) < Tree..adtRank(Branch(__q0, __q1))
Tree..adtRank_3: forall __q0 : int :: forall __q1 : Tree ::  { Tree..adtRank(Chain(__q0, __q1)) }
  Tree..adtRank(__q1) < Tree..adtRank(Chain(__q0, __q1))
Obligation:
Tree..isBranch(t@2) ==> !(Tree..isLeaf(t@2)) ==> Tree..adtRank(Tree..right(t@2)) < Tree..adtRank(t@2)

Label: treeSize_terminates_2
Property: assert
Assumptions:
Tree..adtRank_0: forall __q0 : Tree ::  { Tree..adtRank(__q0) }
  Tree..adtRank(__q0) >= 0
Tree..adtRank_1: forall __q0 : Tree :: forall __q1 : Tree ::  { Tree..adtRank(Branch(__q0, __q1)) }
  Tree..adtRank(__q0) < Tree..adtRank(Branch(__q0, __q1))
Tree..adtRank_2: forall __q0 : Tree :: forall __q1 : Tree ::  { Tree..adtRank(Branch(__q0, __q1)) }
  Tree..adtRank(__q1) < Tree..adtRank(Branch(__q0, __q1))
Tree..adtRank_3: forall __q0 : int :: forall __q1 : Tree ::  { Tree..adtRank(Chain(__q0, __q1)) }
  Tree..adtRank(__q1) < Tree..adtRank(Chain(__q0, __q1))
Obligation:
!(Tree..isBranch(t@2)) ==> !(Tree..isLeaf(t@2)) ==> Tree..adtRank(Tree..tail(t@2)) < Tree..adtRank(t@2)

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
Obligation: treeSize_body_calls_Tree..left_0
Property: assert
Result: ✅ pass

Obligation: treeSize_body_calls_Tree..right_1
Property: assert
Result: ✅ pass

Obligation: treeSize_body_calls_Tree..tail_2
Property: assert
Result: ✅ pass

Obligation: treeSize_terminates_0
Property: assert
Result: ✅ pass

Obligation: treeSize_terminates_1
Property: assert
Result: ✅ pass

Obligation: treeSize_terminates_2
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

---------------------------------------------------------------------
-- Test 9: polymorphic datatype specialized in monomorphic recursive function
-- MyList(a) instantiated as MyList int — axioms must be specialized
---------------------------------------------------------------------

def polyDtTermPgm : Program :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

rec function intListLen (@[cases] xs : MyList int) : int
{
  if MyList..isNil(xs) then 0 else 1 + intListLen(MyList..tl(xs))
};
#end

/-- info: [Strata.Core] Type checking succeeded.


VCs:
Label: intListLen_body_calls_MyList..tl_0
Property: assert
Obligation:
!(MyList..isNil(xs@1)) ==> MyList..isCons(xs@1)

Label: intListLen_terminates_0
Property: assert
Assumptions:
MyList..adtRank_0: forall __q0 : (MyList int) ::  { MyList..adtRank(__q0) }
  MyList..adtRank(__q0) >= 0
MyList..adtRank_1: forall __q0 : int :: forall __q1 : (MyList int) ::  { MyList..adtRank(Cons(__q0, __q1)) }
  MyList..adtRank(__q1) < MyList..adtRank(Cons(__q0, __q1))
Obligation:
!(MyList..isNil(xs@2)) ==> MyList..adtRank(MyList..tl(xs@2)) < MyList..adtRank(xs@2)

---
info:
Obligation: intListLen_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass

Obligation: intListLen_terminates_0
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval verify polyDtTermPgm (options := .default)

---------------------------------------------------------------------
-- Test 10: explicit `decreases` clause matching @[cases] parameter
---------------------------------------------------------------------

def decreasesExplicitPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
  decreases xs
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};
#end

/-- info:
Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval verify decreasesExplicitPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 11: `decreases` on non-@[cases] ADT parameter
-- cases splits on xs, but termination measure is ys
---------------------------------------------------------------------

def decreasesNonCasesPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function zipLen (@[cases] xs : IntList, ys : IntList) : int
  decreases ys
{
  if IntList..isNil(xs) then 0
  else if IntList..isNil(ys) then 0
  else 1 + zipLen(IntList..tl(xs), IntList..tl(ys))
};

procedure TestZipLen() spec {
  ensures true;
}
{
  var ys : IntList;
  // case split on ys
  assert [nilCases]: zipLen(Nil(), ys) == 0;
};
#end

/-- info: [Strata.Core] Type checking succeeded.


VCs:
Label: zipLen_body_calls_IntList..tl_0
Property: assert
Obligation:
!(IntList..isNil(ys@1)) ==> !(IntList..isNil(xs@1)) ==> IntList..isCons(xs@1)

Label: zipLen_body_calls_IntList..tl_1
Property: assert
Obligation:
!(IntList..isNil(ys@1)) ==> !(IntList..isNil(xs@1)) ==> IntList..isCons(ys@1)

Label: zipLen_terminates_0
Property: assert
Assumptions:
IntList..adtRank_0: forall __q0 : IntList ::  { IntList..adtRank(__q0) }
  IntList..adtRank(__q0) >= 0
IntList..adtRank_1: forall __q0 : int :: forall __q1 : IntList ::  { IntList..adtRank(Cons(__q0, __q1)) }
  IntList..adtRank(__q1) < IntList..adtRank(Cons(__q0, __q1))
Obligation:
!(IntList..isNil(ys@2)) ==> !(IntList..isNil(xs@2)) ==> IntList..adtRank(IntList..tl(ys@2)) < IntList..adtRank(ys@2)

Label: nilCases
Property: assert
Obligation:
true

Label: TestZipLen_ensures_0
Property: assert
Obligation:
true

---
info:
Obligation: zipLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: zipLen_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass

Obligation: zipLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: nilCases
Property: assert
Result: ✅ pass

Obligation: TestZipLen_ensures_0
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval verify decreasesNonCasesPgm (options := .default)

---------------------------------------------------------------------
-- Test 12: error — recursive function with no @[cases] or decreases
---------------------------------------------------------------------

def noCasesNoDecreasesPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function bad (xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + bad(IntList..tl(xs))
};
#end

/-- error: recursive function 'bad' requires a 'decreases' clause or a '@[cases]' parameter for termination checking -/
#guard_msgs in
#eval verify noCasesNoDecreasesPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 13: error — decreases on non-ADT parameter (temporary)
---------------------------------------------------------------------

def decreasesNonADTPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function bad (@[cases] xs : IntList, n : int) : int
  decreases n
{
  if IntList..isNil(xs) then 0 else bad(IntList..tl(xs), n - 1)
};
#end

/-- error: recursive function 'bad': decreasing parameter type 'int' is not a known datatype -/
#guard_msgs in
#eval verify decreasesNonADTPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 14: mutual recursion over different mutual datatypes
-- treeSize recurses on RoseTree, listSize on RoseList
---------------------------------------------------------------------

def mutualDtTermPgm : Program :=
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

procedure TestMutualDt() spec {
  ensures true;
}
{
  assert [leaf]: treeSize(Leaf(42)) == 1;
  assert [singleNode]: treeSize(Node(RCons(Leaf(1), RNil()))) == 1;
};
#end

/-- info:
Obligation: treeSize_body_calls_RoseTree..children_0
Property: assert
Result: ✅ pass

Obligation: listSize_body_calls_RoseList..hd_0
Property: assert
Result: ✅ pass

Obligation: listSize_body_calls_RoseList..tl_1
Property: assert
Result: ✅ pass

Obligation: treeSize_terminates_0
Property: assert
Result: ✅ pass

Obligation: listSize_terminates_0
Property: assert
Result: ✅ pass

Obligation: listSize_terminates_1
Property: assert
Result: ✅ pass

Obligation: leaf
Property: assert
Result: ✅ pass

Obligation: singleNode
Property: assert
Result: ✅ pass

Obligation: TestMutualDt_ensures_0
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval verify mutualDtTermPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 15: mutual recursion over different datatypes — non-decreasing
-- cross-call should fail
---------------------------------------------------------------------

def mutualDtNonTermPgm : Program :=
#strata
program Core;

datatype RoseTree { Leaf(val: int), Node(children: RoseList) }
datatype RoseList { RNil(), RCons(hd: RoseTree, tl: RoseList) };

rec function badTree (@[cases] t : RoseTree) : int
{
  if RoseTree..isLeaf(t) then 1 else badList(RoseTree..children(t))
}
function badList (@[cases] xs : RoseList) : int
{
  if RoseList..isRNil(xs) then 0 else badTree(Node(xs))
};
#end

/-- info:
Obligation: badTree_body_calls_RoseTree..children_0
Property: assert
Result: ✅ pass

Obligation: badTree_terminates_0
Property: assert
Result: ✅ pass

Obligation: badList_terminates_0
Property: assert
Result: ❓ unknown -/
#guard_msgs in
#eval verify mutualDtNonTermPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 16: polymorphic mutual datatypes with monomorphic instantiation
-- GenTree(a)/GenList(a) instantiated at int
---------------------------------------------------------------------

def polyMutualDtTermPgm : Program :=
#strata
program Core;

datatype GenTree (a : Type) { GLeaf(val: a), GNode(children: GenList a) }
datatype GenList (a : Type) { GNil(), GCons(hd: GenTree a, tl: GenList a) };

rec function intTreeSize (@[cases] t : GenTree int) : int
{
  if GenTree..isGLeaf(t) then 1 else intListSize(GenTree..children(t))
}
function intListSize (@[cases] xs : GenList int) : int
{
  if GenList..isGNil(xs) then 0 else intTreeSize(GenList..hd(xs)) + intListSize(GenList..tl(xs))
};
#end

/-- info:
Obligation: intTreeSize_body_calls_GenTree..children_0
Property: assert
Result: ✅ pass

Obligation: intListSize_body_calls_GenList..hd_0
Property: assert
Result: ✅ pass

Obligation: intListSize_body_calls_GenList..tl_1
Property: assert
Result: ✅ pass

Obligation: intTreeSize_terminates_0
Property: assert
Result: ✅ pass

Obligation: intListSize_terminates_0
Property: assert
Result: ✅ pass

Obligation: intListSize_terminates_1
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval verify polyMutualDtTermPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 17: precondition used to prove termination
-- predVal recurses unconditionally on pred(n), but the precondition
-- requires !isZero(n), ensuring n is a Succ.
---------------------------------------------------------------------

def precondTermPgm : Program :=
#strata
program Core;

datatype MyNat { Zero(), Succ(pred: MyNat) };

rec function predVal (@[cases] n : MyNat) : int
  requires !MyNat..isZero(n);
{
  if MyNat..isZero(MyNat..pred(n)) then 0 else 1 + predVal(MyNat..pred(n))
};

#end

/-- info: Obligation: predVal_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: predVal_body_calls_MyNat..pred_1
Property: assert
Result: ✅ pass

Obligation: predVal_body_calls_predVal_2
Property: assert
Result: ✅ pass

Obligation: predVal_terminates_0
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval verify precondTermPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 18: recursive call nested inside a non-recursive function call
---------------------------------------------------------------------

def nestedInNonRecPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

function f (xs : IntList) : IntList { xs }

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(f(IntList..tl(xs)))
};
#end

/-- info:
Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval verify nestedInNonRecPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 19: error — decreasing argument contains a bound variable
---------------------------------------------------------------------

def boundVarDecrArgPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function bad (@[cases] xs : IntList) : bool
{
  if IntList..isNil(xs) then true
  else forall y : IntList :: bad(y)
};
#end

/-- error: termination checking: decreasing argument contains a bound variable -/
#guard_msgs in
#eval verify boundVarDecrArgPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 20: error — decreasing argument contains a recursive call
---------------------------------------------------------------------

def recCallInDecrArgPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function bad (@[cases] xs : IntList) : IntList
{
  if IntList..isNil(xs) then Nil() else bad(IntList..tl(bad(xs)))
};
#end

/-- error: termination checking: decreasing argument contains a recursive call -/
#guard_msgs in
#eval verify recCallInDecrArgPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 21: recursive call nested inside non-recursive call — should fail
-- g(x) = x so g does NOT decrease, termination unprovable
---------------------------------------------------------------------

def nestedInNonRecFailPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

function g (xs : IntList) : IntList { xs }

rec function bad (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + bad(g(xs))
};
#end

/-- info:
Obligation: bad_terminates_0
Property: assert
Result: ❓ unknown -/
#guard_msgs in
#eval verify nestedInNonRecFailPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 22: recursive call under a binder but decreasing arg is free
-- forall y :: ... bad(tl(xs)) ... — xs is free, so this is fine
---------------------------------------------------------------------

def recUnderBinderFreePgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function allPos (@[cases] xs : IntList) : bool
{
  if IntList..isNil(xs) then true
  else (forall y : int :: y == IntList..hd(xs)) == allPos(IntList..tl(xs))
};
#end

/-- info:
Obligation: allPos_body_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: allPos_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass

Obligation: allPos_terminates_0
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval verify recUnderBinderFreePgm (options := .quiet)

---------------------------------------------------------------------
-- Test 23: let-binding (lambda application) with valid decreasing arg
-- (fun y => listLen(IntList..tl(xs)))(IntList..hd(xs))
---------------------------------------------------------------------

def letBindingTermPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0
  else (fun y : int => 1 + listLen(IntList..tl(xs)))(IntList..hd(xs))
};
#end

/-- info:
Obligation: listLen_body_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass

Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval verify letBindingTermPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 24: axiom filtering — mutual rec block with two unrelated datatypes
-- f recurses on IntList, g recurses on MyNat; each $$term proc
-- only gets axioms for its own decreasing type's datatype block
---------------------------------------------------------------------

def extraAxiomsPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };
datatype MyNat { Zero(), Succ(pred: MyNat) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
}
function natToInt (@[cases] n : MyNat) : int
{
  if MyNat..isZero(n) then 0 else 1 + natToInt(MyNat..pred(n))
};
#end

/-- info: [Strata.Core] Type checking succeeded.


VCs:
Label: listLen_body_calls_IntList..tl_0
Property: assert
Obligation:
!(IntList..isNil(xs@1)) ==> IntList..isCons(xs@1)

Label: natToInt_body_calls_MyNat..pred_0
Property: assert
Obligation:
!(MyNat..isZero(n@1)) ==> MyNat..isSucc(n@1)

Label: listLen_terminates_0
Property: assert
Assumptions:
IntList..adtRank_0: forall __q0 : IntList ::  { IntList..adtRank(__q0) }
  IntList..adtRank(__q0) >= 0
IntList..adtRank_1: forall __q0 : int :: forall __q1 : IntList ::  { IntList..adtRank(Cons(__q0, __q1)) }
  IntList..adtRank(__q1) < IntList..adtRank(Cons(__q0, __q1))
Obligation:
!(IntList..isNil(xs@2)) ==> IntList..adtRank(IntList..tl(xs@2)) < IntList..adtRank(xs@2)

Label: natToInt_terminates_0
Property: assert
Assumptions:
MyNat..adtRank_0: forall __q0 : MyNat ::  { MyNat..adtRank(__q0) }
  MyNat..adtRank(__q0) >= 0
MyNat..adtRank_1: forall __q0 : MyNat ::  { MyNat..adtRank(Succ(__q0)) }
  MyNat..adtRank(__q0) < MyNat..adtRank(Succ(__q0))
Obligation:
!(MyNat..isZero(n@2)) ==> MyNat..adtRank(MyNat..pred(n@2)) < MyNat..adtRank(n@2)

---
info:
Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: natToInt_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: natToInt_terminates_0
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval verify extraAxiomsPgm (options := .default)

---------------------------------------------------------------------
-- Test 25: error — decreases with non-variable expression
---------------------------------------------------------------------

def decreasesNonVarPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function bad (@[cases] xs : IntList) : int
  decreases IntList..tl(xs)
{
  if IntList..isNil(xs) then 0 else 1 + bad(IntList..tl(xs))
};
#end

/-- error: recursive function 'bad': decreases clause must be a parameter name. Non-structural recursion is not yet supported -/
#guard_msgs in
#eval verify decreasesNonVarPgm (options := .quiet)

end Strata.TerminationCheckTest
