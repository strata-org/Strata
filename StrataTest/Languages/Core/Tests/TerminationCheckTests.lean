/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Transform.TerminationCheck
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)

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
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
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

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: listLen_terminates_0
Property: assert
Obligation:
(forall x : IntList ::  { IntList..adtRank(x) }
  int.ge(IntList..adtRank(x), 0)) ==> (forall hd : int :: forall tl : IntList ::  { IntList..adtRank(Cons(hd, tl)) }
  int.lt(IntList..adtRank(tl), IntList..adtRank(Cons(hd, tl)))) ==> (forall x : IntList ::  { IntList..adtRank(x) }
  !(IntList..isNil(x)) ==> int.ge(IntList..adtRank(x), 1)) ==> !(IntList..isNil(xs@1)) ==> int.lt(IntList..adtRank(IntList..tl(xs@1)), IntList..adtRank(xs@1))

Label: listLen_body_calls_IntList..tl_0
Property: assert
Obligation:
!(IntList..isNil(xs@2)) ==> IntList..isCons(xs@2)

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
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify listLenTermPgm (options := .default)

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

/--
info:
Obligation: contains_terminates_0
Property: assert
Result: ✅ pass

Obligation: contains_body_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: contains_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify containsTermPgm (options := .quiet)

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
#eval Core.verify nonTermPgm (options := .quiet)

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
#eval Core.verify wrongDirPgm (options := .quiet)

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
  else int.add(IntList..hd(xs), sumList(IntList..tl(xs)))
};
#end

/--
info:
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
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify multiBranchPgm (options := .quiet)

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

Obligation: zeroEven
Property: assert
Result: ✅ pass

Obligation: oneOdd
Property: assert
Result: ✅ pass

Obligation: TestMutual_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify mutualTermPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 7: two recFuncBlocks using the same datatype (no duplicate dtRank)
---------------------------------------------------------------------

def sharedDtPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
};

rec function listSum (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else int.add(IntList..hd(xs), listSum(IntList..tl(xs)))
};

procedure Test() spec {
  ensures true;
}
{
  assert [lenNil]: listLen(Nil()) == 0;
  assert [sumNil]: listSum(Nil()) == 0;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: listLen_terminates_0
Property: assert
Obligation:
(forall x : IntList ::  { IntList..adtRank(x) }
  int.ge(IntList..adtRank(x), 0)) ==> (forall hd : int :: forall tl : IntList ::  { IntList..adtRank(Cons(hd, tl)) }
  int.lt(IntList..adtRank(tl), IntList..adtRank(Cons(hd, tl)))) ==> (forall x : IntList ::  { IntList..adtRank(x) }
  !(IntList..isNil(x)) ==> int.ge(IntList..adtRank(x), 1)) ==> !(IntList..isNil(xs@1)) ==> int.lt(IntList..adtRank(IntList..tl(xs@1)), IntList..adtRank(xs@1))

Label: listLen_body_calls_IntList..tl_0
Property: assert
Obligation:
!(IntList..isNil(xs@2)) ==> IntList..isCons(xs@2)

Label: listSum_terminates_0
Property: assert
Obligation:
(forall x : IntList ::  { IntList..adtRank(x) }
  int.ge(IntList..adtRank(x), 0)) ==> (forall hd : int :: forall tl : IntList ::  { IntList..adtRank(Cons(hd, tl)) }
  int.lt(IntList..adtRank(tl), IntList..adtRank(Cons(hd, tl)))) ==> (forall x : IntList ::  { IntList..adtRank(x) }
  !(IntList..isNil(x)) ==> int.ge(IntList..adtRank(x), 1)) ==> !(IntList..isNil(xs@3)) ==> int.lt(IntList..adtRank(IntList..tl(xs@3)), IntList..adtRank(xs@3))

Label: listSum_body_calls_IntList..hd_0
Property: assert
Obligation:
!(IntList..isNil(xs@4)) ==> IntList..isCons(xs@4)

Label: listSum_body_calls_IntList..tl_1
Property: assert
Obligation:
!(IntList..isNil(xs@5)) ==> IntList..isCons(xs@5)

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
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify sharedDtPgm (options := .default)

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
  else if Tree..isBranch(t) then int.add(treeSize(Tree..left(t)), treeSize(Tree..right(t)))
  else int.add(1, treeSize(Tree..tail(t)))
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

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: treeSize_terminates_0
Property: assert
Obligation:
(forall x : Tree ::  { Tree..adtRank(x) }
  int.ge(Tree..adtRank(x), 0)) ==> (forall left : Tree :: forall right : Tree ::  { Tree..adtRank(Branch(left, right)) }
  int.lt(Tree..adtRank(left), Tree..adtRank(Branch(left, right)))) ==> (forall left : Tree :: forall right : Tree ::  { Tree..adtRank(Branch(left, right)) }
  int.lt(Tree..adtRank(right), Tree..adtRank(Branch(left, right)))) ==> (forall head : int :: forall tail : Tree ::  { Tree..adtRank(Chain(head, tail)) }
  int.lt(Tree..adtRank(tail), Tree..adtRank(Chain(head, tail)))) ==> (forall x : Tree ::  { Tree..adtRank(x) }
  !(Tree..isLeaf(x)) ==> int.ge(Tree..adtRank(x), 1)) ==> Tree..isBranch(t@1) ==> !(Tree..isLeaf(t@1)) ==> int.lt(Tree..adtRank(Tree..left(t@1)), Tree..adtRank(t@1))

Label: treeSize_terminates_1
Property: assert
Obligation:
(forall x : Tree ::  { Tree..adtRank(x) }
  int.ge(Tree..adtRank(x), 0)) ==> (forall left : Tree :: forall right : Tree ::  { Tree..adtRank(Branch(left, right)) }
  int.lt(Tree..adtRank(left), Tree..adtRank(Branch(left, right)))) ==> (forall left : Tree :: forall right : Tree ::  { Tree..adtRank(Branch(left, right)) }
  int.lt(Tree..adtRank(right), Tree..adtRank(Branch(left, right)))) ==> (forall head : int :: forall tail : Tree ::  { Tree..adtRank(Chain(head, tail)) }
  int.lt(Tree..adtRank(tail), Tree..adtRank(Chain(head, tail)))) ==> (forall x : Tree ::  { Tree..adtRank(x) }
  !(Tree..isLeaf(x)) ==> int.ge(Tree..adtRank(x), 1)) ==> Tree..isBranch(t@2) ==> !(Tree..isLeaf(t@2)) ==> int.lt(Tree..adtRank(Tree..right(t@2)), Tree..adtRank(t@2))

Label: treeSize_terminates_2
Property: assert
Obligation:
(forall x : Tree ::  { Tree..adtRank(x) }
  int.ge(Tree..adtRank(x), 0)) ==> (forall left : Tree :: forall right : Tree ::  { Tree..adtRank(Branch(left, right)) }
  int.lt(Tree..adtRank(left), Tree..adtRank(Branch(left, right)))) ==> (forall left : Tree :: forall right : Tree ::  { Tree..adtRank(Branch(left, right)) }
  int.lt(Tree..adtRank(right), Tree..adtRank(Branch(left, right)))) ==> (forall head : int :: forall tail : Tree ::  { Tree..adtRank(Chain(head, tail)) }
  int.lt(Tree..adtRank(tail), Tree..adtRank(Chain(head, tail)))) ==> (forall x : Tree ::  { Tree..adtRank(x) }
  !(Tree..isLeaf(x)) ==> int.ge(Tree..adtRank(x), 1)) ==> !(Tree..isBranch(t@3)) ==> !(Tree..isLeaf(t@3)) ==> int.lt(Tree..adtRank(Tree..tail(t@3)), Tree..adtRank(t@3))

Label: treeSize_body_calls_Tree..left_0
Property: assert
Obligation:
Tree..isBranch(t@4) ==> !(Tree..isLeaf(t@4)) ==> Tree..isBranch(t@4)

Label: treeSize_body_calls_Tree..right_1
Property: assert
Obligation:
Tree..isBranch(t@5) ==> !(Tree..isLeaf(t@5)) ==> Tree..isBranch(t@5)

Label: treeSize_body_calls_Tree..tail_2
Property: assert
Obligation:
!(Tree..isBranch(t@6)) ==> !(Tree..isLeaf(t@6)) ==> Tree..isChain(t@6)

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
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify treeSizePgm (options := .default)

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
  if MyList..isNil(xs) then 0 else int.add(1, intListLen(MyList..tl(xs)))
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: intListLen_terminates_0
Property: assert
Obligation:
(forall x : (MyList int) ::  { MyList..adtRank(x) }
  int.ge(MyList..adtRank(x), 0)) ==> (forall hd : int :: forall tl : (MyList int) ::  { MyList..adtRank(Cons(hd, tl)) }
  int.lt(MyList..adtRank(tl), MyList..adtRank(Cons(hd, tl)))) ==> (forall x : (MyList int) ::  { MyList..adtRank(x) }
  !(MyList..isNil(x)) ==> int.ge(MyList..adtRank(x), 1)) ==> !(MyList..isNil(xs@1)) ==> int.lt(MyList..adtRank(MyList..tl(xs@1)), MyList..adtRank(xs@1))

Label: intListLen_body_calls_MyList..tl_0
Property: assert
Obligation:
!(MyList..isNil(xs@2)) ==> MyList..isCons(xs@2)

---
info:
Obligation: intListLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: intListLen_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify polyDtTermPgm (options := .default)

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
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
};
#end

/--
info:
Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify decreasesExplicitPgm (options := .quiet)

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
  else int.add(1, zipLen(IntList..tl(xs), IntList..tl(ys)))
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

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: zipLen_terminates_0
Property: assert
Obligation:
(forall x : IntList ::  { IntList..adtRank(x) }
  int.ge(IntList..adtRank(x), 0)) ==> (forall hd : int :: forall tl : IntList ::  { IntList..adtRank(Cons(hd, tl)) }
  int.lt(IntList..adtRank(tl), IntList..adtRank(Cons(hd, tl)))) ==> (forall x : IntList ::  { IntList..adtRank(x) }
  !(IntList..isNil(x)) ==> int.ge(IntList..adtRank(x), 1)) ==> !(IntList..isNil(ys@1)) ==> !(IntList..isNil(xs@1)) ==> int.lt(IntList..adtRank(IntList..tl(ys@1)), IntList..adtRank(ys@1))

Label: zipLen_body_calls_IntList..tl_0
Property: assert
Obligation:
!(IntList..isNil(ys@2)) ==> !(IntList..isNil(xs@2)) ==> IntList..isCons(xs@2)

Label: zipLen_body_calls_IntList..tl_1
Property: assert
Obligation:
!(IntList..isNil(ys@3)) ==> !(IntList..isNil(xs@3)) ==> IntList..isCons(ys@3)

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
Obligation: zipLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: zipLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: zipLen_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass

Obligation: nilCases
Property: assert
Result: ✅ pass

Obligation: TestZipLen_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify decreasesNonCasesPgm (options := .default)

---------------------------------------------------------------------
-- Test 12: error — recursive function with no @[cases] or decreases
---------------------------------------------------------------------

def noCasesNoDecreasesPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function bad (xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else int.add(1, bad(IntList..tl(xs)))
};
#end

/-- error: recursive function 'bad' requires a 'decreases' clause or a '@[cases]' parameter for termination checking -/
#guard_msgs in
#eval Core.verify noCasesNoDecreasesPgm (options := .quiet)

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
  if IntList..isNil(xs) then 0 else bad(IntList..tl(xs), int.sub(n, 1))
};
#end

/--
info:
Obligation: bad_terminates_0
Property: assert
Result: ❌ fail

Obligation: bad_terminates_1
Property: assert
Result: ✅ pass

Obligation: bad_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify decreasesNonADTPgm (options := .quiet)

---------------------------------------------------------------------
-- An ill-typed recursive function, whose termination lemmas would be generated, is
-- reported by the first type check: the result of `bad` is `bool` but its type is `int`.
---------------------------------------------------------------------

def illTypedRecPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function bad (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then true else bad(IntList..tl(xs))
};
#end

/--
error: ❌ Type checking error.
Impossible to unify bool with int.
-/
#guard_msgs in
#eval Core.verify illTypedRecPgm (options := .quiet)

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
  if RoseList..isRNil(xs) then 0 else int.add(treeSize(RoseList..hd(xs)), listSize(RoseList..tl(xs)))
};

procedure TestMutualDt() spec {
  ensures true;
}
{
  assert [leaf]: treeSize(Leaf(42)) == 1;
  assert [singleNode]: treeSize(Node(RCons(Leaf(1), RNil()))) == 1;
};
#end

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

Obligation: leaf
Property: assert
Result: ✅ pass

Obligation: singleNode
Property: assert
Result: ✅ pass

Obligation: TestMutualDt_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify mutualDtTermPgm (options := .quiet)

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

/--
info:
Obligation: badTree_terminates_0
Property: assert
Result: ✅ pass

Obligation: badList_terminates_0
Property: assert
Result: ❓ unknown

Obligation: badTree_body_calls_RoseTree..children_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify mutualDtNonTermPgm (options := .quiet)

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
  if GenList..isGNil(xs) then 0 else int.add(intTreeSize(GenList..hd(xs)), intListSize(GenList..tl(xs)))
};
#end

/--
info:
Obligation: intTreeSize_terminates_0
Property: assert
Result: ✅ pass

Obligation: intListSize_terminates_0
Property: assert
Result: ✅ pass

Obligation: intListSize_terminates_1
Property: assert
Result: ✅ pass

Obligation: intTreeSize_body_calls_GenTree..children_0
Property: assert
Result: ✅ pass

Obligation: intListSize_body_calls_GenList..hd_0
Property: assert
Result: ✅ pass

Obligation: intListSize_body_calls_GenList..tl_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify polyMutualDtTermPgm (options := .quiet)

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
  if MyNat..isZero(MyNat..pred(n)) then 0 else int.add(1, predVal(MyNat..pred(n)))
};

#end

/--
info:
Obligation: predVal_terminates_0
Property: assert
Result: ✅ pass

Obligation: predVal_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: predVal_body_calls_MyNat..pred_1
Property: assert
Result: ✅ pass

Obligation: predVal_body_calls_predVal_2
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify precondTermPgm (options := .quiet)

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
  if IntList..isNil(xs) then 0 else int.add(1, listLen(f(IntList..tl(xs))))
};
#end

/--
info:
Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify nestedInNonRecPgm (options := .quiet)

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

/-- error: termination checking 'bad': decreasing argument contains a bound variable-/
#guard_msgs in
#eval Core.verify boundVarDecrArgPgm (options := .quiet)

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

/-- error: termination checking 'bad': decreasing argument contains a recursive call -/
#guard_msgs in
#eval Core.verify recCallInDecrArgPgm (options := .quiet)

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
  if IntList..isNil(xs) then 0 else int.add(1, bad(g(xs)))
};
#end

/-- info:
Obligation: bad_terminates_0
Property: assert
Result: ❓ unknown -/
#guard_msgs in
#eval Core.verify nestedInNonRecFailPgm (options := .quiet)

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

/--
info:
Obligation: allPos_terminates_0
Property: assert
Result: ✅ pass

Obligation: allPos_body_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: allPos_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify recUnderBinderFreePgm (options := .quiet)

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
  else (fun y : int => int.add(1, listLen(IntList..tl(xs))))(IntList..hd(xs))
};
#end

/--
info:
Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify letBindingTermPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 24: axiom filtering — mutual rec block with two unrelated datatypes
-- f recurses on IntList, g recurses on MyNat; each termination lemma
-- only gets axioms for its own decreasing type's datatype block
---------------------------------------------------------------------

def extraAxiomsPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };
datatype MyNat { Zero(), Succ(pred: MyNat) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
}
function natToInt (@[cases] n : MyNat) : int
{
  if MyNat..isZero(n) then 0 else int.add(1, natToInt(MyNat..pred(n)))
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: listLen_terminates_0
Property: assert
Obligation:
(forall x : IntList ::  { IntList..adtRank(x) }
  int.ge(IntList..adtRank(x), 0)) ==> (forall hd : int :: forall tl : IntList ::  { IntList..adtRank(Cons(hd, tl)) }
  int.lt(IntList..adtRank(tl), IntList..adtRank(Cons(hd, tl)))) ==> (forall x : IntList ::  { IntList..adtRank(x) }
  !(IntList..isNil(x)) ==> int.ge(IntList..adtRank(x), 1)) ==> !(IntList..isNil(xs@1)) ==> int.lt(IntList..adtRank(IntList..tl(xs@1)), IntList..adtRank(xs@1))

Label: natToInt_terminates_0
Property: assert
Obligation:
(forall x : MyNat ::  { MyNat..adtRank(x) }
  int.ge(MyNat..adtRank(x), 0)) ==> (forall pred : MyNat ::  { MyNat..adtRank(Succ(pred)) }
  int.lt(MyNat..adtRank(pred), MyNat..adtRank(Succ(pred)))) ==> (forall x : MyNat ::  { MyNat..adtRank(x) }
  !(MyNat..isZero(x)) ==> int.ge(MyNat..adtRank(x), 1)) ==> !(MyNat..isZero(n@1)) ==> int.lt(MyNat..adtRank(MyNat..pred(n@1)), MyNat..adtRank(n@1))

Label: listLen_body_calls_IntList..tl_0
Property: assert
Obligation:
!(IntList..isNil(xs@2)) ==> IntList..isCons(xs@2)

Label: natToInt_body_calls_MyNat..pred_0
Property: assert
Obligation:
!(MyNat..isZero(n@2)) ==> MyNat..isSucc(n@2)

---
info:
Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: natToInt_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: natToInt_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify extraAxiomsPgm (options := .default)

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
  if IntList..isNil(xs) then 0 else int.add(1, bad(IntList..tl(xs)))
};
#end

/-- error: ❌ Type checking error.
recursive function 'bad': decreases expression must have type int or be a parameter of a datatype type, got 'IntList' -/
#guard_msgs in
#eval Core.verify decreasesNonVarPgm (options := .quiet)

---------------------------------------------------------------------
-- Test: structural recursion through a let-alias (β-redex) — should pass.
-- A front-end binding that names an intermediate value (see the module
-- docstring of `Strata/Transform/BetaReduce.lean`) lowers to a redex
-- `(λ c. ... f(tl(c))) xs`. The decreasing argument `tl(c)` references the
-- *bound* `c`; β-reducing the alias rewrites it to `tl(xs)` so structural
-- termination goes through instead of erroring on a bound var.
---------------------------------------------------------------------

def letAliasTermPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLenAlias (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0
  else (fun c : IntList => int.add(1, listLenAlias(IntList..tl(c))))(xs)
};
#end

/--
info:
Obligation: listLenAlias_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLenAlias_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify letAliasTermPgm (options := .quiet)

---------------------------------------------------------------------
-- Same shape via Core's surface syntax: `have c : T = v in body` is sugar
-- for the redex `(fun c : T => body)(v)`. The decreasing argument `tl(c)`
-- again references the bound `c`; the checker's non-erasing reduction
-- rewrites it to `tl(xs)` and structural termination passes.
---------------------------------------------------------------------

def haveAliasTermPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLenHave (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0
  else have c : IntList = xs in int.add(1, listLenHave(IntList..tl(c)))
};
#end

/--
info:
Obligation: listLenHave_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLenHave_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify haveAliasTermPgm (options := .quiet)

---------------------------------------------------------------------
-- Regression: a constant-lambda redex must NOT erase a
-- recursive call. `(fun ignored => 0)(bad(xs))` is a constant lambda whose
-- argument carries a non-decreasing recursive call. Plain β-reduction would
-- drop the argument (value-preserving but not call-preserving), hiding the
-- call from the termination checker so the function is silently accepted.
-- `betaReduceRedexesPreservingArgs` leaves such redexes un-reduced, so the
-- obligation is still emitted (and here unprovable, as it should be).
---------------------------------------------------------------------

def constLambdaEraseRecCallPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function bad (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0
  else (fun ignored : int => 0)(bad(xs))
};
#end

/-- info:
Obligation: bad_terminates_0
Property: assert
Result: ❓ unknown -/
#guard_msgs in
#eval Core.verify constLambdaEraseRecCallPgm (options := .quiet)

---------------------------------------------------------------------
-- Direct-AST tests: the callee's measure in a decrease obligation is
-- annotated at the call's type instance.
---------------------------------------------------------------------

section CallInstance

open Lambda

/-- `List a` with constructors `Nil()` and `Cons(hd : a, tl : List a)`. -/
private def listDt : LDatatype Unit :=
  { name := "List", typeArgs := ["a"],
    constrs := [
      { name := ⟨"Nil", ()⟩, args := [] },
      { name := ⟨"Cons", ()⟩,
        args := [(⟨"hd", ()⟩, .ftvar "a"), (⟨"tl", ()⟩, .tcons "List" [.ftvar "a"])] }
    ], constrs_ne := rfl }

private def listTy (t : LMonoTy) : LMonoTy := .tcons "List" [t]

private def opE (n : String) (ty : Option LMonoTy) : Core.Expression.Expr :=
  .op Core.coreLoc ⟨n, ()⟩ ty

private def listVar (x tv : String) : Core.Expression.Expr :=
  .fvar Core.coreLoc ⟨x, ()⟩ (some (listTy (.ftvar tv)))

/-- `if List..isNil(x) then 0 else callee(List..tl(x))` with `x : List tv`; the
    operator `callee` carries the annotation `calleeTy`. -/
private def recBody (x tv callee : String) (calleeTy : Option LMonoTy) :
    Core.Expression.Expr :=
  let t := listTy (.ftvar tv)
  .ite Core.coreLoc (.app Core.coreLoc (opE "List..isNil" (some (.arrow t .bool))) (listVar x tv))
    (.intConst Core.coreLoc 0)
    (.app Core.coreLoc (opE callee calleeTy)
      (.app Core.coreLoc (opE "List..tl" (some (.arrow t t))) (listVar x tv)))

/-- `name<tv>(x : List tv) : int` with body `recBody`, recursive on `x` by
    `@[cases]`, or by `decreases len(x)` when `intMeasure` holds. -/
private def recFn (name tv x callee : String) (calleeTy : Option LMonoTy)
    (intMeasure : Bool) : Core.Function :=
  { name := ⟨name, ()⟩, typeArgs := [tv], isRecursive := true,
    inputs := [(⟨x, ()⟩, listTy (.ftvar tv))], output := .int,
    body := some (recBody x tv callee calleeTy),
    attr := if intMeasure then #[] else #[.inlineIfConstr 0],
    measure := if intMeasure then
        some (.app Core.coreLoc (opE "len" (some (.arrow (listTy (.ftvar tv)) .int)))
          (listVar x tv))
      else none }

/-- `f<tv>(xs : List tv)` calling `g<a>(ys : List a)` and back; each call is
    annotated `List c → int` for the caller's type variable `c` when
    `annotated` holds, and unannotated otherwise. -/
private def fgPgm (tv : String) (annotated intMeasure : Bool) : Core.Program :=
  let callTy (v : String) : Option LMonoTy :=
    if annotated then some (.arrow (listTy (.ftvar v)) .int) else none
  { decls := [
    .type (.data [listDt]) .empty,
    .recFuncBlock [
      recFn "f" tv "xs" "g" (callTy tv) intMeasure,
      recFn "g" "a" "ys" "f" (callTy "a") intMeasure] .empty] }

/-- The conclusion of `e` after its leading quantifiers and implications. -/
private def conclusion : Core.Expression.Expr → Core.Expression.Expr
  | .quant _ _ _ _ _ body => conclusion body
  | .app _ (.app _ (.op _ ⟨"Bool.Implies", _⟩ _) _) body => conclusion body
  | e => e

/-- Run `termCheck` and show each generated lemma's conclusion with its type
    annotations. -/
private def termObligations (p : Core.Program) : Std.Format :=
  let init :=
    { Core.Transform.CoreTransformState.emp with factory := Core.Factory }
  let fmt := (LExpr.instToFormatLExpr Core.CoreLParams.mono).format
  match Core.Transform.run p Core.TermCheck.termCheck init with
  | .error e => f!"transform failed: {e}"
  | .ok (_, p) =>
    Std.Format.joinSep (p.decls.filterMap fun
      | .lemma l _ => some f!"{l.name}: {fmt (conclusion l.e)}"
      | _ => none) Std.Format.line

-- Structural recursion on `List` with annotated calls: in `f<b>`, `g`'s rank
-- is taken at `List b → int`.
/--
info: f_terminates_0: ((~Int.Lt : (arrow int (arrow int bool)))
 ((~List..adtRank : (arrow (List b) int)) ((~List..tl : (arrow (List b) (List b))) %0))
 ((~List..adtRank : (arrow (List b) int)) %0))
g_terminates_0: ((~Int.Lt : (arrow int (arrow int bool)))
 ((~List..adtRank : (arrow (List a) int)) ((~List..tl : (arrow (List a) (List a))) %0))
 ((~List..adtRank : (arrow (List a) int)) %0))
-/
#guard_msgs in
#eval termObligations (fgPgm "b" true false)

-- The same block with unannotated calls: the callee's rank is unannotated.
/--
info: f_terminates_0: ((~Int.Lt : (arrow int (arrow int bool)))
 (~List..adtRank ((~List..tl : (arrow (List b) (List b))) %0))
 ((~List..adtRank : (arrow (List b) int)) %0))
g_terminates_0: ((~Int.Lt : (arrow int (arrow int bool)))
 (~List..adtRank ((~List..tl : (arrow (List a) (List a))) %0))
 ((~List..adtRank : (arrow (List a) int)) %0))
-/
#guard_msgs in
#eval termObligations (fgPgm "b" false false)

-- Int-valued measures `len(x)` with annotated calls: in `f<b>`, `g`'s measure
-- is taken at `List b → int`.
/--
info: f_terminates_0: ((~Int.Le : (arrow int (arrow int bool)))
 #0
 ((~len : (arrow (List b) int)) ((~List..tl : (arrow (List b) (List b))) %0)))
f_terminates_1: ((~Int.Lt : (arrow int (arrow int bool)))
 ((~len : (arrow (List b) int)) ((~List..tl : (arrow (List b) (List b))) %0))
 ((~len : (arrow (List b) int)) %0))
g_terminates_0: ((~Int.Le : (arrow int (arrow int bool)))
 #0
 ((~len : (arrow (List a) int)) ((~List..tl : (arrow (List a) (List a))) %0)))
g_terminates_1: ((~Int.Lt : (arrow int (arrow int bool)))
 ((~len : (arrow (List a) int)) ((~List..tl : (arrow (List a) (List a))) %0))
 ((~len : (arrow (List a) int)) %0))
-/
#guard_msgs in
#eval termObligations (fgPgm "b" true true)

-- In `f<a>`, the call of `g` is annotated at `g`'s declared type `List a → int`.
/--
info: f_terminates_0: ((~Int.Lt : (arrow int (arrow int bool)))
 ((~List..adtRank : (arrow (List a) int)) ((~List..tl : (arrow (List a) (List a))) %0))
 ((~List..adtRank : (arrow (List a) int)) %0))
g_terminates_0: ((~Int.Lt : (arrow int (arrow int bool)))
 ((~List..adtRank : (arrow (List a) int)) ((~List..tl : (arrow (List a) (List a))) %0))
 ((~List..adtRank : (arrow (List a) int)) %0))
-/
#guard_msgs in
#eval termObligations (fgPgm "a" true false)

-- The same block with `f`'s type parameter named `c`: the same lemmas with
-- `f`'s `a` renamed to `c`.
/--
info: f_terminates_0: ((~Int.Lt : (arrow int (arrow int bool)))
 ((~List..adtRank : (arrow (List c) int)) ((~List..tl : (arrow (List c) (List c))) %0))
 ((~List..adtRank : (arrow (List c) int)) %0))
g_terminates_0: ((~Int.Lt : (arrow int (arrow int bool)))
 ((~List..adtRank : (arrow (List a) int)) ((~List..tl : (arrow (List a) (List a))) %0))
 ((~List..adtRank : (arrow (List a) int)) %0))
-/
#guard_msgs in
#eval termObligations (fgPgm "c" true false)

/-- `f<tv>(xs : List tv)` and `g<a, ph>(ys : List a)` calling each other at the caller's type
    variable; `g`'s measure is `len(ys)` under an `ite` on `forall z : ph :: true`. -/
private def fgPhantomPgm (tv ph : String) : Core.Program :=
  let callTy (v : String) : Option LMonoTy := some (.arrow (listTy (.ftvar v)) .int)
  let lenYs : Core.Expression.Expr :=
    .app Core.coreLoc (opE "len" (some (.arrow (listTy (.ftvar "a")) .int))) (listVar "ys" "a")
  let trueE : Core.Expression.Expr := .const Core.coreLoc (.boolConst true)
  let g : Core.Function :=
    { recFn "g" "a" "ys" "f" (callTy "a") true with
      typeArgs := ["a", ph],
      measure := some (.ite Core.coreLoc
                       (.quant Core.coreLoc .all "z" (some (.ftvar ph)) trueE trueE)
        lenYs lenYs) }
  { decls := [
    .type (.data [listDt]) .empty,
    .recFuncBlock [recFn "f" tv "xs" "g" (callTy tv) true, g] .empty] }

-- The type checker rejects `g`, whose type parameter `b` is in neither its
-- input types nor its output type.
/--
info: error: Function 'g': type parameters [b] occur in neither an input type nor the output type,
so a call could not determine them
-/
#guard_msgs in
#eval Std.format (Core.typeCheck .default (fgPhantomPgm "b" "b"))

-- Without type checking, the call of `g` in `f<b>` leaves `g`'s `b` unbound:
-- the lemma names it with a reserved prefix, so `f`'s own `b` cannot capture it.
/--
info: f_terminates_0: ((~Int.Le : (arrow int (arrow int bool)))
 #0
 (if (∀ (bvar:$__termty1) #true) then ((~len : (arrow (List b) int))
   ((~List..tl : (arrow (List b) (List b)))
    %0)) else ((~len : (arrow (List b) int)) ((~List..tl : (arrow (List b) (List b))) %0))))
f_terminates_1: ((~Int.Lt : (arrow int (arrow int bool)))
 (if (∀ (bvar:$__termty1) #true) then ((~len : (arrow (List b) int))
   ((~List..tl : (arrow (List b) (List b)))
    %0)) else ((~len : (arrow (List b) int)) ((~List..tl : (arrow (List b) (List b))) %0)))
 ((~len : (arrow (List b) int)) %0))
g_terminates_0: ((~Int.Le : (arrow int (arrow int bool)))
 #0
 ((~len : (arrow (List a) int)) ((~List..tl : (arrow (List a) (List a))) %0)))
g_terminates_1: ((~Int.Lt : (arrow int (arrow int bool)))
 ((~len : (arrow (List a) int)) ((~List..tl : (arrow (List a) (List a))) %0))
 (if (∀ (bvar:b) #true) then ((~len : (arrow (List a) int)) %0) else ((~len : (arrow (List a) int))
%0)))
-/
#guard_msgs in
#eval termObligations (fgPhantomPgm "b" "b")

-- The same block with `f`'s type parameter named `c`: the same lemmas with
-- `f`'s `b` renamed to `c`.
/--
info: f_terminates_0: ((~Int.Le : (arrow int (arrow int bool)))
 #0
 (if (∀ (bvar:$__termty1) #true) then ((~len : (arrow (List c) int))
   ((~List..tl : (arrow (List c) (List c)))
    %0)) else ((~len : (arrow (List c) int)) ((~List..tl : (arrow (List c) (List c))) %0))))
f_terminates_1: ((~Int.Lt : (arrow int (arrow int bool)))
 (if (∀ (bvar:$__termty1) #true) then ((~len : (arrow (List c) int))
   ((~List..tl : (arrow (List c) (List c)))
    %0)) else ((~len : (arrow (List c) int)) ((~List..tl : (arrow (List c) (List c))) %0)))
 ((~len : (arrow (List c) int)) %0))
g_terminates_0: ((~Int.Le : (arrow int (arrow int bool)))
 #0
 ((~len : (arrow (List a) int)) ((~List..tl : (arrow (List a) (List a))) %0)))
g_terminates_1: ((~Int.Lt : (arrow int (arrow int bool)))
 ((~len : (arrow (List a) int)) ((~List..tl : (arrow (List a) (List a))) %0))
 (if (∀ (bvar:b) #true) then ((~len : (arrow (List a) int)) %0) else ((~len : (arrow (List a) int))
%0)))
-/
#guard_msgs in
#eval termObligations (fgPhantomPgm "c" "b")

-- The same block with `g`'s phantom type parameter named `d`: only `g`'s own
-- lemma changes `b` to `d`; `f`'s lemmas still use the reserved name.
/--
info: f_terminates_0: ((~Int.Le : (arrow int (arrow int bool)))
 #0
 (if (∀ (bvar:$__termty1) #true) then ((~len : (arrow (List b) int))
   ((~List..tl : (arrow (List b) (List b)))
    %0)) else ((~len : (arrow (List b) int)) ((~List..tl : (arrow (List b) (List b))) %0))))
f_terminates_1: ((~Int.Lt : (arrow int (arrow int bool)))
 (if (∀ (bvar:$__termty1) #true) then ((~len : (arrow (List b) int))
   ((~List..tl : (arrow (List b) (List b)))
    %0)) else ((~len : (arrow (List b) int)) ((~List..tl : (arrow (List b) (List b))) %0)))
 ((~len : (arrow (List b) int)) %0))
g_terminates_0: ((~Int.Le : (arrow int (arrow int bool)))
 #0
 ((~len : (arrow (List a) int)) ((~List..tl : (arrow (List a) (List a))) %0)))
g_terminates_1: ((~Int.Lt : (arrow int (arrow int bool)))
 ((~len : (arrow (List a) int)) ((~List..tl : (arrow (List a) (List a))) %0))
 (if (∀ (bvar:d) #true) then ((~len : (arrow (List a) int)) %0) else ((~len : (arrow (List a) int))
%0)))
-/
#guard_msgs in
#eval termObligations (fgPhantomPgm "b" "d")

/-- `IntList` with constructors `Nil()` and `Cons(hd : int, tl : IntList)`. -/
private def intListDt : LDatatype Unit :=
  { name := "IntList", typeArgs := [],
    constrs := [
      { name := ⟨"Nil", ()⟩, args := [] },
      { name := ⟨"Cons", ()⟩,
        args := [(⟨"hd", ()⟩, .int), (⟨"tl", ()⟩, .tcons "IntList" [])] }
    ], constrs_ne := rfl }

/-- `g(@[cases] ys : IntList) : int` with
    `if IntList..isNil(ys) then 0 else g(IntList..tl(ys))`, the recursive call
    unannotated. -/
private def monoPgm : Core.Program :=
  let t : LMonoTy := .tcons "IntList" []
  let ys : Core.Expression.Expr := .fvar Core.coreLoc ⟨"ys", ()⟩ (some t)
  let g : Core.Function :=
    { name := ⟨"g", ()⟩, isRecursive := true,
      inputs := [(⟨"ys", ()⟩, t)], output := .int,
      body := some (.ite Core.coreLoc
                    (.app Core.coreLoc (opE "IntList..isNil" (some (.arrow t .bool))) ys)
        (.intConst Core.coreLoc 0)
        (.app Core.coreLoc (opE "g" none)
          (.app Core.coreLoc (opE "IntList..tl" (some (.arrow t t))) ys))),
      attr := #[.inlineIfConstr 0] }
  { decls := [.type (.data [intListDt]) .empty, .recFuncBlock [g] .empty] }

-- A monomorphic callee with an unannotated call: its rank is taken at
-- `IntList → int`.
/--
info: g_terminates_0: ((~Int.Lt : (arrow int (arrow int bool)))
 ((~IntList..adtRank : (arrow IntList int)) ((~IntList..tl : (arrow IntList IntList)) %0))
 ((~IntList..adtRank : (arrow IntList int)) %0))
-/
#guard_msgs in
#eval termObligations monoPgm

end CallInstance

end Strata.TerminationCheckTest

end
