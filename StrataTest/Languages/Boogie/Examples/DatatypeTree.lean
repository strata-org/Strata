/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

/-!
# Complex Datatype Example: Binary Tree and Pair

This example demonstrates multiple datatypes working together,
including a binary tree structure and a pair type.
-/

def treePgm : Program :=
#strata
program Boogie;

datatype Tree (α : Type) {
  Leaf(value: α),
  Node(left: Tree α, right: Tree α)
};

procedure testLeaf(x: int) returns (r: Tree int)
spec {
  ensures [r_is_leaf]: (Tree$isLeaf(r));
  ensures [value_correct]: (Tree$LeafProj0(r) == x);
}
{
  r := Leaf(x);
  assert [r_is_leaf]: Tree$isLeaf(r);
  assert [value_correct]: (Tree$LeafProj0(r) == x);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram treePgm) |>.snd |>.isEmpty

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: r_is_leaf
Assumptions:


Proof Obligation:
(~Tree$isLeaf (~Leaf $__x0))

Label: value_correct
Assumptions:


Proof Obligation:
((~Tree$LeafProj0 (~Leaf $__x0)) == $__x0)

Label: testLeaf_ensures_0
Assumptions:


Proof Obligation:
(~Tree$isLeaf (~Leaf $__x0))

Label: testLeaf_ensures_1
Assumptions:


Proof Obligation:
((~Tree$LeafProj0 (~Leaf $__x0)) == $__x0)

---
info:
Obligation: r_is_leaf
Result: verified

Obligation: value_correct
Result: verified

Obligation: testLeaf_ensures_0
Result: verified

Obligation: testLeaf_ensures_1
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" treePgm

---------------------------------------------------------------------

def treeNodePgm : Program :=
#strata
program Boogie;

datatype Tree (α : Type) {
  Leaf(value: α),
  Node(left: Tree α, right: Tree α)
};

procedure testNode(left: Tree int, right: Tree int) returns (r: Tree int)
spec {
  ensures [r_is_node]: (Tree$isNode(r));
  ensures [left_correct]: (Tree$NodeProj0(r) == left);
  ensures [right_correct]: (Tree$NodeProj1(r) == right);
}
{
  r := Node(left, right);
  assert [r_is_node]: Tree$isNode(r);
  assert [left_correct]: (Tree$NodeProj0(r) == left);
  assert [right_correct]: (Tree$NodeProj1(r) == right);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram treeNodePgm) |>.snd |>.isEmpty

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: r_is_node
Assumptions:


Proof Obligation:
(~Tree$isNode ((~Node $__left0) $__right0))

Label: left_correct
Assumptions:


Proof Obligation:
((~Tree$NodeProj0 ((~Node $__left0) $__right0)) == $__left0)

Label: right_correct
Assumptions:


Proof Obligation:
((~Tree$NodeProj1 ((~Node $__left0) $__right0)) == $__right0)

Label: testNode_ensures_0
Assumptions:


Proof Obligation:
(~Tree$isNode ((~Node $__left0) $__right0))

Label: testNode_ensures_1
Assumptions:


Proof Obligation:
((~Tree$NodeProj0 ((~Node $__left0) $__right0)) == $__left0)

Label: testNode_ensures_2
Assumptions:


Proof Obligation:
((~Tree$NodeProj1 ((~Node $__left0) $__right0)) == $__right0)

---
info:
Obligation: r_is_node
Result: verified

Obligation: left_correct
Result: verified

Obligation: right_correct
Result: verified

Obligation: testNode_ensures_0
Result: verified

Obligation: testNode_ensures_1
Result: verified

Obligation: testNode_ensures_2
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" treeNodePgm

---------------------------------------------------------------------

def pairPgm : Program :=
#strata
program Boogie;

datatype Pair (α : Type, β : Type) {
  Pair(fst: α, snd: β)
};

procedure testPair(x: int, y: bool) returns (r: Pair int bool)
spec {
  ensures [r_is_pair]: (Pair$isPair(r));
  ensures [fst_correct]: (Pair$PairProj0(r) == x);
  ensures [snd_correct]: (Pair$PairProj1(r) == y);
}
{
  r := Pair(x, y);
  assert [r_is_pair]: Pair$isPair(r);
  assert [fst_correct]: (Pair$PairProj0(r) == x);
  assert [snd_correct]: (Pair$PairProj1(r) == y);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram pairPgm) |>.snd |>.isEmpty

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: r_is_pair
Assumptions:


Proof Obligation:
(~Pair$isPair ((~Pair $__x0) $__y0))

Label: fst_correct
Assumptions:


Proof Obligation:
((~Pair$PairProj0 ((~Pair $__x0) $__y0)) == $__x0)

Label: snd_correct
Assumptions:


Proof Obligation:
((~Pair$PairProj1 ((~Pair $__x0) $__y0)) == $__y0)

Label: testPair_ensures_0
Assumptions:


Proof Obligation:
(~Pair$isPair ((~Pair $__x0) $__y0))

Label: testPair_ensures_1
Assumptions:


Proof Obligation:
((~Pair$PairProj0 ((~Pair $__x0) $__y0)) == $__x0)

Label: testPair_ensures_2
Assumptions:


Proof Obligation:
((~Pair$PairProj1 ((~Pair $__x0) $__y0)) == $__y0)

---
info:
Obligation: r_is_pair
Result: verified

Obligation: fst_correct
Result: verified

Obligation: snd_correct
Result: verified

Obligation: testPair_ensures_0
Result: verified

Obligation: testPair_ensures_1
Result: verified

Obligation: testPair_ensures_2
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" pairPgm

---------------------------------------------------------------------

def pairSwapPgm : Program :=
#strata
program Boogie;

datatype Pair (α : Type, β : Type) {
  Pair(fst: α, snd: β)
};

procedure swap(p: Pair int bool) returns (r: Pair bool int)
spec {
  ensures [fst_swapped]: (Pair$PairProj0(r) == Pair$PairProj1(p));
  ensures [snd_swapped]: (Pair$PairProj1(r) == Pair$PairProj0(p));
}
{
  var x: int;
  var y: bool;

  x := Pair$PairProj0(p);
  y := Pair$PairProj1(p);
  r := Pair(y, x);

  assert [fst_swapped]: (Pair$PairProj0(r) == Pair$PairProj1(p));
  assert [snd_swapped]: (Pair$PairProj1(r) == Pair$PairProj0(p));
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram pairSwapPgm) |>.snd |>.isEmpty

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: fst_swapped
Assumptions:


Proof Obligation:
((~Pair$PairProj0 ((~Pair $__y1) $__x1)) == (~Pair$PairProj1 $__p0))

Label: snd_swapped
Assumptions:


Proof Obligation:
((~Pair$PairProj1 ((~Pair $__y1) $__x1)) == (~Pair$PairProj0 $__p0))

Label: swap_ensures_0
Assumptions:


Proof Obligation:
((~Pair$PairProj0 ((~Pair $__y1) $__x1)) == (~Pair$PairProj1 $__p0))

Label: swap_ensures_1
Assumptions:


Proof Obligation:
((~Pair$PairProj1 ((~Pair $__y1) $__x1)) == (~Pair$PairProj0 $__p0))

---
info:
Obligation: fst_swapped
Result: verified

Obligation: snd_swapped
Result: verified

Obligation: swap_ensures_0
Result: verified

Obligation: swap_ensures_1
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" pairSwapPgm

---------------------------------------------------------------------

end Strata
