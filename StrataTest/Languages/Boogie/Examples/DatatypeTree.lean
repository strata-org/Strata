/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

/-!
# Complex Datatype Example: Binary Tree and Pair (Monomorphic)

This example demonstrates multiple datatypes working together,
including a binary tree structure and a pair type.
Uses concrete types instead of polymorphism.
-/

def intTreeLeafPgm : Program :=
#strata
program Boogie;

datatype IntTree {
  Leaf(value: int),
  Node(left: IntTree, right: IntTree)
};

procedure testLeaf(x: int) returns (r: IntTree)
spec {
  ensures [r_is_leaf]: (IntTree..isLeaf(r));
  ensures [value_correct]: (IntTree..value(r) == x);
}
{
  r := Leaf(x);
  assert [r_is_leaf]: IntTree..isLeaf(r);
  assert [value_correct]: (IntTree..value(r) == x);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram intTreeLeafPgm) |>.snd |>.isEmpty

---------------------------------------------------------------------

def intTreeNodePgm : Program :=
#strata
program Boogie;

datatype IntTree {
  Leaf(value: int),
  Node(left: IntTree, right: IntTree)
};

procedure testNode(left: IntTree, right: IntTree) returns (r: IntTree)
spec {
  ensures [r_is_node]: (IntTree..isNode(r));
  ensures [left_correct]: (IntTree..left(r) == left);
  ensures [right_correct]: (IntTree..right(r) == right);
}
{
  r := Node(left, right);
  assert [r_is_node]: IntTree..isNode(r);
  assert [left_correct]: (IntTree..left(r) == left);
  assert [right_correct]: (IntTree..right(r) == right);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram intTreeNodePgm) |>.snd |>.isEmpty

---------------------------------------------------------------------

def intBoolPairPgm : Program :=
#strata
program Boogie;

datatype IntBoolPair {
  MkPair(fst: int, snd: bool)
};

procedure testPair(x: int, y: bool) returns (r: IntBoolPair)
spec {
  ensures [r_is_pair]: (IntBoolPair..isMkPair(r));
  ensures [fst_correct]: (IntBoolPair..fst(r) == x);
  ensures [snd_correct]: (IntBoolPair..snd(r) == y);
}
{
  r := MkPair(x, y);
  assert [r_is_pair]: IntBoolPair..isMkPair(r);
  assert [fst_correct]: (IntBoolPair..fst(r) == x);
  assert [snd_correct]: (IntBoolPair..snd(r) == y);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram intBoolPairPgm) |>.snd |>.isEmpty

---------------------------------------------------------------------

end Strata
