/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

/-!
# Datatype Tree Integration Test

Tests binary recursive Tree datatypes using the DDM datatype declaration syntax.
Verifies:
- Parsing of Tree datatype declarations with Leaf(val: int) and Node(left: Tree, right: Tree) constructors
- Tester functions (Tree..isLeaf, Tree..isNode)
- Destructor functions (val, left, right) for field access
- Type-checking and verification with binary recursive type
-/

namespace Strata.DatatypeTreeTest

---------------------------------------------------------------------
-- Test 1: Basic Tree Datatype Declaration and Tester Functions
---------------------------------------------------------------------

def treeTesterPgm : Program :=
#strata
program Boogie;

// Define Tree datatype with Leaf(val: int) and Node(left: Tree, right: Tree) constructors
datatype Tree () { Leaf(val: int), Node(left: Tree, right: Tree) };

procedure TestTreeTesters() returns ()
spec {
  ensures true;
}
{
  var t : Tree;
  var u : Tree;

  // Create a Leaf
  t := Leaf(42);

  // Test that t is Leaf
  assert [isLeaf]: Tree..isLeaf(t);

  // Test that t is not Node
  assert [notNode]: !Tree..isNode(t);

  // Create a Node with two Leaf children
  u := Node(Leaf(1), Leaf(2));

  // Test that u is Node
  assert [isNode]: Tree..isNode(u);

  // Test that u is not Leaf
  assert [notLeaf]: !Tree..isLeaf(u);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram treeTesterPgm) |>.snd |>.isEmpty

/--
info:
Obligation: isLeaf
Result: verified

Obligation: notNode
Result: verified

Obligation: isNode
Result: verified

Obligation: notLeaf
Result: verified

Obligation: TestTreeTesters_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" treeTesterPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 2: Tree with Havoc (requires SMT reasoning)
---------------------------------------------------------------------

def treeHavocPgm : Program :=
#strata
program Boogie;

datatype Tree () { Leaf(val: int), Node(left: Tree, right: Tree) };

procedure TestTreeHavoc() returns ()
spec {
  ensures true;
}
{
  var t : Tree;

  // Initialize and then havoc
  t := Leaf(0);
  havoc t;

  // Assume t is Node
  assume Tree..isNode(t);

  // Assert t is not Leaf (should follow from assumption)
  assert [notLeaf]: !Tree..isLeaf(t);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram treeHavocPgm) |>.snd |>.isEmpty

/--
info:
Obligation: notLeaf
Result: verified

Obligation: TestTreeHavoc_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" treeHavocPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 3: Tree Exhaustiveness (exactly one tester is true)
---------------------------------------------------------------------

def treeExhaustivePgm : Program :=
#strata
program Boogie;

datatype Tree () { Leaf(val: int), Node(left: Tree, right: Tree) };

procedure TestTreeExhaustive() returns ()
spec {
  ensures true;
}
{
  var t : Tree;

  // Havoc to get arbitrary Tree
  t := Leaf(0);
  havoc t;

  // At least one tester must be true (exhaustiveness)
  assert [exhaustive]: Tree..isLeaf(t) || Tree..isNode(t);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram treeExhaustivePgm) |>.snd |>.isEmpty

/--
info:
Obligation: exhaustive
Result: verified

Obligation: TestTreeExhaustive_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" treeExhaustivePgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 4: Tree Mutual Exclusion (testers are mutually exclusive)
---------------------------------------------------------------------

def treeMutualExclusionPgm : Program :=
#strata
program Boogie;

datatype Tree () { Leaf(val: int), Node(left: Tree, right: Tree) };

procedure TestTreeMutualExclusion() returns ()
spec {
  ensures true;
}
{
  var t : Tree;

  // Havoc to get arbitrary Tree
  t := Leaf(0);
  havoc t;

  // Assume t is Leaf
  assume Tree..isLeaf(t);

  // Assert t is not Node (mutual exclusion)
  assert [mutualExclusion]: !Tree..isNode(t);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram treeMutualExclusionPgm) |>.snd |>.isEmpty

/--
info:
Obligation: mutualExclusion
Result: verified

Obligation: TestTreeMutualExclusion_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" treeMutualExclusionPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 5: Tree Constructor Equality
---------------------------------------------------------------------

def treeEqualityPgm : Program :=
#strata
program Boogie;

datatype Tree () { Leaf(val: int), Node(left: Tree, right: Tree) };

procedure TestTreeEquality() returns ()
spec {
  ensures true;
}
{
  var t : Tree;
  var u : Tree;

  // Create two Leaf values with same argument
  t := Leaf(42);
  u := Leaf(42);

  // Assert they are equal
  assert [leafEquality]: t == u;

  // Create two Node values with same children
  t := Node(Leaf(1), Leaf(2));
  u := Node(Leaf(1), Leaf(2));

  // Assert they are equal
  assert [nodeEquality]: t == u;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram treeEqualityPgm) |>.snd |>.isEmpty

/--
info:
Obligation: leafEquality
Result: verified

Obligation: nodeEquality
Result: verified

Obligation: TestTreeEquality_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" treeEqualityPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 6: Tree Constructor Inequality
---------------------------------------------------------------------

def treeInequalityPgm : Program :=
#strata
program Boogie;

datatype Tree () { Leaf(val: int), Node(left: Tree, right: Tree) };

procedure TestTreeInequality() returns ()
spec {
  ensures true;
}
{
  var t : Tree;
  var u : Tree;

  // Create Leaf and Node values
  t := Leaf(42);
  u := Node(Leaf(1), Leaf(2));

  // Assert they are not equal
  assert [leafVsNode]: t != u;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram treeInequalityPgm) |>.snd |>.isEmpty

/--
info:
Obligation: leafVsNode
Result: verified

Obligation: TestTreeInequality_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" treeInequalityPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 7: Tree Destructor Functions (val, left, right)
---------------------------------------------------------------------

def treeDestructorPgm : Program :=
#strata
program Boogie;

datatype Tree () { Leaf(val: int), Node(left: Tree, right: Tree) };

procedure TestTreeDestructor() returns ()
spec {
  ensures true;
}
{
  var t : Tree;
  var v : int;
  var l : Tree;
  var r : Tree;

  // Create a Leaf value with known content
  t := Leaf(42);

  // Extract the val using the destructor function
  v := val(t);

  // Assert the extracted val is correct
  assert [valIs42]: v == 42;

  // Create a Node with known children
  t := Node(Leaf(10), Leaf(20));

  // Extract the left child
  l := left(t);

  // Assert the left child is a Leaf with val 10
  assert [leftIsLeaf]: Tree..isLeaf(l);
  assert [leftVal]: val(l) == 10;

  // Extract the right child
  r := right(t);

  // Assert the right child is a Leaf with val 20
  assert [rightIsLeaf]: Tree..isLeaf(r);
  assert [rightVal]: val(r) == 20;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram treeDestructorPgm) |>.snd |>.isEmpty

/--
info:
Obligation: valIs42
Result: verified

Obligation: leftIsLeaf
Result: verified

Obligation: leftVal
Result: verified

Obligation: rightIsLeaf
Result: verified

Obligation: rightVal
Result: verified

Obligation: TestTreeDestructor_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" treeDestructorPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 8: Nested Tree Operations (deeper tree structure)
---------------------------------------------------------------------

def treeNestedPgm : Program :=
#strata
program Boogie;

datatype Tree () { Leaf(val: int), Node(left: Tree, right: Tree) };

procedure TestTreeNested() returns ()
spec {
  ensures true;
}
{
  var t : Tree;
  var leftLeft : Tree;
  var v : int;

  // Create a tree:
  //        Node
  //       /    \
  //     Node   Leaf(3)
  //    /    \
  // Leaf(1) Leaf(2)
  t := Node(Node(Leaf(1), Leaf(2)), Leaf(3));

  // Get the left-left child (should be Leaf(1))
  leftLeft := left(left(t));

  // Assert it's a Leaf
  assert [leftLeftIsLeaf]: Tree..isLeaf(leftLeft);

  // Get its value
  v := val(leftLeft);

  // Assert the value is 1
  assert [leftLeftVal]: v == 1;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram treeNestedPgm) |>.snd |>.isEmpty

/--
info:
Obligation: leftLeftIsLeaf
Result: verified

Obligation: leftLeftVal
Result: verified

Obligation: TestTreeNested_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" treeNestedPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 9: Tree Destructor with Havoc (requires SMT reasoning)
---------------------------------------------------------------------

def treeDestructorHavocPgm : Program :=
#strata
program Boogie;

datatype Tree () { Leaf(val: int), Node(left: Tree, right: Tree) };

procedure TestTreeDestructorHavoc() returns ()
spec {
  ensures true;
}
{
  var t : Tree;
  var v : int;

  // Initialize and then havoc
  t := Leaf(0);
  havoc t;

  // Assume t is a specific Leaf
  assume t == Leaf(100);

  // Extract val
  v := val(t);

  // Assert val is 100
  assert [valIs100]: v == 100;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram treeDestructorHavocPgm) |>.snd |>.isEmpty

/--
info:
Obligation: valIs100
Result: verified

Obligation: TestTreeDestructorHavoc_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" treeDestructorHavocPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 10: Tree with Different Values (inequality of different vals)
---------------------------------------------------------------------

def treeDifferentValuesPgm : Program :=
#strata
program Boogie;

datatype Tree () { Leaf(val: int), Node(left: Tree, right: Tree) };

procedure TestTreeDifferentValues() returns ()
spec {
  ensures true;
}
{
  var t : Tree;
  var u : Tree;

  // Create two Leaf values with different vals
  t := Leaf(1);
  u := Leaf(2);

  // Assert they are not equal
  assert [different_vals]: t != u;

  // Create two Node values with different children
  t := Node(Leaf(1), Leaf(2));
  u := Node(Leaf(2), Leaf(1));

  // Assert they are not equal (different structure)
  assert [different_children]: t != u;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram treeDifferentValuesPgm) |>.snd |>.isEmpty

/--
info:
Obligation: different_vals
Result: verified

Obligation: different_children
Result: verified

Obligation: TestTreeDifferentValues_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" treeDifferentValuesPgm Inhabited.default Options.quiet

end Strata.DatatypeTreeTest
