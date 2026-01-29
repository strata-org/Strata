/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Datatype Rose Tree Integration Test

Tests mutually recursive Rose Tree datatypes using the DDM datatype declaration syntax.
A rose tree is a tree where each node has a value and a list of children (forest).

This requires mutually recursive types:
- RoseTree: a node with a value and a forest of children
- Forest: a list of rose trees

Verifies:
- Parsing of mutually recursive datatype declarations
- Tester functions for both types
- Destructor functions for field access
- Type-checking and verification with mutually recursive types
-/

namespace Strata.DatatypeRoseTreeTest

---------------------------------------------------------------------
-- Test 1: Basic Rose Tree Datatype Declaration and Tester Functions
---------------------------------------------------------------------

def roseTreeTesterPgm : Program :=
#strata
program Core;

// Define mutually recursive Rose Tree and Forest datatypes using mutual block
// Forest is a list of RoseTrees
forward type RoseTree;
forward type Forest;
mutual
  datatype Forest { FNil(), FCons(head: RoseTree, tail: Forest) };
  datatype RoseTree { Node(val: int, children: Forest) };
end;

procedure TestRoseTreeTesters() returns ()
spec {
  ensures true;
}
{
  var t : RoseTree;
  var f : Forest;

  // Create an empty forest
  f := FNil();

  // Test that f is FNil
  assert [isFNil]: Forest..isFNil(f);

  // Test that f is not FCons
  assert [notFCons]: !Forest..isFCons(f);

  // Create a leaf node (node with empty forest)
  t := Node(42, FNil());

  // Test that t is Node
  assert [isNode]: RoseTree..isNode(t);

  // Create a non-empty forest
  f := FCons(Node(1, FNil()), FNil());

  // Test that f is FCons
  assert [isFCons]: Forest..isFCons(f);

  // Test that f is not FNil
  assert [notFNil]: !Forest..isFNil(f);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram roseTreeTesterPgm) |>.snd |>.isEmpty

/--
info:
Obligation: isFNil
Property: assert
Result: ✅ pass

Obligation: notFCons
Property: assert
Result: ✅ pass

Obligation: isNode
Property: assert
Result: ✅ pass

Obligation: isFCons
Property: assert
Result: ✅ pass

Obligation: notFNil
Property: assert
Result: ✅ pass

Obligation: TestRoseTreeTesters_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" roseTreeTesterPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 2: Rose Tree Destructor Functions
---------------------------------------------------------------------

def roseTreeDestructorPgm : Program :=
#strata
program Core;

forward type RoseTree;
forward type Forest;
mutual
  datatype Forest { FNil(), FCons(head: RoseTree, tail: Forest) };
  datatype RoseTree { Node(val: int, children: Forest) };
end;

procedure TestRoseTreeDestructor() returns ()
spec {
  ensures true;
}
{
  var t : RoseTree;
  var f : Forest;
  var v : int;
  var c : Forest;

  // Create a leaf node
  t := Node(42, FNil());

  // Extract the value
  v := RoseTree..val(t);
  assert [valIs42]: v == 42;

  // Extract the children (should be empty forest)
  c := RoseTree..children(t);
  assert [childrenIsNil]: Forest..isFNil(c);

  // Create a forest with one tree
  f := FCons(Node(10, FNil()), FNil());

  // Extract the head
  t := Forest..head(f);
  assert [headIsNode]: RoseTree..isNode(t);
  assert [headVal]: RoseTree..val(t) == 10;

  // Extract the tail
  f := Forest..tail(f);
  assert [tailIsNil]: Forest..isFNil(f);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram roseTreeDestructorPgm) |>.snd |>.isEmpty

/--
info:
Obligation: valIs42
Property: assert
Result: ✅ pass

Obligation: childrenIsNil
Property: assert
Result: ✅ pass

Obligation: headIsNode
Property: assert
Result: ✅ pass

Obligation: headVal
Property: assert
Result: ✅ pass

Obligation: tailIsNil
Property: assert
Result: ✅ pass

Obligation: TestRoseTreeDestructor_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" roseTreeDestructorPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 3: Rose Tree Equality
---------------------------------------------------------------------

def roseTreeEqualityPgm : Program :=
#strata
program Core;

forward type RoseTree;
forward type Forest;
mutual
  datatype Forest { FNil(), FCons(head: RoseTree, tail: Forest) };
  datatype RoseTree { Node(val: int, children: Forest) };
end;

procedure TestRoseTreeEquality() returns ()
spec {
  ensures true;
}
{
  var t1 : RoseTree;
  var t2 : RoseTree;
  var f1 : Forest;
  var f2 : Forest;

  // Create two identical leaf nodes
  t1 := Node(42, FNil());
  t2 := Node(42, FNil());
  assert [leafEquality]: t1 == t2;

  // Create two identical empty forests
  f1 := FNil();
  f2 := FNil();
  assert [emptyForestEquality]: f1 == f2;

  // Create two identical non-empty forests
  f1 := FCons(Node(1, FNil()), FNil());
  f2 := FCons(Node(1, FNil()), FNil());
  assert [forestEquality]: f1 == f2;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram roseTreeEqualityPgm) |>.snd |>.isEmpty

/--
info:
Obligation: leafEquality
Property: assert
Result: ✅ pass

Obligation: emptyForestEquality
Property: assert
Result: ✅ pass

Obligation: forestEquality
Property: assert
Result: ✅ pass

Obligation: TestRoseTreeEquality_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" roseTreeEqualityPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 4: Polymorphic Rose Tree
---------------------------------------------------------------------

def polyRoseTreeHavocPgm : Program :=
#strata
program Core;

forward type RoseTree (a : Type);
forward type Forest (a : Type);
mutual
  datatype Forest (a : Type) { FNil(), FCons(head: RoseTree a, tail: Forest a) };
  datatype RoseTree (a : Type) { Node(val: a, children: Forest a) };
end;

procedure TestPolyRoseTreeHavoc() returns ()
spec {
  ensures true;
}
{
  var t : RoseTree int;
  var f : Forest int;

  havoc t;
  havoc f;

  assume t == Node(42, FNil());
  assume f == FCons(t, FNil());

  assert [valIs42]: RoseTree..val(t) == 42;
  assert [headIsT]: Forest..head(f) == t;
  assert [headVal]: RoseTree..val(Forest..head(f)) == 42;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram polyRoseTreeHavocPgm) |>.snd |>.isEmpty

/--
info:
Obligation: valIs42
Property: assert
Result: ✅ pass

Obligation: headIsT
Property: assert
Result: ✅ pass

Obligation: headVal
Property: assert
Result: ✅ pass

Obligation: TestPolyRoseTreeHavoc_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" polyRoseTreeHavocPgm Inhabited.default Options.quiet

end Strata.DatatypeRoseTreeTest
