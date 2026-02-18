/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Mutual Datatype Integration Tests

Tests mutually recursive datatypes using the DDM datatype declaration syntax.
-/

namespace Strata.MutualDatatypeTest

---------------------------------------------------------------------
-- Test 1: Basic Rose Tree Datatype Declaration and Tester Functions
---------------------------------------------------------------------

def roseTreeTesterPgm : Program :=
#strata
program Core;

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

  f := FNil();
  assert [isFNil]: Forest..isFNil(f);
  assert [notFCons]: !Forest..isFCons(f);

  t := Node(42, FNil());
  assert [isNode]: RoseTree..isNode(t);

  f := FCons(Node(1, FNil()), FNil());
  assert [isFCons]: Forest..isFCons(f);
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
#eval verify roseTreeTesterPgm Inhabited.default
  (options := Options.quiet)

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

  t := Node(42, FNil());

  v := RoseTree..val(t);
  assert [valIs42]: v == 42;

  c := RoseTree..children(t);
  assert [childrenIsNil]: Forest..isFNil(c);

  f := FCons(Node(10, FNil()), FNil());

  t := Forest..head(f);
  assert [headIsNode]: RoseTree..isNode(t);
  assert [headVal]: RoseTree..val(t) == 10;

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
#eval verify roseTreeDestructorPgm Inhabited.default
  (options := Options.quiet)

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

  t1 := Node(42, FNil());
  t2 := Node(42, FNil());
  assert [leafEquality]: t1 == t2;

  f1 := FNil();
  f2 := FNil();
  assert [emptyForestEquality]: f1 == f2;

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
#eval verify roseTreeEqualityPgm Inhabited.default
  (options := Options.quiet)

---------------------------------------------------------------------
-- Test 4: Polymorphic Rose Tree with Havoc (SMT verification)
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
#eval verify polyRoseTreeHavocPgm Inhabited.default
  (options := Options.quiet)

---------------------------------------------------------------------
-- Test 5: Imperative Stmt/StmtList with Havoc (SMT verification)
---------------------------------------------------------------------

/-- Mutually recursive Stmt/StmtList modeling Imperative.Stmt -/
def stmtListHavocPgm : Program :=
#strata
program Core;

forward type Stmt (e : Type, c : Type);
forward type StmtList (e : Type, c : Type);
mutual
  datatype StmtList (e : Type, c : Type) { SNil(), SCons(hd: Stmt e c, tl: StmtList e c) };
  datatype Stmt (e : Type, c : Type) {
    Cmd(cmd: c),
    Block(label: int, blockBody: StmtList e c),
    Ite(cond: e, thenB: StmtList e c, elseB: StmtList e c),
    Loop(guard: e, loopBody: StmtList e c),
    Goto(target: int)
  };
end;

procedure TestStmtListHavoc() returns ()
spec {
  ensures true;
}
{
  var s : Stmt bool int;
  var ss : StmtList bool int;

  havoc s;
  havoc ss;

  // A block containing a single command
  assume s == Block(1, SCons(Cmd(42), SNil()));
  assume ss == SCons(s, SCons(Goto(1), SNil()));

  assert [isBlock]: Stmt..isBlock(s);
  assert [bodyHd]: Stmt..isCmd(StmtList..hd(Stmt..blockBody(s)));
  assert [cmdVal]: Stmt..cmd(StmtList..hd(Stmt..blockBody(s))) == 42;
  assert [secondIsGoto]: Stmt..isGoto(StmtList..hd(StmtList..tl(ss)));
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram stmtListHavocPgm) |>.snd |>.isEmpty

/--
info:
Obligation: isBlock
Property: assert
Result: ✅ pass

Obligation: bodyHd
Property: assert
Result: ✅ pass

Obligation: cmdVal
Property: assert
Result: ✅ pass

Obligation: secondIsGoto
Property: assert
Result: ✅ pass

Obligation: TestStmtListHavoc_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify stmtListHavocPgm Inhabited.default
  (options := Options.quiet)

end Strata.MutualDatatypeTest
