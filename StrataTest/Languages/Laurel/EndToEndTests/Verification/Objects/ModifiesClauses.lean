/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
A modifies clause CAN be placed on any procedure to generate a modifies axiom.
The modifies clause determines which references the procedure may modify.
This modifies axiom states how the in and out heap of the procedure relate.

A modifies clause is crucial on opaque procedures,
since otherwise all heap state is lost after calling them.

-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurel <|
#strata
program Laurel;
composite Container {
  var value: int
}

procedure modifyContainerOpaque(c: Container) returns (b: bool)
  opaque
  modifies c
{
  c#value := c#value + 1;
  true
};

procedure caller()
  opaque
{
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  var b: bool := modifyContainerOpaque(c);
  assert x == d#value // pass
};

// Commented out because
// Transparent assignments are not supported yet
// procedure modifyContainerTransparant(c: Container) returns (i: int)
//{
//  c#value := c#value + 1;
//  7
//};
//procedure modifyContainerWithPermission1(c: Container, d: Container)
//   ensures true
//   modifies c
//{
//    var i: int := modifyContainerTransparant(c);
//}

procedure modifyContainerWildcard(c: Container) returns (i: int)
  opaque
  modifies *
{
  c#value := c#value + 1;
  7
};

procedure modifyContainerWithoutPermission1(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: modifies clause does not hold
  opaque
{
    var i: int := modifyContainerWildcard(c)
};

procedure modifyContainerWithoutPermission2(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: modifies clause could not be proved
  opaque
  modifies d
{
    c#value := 2
};

procedure modifyContainerWithoutPermission3(c: Container, d: Container)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: modifies clause could not be proved
  opaque
  modifies d
{
    var i: bool := modifyContainerOpaque(c)
};

procedure multipleModifiesClauses(c: Container, d: Container, e: Container)
  opaque
  modifies c
  modifies d
;

procedure multipleModifiesClausesCaller()
  opaque
{
  var c: Container := new Container;
  var d: Container := new Container;
  var e: Container := new Container;
  var x: int := e#value;
  multipleModifiesClauses(c, d, e);
  assert x == e#value // pass
};

procedure newObjectDoNotCountForModifies()
  opaque
{
  var c: Container := new Container;
  c#value := 1
};

procedure modifiesWildcardBodiless(c: Container, d: Container)
  opaque
  modifies *;

procedure modifiesWildcardBodilessCaller()
  opaque
  modifies *
{
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  modifiesWildcardBodiless(c, d);
  assert x == d#value // this should fail because modifies * means anything can change
//^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};

procedure modifiesWildcardWithBody(c: Container, d: Container)
  opaque
  modifies *
{
  c#value := 2;
  d#value := 3
};

procedure modifiesWildcardAndSpecific(c: Container, d: Container)
  opaque
  modifies c
  modifies *;

procedure modifiesWildcardAndSpecificCaller()
  opaque
  modifies *
{
  var c: Container := new Container;
  var d: Container := new Container;
  var x: int := d#value;
  modifiesWildcardAndSpecific(c, d);
  assert x == d#value // fails because modifies * subsumes modifies c
//^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-
Field-granular modifies clauses (issue #1402).

A `modifies o#f` clause frames only the `(o, f)` pair: every *other* field of `o`
(and every other object) is preserved across the call, while `o#f` may change.
This is strictly more precise than the object-granular `modifies o`.
-/
#eval testLaurel <|
#strata
program Laurel;
composite Account {
  var balance: int
  var count: int
}

// Opaque stub framing only `self#balance`. Its body writes *only* balance, so it
// must satisfy its own field-granular frame (callee-side enforcement).
procedure deposit(self: Account, amount: int) returns (r: bool)
  opaque
  modifies self#balance
{
  self#balance := self#balance + amount;
  true
};

procedure fieldGranularCaller()
  opaque
{
  var a: Account := new Account;
  var b: Account := new Account;
  var oldCount: int := a#count;
  var oldBalance: int := a#balance;
  var oldBCount: int := b#count;
  var oldBBalance: int := b#balance;
  var ok: bool := deposit(a, 100);
  // Field-granular precision: the unmodified field of the modified object is preserved.
  assert a#count == oldCount;
  // Sibling object is fully preserved (object-granular frame already gave this).
  assert b#count == oldBCount;
  assert b#balance == oldBBalance;
  // The modified field may change -> not provable. This negative control proves
  // the frame is NOT vacuous: it does not silently preserve everything.
  assert a#balance == oldBalance
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-
Callee-side enforcement: a body that writes a field OUTSIDE its field-granular
modifies clause must fail to verify. Here `modifies self#balance` is declared
but the body also writes `self#count`, which is not framed.
-/
#eval testLaurel <|
#strata
program Laurel;
composite Account2 {
  var balance: int
  var count: int
}

procedure overreachingDeposit(self: Account2, amount: int) returns (r: bool)
//        ^^^^^^^^^^^^^^^^^^^ error: modifies clause could not be proved
  opaque
  modifies self#balance
{
  self#balance := self#balance + amount;
  self#count := self#count + 1;
  true
};
#end

/-
SOUNDNESS GATE (issue #1402): cross-type shared field name.

Cross-type field names: `Box1.x` and `Box2.x` are distinct constants, so framing
`b1#x` must not leak to `b2#x`. The three sibling asserts hold; modified `b1#x` is UNKNOWN.
-/
#eval testLaurel <|
#strata
program Laurel;
composite Box1 {
  var x: int
  var y: int
}
composite Box2 {
  var x: int
  var y: int
}

procedure bumpBox1X(self: Box1) returns (r: bool)
  opaque
  modifies self#x
{
  self#x := self#x + 1;
  true
};

procedure crossTypeCaller()
  opaque
{
  var b1: Box1 := new Box1;
  var b2: Box2 := new Box2;
  var oldB1x: int := b1#x;
  var oldB1y: int := b1#y;
  var oldB2x: int := b2#x;
  var oldB2y: int := b2#y;
  var ok: bool := bumpBox1X(b1);
  // Same object, other field: preserved (field granularity).
  assert b1#y == oldB1y;
  // Different type, SAME field name `x`: must be preserved (no cross-type leak).
  assert b2#x == oldB2x;
  // Different type, other field: preserved.
  assert b2#y == oldB2y;
  // Non-vacuity control: modified `b1#x` -> UNKNOWN.
  assert b1#x == oldB1x
//^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-
Vacuity trap: a BODILESS opaque stub must still emit its field frame. The mixed
PROVED/UNKNOWN outcome proves the frame is emitted and non-vacuous with no body.
-/
#eval testLaurel <|
#strata
program Laurel;
composite AccountA {
  var balance: int
  var count: int
}

// Bodiless opaque stub: frames only `self#balance`, no implementation.
procedure depositStub(self: AccountA)
  opaque
  modifies self#balance;

procedure vacuityTrapCaller()
  opaque
{
  var a: AccountA := new AccountA;
  var b: AccountA := new AccountA;
  var oldCount: int := a#count;
  var oldBalance: int := a#balance;
  var oldBCount: int := b#count;
  depositStub(a);
  // Unmodified field of the receiver: preserved (field granularity).
  assert a#count == oldCount;
  // Sibling object's field: preserved.
  assert b#count == oldBCount;
  // The MODIFIED field may change -> UNKNOWN (non-vacuity).
  assert a#balance == oldBalance
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-
Multi-field: `modifies self#x, self#y` frames two fields of one object; the
third field `z` stays preserved while `x` and `y` may change.
-/
#eval testLaurel <|
#strata
program Laurel;
composite Triple {
  var x: int
  var y: int
  var z: int
}

procedure writeXY(self: Triple)
  opaque
  modifies self#x, self#y
{
  self#x := self#x + 1;
  self#y := self#y + 1
};

procedure multiFieldCaller()
  opaque
{
  var t: Triple := new Triple;
  var oldX: int := t#x;
  var oldY: int := t#y;
  var oldZ: int := t#z;
  writeXY(t);
  // Unframed field: preserved.
  assert t#z == oldZ;
  // Framed fields: may change -> UNKNOWN.
  assert t#x == oldX;
//^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  assert t#y == oldY
//^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-
Mixed: `modifies o, p#f` combines a whole-object entry with a field entry.
`p`'s other field and a sibling stay preserved; `o#w` and `p#f` go UNKNOWN.
-/
#eval testLaurel <|
#strata
program Laurel;
composite Whole {
  var w: int
}
composite Part {
  var f: int
  var g: int
}

procedure mixedMod(o: Whole, p: Part)
  opaque
  modifies o, p#f
{
  o#w := o#w + 1;
  p#f := p#f + 1
};

procedure mixedCaller()
  opaque
{
  var o: Whole := new Whole;
  var p: Part := new Part;
  var s: Whole := new Whole;
  var oldOw: int := o#w;
  var oldPf: int := p#f;
  var oldPg: int := p#g;
  var oldSw: int := s#w;
  mixedMod(o, p);
  // `p`'s OTHER field: preserved (field granularity on p#f).
  assert p#g == oldPg;
  // Sibling whole object: preserved.
  assert s#w == oldSw;
  // Whole-object entry `o`: any field may change -> UNKNOWN.
  assert o#w == oldOw;
//^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  // Framed field `p#f`: may change -> UNKNOWN.
  assert p#f == oldPf
//^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-
Inheritance: `modifies d#bval` names an INHERITED field (declared in `Base`,
qualified `Base.bval`). Derived-only `dval` stays preserved; inherited `bval` is UNKNOWN.
-/
#eval testLaurel <|
#strata
program Laurel;
composite Base {
  var bval: int
}
composite Derived extends Base {
  var dval: int
}

procedure bumpInherited(d: Derived)
  opaque
  modifies d#bval
{
  d#bval := d#bval + 1
};

procedure inheritanceCaller()
  opaque
{
  var d: Derived := new Derived;
  var oldBval: int := d#bval;
  var oldDval: int := d#dval;
  bumpInherited(d);
  // Derived-only field: preserved (inherited field framed, not this one).
  assert d#dval == oldDval;
  // Inherited framed field: may change -> UNKNOWN.
  assert d#bval == oldBval
//^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end


/-
Callee-side field enforcement: declaring modifies o.x but writing o.y must fail.
-/
#eval testLaurel <|
#strata
program Laurel;
composite Pair {
  var x: int
  var y: int
}

procedure overreachX(self: Pair)
//        ^^^^^^^^^^ error: modifies clause could not be proved
  opaque
  modifies self#x
{
  self#y := self#y + 1
};
#end
