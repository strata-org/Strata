/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
Chained field access on nested composites (`o#inner#count`), both read and
write. Single-level field access (`o#inner`, `i#count`) already worked; this
exercises the chaining enabled by three changes:

  * Parse — `fieldAccess` is now `leftassoc`, so `a#b#c` left-recurses.
  * Resolution — `targetTypeName` resolves a `.Var (.Field ..)` target by
    recursing on the inner target and looking the field up in that type's scope.
  * Heap — the field-read arm recurses into its target, so a nested
    `FieldSelect` is eliminated rather than leaking raw into `readField`.
-/

#eval testLaurel <|
#strata
program Laurel;
composite Inner {
  var count: int
}

composite Outer {
  var inner: Inner
}

// Three nested composite levels, for the depth-3 chain `a#mid#inner#count`.
composite Innermost {
  var count: int
}

composite Middle {
  var inner: Innermost
}

composite Outermost {
  var mid: Middle
}

procedure chainedReadWrite()
  opaque
{
  var o: Outer := new Outer;
  var i: Inner := new Inner;
  o#inner := i;

  o#inner#count := 7;
  assert o#inner#count == 7;

  // Write through the chain again and read it back.
  o#inner#count := o#inner#count + 1;
  assert o#inner#count == 8;

  // The chained read agrees with the single-level read of the same object.
  assert i#count == 8
};

procedure chainedReadAfterInnerAssign()
  opaque
{
  var o: Outer := new Outer;
  var i: Inner := new Inner;
  i#count := 3;
  o#inner := i;
  // Reading through the chain sees the value written on `i` directly.
  assert o#inner#count == 3
};

procedure chainedAliasing()
  opaque
{
  var o: Outer := new Outer;
  var i: Inner := new Inner;
  o#inner := i;
  o#inner#count := 1;

  // `i` and `o#inner` alias the same Inner, so a write through one is seen
  // through the other.
  i#count := 42;
  assert o#inner#count == 42
};

procedure depth3ReadWrite()
  opaque
{
  var a: Outermost := new Outermost;
  var b: Middle := new Middle;
  var c: Innermost := new Innermost;
  a#mid := b;
  b#inner := c;

  a#mid#inner#count := 9;
  assert a#mid#inner#count == 9;
  // The depth-3 chain agrees with the single-level read of the same object.
  assert c#count == 9
};

procedure chainedReadOnBothSides()
  opaque
{
  var o: Outer := new Outer;
  var p: Outer := new Outer;
  var i: Inner := new Inner;
  var j: Inner := new Inner;
  o#inner := i;
  p#inner := j;
  i#count := 4;
  j#count := 4;
  // Chained read on both operands of a comparison.
  assert o#inner#count == p#inner#count
};

// Paren-free chained incr/decr: `o#inner#count++` parses as `(o#inner#count)++`
// because `fieldAccess` (prec 95) binds tighter than postfix `++`/`--` (prec 90),
// and `leftassoc` lets the chain `o#inner#count` left-recurse.
procedure chainedParenFreeIncrDecr()
  opaque
{
  var o: Outer := new Outer;
  var i: Inner := new Inner;
  o#inner := i;
  o#inner#count := 10;
  o#inner#count++;
  assert o#inner#count == 11;
  o#inner#count--;
  assert o#inner#count == 10;
  // Postfix in expression position yields the OLD value (10); the cell becomes 11.
  var y: int := o#inner#count++;
  assert o#inner#count == 11;
  assert y == 10
};

// Negative: an unconstrained chained field has no known value, so asserting a
// concrete value must NOT be provable. Pins the chained read as non-vacuous.
procedure chainedReadUnconstrainedFails()
  opaque
{
  var o: Outer := new Outer;
  var i: Inner := new Inner;
  o#inner := i;
  assert o#inner#count == 7
//^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};

// Negative (frame soundness): two distinct outers whose inner fields MAY alias.
// A write through `a#inner` may be observed through `b#inner`, so the post-write
// value of `b#inner#count` is not provably its pre-write value.
procedure chainedMayAliasFails()
  opaque
{
  var a: Outer := new Outer;
  var b: Outer := new Outer;
  var i: Inner := new Inner;
  a#inner := i;
  b#inner := i;
  a#inner#count := 5;
  assert b#inner#count == 0
//^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};

// Negative (write isolation): a write through one chain must not be observable on
// a genuinely disjoint, freshly-allocated object.
procedure chainedWriteIsolationFails()
  opaque
{
  var o: Outer := new Outer;
  var i: Inner := new Inner;
  var d: Inner := new Inner;
  o#inner := i;
  o#inner#count := 7;
  assert d#count == 7
//^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end
