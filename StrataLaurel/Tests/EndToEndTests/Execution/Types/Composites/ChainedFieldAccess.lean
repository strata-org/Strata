/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

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

#eval testLaurelExecution {} <|
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
  entry
  opaque
  modifies *
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
  entry
  opaque
  modifies *
{
  var o: Outer := new Outer;
  var i: Inner := new Inner;
  i#count := 3;
  o#inner := i;
  // Reading through the chain sees the value written on `i` directly.
  assert o#inner#count == 3
};

procedure chainedAliasing()
  entry
  opaque
  modifies *
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
  entry
  opaque
  modifies *
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
  entry
  opaque
  modifies *
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
  entry
  opaque
  modifies *
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

#end

-- No Core interpreter: reading a never-written field leaves a residual `select`, so the assert "did not reduce to bool".
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
composite Inner {
  var count: int
}

composite Outer {
  var inner: Inner
}

// Negative: an unconstrained chained field has no known value, so asserting a
// concrete value must NOT be provable. Pins the chained read as non-vacuous.
procedure chainedReadUnconstrainedFails()
  opaque
{
  var o: Outer := new Outer;
  var i: Inner := new Inner;
  o#inner := i;
  assert o#inner#count == 7
//^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
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
//^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
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
//^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
procedure runAll() entry
  opaque
  modifies *
{
  chainedReadUnconstrainedFails();
  chainedMayAliasFails();
  chainedWriteIsolationFails()
};
#end

/-! ## Chaining THROUGH a generic composite's field

The chains above are all between ordinary composites. Here the middle link is a field whose
declared type is the generic composite's own type parameter (`Pair<A, B>`'s `b: B`), so the
field's type only becomes a composite at the instantiation — `Pair<int, Z>` makes `p#b` a
`Z`, which is what lets `p#b#az` resolve at all. `targetTypeName` therefore has to look the
inner field up in the MONOMORPHIZED holder's scope; against the generic declaration `b` has
type `B`, which has no fields.

Both blocks mark an `entry`, so the chain is also WALKED: `p#b#az` is read through the
monomorphized holder at runtime, not only resolved. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Z { var az: int }
composite W { var aw: int }
composite Zw { var z2: W }
composite Pair<A, B> { var a: A
 var b: B }

// Read through the generic field.
procedure genericChainedRead()
  entry
  opaque
  modifies *
{
  var p: Pair<int, Z> := new Pair<int, Z>;
  var zz: Z := new Z;
  zz#az := 5;
  p#b := zz;
  assert p#b#az == 5
};

// Write through the generic field, then read it back.
procedure genericChainedWrite()
  entry
  opaque
  modifies *
{
  var p: Pair<int, Z> := new Pair<int, Z>;
  var zz: Z := new Z;
  p#b := zz;
  p#b#az := 7;
  assert p#b#az == 7
};

// Three levels, the first of which is the generic field: resolution has to recurse through
// the monomorphized type rather than stopping at the first ordinary composite.
procedure genericChainedThreeLevels()
  entry
  opaque
  modifies *
{
  var p: Pair<int, Zw> := new Pair<int, Zw>;
  var zz: Zw := new Zw;
  var ww: W := new W;
  ww#aw := 9;
  zz#z2 := ww;
  p#b := zz;
  assert p#b#z2#aw == 9
};
#end

-- SOUNDNESS twin: the chained read through the generic field is constrained, so a false
-- claim must fail rather than pass on a field that resolved to something unconstrained.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Z { var az: int }
composite Pair<A, B> { var a: A
 var b: B }

procedure genericChainedReadFalse()
  entry
  opaque
  modifies *
{
  var p: Pair<int, Z> := new Pair<int, Z>;
  var zz: Z := new Z;
  zz#az := 5;
  p#b := zz;
  assert p#b#az == 6
//^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- The generic chain resolves fields that genuinely exist and no more: `nope` is on neither
-- `Pair` nor the `Z` its `b` field became, so the chain must still be rejected. Looking the
-- field up in the monomorphized holder's scope is what makes `p#b#az` work; it must not also
-- make `p#b#nope` work.
#eval testLaurelResolution <|
#strata
program Laurel;
composite Z { var az: int }
composite Pair<A, B> { var a: A
 var b: B }

procedure genericChainedUnknownField()
  opaque
  modifies *
{
  var p: Pair<int, Z> := new Pair<int, Z>;
  var zz: Z := new Z;
  p#b := zz;
  assert p#b#nope == 5
//           ^^^^ error: Resolution failed: 'nope' is not defined
};
#end
