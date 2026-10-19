/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # A type-variable field is checked at the holder's instantiation

`GHolder<T> { var h: T }` declares `h` with no concrete type. At a use site the holder does
have one, so `g: GHolder<Pair<int, bool>>` makes `g#h` a `Pair<int, bool>` — and an access
that treats it as anything else has to be rejected. The check substitutes the DECLARING
composite's parameters: the holder's own arguments for its own field, and the remap-aware
`substitutedAncestors` for an inherited one.

This check can only ever REJECT. On polymorphic code — a holder whose arguments are
themselves type variables — the substitution is the identity and the field stays a `.TVar`,
which is why there is no accepting case that depends on it. So the positive controls below
are not there to show the check works; they are there to show it does not FIRE when the
access is correct, which is the only way it could do damage.

Three declaration shapes, because the substitution comes from a different place in each:

* the field is the holder's OWN — substitute the holder's arguments;
* the field is INHERITED at the parent's own parameter — substitute through the ancestor;
* the field is inherited through a REMAP (`GHolder<A, B> extends Base<B, A>`) — the
  substitution has to follow the swap, so inherited `h: U` at `GHolder<int, bool>` is a
  `bool`. Writing an `int` there is the case a remap-blind check would wrongly accept.

Read and write are both covered, since a check that walked only assignment targets would
miss a read into a wrongly-typed local.
-/

/-! ## The holder's OWN type-variable field -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Pair<X, Y> { var a: X
 var b: Y }
composite Other { var z: int }
composite GHolder<T> { var h: T }

procedure ownFieldWriteWrongType(g: GHolder<Pair<int, bool>>)
  opaque
  modifies g
{
  var o: Other := new Other;
  g#h := o
//       ^ error: expected 'Pair<int, bool>', got 'Other'
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
composite Pair<X, Y> { var a: X
 var b: Y }
composite Other { var z: int }
composite GHolder<T> { var h: T }

procedure ownFieldReadWrongType(g: GHolder<Pair<int, bool>>)
  opaque
{
  var o: Other := g#h
//                  ^ error: expected 'Other', got 'Pair<int, bool>'
};
#end

/-! ## An INHERITED type-variable field -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Pair<X, Y> { var a: X
 var b: Y }
composite Other { var z: int }
composite Base<T> { var h: T }
composite GHolder<T> extends Base<T> { var k: int }

procedure inheritedFieldWriteWrongType(g: GHolder<Pair<int, bool>>)
  opaque
  modifies g
{
  var o: Other := new Other;
  g#h := o
//       ^ error: expected 'Pair<int, bool>', got 'Other'
};
#end

-- Through the REMAP: `GHolder<A, B> extends Base<B, A>`, so inherited `h: U` at
-- `GHolder<int, bool>` is the child's SECOND argument — a `bool`. A remap-blind substitution
-- would make it `int` and accept the `7`.
#eval testLaurelResolution <|
#strata
program Laurel;
composite Base<U, V> { var h: U }
composite GHolder<A, B> extends Base<B, A> { var k: int }

procedure remappedInheritedFieldWriteWrongType(g: GHolder<int, bool>)
  opaque
  modifies g
{
  g#h := 7
//       ^ error: expected 'bool', got 'int'
};
#end

/-! ## Controls: the correct accesses are NOT rejected

Same three shapes, with the type the substitution actually yields. If the check over-fired,
these would fail — and every accepting case in `Execution/` that goes through a generic
composite's field would fail with them. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Pair<X, Y> { var a: X
 var b: Y }
composite GHolder<T> { var h: T }

procedure ownFieldCorrectType(g: GHolder<Pair<int, bool>>)
  opaque
  modifies g
{
  var p: Pair<int, bool> := new Pair<int, bool>;
  g#h := p;
  var q: Pair<int, bool> := g#h;
  assert 1 == 1
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
composite Pair<X, Y> { var a: X
 var b: Y }
composite Base<T> { var h: T }
composite GHolder<T> extends Base<T> { var k: int }

procedure inheritedFieldCorrectType(g: GHolder<Pair<int, bool>>)
  opaque
  modifies g
{
  var p: Pair<int, bool> := new Pair<int, bool>;
  g#h := p;
  assert 1 == 1
};
#end
