/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel
import StrataDDM.Integration.Lean.HashCommands

open StrataTest.Util
open Strata

/-!
# Immutable sets

`Set` is a built-in: `CoreDefinitionsForLaurel` declares `opaque Set<T>` plus its
operations, and each operation lowers to the matching `Set.*` function in
`Core.Factory`. Nothing here declares anything — these programs use the prelude.

`Set` is its own Core sort, not a `Map T bool` alias, so the SMT encoder can later be
pointed at a dedicated set theory. Today it encodes as an uninterpreted sort constrained
by the pointwise `Set.*` axioms.

Sets are immutable with value semantics: `setInsert`/`setRemove` return a new set and
never modify their argument, so no heap reasoning is involved.
-/

/-! ## Membership after insert and remove -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure insertThenContains(s: Set<int>, a: int)
  opaque
{
  assert setContains(setInsert(s, a), a)
};

procedure removeThenNotContains(s: Set<int>, a: int)
  opaque
{
  assert !setContains(setRemove(s, a), a)
};

// A different element is unaffected — the "preserve" half, and what makes this a set
// rather than a black box.
procedure otherElementUnaffected(s: Set<int>, a: int, b: int)
  requires a != b
  opaque
{
  assert setContains(setInsert(s, a), b) == setContains(s, b);
  assert setContains(setRemove(s, a), b) == setContains(s, b)
};

// Immutability: the operand is not modified.
procedure operandUnchanged(s: Set<int>, a: int, b: int)
  opaque
{
  var before: bool := setContains(s, b);
  var t: Set<int> := setInsert(s, a);
  assert setContains(s, b) == before
};

// The empty set has no members. Its element type comes from the declared type of the
// binding, since no argument determines it.
procedure emptyHasNoMembers(a: int)
  opaque
{
  var e: Set<int> := setEmpty();
  assert !setContains(e, a)
};
#end

/-! ## Algebraic laws, from the pointwise axioms -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure unionIsMembership(s: Set<int>, t: Set<int>, a: int)
  opaque
{
  assert setContains(setUnion(s, t), a) == (setContains(s, a) || setContains(t, a))
};

procedure intersectIsMembership(s: Set<int>, t: Set<int>, a: int)
  opaque
{
  assert setContains(setIntersect(s, t), a) == (setContains(s, a) && setContains(t, a))
};

procedure differenceIsMembership(s: Set<int>, t: Set<int>, a: int)
  opaque
{
  assert setContains(setDifference(s, t), a) == (setContains(s, a) && !setContains(t, a))
};

// Derived: an inserted element is in the union with anything.
procedure insertThenUnion(s: Set<int>, t: Set<int>, a: int)
  opaque
{
  assert setContains(setUnion(setInsert(s, a), t), a)
};

// Derived: difference removes exactly what the second set holds.
procedure differenceOfInsert(s: Set<int>, a: int)
  opaque
{
  var only: Set<int> := setInsert(setEmpty(), a);
  assert !setContains(setDifference(s, only), a)
};
#end

/-! ## Nested construction

Each axiom is triggered on `Set.contains` *of the operation*, so a nested construction needs
the trigger to fire once per layer: asking about `a` in `setInsert(setInsert(s, a), b)` fires
the outer insert's axiom, which reduces to a question about `a` in the inner set, which must
fire the inner insert's axiom in turn. A trigger that does not chain leaves the inner
membership unprovable, which no single-layer test would catch. -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure nestedInsertMembership(s: Set<int>, a: int, b: int)
  requires a != b
  opaque
{
  var t: Set<int> := setInsert(setInsert(s, a), b);
  assert setContains(t, a);
  assert setContains(t, b)
};

// Insert then remove a DIFFERENT element: the inserted one survives, so the chain carries the
// `!=` through the remove axiom as well as the insert one.
procedure insertThenRemoveOther(s: Set<int>, a: int, b: int)
  requires a != b
  opaque
{
  var t: Set<int> := setRemove(setInsert(s, a), b);
  assert setContains(t, a);
  assert !setContains(t, b)
};

// Three layers over the empty set, so membership is decided outright rather than relative to
// an unknown starting set.
procedure builtFromEmpty(a: int, b: int, c: int)
  requires a != b
  requires b != c
  requires a != c
  opaque
{
  var t: Set<int> := setInsert(setInsert(setInsert(setEmpty(), a), b), c);
  assert setContains(t, a);
  assert setContains(t, b);
  assert setContains(t, c)
};
#end

/-! Must-fail twin: an element never inserted is absent from the nested construction, so the
    chaining above is not simply making every membership question provable.

    Note the verdict is "could not be proved", not "does not hold": the solver declines to
    prove membership rather than producing a counterexample. Refuting it would mean chaining
    the empty-set axiom together with both insert axioms in the right order, which the
    triggers do not drive. Positive membership chains (above); negative membership through a
    nested construction does not. -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure nestedDoesNotAddOthers(a: int, b: int, c: int)
  requires a != b
  requires b != c
  requires a != c
  opaque
{
  var t: Set<int> := setInsert(setInsert(setEmpty(), a), b);
  assert setContains(t, c)
//^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! ## Sets are generic

The element type is a real Core sort argument, so `Set<bool>` is a different sort from
`Set<int>` and the operations instantiate per call site. -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure genericElementTypes(sb: Set<bool>, si: Set<int>, b: bool, i: int)
  opaque
{
  assert setContains(setInsert(sb, b), b);
  assert setContains(setInsert(si, i), i)
};
#end

/-! ## Must-fail twins

Each pins that the axioms say only what they should. Without these the block above could
be passing because `setContains` is over-constrained. -/
#eval testLaurelVerification <|
#strata
program Laurel;
// Inserting `a` says nothing about a different element `b`.
procedure insertDoesNotAddOthers(s: Set<int>, a: int, b: int)
  requires a != b
  opaque
{
  assert setContains(setInsert(s, a), b)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};

// Union is not intersection: membership in the union does not imply membership in
// both operands.
procedure unionIsNotIntersect(s: Set<int>, t: Set<int>, a: int)
  requires setContains(setUnion(s, t), a)
  opaque
{
  assert setContains(s, a)
//^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end
