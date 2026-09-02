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
# Sequences

`Sequence` is a built-in: `CoreDefinitionsForLaurel` declares `opaque Sequence<T>` plus
its operations, and each operation lowers to the matching `Sequence.*` function in
`Core.Factory`. Nothing here declares anything — these programs use the prelude.

What holds is what those Core axioms state, and they are written in terms of
`Sequence.length` and `Sequence.select`. So the facts available are pointwise: how long a
result is, and what sits at a given index. Equalities between two separately-constructed
sequences are not available — nothing relates them beyond their lengths and elements — which
is why this file asserts none.

Sequences are immutable with value semantics: `seqBuild`/`seqUpdate`/`seqAppend` return a
new sequence and never modify their argument, so no heap reasoning is involved.

`seqSelect`, `seqUpdate`, `seqTake` and `seqDrop` are *partial*: their Core counterparts
carry bounds preconditions, so each call site gets a bounds proof obligation. That is why
the procedures below state the bounds they rely on in `requires` clauses.
-/

/-! ## Length -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure lengthIsNonNegative(s: Sequence<int>)
  opaque
{
  assert seqLength(s) >= 0
};

// The empty sequence has length zero. Its element type comes from the declared type of
// the binding, since no argument determines it.
procedure emptyHasLengthZero()
  opaque
{
  var e: Sequence<int> := seqEmpty();
  assert seqLength(e) == 0
};

procedure buildIncrementsLength(s: Sequence<int>, v: int)
  opaque
{
  assert seqLength(seqBuild(s, v)) == seqLength(s) + 1
};

procedure appendAddsLengths(s: Sequence<int>, t: Sequence<int>)
  opaque
{
  assert seqLength(seqAppend(s, t)) == seqLength(s) + seqLength(t)
};

procedure updatePreservesLength(s: Sequence<int>, i: int, v: int)
  requires 0 <= i
  requires i < seqLength(s)
  opaque
{
  assert seqLength(seqUpdate(s, i, v)) == seqLength(s)
};

// A chain needs the length fact once per layer.
procedure nestedUpdatePreservesLength(s: Sequence<int>, i: int, j: int, v: int, w: int)
  requires 0 <= i
  requires i < seqLength(s)
  requires 0 <= j
  requires j < seqLength(s)
  opaque
{
  assert seqLength(seqUpdate(seqUpdate(s, i, v), j, w)) == seqLength(s);
  assert seqLength(seqUpdate(seqUpdate(seqUpdate(s, i, v), j, w), i, w)) == seqLength(s)
};

// The length is reached through a binding, not written on the update term.
procedure updateLengthThroughBinding(s: Sequence<int>, i: int, v: int)
  requires 0 <= i
  requires i < seqLength(s)
  opaque
{
  var t: Sequence<int> := seqUpdate(s, i, v);
  var n: int := seqLength(t);
  assert n == seqLength(s)
};
#end

/-! ## Indexing

`seqSelect` is bounds-checked, so every one of these needs its index in range. -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure updateAtIndex(s: Sequence<int>, i: int, v: int)
  requires 0 <= i
  requires i < seqLength(s)
  opaque
{
  assert seqSelect(seqUpdate(s, i, v), i) == v
};

procedure updateLeavesOthers(s: Sequence<int>, i: int, n: int, v: int)
  requires 0 <= i
  requires i < seqLength(s)
  requires 0 <= n
  requires n < seqLength(s)
  requires n != i
  opaque
{
  assert seqSelect(seqUpdate(s, i, v), n) == seqSelect(s, n)
};

// The element just appended sits at the old end.
procedure buildThenSelect(s: Sequence<int>, v: int)
  opaque
{
  assert seqSelect(seqBuild(s, v), seqLength(s)) == v
};

// Building does not disturb the existing elements.
procedure buildPreservesEarlier(s: Sequence<int>, v: int, i: int)
  requires 0 <= i
  requires i < seqLength(s)
  opaque
{
  assert seqSelect(seqBuild(s, v), i) == seqSelect(s, i)
};

// Concatenation indexes into the left operand below its length and the right one above.
procedure appendSelectsLeft(s: Sequence<int>, t: Sequence<int>, i: int)
  requires 0 <= i
  requires i < seqLength(s)
  opaque
{
  assert seqSelect(seqAppend(s, t), i) == seqSelect(s, i)
};

procedure appendSelectsRight(s: Sequence<int>, t: Sequence<int>, i: int)
  requires 0 <= i
  requires i < seqLength(t)
  opaque
{
  assert seqSelect(seqAppend(s, t), seqLength(s) + i) == seqSelect(t, i)
};
#end

/-! ## Immutability

The operand of a sequence operation is never modified — the result is a new value. -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure operandUnchanged(s: Sequence<int>, i: int, v: int)
  requires 0 <= i
  requires i < seqLength(s)
  opaque
{
  var before: int := seqSelect(s, i);
  var lenBefore: int := seqLength(s);
  var t: Sequence<int> := seqBuild(s, v);
  assert seqSelect(s, i) == before;
  assert seqLength(s) == lenBefore
};
#end

/-! ## Slicing

`seqTake(s, n)` keeps the first `n` elements and `seqDrop(s, n)` discards them. Both are
partial, requiring `0 <= n <= seqLength(s)` — note the non-strict upper bound, unlike
`seqSelect`. -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure takeLength(s: Sequence<int>, n: int)
  requires 0 <= n
  requires n <= seqLength(s)
  opaque
{
  assert seqLength(seqTake(s, n)) == n
};

procedure dropLength(s: Sequence<int>, n: int)
  requires 0 <= n
  requires n <= seqLength(s)
  opaque
{
  assert seqLength(seqDrop(s, n)) == seqLength(s) - n
};

procedure takeSelects(s: Sequence<int>, n: int, j: int)
  requires 0 <= n
  requires n <= seqLength(s)
  requires 0 <= j
  requires j < n
  opaque
{
  assert seqSelect(seqTake(s, n), j) == seqSelect(s, j)
};

procedure dropSelects(s: Sequence<int>, n: int, j: int)
  requires 0 <= n
  requires n <= seqLength(s)
  requires 0 <= j
  requires j < seqLength(s) - n
  opaque
{
  assert seqSelect(seqDrop(s, n), j) == seqSelect(s, j + n)
};
#end

/-! ## Membership

`seqContains(s, v)` holds when some index of `s` carries `v` — that existential over
`Sequence.select` is exactly what its axiom says. -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure buildThenContains(s: Sequence<int>, v: int)
  opaque
{
  assert seqContains(seqBuild(s, v), v)
};

procedure emptyContainsNothing(v: int)
  opaque
{
  var e: Sequence<int> := seqEmpty();
  assert !seqContains(e, v)
};

#end

/-! ## Distinctness

`seqLength` is a function of the sequence, so a length change forces a different value. This
is the one equality-shaped fact the axioms give. -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure buildChangesSequence(s: Sequence<int>, v: int)
  opaque
{
  assert seqBuild(s, v) != s
};
#end

/-! ## Sequences are generic

The element type is a real Core sort argument, so `Sequence<bool>` is a different sort
from `Sequence<int>`, and nesting works: `Sequence<Sequence<int>>` is a sequence whose
elements are themselves sequences. -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure genericElementTypes(sb: Sequence<bool>, si: Sequence<int>, b: bool, i: int)
  opaque
{
  assert seqContains(seqBuild(sb, b), b);
  assert seqContains(seqBuild(si, i), i)
};

procedure nestedSequence(ss: Sequence<Sequence<int>>, inner: Sequence<int>, a: int)
  opaque
{
  var withA: Sequence<int> := seqBuild(inner, a);
  assert seqContains(seqBuild(ss, withA), withA);
  assert seqLength(seqBuild(ss, withA)) == seqLength(ss) + 1
};
#end

/-! ## Where `seqEmpty()`'s element type comes from

`seqEmpty()` takes no argument, so its element type comes from context. With nothing to fix
it the type variable reaches the SMT encoder unresolved and is reported as a `strata-bug`,
blaming the compiler for a genuinely ambiguous program. The map side catches the same shape
earlier with an actionable message; `seqLength` has no such guard, so this pins today's
behaviour and will fail if it improves. -/
#eval testLaurelVerification <|
#strata
program Laurel;
// `seqLength` returns `int` and mentions `T` nowhere, so nothing here determines it.
procedure emptyElemTypeUndetermined()
  opaque
{
  assert seqLength(seqEmpty()) == 0
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ strata-bug: should be fully monomorphic
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
// Determined by the value argument rather than by an annotation, so no `strata-bug`.
procedure emptyElemTypeFromValueArgument()
  opaque
{
  assert seqLength(seqBuild(seqEmpty(), 1)) == 1
};
#end

/-! ## Bounds obligations

All four partial operations state their bounds as a Laurel `requires`, so an unguarded
argument is reported as a `precondition`. -/
#eval testLaurelVerification <|
#strata
program Laurel;
// Strict upper bound: `seqSelect` needs `0 <= i < seqLength(s)`.
procedure selectWithoutBounds(s: Sequence<int>, i: int)
  opaque
{
  var x: int := seqSelect(s, i)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
};

// Non-strict upper bound: `seqTake` needs `0 <= n <= seqLength(s)`.
procedure takeWithoutBounds(s: Sequence<int>, n: int)
  opaque
{
  var t: Sequence<int> := seqTake(s, n)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
};

// A partially guarded index is still reported: the lower bound alone is not enough.
procedure selectWithLowerBoundOnly(s: Sequence<int>, i: int)
  requires 0 <= i
  opaque
{
  var x: int := seqSelect(s, i)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
};

procedure updateWithoutBounds(s: Sequence<int>, i: int, v: int)
  opaque
{
  var t: Sequence<int> := seqUpdate(s, i, v)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
};

procedure dropWithoutBounds(s: Sequence<int>, n: int)
  opaque
{
  var t: Sequence<int> := seqDrop(s, n)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
};
#end

/-! The guarded twins: with the bound stated, the obligation is discharged. Without these
    the block above would only show that *something* is being reported, not that the
    obligation is the bound and that meeting it suffices. -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure selectWithBounds(s: Sequence<int>, i: int)
  requires 0 <= i
  requires i < seqLength(s)
  opaque
{
  var x: int := seqSelect(s, i)
};

procedure takeWithBounds(s: Sequence<int>, n: int)
  requires 0 <= n
  requires n <= seqLength(s)
  opaque
{
  var t: Sequence<int> := seqTake(s, n)
};

procedure updateWithBounds(s: Sequence<int>, i: int, v: int)
  requires 0 <= i
  requires i < seqLength(s)
  opaque
{
  var t: Sequence<int> := seqUpdate(s, i, v)
};

procedure dropWithBounds(s: Sequence<int>, n: int)
  requires 0 <= n
  requires n <= seqLength(s)
  opaque
{
  var t: Sequence<int> := seqDrop(s, n)
};
#end

/-! ## Must-fail twins

Each pins that the encoding says only what it should. Without these the blocks above could
be passing because the operations are over-constrained. -/
#eval testLaurelVerification <|
#strata
program Laurel;
// Appending `v` says nothing about a different value `w`.
procedure buildDoesNotAddOthers(s: Sequence<int>, v: int, w: int)
  requires v != w
  opaque
{
  assert seqContains(seqBuild(s, v), w)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};

// Membership in a concatenation does not locate the element in the left operand.
procedure containsDoesNotLocalize(s: Sequence<int>, t: Sequence<int>, v: int)
  requires seqContains(seqAppend(s, t), v)
  opaque
{
  assert seqContains(s, v)
//^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};

// Writing index `i` says nothing about a different index `n`.
procedure updateDoesNotSetOthers(s: Sequence<int>, i: int, n: int, v: int)
  requires 0 <= i
  requires i < seqLength(s)
  requires 0 <= n
  requires n < seqLength(s)
  requires n != i
  opaque
{
  assert seqSelect(seqUpdate(s, i, v), n) == v
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end
