/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Block invariants and backward `goto`s meeting `yield`, on the **full
elaboration** path (the test defaults, *not* `coroutineOptions`): the coroutine
body is linearized into dispatch states, and a yield-containing block is split
across states — dissolving the block, so its label and invariants cannot be
carried. `CoroutineElaboration` must reject such a block rather than drop its
clauses: dropped, an `invariant false` would silently pass, and a `goto` back
to the dissolved label would dangle.

Three cases:

  * **(1) Invariant on a yield-containing block — rejected.** The block is
    split across `$pc` states, so there is no block entry or back edge left to
    check the invariant at.

  * **(2) Same block without the yield — invariant still checked.** A
    yield-free block is kept whole as one straight-line state, so its
    `invariant false` survives into `RestructureGotos`' entry assert and fails
    as it should.

  * **(3) `goto` back into a yield-containing block — rejected.** The label
    dissolves with the block, so the backward jump has no sound lowering.

  * **(4) forward `exit` out of a yield-containing block — rejected.** Same
    dissolution: the label is gone, so the forward jump would dangle (it used
    to surface as an internal "label is not in scope" error).

  * **(5) `exit` crossing a dissolved region to an outer label — rejected.**
    The outer block contains the yield too, so it dissolves as well; the
    scan of the outer block catches the jump.

  * **(6) `exit` within a yield-free block of a coroutine — still works.**
    The yield-free block is kept whole as one state, label intact, so the
    jump needs no rejection.
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util

/-! ## (1) Invariant on a yield-containing block — rejected. -/

#eval testLaurelVerification <|
#strata
program Laurel;

coroutine invariantOverYield(n: int)
  modifies *
{
  var i: int := 0;
  var x: int := 0;
  { x := i; yield; i := i + 1 } blk invariant false
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: an invariant on a block containing 'yield' is not supported in a coroutine
};
#end

/-! ## (2) The same block without the yield still fails its invariant.

The point of this case is the "assertion does not hold": the yield-free block
is kept whole, so `RestructureGotos` still turns its `invariant false` into a
failing entry assert. The `modifies` diagnostic is a pre-existing artifact of
the full-elaboration path — the generated `resume` fails its own frame check
for *any* coroutine on this path (which is why every other verification test
uses `coroutineOptions`); it is pinned only because annotations must be
exact. -/

#eval testLaurelVerification <|
#strata
program Laurel;

coroutine invariantBesideYield(n: int)
//        ^^^^^^^^^^^^^^^^^^^^ error: modifies clause does not hold
  modifies *
{
  var i: int := 0;
  var x: int := 0;
  { x := i; i := i + 1 } blk invariant false;
//                                     ^^^^^ error: assertion does not hold
  yield
};
#end

/-! ## (3) A backward `goto` into a yield-containing block — rejected. -/

#eval testLaurelVerification <|
#strata
program Laurel;

coroutine gotoOverYield(n: int)
  modifies *
{
  var i: int := 0;
  { yield; i := i + 1; goto blk } blk
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: a 'goto' back to the start of a block containing 'yield' is not supported in a coroutine
};
#end

/-! ## (4) A forward `exit` out of a yield-containing block — rejected. -/

#eval testLaurelVerification <|
#strata
program Laurel;

coroutine exitOverYield(n: int)
  modifies *
{
  var i: int := 0;
  var x: int := 0;
  { x := i; yield; if x == 0 then { exit blk }; i := i + 1 } blk
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: an 'exit' out of a block containing 'yield' is not supported in a coroutine
};
#end

/-! ## (5) An `exit` crossing the dissolved region to an outer label — rejected.

The jump sits inside an unlabelled yield-containing block, but its target is
the outer labelled block; the outer block contains the yield too, so it also
dissolves, and the scan of the outer block reports the jump. -/

#eval testLaurelVerification <|
#strata
program Laurel;

coroutine exitOuterOverYield(n: int)
  modifies *
{
  var i: int := 0;
  {
//^^^^^^^ error: an 'exit' out of a block containing 'yield' is not supported in a coroutine
    { yield; if i == 0 then { exit outer }; i := i + 1 };
    i := 2
  } outer
};
#end

/-! ## (6) An `exit` within a yield-free block of a coroutine — still works.

The yield-free labelled block is kept whole as one straight-line state, label
intact, so the forward jump inside it needs no rejection. The `modifies`
diagnostic is the same pre-existing full-elaboration-path artifact as in (2). -/

#eval testLaurelVerification <|
#strata
program Laurel;

coroutine exitBesideYield(n: int)
//        ^^^^^^^^^^^^^^^ error: modifies clause does not hold
  modifies *
{
  var i: int := 0;
  { if i == 0 then { exit blk }; i := 1 } blk;
  yield
};
#end
