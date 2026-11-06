/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Loop invariant well-formedness

A loop invariant is assumed and re-asserted at the loop head, over the
loop-carried variables on an arbitrary iteration, so its well-formedness is
established at that state rather than in the loop's pre-state — where more is
known and the obligation can be vacuously discharged.

The `LoopInvariantWellFormedness` pass emits, before each loop with invariants,
`if * { havoc(loop targets); assume each invariant in order; assume false }`.
Lowering those assumed invariants produces the well-formedness obligations
(precondition asserts for calls, definedness asserts for partial operations) at
the loop-head state.

This happens in Laurel rather than Core: a Core loop invariant is a plain
expression and cannot carry the `assert callee$pre_i(args)` a call's check
requires.

These cases are **verifier-only**, so they live here rather than under
`Execution/` and run through `testLaurelVerification` (verification only). Each obligation is about the *symbolic*
loop-head state, where the loop-carried variables are havoc'd. The interpreter
walks one concrete path on which those variables hold specific values (`d == 1`
on the first iteration), so it never reaches the state that violates the
precondition and cannot reproduce these diagnostics. See the wording and
strictness notes on `testLaurelVerification` / `testLaurelExecution` in `StrataTest/Util/TestLaurel.lean`.

For the interpretable counterpart — an ordinary loop whose verification the
emitted block leaves undisturbed — see
`Execution/StmtExpr/Stmt/LoopInvariantWellFormedness.lean`.
-/

/-! ## A call in an invariant has its precondition checked at the loop head

`d` is havoc'd at the loop head, so `pureDiv`'s `y != 0` cannot be discharged
there and the verifier reports the precondition failure against the call.

Two diagnostics land on the invariant, at different spans. The narrower one
covers the call and is the well-formedness failure this pass exists to surface.
The wider one covers the whole invariant: with its call's precondition
unproven, `pureDiv(10, d)` is an uninterpreted application, so the invariant
itself cannot be proved at the loop head either. -/

#eval testLaurelVerification <|
#strata
program Laurel;

procedure pureDiv(x: int, y: int): int
  requires y != 0
{
  return x / y
};

procedure callInInvariantUnchecked() entry opaque {
  var d: int := 1;
  var i: int := 0;
  while (i < 10)
    invariant pureDiv(10, d) >= 0
//            ^^^^^^^^^^^^^^ error: precondition does not hold
//            ^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    d := d + 1;
    i := i + 1
  }
};
#end

/-! ## Well-formedness obligations chain across invariants

Each invariant is assumed after its own checks, so `d > 0` is available when
`pureDiv(10, d)`'s precondition is checked and the obligation is discharged. -/

#eval testLaurelVerification <|
#strata
program Laurel;

procedure pureDiv(x: int, y: int): int
  requires y != 0
{
  return x / y
};

procedure chainedInvariants() entry opaque {
  var d: int := 1;
  var i: int := 0;
  while (i < 10)
    invariant d > 0
    invariant pureDiv(10, d) >= 0
  {
    d := d + 1;
    i := i + 1
  }
};
#end

/-! ## The pre-state does not discharge a loop-head obligation

`d` is `1` before the loop and decreases toward `0` across iterations. The
obligation holds in the pre-state but not at the loop head, where `d` is havoc'd,
so checking it at the loop head is what surfaces the failure. As above, the
unproven precondition also leaves the invariant itself unprovable. -/

#eval testLaurelVerification <|
#strata
program Laurel;

procedure pureDiv(x: int, y: int): int
  requires y != 0
{
  return x / y
};

procedure preStateIsNotEnough() entry opaque {
  var d: int := 1;
  var i: int := 0;
  while (i < 10)
    invariant pureDiv(10, d) >= 0
//            ^^^^^^^^^^^^^^ error: precondition does not hold
//            ^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    d := d - 1;
    i := i + 1
  }
};
#end

/-! ## A quantifier in an invariant keeps its call's obligation

The contract pass injects `pureDiv`'s precondition assert inside the
quantifier's body, and the transparency pass must strip it from the invariant
— a proof block is a block expression with uninitialized declarations, which
nothing lowers in a spec position. The obligation is not lost: the
well-formedness block planted before the loop carries the same assert in
statement position, so unguarded it fails at the loop head, and guarded by a
preceding invariant it is discharged and the loop verifies. The quantifier's
goal is reflexive on purpose -- the invariant itself is trivially provable, so
the precondition obligation is the only thing each case can fail on. Before the
transparency pass learned to keep loop spec positions pure, both of these
programs were refused with "local variables must have initializers in
transparent bodies or contracts". -/

#eval testLaurelVerification <|
#strata
program Laurel;

procedure pureDiv(x: int, y: int): int
  requires y != 0
{
  return x / y
};

procedure quantifiedCallInInvariantUnchecked() entry opaque {
  var d: int := 1;
  var i: int := 0;
  while (i < 10)
    invariant forall(k: int) => 0 <= k ==> pureDiv(k, d) == pureDiv(k, d)
//                                         ^^^^^^^^^^^^^ error: precondition does not hold
//                                                          ^^^^^^^^^^^^^ error: precondition does not hold
  {
    d := d - 1;
    i := i + 1
  }
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;

procedure pureDiv(x: int, y: int): int
  requires y != 0
{
  return x / y
};

procedure quantifiedCallInInvariantChecked() entry opaque {
  var d: int := 1;
  var i: int := 0;
  while (i < 10)
    invariant d > 0
    invariant forall(k: int) => 0 <= k ==> pureDiv(k, d) == pureDiv(k, d)
  {
    d := d + 1;
    i := i + 1
  }
};
#end
