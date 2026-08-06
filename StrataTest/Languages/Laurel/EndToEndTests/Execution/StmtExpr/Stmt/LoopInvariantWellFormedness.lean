/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Loop invariant well-formedness: an ordinary loop is undisturbed

The `LoopInvariantWellFormedness` pass emits, before each loop with invariants,
`if * { havoc(loop targets); assume each invariant in order; assume false }`.

Two properties keep that block from affecting a loop whose invariants are already
well-formed. The invariants are only *assumed* in the block, never asserted — the
havoc'd state is arbitrary, so asserting one there would be unprovable. And
`assume false` severs the branch, so the havoc does not reach the pre-state and
the block does not make later obligations vacuous.

The loop below therefore verifies, and its post-loop assertion — which depends on
the loop-carried `i` — still holds. Because both properties hold, the verifier and
the interpreter agree, so this case runs through both via `testLaurelMultiple`.

The cases where the pass changes the outcome are verifier-only (their obligations
concern the havoc'd loop-head state, which the interpreter's single concrete path
never reaches) and live in
`Verification/Fundamentals/LoopInvariantWellFormedness.lean`.
-/

#eval testLaurelMultiple
#strata
program Laurel;
procedure ordinaryLoopUnaffected() entry opaque {
  var i: int := 3;
  while (i > 0)
    invariant i >= 0
  {
    i := i - 1
  };
  assert i == 0
};
#end
