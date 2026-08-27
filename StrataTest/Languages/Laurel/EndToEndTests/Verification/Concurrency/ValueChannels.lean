/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Value channels (`yields` / `resumes`) on the verification (YieldElim) path,
under `verifyCoroutine := true`.

Concrete execution of coroutines — pinning actual yielded values through the
interpreter — is deferred until the interpreter supports `$heap`, so the verifier
is currently the only path (SMT cannot unroll the state machine to prove
`a == 1, 2, 3`). Here we check the same surface features —
`yields`, multi-`yield`, `resumes`, a body local, and a `while` loop — against
rely/guarantee contracts the verifier *can* discharge:

  * A `yields (x)` binding is the coroutine's own output. The body writes it
    before every `yield`, the caller only reads it, so it persists across a step
    untouched: the guarantee is checked at each `yield` and at the post-last-yield
    exit (`addExitGuarantees`).
  * A `resumes (y)` binding is a fresh caller-supplied value at every resume, so
    YieldElim havocs it to an arbitrary value at every step. A `rely` is a
    *reflexive* two-state heap relation and does not constrain the resumed value,
    so a guarantee has to hold for *any* resumed value (see the negative case).

YieldElim lowers each `yield` to an inline `assert G; …; havocHeap(); …; assume R`
step; the `havocHeap()` environment step means a terminating coroutine body must
be `modifies *`, exactly as the `ExitGuarantee` examples are.
-/

import StrataTest.Languages.Laurel.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util.Concurrency

/-! ## `yields`: the yielded value is checked at every `yield` and at the exit
tail. Each step writes `x` before suspending; the scalar binding persists, so
`guarantees x >= 1` holds at all three yields and at the final `resume → halt`
segment. -/

#eval testCoroutine <|
#strata
program Laurel;
coroutine counter() yields (x: int)
  guarantees x >= 1
  modifies *
{
  x := 1; yield;
  x := 2; yield;
  x := 3; yield
};
#end

/-! ## A `while` loop in the body with a `yields` binding. The invariant carries
the yielded value's property across the loop's back-edge, so it holds at the
in-loop `yield` and after the loop exits. -/

#eval testCoroutine <|
#strata
program Laurel;
coroutine ticker() yields (x: int)
  guarantees x >= 0
  modifies *
{
  x := 0;
  var i: int := 0;
  while (i < 3)
    invariant i >= 0
    invariant x >= 0
  {
    x := i;
    yield;
    i := i + 1
  }
};
#end

/-! ## `resumes`: the body reads the resumed value `y` (fresh and arbitrary at
every step) but yields `max(y, 0)`, so `guarantees x >= 0` holds for *any*
resumed value — at each yield and at the exit tail. -/

#eval testCoroutine <|
#strata
program Laurel;
coroutine clamp() yields (x: int) resumes (y: int)
  guarantees x >= 0
  modifies *
{
  if y >= 0 then { x := y } else { x := 0 };
  yield;
  if y >= 0 then { x := y } else { x := 0 };
  yield
};
#end

/-! ## A `resumes` binding together with a real `relies`. The rely is a two-state
heap relation — the environment does not move `c#v` — and says nothing about the
resumed value, which is re-havoced at every step. The guarantee `x >= c#v` needs
both halves: `x` is computed from the pre-suspension `c#v` and clamped against a
negative `y`, and it survives the environment step only because the rely is
assumed *after* the heap havoc (and against the fresh `y`, not the previous
step's). -/

#eval testCoroutine <|
#strata
program Laurel;
composite Cell { var v: int }

coroutine feeder(c: Cell) yields (x: int) resumes (y: int)
  relies old(c#v) == c#v
  guarantees x >= c#v
  modifies *
{
  if y >= 0 then { x := c#v + y } else { x := c#v };
  yield;
  if y >= 0 then { x := c#v + y } else { x := c#v };
  yield
};
#end

/-! ## Negative: the resumed value is arbitrary. Yielding it directly cannot
prove `x >= 0` — the guarantee is rejected at the `yield` (the resumed value may
be negative) and at the exit tail. This is the soundness dual of `clamp`: a
`rely` is a reflexive heap relation and never constrains the resumed value, so
the body must be correct for every `y`. -/

#eval testCoroutine <|
#strata
program Laurel;
coroutine echoNonneg() yields (x: int) resumes (y: int)
  guarantees x >= 0
//           ^^^^^^ error: coroutine exit: guarantee does not hold
  modifies *
{
  x := y; yield
//        ^^^^^ error: coroutine yield: guarantee does not hold
};
#end
