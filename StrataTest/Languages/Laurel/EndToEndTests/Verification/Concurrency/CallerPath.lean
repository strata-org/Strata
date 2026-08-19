/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Caller-side coroutine reasoning under `verifyCoroutine := true`. When a
procedure spawns a coroutine and calls `resume`, the generated opaque
resume carries relies→requires and guarantees→ensures as two-state
postconditions about the coroutine's original parameters. The caller
observes these directly — no composite-field indirection.

  * **Positive (one-state guarantee):** caller asserts the guarantee after resume.
  * **Positive (two-state guarantee):** `old(s#x) <= s#x` combined with
    the entry fact `s#x == 0` gives `s#x >= 0`.
  * **Positive (rely preservation):** the rely establishes `s#x` unchanged
    across the resume entry, so the caller retains prior knowledge.
  * **Negative (no rely):** without a rely preserving `s#x`, the
    guarantee `old(s#x) <= s#x` does not imply `s#x == 0`.
-/

import StrataTest.Languages.Laurel.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util.Concurrency

/-! ## Positive: one-state guarantee observed by caller. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine worker(s: Cell)
  relies old(s#x) == s#x
  guarantees s#x >= 0
  modifies *
{
  s#x := 1;
  yield
};

procedure caller(s: Cell)
  requires s#x == 0
  opaque
  modifies *
{
  var co: worker := worker(s);
  resume(co);
  assert s#x >= 0
};
#end

/-! ## Positive: two-state guarantee gives monotonicity. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine inc(s: Cell)
  relies old(s#x) == s#x
  guarantees old(s#x) <= s#x
  modifies *
{
  s#x := s#x + 1;
  yield
};

procedure callerMonotonic(s: Cell)
  requires s#x == 0
  opaque
  modifies *
{
  var co: inc := inc(s);
  resume(co);
  assert s#x >= 0
};
#end

/-! ## Positive: rely preserves value across resume. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine preserving(s: Cell)
  relies old(s#x) == s#x
  guarantees old(s#x) == s#x
  modifies *
{
  yield
};

procedure callerPreserved(s: Cell)
  requires s#x == 42
  opaque
  modifies *
{
  var co: preserving := preserving(s);
  resume(co);
  assert s#x == 42
};
#end

/-! ## Negative: without a rely, the guarantee is insufficient. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine noop(s: Cell)
  guarantees old(s#x) <= s#x
  modifies *
{
  s#x := s#x + 1;
  yield
};

procedure callerBad(s: Cell)
  requires s#x == 0
  opaque
  modifies *
{
  var co: noop := noop(s);
  resume(co);
  assert s#x == 0
//^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! ## Negative: reassigning a spawned coroutine variable is rejected.

The caller-path resume threads one spawn's arguments per variable name, so a
variable that is spawned twice (here, reassigned to a fresh instance) cannot be
threaded soundly. The pass rejects the second spawn rather than silently
instantiating the resume's rely/guarantee with stale arguments. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine worker2(s: Cell)
  guarantees s#x >= 0
  modifies *
{
  s#x := 1;
  yield
};

procedure callerReassign(s: Cell, t: Cell)
  requires s#x == 0
  requires t#x == 0
  opaque
  modifies *
{
  var co: worker2 := worker2(s);
  resume(co);
  co := worker2(t)
//^^^^^^^^^^^^^^^^ error: spawned more than once
};
#end

/-! ## Positive: resuming the same instance in both arms of a conditional.

The caller's rely-old heap snapshot (`$h1_co`, tracking H1) is declared at the
spawn site, which dominates every resume of `co` — so resuming on disjoint
control-flow paths (here, both arms of a conditional) is threaded soundly. Each
arm's resume observes the guarantee `old(s#x) <= s#x` against the rely
`old(s#x) == s#x`, giving `s#x >= 0` on both paths. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine incBranch(s: Cell)
  relies old(s#x) == s#x
  guarantees old(s#x) <= s#x
  modifies *
{
  s#x := s#x + 1;
  yield
};

procedure callerBranch(s: Cell, c: bool)
  requires s#x == 0
  opaque
  modifies *
{
  var co: incBranch := incBranch(s);
  if c then { resume(co) } else { resume(co) };
  assert s#x >= 0
};
#end

/-! ## Negative: resuming a coroutine held in a composite field.

The caller tracks a per-instance rely-old heap snapshot keyed on the coroutine
variable, which requires the resumed instance to be a plain local. A field
receiver (`resume(h#co)`) has no such local, so threading cannot proceed and the
pass reports it rather than emitting an ill-formed resume call. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine fieldCo(s: Cell)
  relies old(s#x) == s#x
  guarantees old(s#x) <= s#x
  modifies *
{
  s#x := s#x + 1;
  yield
};

composite Holder { var co: fieldCo }

procedure callerField(h: Holder, s: Cell)
  requires s#x == 0
  opaque
  modifies *
{
  h#co := fieldCo(s);
  resume(h#co)
//^^^^^^^^^^^^ error: receiver is not a simple variable
};
#end

/-! ## Spawn arguments are captured at the spawn, not re-read at the resume.

A coroutine captures its inputs once, when it is spawned, so the caller's
instantiation of the guarantee must use the spawn-time values. Mutating the
argument variable afterwards must not move the summary with it: here `v` is 99 at
the spawn and 3 at the resume, and the provable fact is `g#x == 99`. Before the
spawn arguments were snapshotted, the caller proved `g#x == 3` — a value the
coroutine never saw — and could not prove `g#x == 99`. -/

#eval testCoroutine <|
#strata
program Laurel;

composite G { var x: int }

coroutine setter(g: G, v: int)
  relies old(g#x) == g#x
  guarantees g#x == v
  modifies *
{
  g#x := v;
  yield
};

procedure callerSpawnCapture(g: G)
  opaque
  modifies *
{
  var v: int := 99;
  var co: setter := setter(g, v);
  v := 3;
  resume(co);
  assert g#x == 99
};
#end

/-! ## Negative: the same program asserting the resume-time value. `v` is 3 when
`resume` runs, but the coroutine captured 99, so `g#x == 3` is not provable — and
must not be. -/

#eval testCoroutine <|
#strata
program Laurel;

composite G { var x: int }

coroutine setter2(g: G, v: int)
  relies old(g#x) == g#x
  guarantees g#x == v
  modifies *
{
  g#x := v;
  yield
};

procedure callerSpawnCaptureNeg(g: G)
  opaque
  modifies *
{
  var v: int := 99;
  var co: setter2 := setter2(g, v);
  v := 3;
  resume(co);
  assert g#x == 3
//^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! ## A heap read as a spawn argument is captured by value too: `s#k` is 99 at
the spawn and 3 at the resume. -/

#eval testCoroutine <|
#strata
program Laurel;

composite G { var x: int }
composite K { var k: int }

coroutine setter3(g: G, v: int)
  relies old(g#x) == g#x
  guarantees g#x == v
  modifies *
{
  g#x := v;
  yield
};

procedure callerSpawnCaptureHeap(g: G, s: K)
  opaque
  modifies *
{
  s#k := 99;
  var co: setter3 := setter3(g, s#k);
  s#k := 3;
  resume(co);
  assert g#x == 99
};
#end
