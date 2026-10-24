/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Concrete execution of coroutines: spawning an instance, `resume`, the value
channels in both directions, `has_next`, and the completion value.

**Why the interpreters are the only paths here.** `testLaurelExecution` holds every
path it runs to the *same* inline `// ^^^` annotations, and these blocks assert
the actual schedule — `resume` number two yields 2, not 1 — which the verifier
cannot produce: it summarizes a `resume` by the coroutine's rely/guarantee
contract, so a per-step value is not provable (see
`Tests/EndToEndTests/Verification/Concurrency/ValueChannels.lean`).

Annotating those as expected verifier diagnostics is not an option either: an
annotation must fire on *every* enabled path, and the interpreters pass these
asserts. So the blocks below are interpreter-only, and each one's asserts are
chosen to fail if the schedule is wrong — a body that ran straight through on the
first `resume`, or one that restarted from the top on the second, reports a
different value rather than passing quietly. A block the Core interpreter cannot
run says why.

The rely/guarantee *verification* of the same constructs lives under
`Tests/EndToEndTests/Verification/Concurrency/`; this file is about what actually
runs.
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-- The paths `testLaurelExecution` can run here: the two interpreters (see the file
    comment). -/
private def interpreters : MultiplePathTestOptions := { skipVerification := true }

/-- `interpreters` reduced to the standalone Laurel interpreter. -/
private def laurelOnly : MultiplePathTestOptions :=
  { interpreters with skipCoreInterpreter := true }

/-! ## A straight-line coroutine, resumed to completion

Three `yield`s, so four resumes: each of the first three hands back the value the
body wrote to the `yields` binding just before suspending, and the fourth runs the
tail of the body and finishes it. A body that ignored its suspension point and
restarted would answer `1` every time. -/

-- No Core interpreter: the state machine a coroutine lowers to ends at its last `yield`, so it
-- finishes one `resume` early.
#eval testLaurelExecution laurelOnly <|
#strata
program Laurel;
coroutine counter() yields (x: int)
  modifies *
{
  x := 1; yield;
  x := 2; yield;
  x := 3; yield
};

procedure driveStraightLine()
  entry
  opaque
  modifies *
{
  var co: counter := counter();
  var a: int := resume(co);
  assert a == 1;
  var b: int := resume(co);
  assert b == 2;
  var c: int := resume(co);
  assert c == 3;
  assert has_next(co);
  resume(co);
  assert !has_next(co)
};
#end

/-! ## A `yield` inside a `while`

The loop variable is an ordinary local, saved with the frame and restored on the
next resume, and the resumed iteration re-enters the body *without* re-testing
the condition — it was already inside it. Both halves are observable here: `i`
resetting to 0 would repeat `0`, and re-running the statements before the `yield`
would repeat the previous value. The spawn argument bounds the loop, so the last
resume also drives the loop to its exit and completes the body. -/

#eval testLaurelExecution interpreters <|
#strata
program Laurel;
coroutine ticker(n: int) yields (x: int)
  modifies *
{
  var i: int := 0;
  while (i < n)
  {
    x := i * 10;
    yield;
    i := i + 1
  }
};

procedure driveLoop()
  entry
  opaque
  modifies *
{
  var co: ticker := ticker(3);
  var a: int := resume(co);
  assert a == 0;
  var b: int := resume(co);
  assert b == 10;
  var c: int := resume(co);
  assert c == 20;
  assert has_next(co);
  resume(co);
  assert !has_next(co)
};
#end

/-! ## A value sent in by `resume`, read by the expression form of `yield`

`resume(co, v)` sends `v` in; the suspended `z := yield` evaluates to it when the
body wakes up. The body keeps the first sent value in a local and adds the second
to it, so a run that dropped either one — or that re-read the first `yield`'s
value at the second — answers something else. -/

-- No Core interpreter: lowering it to Core fails with an internal resolution error.
#eval testLaurelExecution laurelOnly <|
#strata
program Laurel;
coroutine adder() yields (x: int) resumes (y: int)
  modifies *
{
  x := 0;
  var z: int := yield;
  x := z + 1;
  var w: int := yield;
  x := z + w;
  yield
};

procedure driveSend()
  entry
  opaque
  modifies *
{
  var co: adder := adder();
  var a: int := resume(co);
  assert a == 0;
  var b: int := resume(co, 5);
  assert b == 6;
  var c: int := resume(co, 7);
  assert c == 12
};
#end

/-! ## `has_next` after the body falls off its end

`has_next(co)` stays true until the body has actually run off its end, which is one
resume *after* the last yielded value -- the resume that runs the tail. -/

-- No Core interpreter: the state machine a coroutine lowers to ends at its last `yield`, so it
-- finishes one `resume` early.
#eval testLaurelExecution laurelOnly <|
#strata
program Laurel;
coroutine once() yields (x: int)
  modifies *
{
  x := 5;
  yield
};

procedure driveFallOff()
  entry
  opaque
  modifies *
{
  var co: once := once();
  var a: int := resume(co);
  assert a == 5;
  resume(co);
  assert !has_next(co)
};
#end

/-! ## Resuming a finished coroutine is an error

Completion is observable (`has_next`), so resuming past it is a client mistake
rather than a no-op, and saying so is the only way a driver loop with the test in
the wrong place fails where the bug is. It is the interpreter's half of the
`notDone` precondition the verification path puts on a generated `resume`. -/

/-- error: 'resume' of coroutine 'tiny' after it ran to completion
-/
#guard_msgs in
-- No Core interpreter: the state machine a coroutine lowers to ends at its last `yield`, so it
-- finishes one `resume` early.
#eval testLaurelExecution laurelOnly <|
#strata
program Laurel;
coroutine tiny() yields (x: int)
  modifies *
{
  x := 1;
  yield
};

procedure driveOverrun()
  entry
  opaque
  modifies *
{
  var co: tiny := tiny();
  resume(co);
  resume(co);
  resume(co)
};
#end

/-! ## Two instances of one coroutine advance independently

Each spawn captures its own arguments and carries its own frame and suspension
point, so interleaving two instances of the same `coroutine` must not let either
observe the other's position. -/

#eval testLaurelExecution interpreters <|
#strata
program Laurel;
coroutine steps(base: int) yields (x: int)
  modifies *
{
  x := base + 1; yield;
  x := base + 2; yield
};

procedure driveTwoInstances()
  entry
  opaque
  modifies *
{
  var p: steps := steps(100);
  var q: steps := steps(200);
  var a: int := resume(p);
  assert a == 101;
  var b: int := resume(q);
  assert b == 201;
  var c: int := resume(p);
  assert c == 102;
  var d: int := resume(q);
  assert d == 202
};
#end

/-! ## An ordinary procedure call on either side of a `yield`

A `yield` suspends the coroutine whose body lexically contains it, so a procedure
called from that body is not part of the coroutine: it gets a frame of its own and
its position is its own business. Calls before and after the suspension both have
to work, and the value the first one produced has to still be there afterwards. -/

#eval testLaurelExecution interpreters <|
#strata
program Laurel;
procedure double(n: int) returns (r: int)
  opaque
{
  return n * 2
};

coroutine doubling() yields (x: int)
  modifies *
{
  x := double(3);
  yield;
  x := double(x);
  yield
};

procedure driveCalls()
  entry
  opaque
  modifies *
{
  var co: doubling := doubling();
  var a: int := resume(co);
  assert a == 6;
  var b: int := resume(co);
  assert b == 12
};
#end

/-! ## One coroutine driving another

Delegation — Python's `yield from` — is a `resume` inside a coroutine body, which
means one suspension has to nest inside another: the inner resume installs its own
frame, position and pending seek, and the outer body's must be exactly where they
were when the inner one returns. The outer coroutine also suspends from inside a
`while` whose condition reads the inner coroutine's completion. -/

-- No Core interpreter: the state machine a coroutine lowers to ends at its last `yield`, so it
-- finishes one `resume` early.
#eval testLaurelExecution laurelOnly <|
#strata
program Laurel;
coroutine inner() yields (x: int)
  modifies *
{
  x := 1; yield;
  x := 2; yield
};

coroutine outer() yields (x: int)
  modifies *
{
  var i: inner := inner();
  var v: int := resume(i);
  while (has_next(i))
  {
    x := v * 10;
    yield;
    v := resume(i)
  }
};

procedure driveDelegation()
  entry
  opaque
  modifies *
{
  var co: outer := outer();
  var a: int := resume(co);
  assert a == 10;
  var b: int := resume(co);
  assert b == 20;
  assert has_next(co);
  resume(co);
  assert !has_next(co)
};
#end

/-! ## A `yield` under an `if`, resumed into the arm it suspended in

The branch a coroutine suspended inside is part of its suspension point, so the
resume re-enters *that* arm rather than re-deciding by re-testing the condition —
which the caller may have invalidated in the meantime. Here the coroutine reads a
cell the caller writes between resumes: the first resume takes the `then` arm, the
caller then flips the cell, and the statements after the `yield` in the `then` arm
must still be the ones that run. -/

#eval testLaurelExecution interpreters <|
#strata
program Laurel;
composite Cell { var flag: bool }

coroutine branching(c: Cell) yields (x: int)
  modifies *
{
  if c#flag then
  {
    x := 1;
    yield;
    x := 2;
    yield
  }
  else
  {
    x := 91;
    yield;
    x := 92;
    yield
  }
};

procedure driveBranch()
  entry
  opaque
  modifies *
{
  var c: Cell := new Cell;
  c#flag := true;
  var co: branching := branching(c);
  var a: int := resume(co);
  assert a == 1;
  c#flag := false;
  var b: int := resume(co);
  assert b == 2
};
#end

/-! ## A `yield` nested in an expression

A resume re-enters at the statement that suspended, so the interpreter lifts a
nested `yield` into a statement of its own before the body runs, with every operand
evaluated before it moved into a temporary. Nothing is evaluated twice: `bump`
runs once although the statement around it suspends, both `yield`s in one sum
deliver their own resumed value, a `yield` in a `while` condition is tested on
every iteration, and the right operand of `&&` still runs only when the left is
true. -/

-- No Core interpreter: lowering it to Core fails with an internal resolution error.
#eval testLaurelExecution laurelOnly <|
#strata
program Laurel;
composite Cell {
  var n: int
}

procedure bump(c: Cell) returns (r: int)
  opaque
  modifies *
{
  c#n := c#n + 1;
  r := 1
};

coroutine once(c: Cell) yields (x: int) resumes (y: int)
  modifies *
{
  x := 0;
  var z: int := bump(c) + yield;
  x := z;
  yield
};

coroutine sum() yields (x: int) resumes (y: int)
  modifies *
{
  x := 0;
  var z: int := (yield) + (yield);
  x := z;
  yield
};

coroutine loop() yields (x: int) resumes (y: bool)
  modifies *
{
  x := 0;
  while (yield) {
    x := x + 1
  };
  x := 100 + x;
  yield
};

coroutine lazy(c: Cell) yields (x: int) resumes (y: bool)
  modifies *
{
  x := 0;
  var b: bool := c#n > 100 && yield;
  x := if b then 1 else 2;
  yield
};

procedure driveNested()
  entry
  opaque
  modifies *
{
  var c: Cell := new Cell;
  c#n := 0;
  var co: once := once(c);
  var a: int := resume(co);
  var b: int := resume(co, 5);
  assert b == 6;
  assert c#n == 1;

  var s: sum := sum();
  var s0: int := resume(s);
  var s1: int := resume(s, 3);
  var s2: int := resume(s, 4);
  assert s2 == 7;

  var w: loop := loop();
  var w0: int := resume(w);
  var w1: int := resume(w, true);
  var w2: int := resume(w, true);
  var w3: int := resume(w, false);
  assert w3 == 102;
  assert has_next(w);

  var l: lazy := lazy(c);
  var l0: int := resume(l);
  assert l0 == 2
};
#end

/-! ## A `catch` binding in a resumed handler

The handler suspends while its binding shadows a local of the same name; when the
resumed handler finishes, the local is visible again. -/

-- No Core interpreter: lowering it to Core fails with an internal resolution error.
#eval testLaurelExecution laurelOnly <|
#strata
program Laurel;
coroutine g() yields (x: int) resumes (y: int)
  modifies *
{
  var e: int := 10;
  x := 0;
  try {
    throw 3
  } catch e {
    x := e;
    yield
  };
  x := e;
  yield
};

procedure driveShadow()
  entry
  opaque
  modifies *
{
  var co: g := g();
  var a: int := resume(co);
  assert a == 3;
  var b: int := resume(co, 0);
  assert b == 10
};
#end

/-! ## A coroutine cannot resume itself

Resuming an instance from inside its own body would replay the body into itself
without end, so it is refused. -/

/-- error: 'resume' of coroutine 'gen' from inside its own body [in gen]
-/
#guard_msgs in
-- No Core interpreter: it does not refuse the self-resume, and runs out of fuel instead.
#eval testLaurelExecution laurelOnly <|
#strata
program Laurel;
composite Holder {
  var co: gen
}

coroutine gen(h: Holder) yields (x: int)
  modifies *
{
  x := 1;
  yield;
  var inner: int := resume(h#co);
  x := 2;
  yield
};

procedure driveSelf()
  entry
  opaque
  modifies *
{
  var h: Holder := new Holder;
  var co: gen := gen(h);
  h#co := co;
  resume(co);
  resume(co)
};
#end

/-! ## A shadowing block across a suspension

The coroutine suspends inside a block whose declaration shadows a local; resuming
re-enters the block, and leaving it afterwards still restores the outer value. -/

#eval testLaurelExecution interpreters <|
#strata
program Laurel;
coroutine g() yields (r: int)
  modifies *
{
  var x: int := 0;
  {
    var x: int := 1;
    r := x;
    yield
  };
  r := x;
  yield
};

procedure driveScope()
  entry
  opaque
  modifies *
{
  var co: g := g();
  var a: int := resume(co);
  assert a == 1;
  var b: int := resume(co);
  assert b == 0
};
#end

/-! ## A loop whose condition suspends still checks its invariant

The invariant is checked after each test of the condition, as for any `while`, so it
fails on the third test, once the body has run twice. -/

-- No Core interpreter: lowering it to Core fails with an internal resolution error.
#eval testLaurelExecution laurelOnly <|
#strata
program Laurel;
coroutine counter() yields (x: int) resumes (y: bool)
  modifies *
{
  x := 0;
  while (yield)
    invariant x < 2
//            ^^^^^ error: assertion does not hold
  {
    x := x + 1
  };
  yield
};

procedure driveInvariant()
  entry
  opaque
  modifies *
{
  var co: counter := counter();
  var a: int := resume(co);
  var b: int := resume(co, true);
  var c: int := resume(co, true);
  var d: int := resume(co, false)
};
#end

/-! ## A store across a suspension goes to the receiver it took first

A field store evaluates its receiver before its value, so before a `yield` in the value,
and a resume does not evaluate it again. The caller replaces `s#r` while the body is
suspended, and each store still goes to the box `s#r` held before its `yield`: `b` for
the block value, `c` for the value the second resume sends. -/

-- No Core interpreter: lowering it to Core fails with an internal resolution error.
#eval testLaurelExecution laurelOnly <|
#strata
program Laurel;
composite Box {
  var x: int
}
composite Slot {
  var r: Box
}
coroutine storer(s: Slot) yields (v: int) resumes (w: int)
  modifies *
{
  v := 0;
  s#r#x := { yield; 5 };
  s#r#x := yield
};

procedure driveStoreAcrossSuspension()
  entry
  opaque
  modifies *
{
  var s: Slot := new Slot;
  var b: Box := new Box;
  var c: Box := new Box;
  var d: Box := new Box;
  b#x := 0;
  c#x := 0;
  d#x := 0;
  s#r := b;
  var co: storer := storer(s);
  resume(co);
  s#r := c;
  resume(co, 0);
  assert b#x == 5 && c#x == 0;
  s#r := d;
  resume(co, 7);
  assert c#x == 7 && d#x == 0
};
#end

/-! ## Both interpreters store across a suspension into the receiver it took first

`x := yield` keeps its receiver across the suspension on the elaborated path too, also when the
receiver is a generic instance method's result: the caller replaces `c#cur` before the second
resume, and the store still goes to `b`. -/

#eval testLaurelExecution interpreters <|
#strata
program Laurel;
composite Box<T> {
  var x: T
}
composite Cell {
  var cur: Box<int>
  procedure pick<U>(self: Cell, b: Box<U>) returns (r: Box<U>) opaque ensures r == b { r := b };
}
coroutine picker(c: Cell) resumes (n: int)
  modifies *
{
  c#pick(c#cur)#x := yield
};

procedure drivePicker()
  entry
  opaque
  modifies *
{
  var c: Cell := new Cell;
  var b: Box<int> := new Box<int>;
  var d: Box<int> := new Box<int>;
  b#x := 0;
  d#x := 0;
  c#cur := b;
  var co: picker := picker(c);
  resume(co, 1);
  c#cur := d;
  resume(co, 7);
  assert b#x == 7 && d#x == 0
};
#end

/-! ## A suspension inside a receiver

A store's or an update operator's receiver may itself suspend, here in a call's argument:
`bump` adds 1 to `s#n` once per receiver, not again when the body resumes, and each target is
the box `s#r` names after the resume. -/

-- No Core interpreter: lowering it to Core fails with an internal resolution error.
#eval testLaurelExecution laurelOnly <|
#strata
program Laurel;
composite Box {
  var x: int
}
composite Slot {
  var r: Box
  var n: int
}
procedure bump(s: Slot) returns (k: int)
  opaque
  modifies s
{
  s#n := s#n + 1;
  k := s#n
};
procedure pick(s: Slot, k: int, w: int) returns (b: Box)
  opaque
{
  b := s#r
};
coroutine suspendingReceivers(s: Slot) yields (v: int) resumes (w: int)
  modifies *
{
  v := 0;
  pick(s, bump(s), yield)#x := s#n;
  pick(s, bump(s), yield)#x++
};

procedure driveSuspendingReceivers()
  entry
  opaque
  modifies *
{
  var s: Slot := new Slot;
  var b: Box := new Box;
  var c: Box := new Box;
  var d: Box := new Box;
  b#x := 0;
  c#x := 0;
  d#x := 10;
  s#n := 0;
  s#r := b;
  var co: suspendingReceivers := suspendingReceivers(s);
  resume(co);
  s#r := c;
  resume(co, 0);
  assert s#n == 2 && c#x == 1 && b#x == 0;
  s#r := d;
  resume(co, 0);
  assert s#n == 2 && d#x == 11
};
#end
