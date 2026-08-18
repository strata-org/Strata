/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Coroutine surface syntax: parse + resolution.

Coroutines, `yield`, `resume`, `has_next`, and rely/guarantee clauses
parse and resolve cleanly. A coroutine name is dual: it names a type in
annotation position (`co: c`) and a constructor in call position
(`c(args)`); resolution registers it as a `coroutineType`.

`CoroutineElaboration` later replaces `coroutine c` with a generated
state composite `cState` (carrying `resume` / `has_next` instance
procedures) plus a spawn constructor, and rewrites the caller side
(`co: c` → `co: cState`, `resume(co, v)` → `co#resume(v)`). The
verification of the generated state-machine obligations is exercised
separately; these tests pin only that the surface forms resolve.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Smallest coroutine: empty body, no spec. -/

#eval testLaurelResolution <|
#strata
program Laurel;
coroutine empty()
{
};
#end

/-! ## Counter coroutine: a single `yield` inside a `while` body, driven
by a `resume` from a regular procedure. -/

#eval testLaurelResolution <|
#strata
program Laurel;
coroutine counter() yields (x: int)
{
  var i: int := 0;
  while (i < 3)
    invariant i >= 0
  {
    x := i;
    yield;
    i := i + 1
  }
};

procedure driver()
  opaque
{
  var co: counter := counter();
  resume(co)
};
#end

/-! ## Yielding a value via the `yields` binding: assign, then suspend. -/

#eval testLaurelResolution <|
#strata
program Laurel;
coroutine emit() yields (x: int)
{
  x := 1; yield;
  x := 2; yield;
  x := 3; yield
};
#end

/-! ## `resume` in expression position binds the yielded value. -/

#eval testLaurelResolution <|
#strata
program Laurel;
coroutine producer(seed: int) yields (x: int)
{
  x := seed; yield
};

procedure driver(): int
  opaque
{
  var co: producer := producer(0);
  var z: int := 0;
  z := resume(co);
  return z
};
#end

/-! ## `resume(co, v)` sends a value in; a `resumes` binding declares the
incoming channel, and `relies` / `guarantees` carry per-yield obligations. -/

#eval testLaurelResolution <|
#strata
program Laurel;
coroutine echo() yields (x: int) resumes (y: int)
  relies y >= 0
  guarantees x >= 0
{
  x := 0; yield
};

procedure driver()
  opaque
{
  var co: echo := echo();
  resume(co, 42)
};
#end

/-! ## `has_next(co)` as a loop guard around `resume(co)`. -/

#eval testLaurelResolution <|
#strata
program Laurel;
coroutine ticker() yields (x: int)
{
  var i: int := 0;
  while (i < 3)
    invariant i >= 0
  {
    x := i;
    yield;
    i := i + 1
  }
};

procedure driver()
  opaque
{
  var co: ticker := ticker();
  while (has_next(co))
    invariant true
  {
    resume(co)
  }
};
#end
