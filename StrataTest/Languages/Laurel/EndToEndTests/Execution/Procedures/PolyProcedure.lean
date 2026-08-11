/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Polymorphic procedures through the full pipeline

`UnitTests/PolyProcedureTest.lean` drives polymorphic procedures through the corpus
harness, which runs the VERIFIER only and asserts four counters
(`translated`/`numVCs`/`numFailures`/`numErrorOutcomes`). These tests run them through
the *entire* pipeline with `testLaurelExecution { skipCoreInterpreter := false }` — translate + all lowering passes +
verify + **interpret** — checking both modes against the same inline annotations.

That second mode is the point. Polymorphic procedures ride per-call-site type-variable
freshening in `CallElim`, which rewrites each call's contract before Core sees it; nothing
else here checks that the concrete interpreter agrees with the verifier about what a
polymorphic call actually computes. A freshening bug that produced a *consistent but wrong*
instantiation could satisfy the verifier's own obligations and still execute the wrong
value.

Scope: value-`T` procedures only, i.e. no generic composites. The interpreter does not
model the heap, and a generic composite is a heap reference, so the composite cases stay
verifier-only (`Types/Composites/GenericComposite.lean`). Bodies are TRANSPARENT: an
`opaque ensures` on a polymorphic procedure emits that procedure's own body VC.  With
`MonomorphizeFunctions` inserted after `typeCheckPhase` (see
`Strata/Transform/MonomorphizeFunctions.lean`), each such body is specialized at the
ground instantiations reached from its call sites before SMT encoding, so both value
assertions and the dual-mode interpreter/verifier check succeed for every case in this
file.
-/

-- Multi-instantiation in one caller: the same `idp` at `int` and at `bool`. Per-call-site
-- freshening means the two sites do not share one `T`; without it the shared variable
-- would have to unify with both `int` and `bool`. Both modes must agree on the values.
#eval testLaurelExecution { skipCoreInterpreter := false }
#strata
program Laurel;

procedure idp<T>(x: T): T { return x };

procedure multiInstantiation()
  entry
  opaque
{
  var a: int := idp(5);
  assert a == 5;
  var b: bool := idp(true);
  assert b == true;
  var s: string := idp("hi");
  assert s == "hi"
};
#end

-- SOUNDNESS twin: a FALSE assertion on a polymorphic result must fail in both modes.
-- Guards against the instantiated result becoming unconstrained (which would let the
-- verifier pass it vacuously) and against the interpreter computing something else.
#eval testLaurelExecution { skipCoreInterpreter := false }
#strata
program Laurel;

procedure idp<T>(x: T): T { return x };

procedure falseOnPolyResult()
  entry
  opaque
{
  var a: int := idp(5);
  assert a == 6
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- The type variable used in a COMPUTED position, not just passed through: `dup` returns
-- its argument combined with itself, so a wrong instantiation changes the value rather
-- than merely the type. Pins that freshening keeps the input and output slots coupled.
#eval testLaurelExecution { skipCoreInterpreter := false }
#strata
program Laurel;

procedure pick<T>(useFirst: bool, a: T, b: T): T {
  return if useFirst then a else b
};

procedure computedPolySlot()
  entry
  opaque
{
  var i: int := pick(true, 7, 9);
  assert i == 7;
  var j: int := pick(false, 7, 9);
  assert j == 9;
  var t: bool := pick(true, false, true);
  assert t == false
};
#end

-- A polymorphic procedure calling ANOTHER polymorphic procedure at its own type variable.
-- The inner call's freshened variable must resolve to the outer instantiation, not to a
-- second independent one.  After `MonomorphizeFunctions` pre-encoding, `wrap<int>` and
-- `wrap<bool>` are specialized before SMT so the poly-to-poly call encodes cleanly and
-- both value assertions verify in both modes.
#eval testLaurelExecution { skipCoreInterpreter := false }
#strata
program Laurel;

procedure idp<T>(x: T): T { return x };
procedure wrap<T>(x: T): T { return idp(x) };

procedure nestedPoly()
  entry
  opaque
{
  var a: int := wrap(3);
  assert a == 3;
  var b: bool := wrap(false);
  assert b == false
};
#end

/-! ## Two type parameters, with the returned one differing from the discarded one

`firstOf` returns its FIRST argument, and is called at both orderings so the returned and
discarded parameters have different types each time. A substitution that crossed or dropped a
slot returns the wrong value here rather than failing to typecheck. -/

#eval testLaurelExecution { skipCoreInterpreter := false } <|
#strata
program Laurel;
procedure firstOf<A, B>(a: A, b: B): A { return a };

procedure twoTypeParams()
  entry
  opaque
{
  var a: int := firstOf(1, true);
  assert a == 1;
  var b: bool := firstOf(false, 9);
  assert b == false
};
#end

/-! ## The two-parameter result is really observed

A wrong expected value must FAIL, so the asserts above are pinning an evaluated result rather
than passing on a body the pipeline silently dropped. -/

#eval testLaurelExecution { skipCoreInterpreter := false } <|
#strata
program Laurel;
procedure firstOf<A, B>(a: A, b: B): A { return a };

procedure twoTypeParamsWrong()
  entry
  opaque
{
  var a: int := firstOf(1, true);
  assert a == 2
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

