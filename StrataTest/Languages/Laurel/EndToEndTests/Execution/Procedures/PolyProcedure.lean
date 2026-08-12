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
`opaque ensures` on a polymorphic procedure emits that procedure's own body VC, which
cannot be encoded until the two Core SMT-encoder fixes land — see
`UnitTests/PolyProcedureTest.lean` and the `knownEncoderErrors` field on the corpus
harness. Keeping these bodies transparent is what lets the end-to-end path be pinned
today rather than deferred with the corpus cases.
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
-- second independent one.
--
-- TRANSITIONAL: this shape reaches the SMT encoder with a bare type variable and cannot be
-- encoded until the two Core encoder fixes land ("encode a polymorphic function's body in
-- its own typeArg scope" and "encode free type variables as uninterpreted sorts, soundly").
-- Unlike the corpus cases, the error is asserted here VERBATIM rather than absorbed into a
-- counter, so the message is visible in test source and a change in the failure mode fails
-- the build. Note the transparent body does NOT avoid it: the poly-to-poly CALL is what
-- synthesizes the free type variable. Replace these two annotations with the intended
-- value assertions once the encoder fixes merge.
--
-- `testLaurelExecution {}`, not `testLaurelExecution { skipCoreInterpreter := false }`, for the same reason: the encoding error is a
-- VERIFIER-only artifact — the interpreter performs no SMT encoding, so it cannot produce
-- these diagnostics, and the dual-mode runner requires every annotation to fire in both
-- modes. This case rejoins the dual-mode set when the annotations above are replaced.
#eval testLaurelExecution {}
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
//^^^^^^^^^^^^^ strata-bug: analysis error: SMT Encoding Error! Cannot encode unresolved type variable 'T' to SMT, polymorphic function body verification is not yet supported.
  var b: bool := wrap(false);
  assert b == false
//^^^^^^^^^^^^^^^^^ strata-bug: analysis error: SMT Encoding Error! Cannot encode unresolved type variable 'T' to SMT, polymorphic function body verification is not yet supported.
};
#end
