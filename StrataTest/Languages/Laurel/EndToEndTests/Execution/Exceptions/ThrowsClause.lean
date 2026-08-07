/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
The `throws` declaration itself, treated as a feature in its own right: what it
does to a procedure's signature, its contract, and its callers — without a `try`
in the picture. `throwsOn` cases are `ThrowsOnClause.lean`; handling is
`TryCatchThrow.lean` and `TryFinallyThrow.lean`.

Declaring `throws T` changes how the *normal* contract lowers. The procedure
returns a single `Result<Val, T>`, so a plain `ensures P` no longer holds
unconditionally — it becomes `Result..isGood($result) ==> P[out := value($result)]`,
which says nothing on a throwing path. The cases below pin that this guarded form
is still **checked** on exit and still **assumed** at call sites, in both
directions, because a postcondition that silently became vacuous would be the same
class of unsoundness as an unstated `throwsOn` case.

Also here:
  * exceptional exit by *propagation* — a callee throws and the caller merely
    declares `throws` rather than catching, which is the third way a procedure can
    exit exceptionally and the one with no `try` involved;
  * `requires` on a throwing procedure, which is unaffected by the lowering since
    preconditions are evaluated on entry, before any result exists;
  * `return <value>` from a throwing procedure, which reaches this pass only
    because `eliminateValueInReturns` runs first and has already moved the payload
    into an assignment;
  * the transparent-callee rejection, which is a property of the declaration
    rather than a combination of its own: a transparent body is restricted to the
    statement language `MergeAndLiftReturns` accepts, which has no `throw`.

The escape rules for the declaration — no-escape and the subtype upper bound —
are rejections, so they live in `Resolution/Exceptions/ThrowsEscape.lean`.

Run through `testLaurel` (the verifier) rather than `testLaurelMultiple`: these cases
throw composite values, which live on the heap, and the interpret path does not
support the heap yet. Where a construct can be exercised without the heap it is run
both ways instead; see `Throw.lean`.
-/

/-! ## A normal `ensures` under `throws` -/
-- Good-path `ensures` is checked on exit: `safeInc` establishes `r > x` on the
-- (only, non-throwing) path, so the guarded postcondition discharges.
#eval testLaurel <|
#strata
program Laurel;
composite Err {}
procedure safeInc(x: int)
  returns (r: int)
  throws (e: Err)
  opaque
  ensures r > x
{
  r := x + 1
};
#end

-- Good-path `ensures` is assumed at a call site: inside the `try`, the call to
-- `produce` returns on the Good path, so the caller may rely on `ensures r > 10`
-- for the unwrapped value and prove `out > 10`.
#eval testLaurel <|
#strata
program Laurel;
composite Err {}
procedure produce()
  returns (r: int)
  throws (e: Err)
  opaque
  ensures r > 10
{
  r := 20
};
procedure consume()
  returns (out: int)
  opaque
{
  try {
    out := produce();
    assert out > 10
  } catch c {
    out := 0
  }
};
#end

-- Negative: the good-path `ensures` does not hold — `badInc` returns `x - 1`,
-- which is not `> x` — so the guarded postcondition fails on the Good path.
#eval testLaurel <|
#strata
program Laurel;
composite Err {}
procedure badInc(x: int)
  returns (r: int)
  throws (e: Err)
  opaque
  ensures r > x
//        ^^^^^ error: postcondition does not hold
{
  r := x - 1
};
#end

/-! ## Exceptional exit by propagation (no `try` in between)

A procedure declares `throws` and lets a callee's exception travel out uncaught,
rather than throwing directly or catching it. The rejection side (a caller that
declares no `throws`) is in `Resolution/Exceptions/ThrowsEscape.lean`; the direct
`throw` is in `Throw.lean`.

The mechanism is the `.StaticCall` arm of the lowering: it binds the callee's
`Result`, and on `Bad` copies the error into the enclosing region's exception variable
and exits to its throw target. The second case pins the consequence that is easiest to
get wrong when reading that arm — after a throwing call the *normal* continuation is
reachable only on the `Good` path, so a `Bad` result cannot fall through into the
statements following the call. -/

-- A callee's exception propagates through a procedure that only declares `throws`,
-- and is caught by its caller.
#eval testLaurel <|
#strata
program Laurel;
composite Err {}
procedure thrower(x: int) returns (r: int)
  throws (e: Err)
  opaque
{
  if x < 0 then {
    var e: Err := new Err;
    throw e
  };
  r := x
};
procedure propagates(x: int) returns (r: int)
  throws (e: Err)
  opaque
{
  r := thrower(x)
};
procedure catchesPropagated(x: int) returns (out: int)
  opaque
{
  out := 0;
  try {
    out := propagates(x)
  } catch e when e is Err {
    out := -1
  }
};
#end

-- After a throwing call, the statements that follow run only on the `Good` path, so
-- the callee's normal postcondition is available to them unconditionally. If a `Bad`
-- result could fall through, `r >= 0` would not hold here.
#eval testLaurel <|
#strata
program Laurel;
composite Err {}
procedure nonNegativeOrThrow(x: int) returns (r: int)
  throws (e: Err)
  opaque
  ensures r >= 0
{
  if x < 0 then {
    var e: Err := new Err;
    throw e
  };
  r := x
};
procedure usesResultAfterCall(x: int) returns (out: int)
  throws (e: Err)
  opaque
  ensures out >= 0
{
  var v: int := nonNegativeOrThrow(x);
  assert v >= 0;
  out := v
};
#end

/-! ## A transparent callee cannot throw

The reason is not the exception work. Transparent bodies are restricted to a small
statement language by `MergeAndLiftReturns`, which turns them into a single
expression, and that language has no `throw` (nor `try`) — so a transparent procedure
cannot throw at all, conditionally or otherwise, since any `throw` is the last
statement of some block. The same restriction rejects loops and a non-final
`if`/`else` there.

The combination therefore reduces to its rejection, pinned below. If transparent
bodies gain a wider statement language, this test is where the change shows up. Until
then the throwing-call combinations are covered with an opaque callee, in
`ThrowsOnClause.lean`. -/

-- A transparent (no `opaque`) procedure that throws: rejected, at the `throw`.
#eval testLaurel <|
#strata
program Laurel;
composite Err {}
procedure thrower(x: int): int
  throws (e: Err)
{
  if x < 0 then {
    var e: Err := new Err;
    throw e
//  ^^^^^^^ error: ending a transparent body with a Throw statement is not supported
  };
  return x
};
procedure catchesTransparent(x: int) returns (out: int)
  opaque
{
  out := 0;
  try {
    out := thrower(x)
  } catch e when e is Err {
    out := -1
  }
};
#end

/-! ## `requires` on a throwing procedure

Preconditions are untouched by the lowering, because they are evaluated on entry —
before any `Result` exists to be `Good` or `Bad`. So the ordinary contract applies: the
body may assume it, and each call site must establish it. -/

-- Positive: the body assumes the precondition, and a caller that satisfies it verifies.
#eval testLaurel <|
#strata
program Laurel;
composite Err {}
procedure needsNonNeg(x: int)
  returns (r: int)
  throws (e: Err)
  requires x >= 0 summary "the input is non-negative"
  opaque
  ensures r == x
{
  assert x >= 0;
  r := x
};
procedure callsWithGoodInput()
  returns (out: int)
  throws (e: Err)
  opaque
{
  out := needsNonNeg(5)
};
#end

-- Negative: a caller that violates it is reported at the call site, in the author's
-- words rather than the default phrasing.
#eval testLaurel <|
#strata
program Laurel;
composite Err {}
procedure needsNonNeg2(x: int)
  returns (r: int)
  throws (e: Err)
  requires x >= 0 summary "the input is non-negative"
  opaque
  ensures r == x
{
  r := x
};
procedure callsWithBadInput()
  returns (out: int)
  throws (e: Err)
  opaque
{
  out := needsNonNeg2(-1)
//       ^^^^^^^^^^^^^^^^ error: the input is non-negative could not be proved
};
#end

/-! ## `return` with a value

`return <expr>` reaches this lowering only because `eliminateValueInReturns` runs
first and has already rewritten the payload into an assignment to the named output.
By the time the exceptional channel is lowered there is no value riding on the
`return` for the `Result` assembly to lose — which is why that ordering is a declared
dependency of the pass rather than a comment. -/

#eval testLaurel <|
#strata
program Laurel;
composite Err {}
procedure returnsValueOrThrows(x: int)
  returns (r: int)
  throws (e: Err)
  opaque
  ensures r == x
{
  if x < 0 then {
    var er: Err := new Err;
    throw er
  };
  return x
};
#end

/-! ## The short `: T` return form under `throws`

`: T` is sugar for `returns ($result: T)` — the translator mints an output under
the literal `resultOutputName` (see `ConcreteToAbstractTreeTranslator`). The
`Result` carrier `EliminateExceptions` injects prefers that same spelling, so in a
short-form procedure the two would claim one identifier — the signature carrying
`Result<…>` while the body assigns an `int`. The pass therefore freshens the
carrier against every name the procedure binds: here it becomes `$result_1`, and
the program lowers like any other. Downstream passes are unaffected by the chosen
spelling: every reference to the carrier — the `isGood`/`isBad` guards on
postconditions and modifies groups — is emitted by `EliminateExceptions` itself at
the point it mints the name, so nothing later recognizes the carrier at all.

Both spellings are pinned because the freshening keys off the *name*, not the
sugar. Writing `$result` by hand in an explicit `returns` clause reaches the
identical state, so coverage of only the short form would miss the second case.

The freshening must see *every* binder, not just signature names: a quantifier
in a case postcondition may bind `$result` itself, and that postcondition is
exactly where the pass splices references to the carrier. If the freshener
missed the binder it would pick `$result` and the spliced reference would be
captured by the authored `forall` — silently, since nothing downstream could
tell. The third case pins that program; the arm-by-arm collision coverage is
`CarrierFreshnessTest.lean`. -/

-- Short form, with a `throwsOn` case and an `ensures` so the contract rewriting has
-- to reach the postconditions and not just the body.
#eval testLaurel <|
#strata
program Laurel;
composite Err {}
procedure shortFormOrThrows(x: int): int
  throws (e: Err)
  opaque
  ensures $result == x
  throwsOn x < 0 {}
{
  if x < 0 then {
    var er: Err := new Err;
    throw er
  };
  return x
};
#end

-- The explicit form with the output named `$result` by hand: the same program as far
-- as this pass is concerned, since `: T` desugars to exactly this.
#eval testLaurel <|
#strata
program Laurel;
composite Err {}
procedure explicitDollarResult(x: int)
  returns ($result: int)
  throws (e: Err)
  opaque
  ensures $result == x
{
  if x < 0 then {
    var er: Err := new Err;
    throw er
  };
  return x
};
#end

-- A quantifier binder named `$result` inside a case postcondition: the carrier
-- freshens to `$result_1`, so the `e` substituted into the case's `ensures`
-- refers to the carrier, not the authored quantified variable.
#eval testLaurel <|
#strata
program Laurel;
composite Err {}
procedure quantifierBindsResult(x: int)
  throws (e: Err)
  opaque
  throwsOn x < 0 {
    ensures forall($result: int) => e is Err
  }
{
  if x < 0 then {
    var er: Err := new Err;
    throw er
  }
};
#end

/-! ## The carrier is referenced, never recognized

A lowered procedure's frames are guarded on its `Result` carrier, and the guard is
attached by `EliminateExceptions` at the point of creation — it rides on the
modifies group itself, so no downstream pass ever asks *whether* a carrier exists
or *which output* it is. Nothing recognizes the carrier by its name or by its
type, and these cases pin why neither inference would be sound:

- its name is the author's to take: the short `: T` form mints a value output
  under the same preferred spelling, and the pass simply freshens its carrier to
  `$result_1` (the two short-form cases above are that, end to end);
- its type is the author's to declare: a program with no exceptions may define a
  `Result` datatype of its own (only exception-*using* programs have the name
  reserved, by `validateExceptionLowerability`).

The procedure below is bait for both inferences at once — an output named
`$result` *and* typed at a user-declared `Result`, on a procedure that throws
nothing, with a `modifies` clause so a frame is actually built. Misread it as
lowered and its frame gets guarded by a `Result..isGood` that resolution then
rejects, surfacing as an internal error from a pass that did nothing wrong. It
must verify cleanly. -/

#eval testLaurel <|
#strata
program Laurel;
composite Cell {
  value: int
}
datatype Result<A, B> {
  Ok(a: A),
  Fail(b: B)
}
procedure baitForCarrierInference(c: Cell)
  returns ($result: (Result<int, bool>))
  opaque
  modifies c
{
  c#value := 1;
  $result := Ok(0)
};
#end

-- Control: the identical procedure with an ordinary output name and type. Pinning
-- both means a regression to name- or type-inference fails the bait case while this
-- one still passes, pointing straight at the cause.
#eval testLaurel <|
#strata
program Laurel;
composite Cell {
  value: int
}
procedure ordinaryOutput(c: Cell) returns (r: int)
  opaque
  modifies c
{
  c#value := 1;
  r := 0
};
#end
