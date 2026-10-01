/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-
A `catch` binding that resolution cannot type is typed `Unknown`, and
`EliminateExceptions.lowerTry` reads an `Unknown` binding as "this handler can
never fire" and DISCARDS the clause — the body is then verified as if no handler
were present, and the handler's own obligations vanish with it. Carrying only a
`.warning` for that, as `Check.tryCatch` does, is not enough: every pipeline gate
is spelled `kind != .warning`, so a program whose handler was dropped verifies
green.

Two halves, both pinned here:

  1. The shapes that `collectThrownTypes` now types, so the handler survives and
     its obligations are real again — a `throw` of a call's result (typed from the
     callee's single output) and a `throw` of an unannotated local (typed from its
     initializer). The failing `assert` inside each handler is the evidence: it is
     only reachable if the clause was kept.
  2. A shape it still cannot type structurally — a `throw` of a field read — where
     `checkPropagationEdges` backstops with a hard error. That check runs
     post-resolution with the model, so `exceptionEscapes` CAN type the operand;
     the disagreement between the two analyses is exactly the hole.

The backstop fires on "a type was available and the binding did not get it", not
merely on "the binding is `Unknown`". It re-derives the join over what escapes, so
the *other* producer of an `Unknown` binding — thrown types with no common ancestor,
where no valid type exists at all — joins to `none` and stays this check's business
to ignore: `Check.tryCatch` already rejects it, and reporting twice would say
nothing new. That case is pinned by `noCommonAncestor` in
`EndToEndTests/Execution/Exceptions/TryCatchThrow.lean`, which still expects exactly
one error.

A `try` whose body genuinely throws nothing typeable keeps the plain `.warning`
and no error — an empty escape set joins to `none` as well. Pinned by the
`badGuard` block in `CatchGuardTyping.lean`, whose body is just `assert true`.
-/

-- (1a) `throw f()` is typed from `f`'s single output, so the handler survives and the
-- caught value is the thrown one. The failing `assert` is what shows the clause is
-- still in the program: a discarded one takes its obligations with it.
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure f() returns (q: int) opaque { return 7 };
procedure throwsCallResult() returns (r: int) opaque
{
  try {
    throw f()
  } catch c {
    assert c == 8
//  ^^^^^^^^^^^^^ error: assertion does not hold
  };
  r := 0
};
#end

-- (1b) An unannotated local is typed from its initializer, so `var e := 7; throw e`
-- reaches the binding too. No warning: the body's thrown type is determined.
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure throwsInferredLocal() returns (r: int) opaque
{
  try {
    var e := 7;
    throw e
  } catch c {
    assert c == 8
//  ^^^^^^^^^^^^^ error: assertion does not hold
  };
  r := 0
};
#end

-- (2) A `throw` of a field read is still not typed structurally, so the binding is
-- `Unknown` and the clause would be dropped — on a body that demonstrably throws.
-- The hard error is the backstop: without it this program verifies green with only
-- the warning, even though the handler (and any obligation inside it) is gone.
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
composite Box { var v: int }
procedure throwsFieldRead(b: Box) returns (r: int) opaque
{
  try {
//^ warning: the `catch` clause(s) of this `try` can never fire
//^ error: the `catch` binding of this `try` was left untyped, but the body throws an exception of type 'int'
    throw b#v
  } catch c {
    assert false
  };
  r := 0
};
#end
