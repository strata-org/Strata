/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
## Prelude names live in the reserved `$` namespace

`CoreDefinitionsForLaurel` is prepended to *every* Laurel program, so each name it
declares is a name a user program can no longer use. Mixing a user-declared
procedure with an `external` overload of the same name is rejected outright ("A set
of procedure overloads must not have any external procedures"), so an unprefixed
prelude name is a hard source-compatibility break rather than a shadowing nuisance.

Every prelude procedure therefore carries Laurel's reserved `$` prefix — the
type-specific delegates (`$intAdd`, `$boolNot`, `$bv32SLt`, …) as well as the
overloaded operator wrappers (`$add`, `$lt`, …) and the `$Box` placeholder.
`LaurelToCoreSchemaPass` matches on the bare names via `dropReservedPrefix`, so the
prefix lives in one place rather than in every match arm.

This test pins the property down: a program declaring its own `intAdd`, `eq`,
`andThen` and `strConcat` resolves, and calls to them resolve to the user's
procedures.

Resolving is not enough to prove the property, so the second block below runs the
*whole pipeline*: `dropReservedPrefix` returns `none` for an unprefixed name, so
`isOperatorProcName` rejects it and the user's procedure is called. Were the prefix
merely tolerated rather than required, a user-declared `intAdd` would reach
`LaurelToCoreSchemaPass`'s operator path and be lowered straight to Core's `+`,
discarding the user's body with no diagnostic at all.

Still unprefixed, deliberately: `select`, `update` and `mapConst`. Those are Core's
own map operator names (`Core.CoreOp`, `Core.Factory`), so the Laurel declaration has
to match the name Core expects — renaming them needs a matching Core-side change and
is left as follow-up.
-/

#eval testLaurelResolution <|
#strata
program Laurel;

procedure intAdd(a: int, b: int) : int
  opaque
{
  return a + b
};

procedure eq(a: int, b: int) : bool
  opaque
{
  return a == b
};

procedure andThen(a: bool, b: bool) : bool
  opaque
{
  return a && b
};

procedure strConcat(a: string, b: string) : string
  opaque
{
  return a
};

// A user datatype named `Box` must also survive: `HeapParameterization` generates
// its own `$Box`, which is a distinct, reserved name.
datatype Box { MkUserBox(contents: int) }

procedure useThem(x: int, s: string) opaque {
  var a: int := intAdd(x, 0);
  var b: bool := eq(x, x);
  var c: bool := andThen(b, b);
  var d: string := strConcat(s, s);
  var e: Box := MkUserBox(x)
};
#end

-- Resolution alone cannot catch a built-in shadowing a user procedure, because the
-- substitution happens in `LaurelToCoreSchemaPass`. Run the full pipeline and pin
-- the *semantics*: each body deliberately computes something other than the
-- operator it shares a name with, so the asserts hold only if the user's procedure
-- is the one being called.
#eval testLaurel <|
#strata
program Laurel;

// Subtracts, despite being named after addition.
procedure intAdd(a: int, b: int) : int
{
  return a - b
};

// Always false, despite being named after equality.
procedure eq(a: int, b: int) : bool
{
  return false
};

// Returns its *left* operand, despite being named after concatenation.
procedure strConcat(a: string, b: string) : string
{
  return a
};

procedure userProceduresWin() entry opaque {
  assert intAdd(5, 3) == 2;
  assert !eq(1, 1);
  assert strConcat("a", "b") == "a";
  // The operators themselves are unaffected: `+` is still `$add`.
  assert 5 + 3 == 8;
  assert (1 == 1)
};
#end
