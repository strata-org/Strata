/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
/-
Tests that `TypeAliasElim` correctly rewrites Laurel programs.

Uses `runPassForIdiomaticity`, the shared idiomaticity driver: parse, resolve,
run `typeAliasElimPass`, print the result for the `#guard_msgs` golden.

`renderProgramForIdiomaticity` prints type declarations, so a golden showing only
the procedures pins BOTH halves of the pass: every `UserDefined` reference
unfolded to the alias target, and the `.Alias` entries dropped from
`program.types`. The cycle case needs nothing beyond the golden either — a
non-terminating `resolveAliasType` would hang the elaborator rather than print.
-/

meta import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.TypeAliasElim

open Strata
open StrataTest.Util

namespace Strata.Laurel

-- ============================================================
-- 1. Chained aliases: A = int; B = A  →  both resolved to int
-- ============================================================

/--
info: procedure test(x: int)
  returns (r: int)
{
  return x
};
-/
#guard_msgs in
#eval runPassForIdiomaticity typeAliasElimPass <|
#strata
program Laurel;
type A = int
type B = A

procedure test(x: B) returns (r: A) { return x };
#end

-- ============================================================
-- 2. Cycle detection: C = D; D = C  →  terminates gracefully
-- ============================================================

-- The visited-set guard in `resolveAliasType` stops the infinite unfolding and
-- leaves the reference as written (`x: C`), while both alias declarations are
-- still dropped.
/--
info: procedure cyclic(x: C)
  opaque
{
  assert true
};
-/
#guard_msgs in
#eval runPassForIdiomaticity typeAliasElimPass <|
#strata
program Laurel;
type C = D
type D = C

procedure cyclic(x: C) opaque { assert true };
#end

-- ============================================================
-- 3. Aliases in procedure signatures (param + return types)
-- ============================================================

/--
info: procedure compute(a: int, b: bool)
  returns (r: int)
{
  return a
};
-/
#guard_msgs in
#eval runPassForIdiomaticity typeAliasElimPass <|
#strata
program Laurel;
type MyInt = int
type MyBool = bool

procedure compute(a: MyInt, b: MyBool) returns (r: MyInt) { return a };
#end

end Laurel
