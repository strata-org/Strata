/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util StrataTest.Util.Concurrency

/-!
Regression: a type alias in a coroutine's `relies` / `guarantees` clauses or `yields` /
`resumes` bindings must be expanded like one anywhere else. The coroutine keeps its contract
until `YieldElim`, well after `TypeAliasElim` removes the alias, so an alias left in the
contract made the re-resolution after `TypeAliasElim` report `'Count' is not defined` as an
internal error.
-/

#eval testLaurelVerification (options := coroutineOptions) <|
#strata
program Laurel;
type Count = int
coroutine clamp() yields (x: Count) resumes (y: Count)
  relies forall(n: Count) => n == n
  guarantees forall(n: Count) => n == n
  guarantees x >= 0
  modifies *
{
  if y >= 0 then { x := y } else { x := 0 };
  yield
};
#end
