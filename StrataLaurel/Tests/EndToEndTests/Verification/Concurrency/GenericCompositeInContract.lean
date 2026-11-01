/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util StrataTest.Util.Concurrency

/-!
Regression: a generic-composite instantiation in a coroutine's `yields` / `resumes` bindings must
be monomorphized like one anywhere else, and so must one in its `relies` / `guarantees` clauses.
The coroutine keeps its contract until `YieldElim`, after `MonomorphizeComposites` drops the
generic `Box`, so a `Box<int>` left in a binding made the re-resolution after
`MonomorphizeComposites` report `'Box' is not defined` as an internal error.
-/

#eval testLaurelVerification (options := coroutineOptions) <|
#strata
program Laurel;
composite Box<T> { var val: T }
coroutine forward(b: Box<int>) yields (x: Box<int>) resumes (y: Box<int>)
  relies forall(z: Box<int>) => z == z
  guarantees forall(z: Box<int>) => z == z
  modifies *
{
  x := b; yield;
  x := y; yield
};
#end
