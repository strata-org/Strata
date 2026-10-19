/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Shared test options for the YieldElim concurrency tests. `coroutineOptions` is
the test defaults plus `verifyCoroutine := true`, which every test file in this
directory needs and none should spell out again.

Use:

  #eval testLaurelVerification (options := coroutineOptions) <| #strata
  program Laurel;
  ...
  #end

See `README.md` in this directory for what each test file covers, and for the
split between the per-construct feature tests here and the algorithm case
studies under `Examples/`.
-/

import StrataLaurel.Tests.Util.TestLaurel

namespace StrataTest.Util.Concurrency

open StrataTest.Util Strata StrataDDM

/-- The test defaults plus `verifyCoroutine := true`. Drops the boilerplate
    options block every concurrency test would otherwise repeat.

    Every test in this directory pairs these options with
    `testLaurelVerification`: a coroutine's `resume`/`yield` schedule over all
    interleavings is what the tests are about, which one concrete run cannot
    show, so no block here marks an `entry`. -/
def coroutineOptions : Laurel.LaurelVerifyOptions :=
  { defaultLaurelTestOptions with
    translateOptions := { defaultLaurelTestOptions.translateOptions with
      verifyCoroutine := true } }

end StrataTest.Util.Concurrency
