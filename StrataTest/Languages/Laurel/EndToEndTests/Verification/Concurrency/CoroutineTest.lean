/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Shared test helper for the YieldElim concurrency tests. Every test file
in this directory wants the same options block — `verifyCoroutine :=
true` plus the defaults — and was duplicating ~5 lines per `#eval
testLaurelExecution` invocation. This helper hoists that boilerplate into a
single named function `testCoroutine`.

Use:

  #eval testCoroutine <| #strata
  program Laurel;
  ...
  #end

See `README.md` in this directory for what each test file covers, and for the
split between the per-construct feature tests here and the algorithm case
studies under `Examples/`.
-/

import StrataTest.Util.TestLaurel

namespace StrataTest.Util.Concurrency

open StrataTest.Util Strata StrataDDM

/-- Run `testLaurelExecution` with `verifyCoroutine := true`. Drops the
    boilerplate options block every concurrency test would otherwise
    repeat. -/
def testCoroutine (block : SourcedProgram) : IO Unit :=
  testLaurelExecution {}
    (options := { defaultLaurelTestOptions with
      translateOptions := { defaultLaurelTestOptions.translateOptions with
        verifyCoroutine := true } })
    block

end StrataTest.Util.Concurrency
