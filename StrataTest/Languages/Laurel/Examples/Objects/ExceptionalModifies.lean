/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
The exceptional frame `onThrow modifies …` (E4): the modifies clause that
applies on the *throwing* path, mirroring the normal `modifies` that applies on
the normal-return path.

A throwing procedure's normal `modifies` frame is lowered (via `ModifiesClauses`
+ the Good-path wrap) to `Result..isGood($result) ==> <only normal targets
change>`, so it says nothing when the procedure throws. `onThrow modifies T`
adds the complementary Bad-path frame, lowered by `EliminateExceptions` to
`Result..isBad($result) ==> <only T changes>`. So the two paths can name
different frames, and the throwing-path frame is *checked* on the body and
*assumed* at call sites.
-/

-- Positive: the body honours both frames — on the normal path only `c` changes,
-- on the throwing path only `logCell` changes (the freshly-allocated `Err` is
-- excluded from the frame, since it did not exist in the pre-state heap).
#eval testLaurel <|
#strata
program Laurel;
composite Cell {
  value: int
}
composite Err extends BaseException {}
procedure doWork(c: Cell, logCell: Cell, fail: bool)
  returns (r: int)
  throws Err
  opaque
  modifies c
  onThrow modifies logCell
{
  if fail then {
    logCell#value := 1;
    var e: Err := new Err;
    throw e
  };
  c#value := 42;
  r := 0
};
#end

-- Negative: on the throwing path this modifies `c`, but `onThrow modifies
-- logCell` claims only `logCell` may change there, so the exceptional frame
-- check fails.
#eval testLaurel <|
#strata
program Laurel;
composite Cell {
  value: int
}
composite Err extends BaseException {}
procedure doWorkBad(c: Cell, logCell: Cell)
//        ^^^^^^^^^ error: assertion could not be proved
  returns (r: int)
  throws Err
  opaque
  modifies c
  onThrow modifies logCell
{
  c#value := 99;
  var e: Err := new Err;
  throw e
};
#end
