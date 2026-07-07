/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Regression coverage for `LiftImperativeExpressions` handling `try`/`catch`/
`finally` and `throw`. The lift pass (which moves assignments and imperative
calls out of expression position — e.g. the heap operations a lowered `new`
expands to) previously skipped `Try`/`Throw` via its wildcard, so a `new` (or
other lift-needing statement) *inside* a `try` region reached Core translation
unlifted and failed with a `strata-bug` ("destructive assignments ... should
have been lifted"). Both `transformStmt` arms now recurse into the body, each
handler, and the `finally`, so these programs lower and verify.
-/

-- `new` inside the try body: the heap ops it expands to are lifted within the
-- body; the throw is caught and control resumes (r == 2).
#eval testLaurel <|
#strata
program Laurel;
composite MyError extends BaseException {}
procedure newInsideTry()
  returns (r: int)
  opaque
{
  r := 0;
  try {
    var e: MyError := new MyError;
    throw e
  } catch c when c is MyError {
    r := 2
  };
  assert r == 2
};
#end

-- `new` inside a catch handler and inside a finally body are both lifted. The
-- handler sets r := 1, finally runs on the fall-through and adds 1 (r == 2).
#eval testLaurel <|
#strata
program Laurel;
composite MyError extends BaseException {}
procedure newInHandlerAndFinally()
  returns (r: int)
  opaque
{
  var e: MyError := new MyError;
  r := 0;
  try {
    throw e
  } catch c when c is MyError {
    var h: MyError := new MyError;
    r := 1
  } finally {
    var f: MyError := new MyError;
    r := r + 1
  };
  assert r == 2
};
#end
