/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelVerification <|
#strata
program Laurel;

procedure innerExitValue(a: int) returns (r: int)
{
  r := { var s: int := 0; { if a > 0 then { s := 1; exit m }; s := 2 } m; s + 10 };
  return r
};

procedure testInnerExitValue()
  opaque
{
  assert innerExitValue(1) == 11;
  assert innerExitValue(-1) == 12;
  assert innerExitValue(1) == 12
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;

procedure innerExitInContract(a: int) returns (r: int)
  requires { var ok: bool := false; { if a > 0 then { ok := true; exit m }; ok := false } m; ok }
  opaque
  ensures r == a
{
  return a
};

procedure testInnerExitInContract()
  opaque
{
  assert innerExitInContract(1) == 1;
  assert innerExitInContract(-1) == -1
//       ^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;

procedure ownLabelValue(c: bool) returns (r: int)
{
  r := { if c then { exit v }; 5 } v;
//     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: an `exit` or `return` inside an assigned block value is not YET supported in transparent bodies or contracts
  return r
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;

procedure outerLabelValue(c: bool) returns (r: int)
{
  r := 1;
  {
    r := { if c then { exit done }; 5 };
//       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: an `exit` or `return` inside an assigned block value is not YET supported in transparent bodies or contracts
    r := r + 100
  } done;
  return r
};
#end
