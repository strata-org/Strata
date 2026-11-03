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

procedure loopInvariantWithStatements()
  opaque
{
  var i: int := 0;
  while (i < 3)
    invariant { var s: bool := i <= 3; if i < 10 then { s := i <= 3 } else { s := false }; { if i < 0 then { s := false; exit m }; s := s } m; s }
  {
    i := i + 1
  };
  assert i == 3
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;

procedure loopInvariantWithStatementsFalse()
  opaque
{
  var i: int := 0;
  while (i < 3)
    invariant { var s: bool := i <= 2; if i < 10 then { s := i <= 2 } else { s := false }; { if i < 0 then { s := false; exit m }; s := s } m; s }
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    i := i + 1
  };
  assert i == 3
};
#end


#eval testLaurelVerification <|
#strata
program Laurel;

procedure loopInvariantExitsOuter()
  opaque
{
  var i: int := 0;
  {
    while (i < 3)
      invariant { var s: bool := i <= 3; if i < 0 then { exit done }; s }
//              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: an `exit` or `return` inside a loop invariant or decreases clause is not YET supported
    {
      i := i + 1
    }
  } done;
  assert i == 3
};
#end
