/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! A precondition is checked at the call. -/

#eval testLaurelExecution { skipCortexInterpreter := false } <|
#strata
program Laurel;
procedure half(x: int) returns (r: int)
  requires x >= 0 summary "non-negative argument"
  opaque
{
  r := x / 2
};

procedure main()
  entry
  opaque
{
  var y: int := half(0 - 4)
//              ^^^^^^^^^^^ error: non-negative argument does not hold
};
#end

/-! The control: a precondition that holds. -/

#eval testLaurelExecution { skipCortexInterpreter := false } <|
#strata
program Laurel;
procedure half(x: int) returns (r: int)
  requires x >= 0 summary "non-negative argument"
{
  r := x / 2
};

procedure main()
  entry
  opaque
{
  var y: int := half(4);
  assert y == 2
};
#end
