/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! A generic composite and a procedure without a body that the entry does not reach
leave the program runnable. -/

#eval testLaurelExecution { skipCortexInterpreter := false } <|
#strata
program Laurel;
composite Box<T> { var v: T }

procedure unused(x: int) returns (r: int)
  opaque;

procedure main()
  entry
  opaque
{
  assert 1 + 1 == 2
};
#end
