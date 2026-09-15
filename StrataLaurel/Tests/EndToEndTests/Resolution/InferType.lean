/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure foo()
  opaque
{
  <?>
//^^^ error: could not infer type
};
#end
