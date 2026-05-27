/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExpect <|
#strata_expect
program Laurel;
procedure foo()
  opaque
{
  <?>
//^^^ error: could not infer type
};
#end
