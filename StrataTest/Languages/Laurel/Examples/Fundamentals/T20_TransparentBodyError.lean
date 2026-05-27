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
procedure transparentBody()
//        ^^^^^^^^^^^^^^^ error: transparent procedures are not yet supported. Add 'opaque' to make the procedure opaque
{
  assert true
};
#end
