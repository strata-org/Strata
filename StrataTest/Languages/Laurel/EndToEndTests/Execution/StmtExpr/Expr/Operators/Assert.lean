/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelMultiple <|
#strata
program Laurel;

procedure foo()
  entry
  opaque
{
    assert true;
    assert false;
//  ^^^^^^^^^^^^ error: assertion does not hold
    assert false
//  ^^^^^^^^^^^^ error: assertion does not hold
};
#end
