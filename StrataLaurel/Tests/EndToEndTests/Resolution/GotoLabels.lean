/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! A `goto` must name an enclosing block. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure noSuchBlock()
  opaque
{
    { goto elsewhere } here
//    ^^^^^^^^^^^^^^ error: label 'elsewhere' is not in scope
};
#end
