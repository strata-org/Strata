/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! The translation to Core reports arrays as not yet supported, an element write included,
rather than dropping it. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure p(a: Array<int>)
  opaque
  modifies *
{
  a[0] := 5;
//^^^^^^^^^ not-yet-implemented: arrays are not yet supported by the translation to Core
  assert false
};
#end

/-! An array type alone is reported, rather than surfacing later as an unknown type. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure q(a: Array<int>)
//             ^^^^^^^^^^ not-yet-implemented: arrays are not yet supported by the translation to Core
  opaque
{
  assert true
};
#end
