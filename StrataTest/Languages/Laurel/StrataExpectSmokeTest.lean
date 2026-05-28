/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Smoke test for the `#strata` test ergonomics. See `StrataTest.Util.TestLaurel`
for the helpers.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Positive smoke test -/

#eval testLaurel
#strata
program Laurel;
procedure foo() opaque { assert true };
#end

/-! ## Negative smoke test: variable used as type. The inline annotation pins
    the expected diagnostic to the line above it. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure foo() opaque {
  var x: int := 1;
  var y: x := 2
//       ^ error: 'x' resolves to variable, but expected
};
#end

/-! ## Negative smoke test: a verifier-level diagnostic. -/

#eval testLaurel <|
#strata
program Laurel;
procedure unsafeDivision(x: int)
  opaque
{
  var z: int := 10 / x
//^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end
