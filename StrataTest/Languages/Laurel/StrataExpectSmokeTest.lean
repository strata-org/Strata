/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Smoke test for the `#strata` / `#strata_expect` test ergonomics.
See `StrataTest.Util.TestLaurel` for the helpers and
`Strata.DDM.Integration.Lean.HashCommandsExpect` for the elaborator.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Positive smoke test -/

/-- info: ok -/
#guard_msgs in
#eval testLaurel
#strata
program Laurel;
procedure foo() opaque { assert true };
#end

/-! ## Negative smoke test: variable used as type. The inline annotation pins
    the expected diagnostic to the line above it. -/

#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
procedure foo() opaque {
  var x: int := 1;
  var y: x := 2
//       ^ error: 'x' resolves to variable, but expected
};
#end

/-! ## Negative smoke test: a verifier-level diagnostic. -/

#eval testLaurelExpect <|
#strata_expect
program Laurel;
procedure unsafeDivision(x: int)
  opaque
{
  var z: int := 10 / x
//^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end
