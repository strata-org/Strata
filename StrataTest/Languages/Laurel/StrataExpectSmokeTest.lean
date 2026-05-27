/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Smoke test for the new `#strata` / `#strata_expect` test ergonomics.
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

/-! ## Contract: #strata_expect with no diagnostics throws -/

/-- error: #strata_expect block produced no diagnostics; use #strata for positive tests -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
procedure foo() opaque { assert true };
#end

/-! ## Negative smoke test: variable used as type -/

/-- info: 4:9-10  error: 'x' resolves to variable, but expected composite type, constrained type, datatype definition, type alias -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
procedure foo() opaque {
  var x: int := 1;
  var y: x := 2
};
#end
