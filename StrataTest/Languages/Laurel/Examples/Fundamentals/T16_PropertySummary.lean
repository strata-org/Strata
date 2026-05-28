/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

def program := r#"
procedure divide(x: int, y: int) returns (result: int)
  requires y != 0 summary "divisor is non-zero"
// Call elimination reports precondition errors at the call site.
  opaque
{
  assert y == 0 summary "divisor is zero";
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: divisor is zero does not hold
  return x
};

procedure checkPositive(n: int) returns (ok: bool)
  opaque
{
  var x: int := divide(3, 0)
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: divisor is non-zero does not hold
};
"#

#guard_msgs (drop info, error) in
#eval testInputWithOffset "PropertySummary" program 14 processLaurelFile

end Strata.Laurel
