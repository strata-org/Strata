/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Python.TestExamples
import StrataTest.Util.TestDiagnostics

open StrataTest.Util
open Strata.Python (processPythonFile withPython)
open Strata.Parser (stringInputContext)
open Strata

namespace Strata.Python.Issue1000

/-! ## Test: Procedure call inside negated if-condition (Issue #1000)

Verifies that calling a procedure inside `not` in an `if` condition
does not produce a spurious "calls to procedures are not supported
in functions or contracts" error. The exception-check assert generated
by the Python pipeline must have its procedure calls lifted out by the
LiftExpressionAssignments pass.
-/

-- Minimal reproduction from issue #1000.
#guard_msgs in
#eval withPython fun pythonCmd => do
  let program :=
"def ensure_exists() -> bool:
    return True

def main() -> None:
    if not ensure_exists():
        return
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  for d in diags do
    if stringContains d.message "calls to procedures are not supported" then
      throw <| .userError s!"Unexpected error: {d.message}"

end Strata.Python.Issue1000
