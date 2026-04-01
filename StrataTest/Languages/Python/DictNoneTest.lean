/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Python.TestExamples
import StrataTest.Util.TestDiagnostics
import StrataTest.Util.Python

/-! ## Tests: None-for-typed-parameter detection

In Python, passing `None` where a typed parameter (str, int, etc.) is
expected is a common bug pattern. For example:

    config = {"DBSubnetGroupName": None}
    rds.create_db_instance(**config)

The API expects a string but receives None, causing a runtime error.
These tests verify that the pipeline detects such mismatches.
-/

namespace Strata.Python.DictNoneTest

open Strata.Python (processPythonFile withPython)
open Strata.Parser (stringInputContext)

-- Test 1: Using a valid int should succeed.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def main() -> None:
    x: int = 5
    assert x == 5
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size ≠ 0 then
    throw <| .userError s!"Expected 0 diagnostics, got {diags.size}: {diags.map (·.message)}"

-- Test 2: Assigning None to an int variable and asserting a concrete value.
-- The assertion `x == 5` correctly fails because x is None, not 5.
-- This demonstrates that None values DO flow through the pipeline and
-- can be detected by assertions that depend on the value.
/--
info: DictNoneTest.2: got 1 diagnostics — correctly detected None ≠ 5
-/
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def main() -> None:
    x: int = None
    assert x == 5
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size ≥ 1 then
    IO.eprintln s!"DictNoneTest.2: got {diags.size} diagnostics — correctly detected None ≠ 5"
  else
    throw <| .userError s!"Expected ≥1 diagnostic for None-as-int, got 0"

-- Test 3: Assigning None to an int variable WITHOUT a value-dependent assertion.
-- The type annotation `x: int = None` is not enforced — None flows through.
-- This is the gap: there's no automatic type check at the assignment site.
/--
info: DictNoneTest.3: got 0 diagnostics — None-for-int NOT detected without value assertion
-/
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def main() -> None:
    x: int = None
    y: int = 10
    assert y == 10
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  IO.eprintln s!"DictNoneTest.3: got {diags.size} diagnostics — None-for-int NOT detected without value assertion"

end Strata.Python.DictNoneTest
