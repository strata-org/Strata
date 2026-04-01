/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Python.TestExamples
import StrataTest.Util.TestDiagnostics
import StrataTest.Util.Python

/-! ## Tests: None-for-typed-parameter detection

These tests verify that passing `None` where a typed parameter is expected
is correctly detected as a bug, both for direct assignments and dict unpacking.
-/

namespace Strata.Python.DictNoneTest

open Strata.Python (processPythonFile withPython)
open Strata.Parser (stringInputContext)

-- Test 1: Using a valid int should succeed.
#guard_msgs (drop info) in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def main() -> None:
    x: int = 5
    assert x == 5
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size ≠ 0 then
    throw <| .userError s!"Expected 0 diagnostics, got {diags.size}: {diags.map (·.message)}"

-- Test 2: Assigning None to an int variable with a value-dependent assertion.
#guard_msgs (drop info) in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def main() -> None:
    x: int = None
    assert x == 5
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size == 0 then
    throw <| .userError s!"Expected ≥1 diagnostic for None-as-int, got 0"

-- Test 3: x: int = None without value assertion — type assertion catches it.
#guard_msgs (drop info) in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def main() -> None:
    x: int = None
    y: int = 10
    assert y == 10
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size == 0 then
    throw <| .userError s!"Expected ≥1 diagnostic for None-for-int, got 0"

-- Test 4: Dict unpacking with None for typed parameter.
-- f(x: int) called via **{"x": None} detected at call site.
#guard_msgs (drop info) in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def f(x: int) -> None:
    y: int = x + 1

def main() -> None:
    d: dict[str, Any] = {\"x\": None}
    f(**d)
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size == 0 then
    throw <| .userError s!"Expected ≥1 diagnostic for dict-unpacking None-for-int, got 0"

-- Test 5: Negative list indexing on potentially empty list.
-- xs[-1] emits a bounds check: assert len(xs) >= 1.
#guard_msgs (drop info) in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def main() -> None:
    xs: list[Any] = []
    x: Any = xs[-1]
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size == 0 then
    throw <| .userError s!"Expected ≥1 diagnostic for negative indexing on empty list, got 0"

-- Test 6: len() on a class instance without __len__.
-- This should be rejected as a user error.
#guard_msgs (drop info) in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"class MyObj:
    name: str
    def __init__(self, name: str) -> None:
        self.name = name

def main() -> None:
    obj: MyObj = MyObj(\"test\")
    n: int = len(obj)
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size == 0 then
    throw <| .userError s!"Expected ≥1 diagnostic for len() on non-iterable, got 0"

-- Test 5: Calling a function with a misspelled keyword argument name.
-- The function signature has "name" but the call uses "nme".
-- This is caught as a user error during translation.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def f(name: str) -> None:
    pass

def main() -> None:
    f(nme=\"hello\")
"
  match ← processPythonFile pythonCmd (stringInputContext "test.py" program) |>.toBaseIO with
  | .ok diags =>
    if diags.size == 0 then
      throw <| .userError "Expected error for misspelled kwarg, got success"
  | .error _ => pure ()  -- Expected: translation error for unknown kwarg

end Strata.Python.DictNoneTest
