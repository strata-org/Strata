/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Python.TestExamples
import StrataTest.Util.TestDiagnostics
import Strata.DDM.Parser

/-! ## Test: Inline Python verification via processPythonFile

Verifies that `processPythonFile` correctly runs the full
Python → Laurel → Core → SMT pipeline and produces diagnostics.
-/

namespace Strata.Python.VerifyPythonTest

open StrataTest.Util
open Strata.Python (processPythonFile withPython)
open Strata.Parser (stringInputContext)

-- Passing assertions produce no diagnostics.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def main() -> None:
    x: int = 5
    y: int = 10
    assert x == 5
    assert y == 10
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size ≠ 0 then
    throw <| .userError s!"Expected 0 diagnostics, got {diags.size}"

-- Failing assertion produces a diagnostic with the expected message.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def main() -> None:
    x: int = 5
    assert x == 6
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  unless diags.any (·.message == "assertion could not be proved") do
    throw <| .userError s!"Expected 'assertion could not be proved', got: {diags.map (·.message)}"

-- Mix of passing and failing assertions: only failing ones produce diagnostics.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def main() -> None:
    x: int = 5
    assert x == 5
    assert x == 6
    assert x == 7
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  -- x == 6 and x == 7 should fail; x == 5 should pass
  if diags.size ≠ 2 then
    throw <| .userError s!"Expected 2 diagnostics, got {diags.size}: {diags.map (·.message)}"

-- Diagnostic line numbers point to the correct assertion.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def main() -> None:
    x: int = 5
    assert x == 5
    assert x == 6
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  match diags.find? (·.message == "assertion could not be proved") with
  | some d =>
    -- "assert x == 6" is on line 4
    if d.start.line ≠ 4 then
      throw <| .userError s!"Expected diagnostic on line 4, got line {d.start.line}"
  | none =>
    throw <| .userError s!"Expected a failing diagnostic"

-- Annotated-style test using testInputWithOffset and # comment expectations.
-- testInputWithOffset prints on success; we validate silently here instead.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def main() -> None:
    x: int = 5
    assert x == 5
    assert x == 6
#   ^^^^^^^^^^^^^ error: assertion could not be proved
"
  let inputContext := stringInputContext "AnnotatedPython" program
  let expectations := parseDiagnosticExpectations program
  let expectedErrors := expectations.filter (fun e => e.level == "error")
  let diagnostics ← processPythonFile pythonCmd inputContext
  for exp in expectedErrors do
    unless diagnostics.any (fun d => matchesDiagnostic d exp) do
      throw <| .userError s!"Unmatched expectation: line {exp.line}, {exp.message}"
  for d in diagnostics do
    unless expectedErrors.any (fun exp => matchesDiagnostic d exp) do
      throw <| .userError s!"Unexpected diagnostic: line {d.start.line}, {d.message}"

-- Multiple `with` blocks reusing the same variable name should not crash.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def main(path1: str, path2: str) -> None:
    with open(path1, 'w') as f:
        f.write('hello')
    with open(path2, 'w') as f:
        f.write('world')
"
  let _diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  pure ()

-- Try/except with str(e) on PythonError should not produce type checking errors.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def handle_error() -> bool:
    try:
        x: int = 1
    except Exception as e:
        if 'key' in str(e):
            return True
    return False
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test_try_except.py" program)
  if diags.size ≠ 0 then
    throw <| .userError s!"Expected 0 diagnostics, got {diags.size}"

-- Multi-output prelude procedures: timedelta_func returns (delta: Any, maybe_except: Error).
-- This tests that withException detects the multi-output signature and generates
-- a 2-target assignment, and that computeExprType returns Unknown (→ Any in Core).
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"from datetime import datetime, timedelta

def main() -> None:
    now: datetime = datetime.now()
    delta: timedelta = timedelta(days=7)
    start: datetime = now - delta
    assert start <= now
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size ≠ 0 then
    throw <| .userError s!"Expected 0 diagnostics, got {diags.size}: {diags.map (·.message)}"

-- Returning a Composite-typed value from a function with Any return type
-- should not crash; the Composite is replaced with a Hole (unconstrained value).
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"from typing import Any

class MyService:
    name: str

    def __init__(self, name: str) -> None:
        self.name = name

def create_service() -> Any:
    svc: MyService = MyService(\"test\")
    return svc
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size ≠ 0 then
    throw <| .userError s!"Expected 0 diagnostics, got {diags.size}"

end Strata.Python.VerifyPythonTest
