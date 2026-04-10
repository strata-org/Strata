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
open Strata.Python (processPythonFile withPython containsSubstr)
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

-- datetime.now() with optional tz parameter and timedelta arithmetic.
-- Also exercises multi-output prelude procedure detection (timedelta_func
-- returns (delta: Any, maybe_except: Error)).
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"from datetime import datetime, timedelta

def main() -> None:
    now: datetime = datetime.now(None)
    delta: timedelta = timedelta(days=7)
    start: datetime = now - delta
    assert start <= now
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size ≠ 0 then
    throw <| .userError s!"Expected 0 diagnostics, got {diags.size}: {diags.map (·.message)}"

-- Calling a user-defined function with too many positional args should error.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def greet(name: str) -> str:
    return name

def main() -> None:
    x: str = greet(\"alice\", \"extra\")
"
  try
    let _ ← processPythonFile pythonCmd (stringInputContext "test.py" program)
    throw <| IO.userError "Expected pipeline error for too many positional arguments"
  catch e =>
    let msg := toString e
    unless containsSubstr msg "too many positional arguments" do
      throw <| IO.userError s!"Expected 'too many positional arguments' error, got: {msg}"

-- Extra positional args with **kwargs expansion should also error.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"def greet(name: str) -> str:
    return name

def main() -> None:
    d: dict = {}
    x: str = greet(\"alice\", \"extra\", **d)
"
  try
    let _ ← processPythonFile pythonCmd (stringInputContext "test.py" program)
    throw <| IO.userError "Expected pipeline error for too many positional arguments"
  catch e =>
    let msg := toString e
    unless containsSubstr msg "too many positional arguments" do
      throw <| IO.userError s!"Expected 'too many positional arguments' error, got: {msg}"

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

-- Class with field initialized via constructor call.
-- Verifies that dispatch detection in __init__ doesn't break
-- normal class translation.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"class Wrapper:
    name: str
    def __init__(self, name: str) -> None:
        self.name = name
    def greet(self) -> str:
        return self.name

def main() -> None:
    w: Wrapper = Wrapper(\"test\")
    r: str = w.greet()
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size ≠ 0 then
    throw <| .userError s!"Expected 0 diagnostics, got {diags.size}"

-- Regression test: class with self.field = Constructor() translates without crashing.
-- Verifies that field method calls on user-defined classes don't cause
-- "Coercion to Any not supported" or other translation errors.
#guard_msgs (drop info) in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"class Svc:
    name: str
    def __init__(self) -> None:
        self.name = \"x\"
    def do_thing(self, val: str) -> None:
        pass

class Wrapper:
    svc: Svc
    def __init__(self) -> None:
        self.svc = Svc()
    def run(self) -> None:
        self.svc.do_thing(val=\"hello\")

def main() -> None:
    w: Wrapper = Wrapper()
    w.run()
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  -- Translation should succeed without coercion errors
  for d in diags do
    if d.message.contains "Coercion to Any not supported" then
      throw (IO.userError s!"Unexpected coercion error: {d.message}")
  -- Log diagnostic count for visibility; fail if unexpectedly many
  if diags.size > 10 then
    throw (IO.userError s!"Unexpected number of diagnostics: {diags.size}: {diags.map (·.message)}")

-- Dispatch detection inside try/except in __init__.
-- self.svc = Svc() inside a try block should still be detected.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"class Svc:
    name: str
    def __init__(self) -> None:
        self.name = \"x\"
    def do_thing(self, val: str) -> None:
        pass

class Wrapper:
    svc: Svc
    def __init__(self) -> None:
        try:
            self.svc = Svc()
        except:
            pass
    def run(self) -> None:
        self.svc.do_thing(val=\"hello\")

def main() -> None:
    w: Wrapper = Wrapper()
    w.run()
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  for d in diags do
    if d.message.contains "Coercion to Any not supported" then
      throw (IO.userError s!"Unexpected coercion error in try/except dispatch: {d.message}")

end Strata.Python.VerifyPythonTest
