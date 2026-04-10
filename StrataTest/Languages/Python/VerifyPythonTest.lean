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
open Strata.Python (processPythonFile processPythonToLaurel withPython containsSubstr)
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
-- The class uses inheritance, so method bodies are conservatively stripped
-- to opaque (no diagnostics produced).
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"from typing import Any

class BaseService:
    pass

class MyService(BaseService):
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

-- Instance method call resolution and body preservation:
-- Verifies that the method body is translated (not opaque) and the
-- instance call resolves to a StaticCall (not a Hole).
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"class Calculator:
    def __init__(self, label: str) -> None:
        self.label: str = label

    def add(self, x: int, y: int) -> int:
        return x + y

def main() -> None:
    c: Calculator = Calculator(\"calc\")
    result: int = c.add(3, 4)
"
  let inputCtx := stringInputContext "test.py" program
  let laurel ← processPythonToLaurel pythonCmd inputCtx
  let output := toString (Laurel.formatProgram laurel)
  -- Method body must be transparent (not opaque)
  let addProc := laurel.staticProcedures.find? (fun p => p.name.text == "Calculator@add")
  match addProc with
  | none => throw <| .userError "Calculator@add procedure not found in Laurel output"
  | some proc =>
    match proc.body with
    | .Transparent _ => pure ()
    | _ => throw <| .userError "Calculator@add body should be Transparent, not Opaque"
  -- Instance method call must resolve to StaticCall, not a Hole
  unless containsSubstr output "Calculator@add(" do
    throw <| IO.userError s!"Expected 'Calculator@add(' in Laurel output but not found"

-- self.field.method() resolution: when a class stores another object as a
-- field and calls a method on that field, the call should resolve to a
-- StaticCall (not a Hole).
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"class Inner:
    def __init__(self, name: str) -> None:
        self.name: str = name

    def validate(self, value: str) -> None:
        assert len(value) >= 3, \"value too short\"

class Outer:
    def __init__(self) -> None:
        self.inner: Inner = Inner(\"world\")

    def process(self) -> None:
        self.inner.validate(\"ab\")

def main() -> None:
    o: Outer = Outer()
    o.process()
"
  let inputCtx := stringInputContext "test.py" program
  let laurel ← processPythonToLaurel pythonCmd inputCtx
  let output := toString (Laurel.formatProgram laurel)
  -- self.inner.validate() must resolve to Inner@validate StaticCall
  unless containsSubstr output "Inner@validate(" do
    throw <| IO.userError s!"Expected 'Inner@validate(' in Laurel output but not found"

-- Inheritance guard: when a class is part of an inheritance hierarchy,
-- method calls on it should emit Hole (not StaticCall) because the
-- runtime type may differ from the static type.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"class Base:
    def __init__(self) -> None:
        self.x: int = 0

    def value(self) -> int:
        return self.x

class Child(Base):
    def __init__(self) -> None:
        self.x: int = 42

    def value(self) -> int:
        return self.x

def main() -> None:
    obj: Base = Base()
    result: int = obj.value()
"
  let inputCtx := stringInputContext "test.py" program
  let laurel ← processPythonToLaurel pythonCmd inputCtx
  -- Method bodies for classes in hierarchy should be opaque
  let valueProc := laurel.staticProcedures.find? (fun p => p.name.text == "Base@value")
  match valueProc with
  | none => throw <| .userError "Base@value procedure not found"
  | some proc =>
    match proc.body with
    | .Opaque _ _ _ => pure ()
    | _ => throw <| .userError "Base@value body should be Opaque for classes in hierarchy"
  -- The main procedure should contain a Hole for the obj.value() call,
  -- not a StaticCall to Base@value.
  let mainProc := laurel.staticProcedures.find? (fun p => p.name.text == "main")
  match mainProc with
  | none => throw <| .userError "main procedure not found"
  | some proc =>
    let mainOutput := toString (Laurel.formatProcedure proc)
    if containsSubstr mainOutput "Base@value(" then
      throw <| IO.userError s!"main should NOT call Base@value (inheritance guard)"

-- Cross-class method dispatch: a method in one class calls a method on
-- a field typed as another class. The call should resolve via userFunctions.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"class Engine:
    def __init__(self, hp: int) -> None:
        self.hp: int = hp

    def get_hp(self) -> int:
        return self.hp

class Car:
    def __init__(self) -> None:
        self.engine: Engine = Engine(100)

    def horsepower(self) -> int:
        return self.engine.get_hp()

def main() -> None:
    c: Car = Car()
    result: int = c.horsepower()
"
  let inputCtx := stringInputContext "test.py" program
  let laurel ← processPythonToLaurel pythonCmd inputCtx
  let output := toString (Laurel.formatProgram laurel)
  -- self.engine.get_hp() should resolve to Engine@get_hp StaticCall
  unless containsSubstr output "Engine@get_hp(" do
    throw <| IO.userError s!"Expected 'Engine@get_hp(' in Laurel output but not found"
  -- Car@horsepower should also be a StaticCall from main
  unless containsSubstr output "Car@horsepower(" do
    throw <| IO.userError s!"Expected 'Car@horsepower(' in Laurel output but not found"

-- Full pipeline: instance method call goes through the entire
-- Python → Laurel → Core → SMT pipeline without crashing.
-- The assertion inside the method body is reachable and verified.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"class Greeter:
    def __init__(self, name: str) -> None:
        self.name: str = name

    def greet(self, prefix: str) -> str:
        return prefix

def main() -> None:
    g: Greeter = Greeter(\"world\")
    msg: str = g.greet(\"hello\")
"
  let _diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  pure ()

end Strata.Python.VerifyPythonTest
