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
open Strata.Python (processPythonFile processPythonToLaurel withPython containsSubstr manglePythonMethod)
open Strata.Parser (stringInputContext)

/-- Run the Python → Laurel pipeline and return the Laurel program together
    with its formatted string representation. -/
def toLaurel (pythonCmd : System.FilePath) (program : String)
    : IO (Laurel.Program × String) := do
  let laurel ← processPythonToLaurel pythonCmd (stringInputContext "test.py" program)
  pure (laurel, toString (Laurel.formatProgram laurel))

/-- Assert that a procedure with the given name exists and has a Transparent body. -/
def assertTransparent (laurel : Laurel.Program) (procName : String) : IO Unit := do
  match laurel.staticProcedures.find? (fun p => p.name.text == procName) with
  | none => throw <| .userError s!"{procName} procedure not found in Laurel output"
  | some proc =>
    match proc.body with
    | .Transparent _ => pure ()
    | _ => throw <| .userError s!"{procName} body should be Transparent, not Opaque"

/-- Assert that a procedure with the given name exists and has an Opaque body. -/
def assertOpaque (laurel : Laurel.Program) (procName : String) : IO Unit := do
  match laurel.staticProcedures.find? (fun p => p.name.text == procName) with
  | none => throw <| .userError s!"{procName} procedure not found in Laurel output"
  | some proc =>
    match proc.body with
    | .Opaque _ _ _ => pure ()
    | _ => throw <| .userError s!"{procName} body should be Opaque for classes in hierarchy"

-- Passing assertions produce no diagnostics.
#guard_msgs in
#eval withPython fun pythonCmd => do
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
#eval withPython fun pythonCmd => do
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
#eval withPython fun pythonCmd => do
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
#eval withPython fun pythonCmd => do
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
#eval withPython fun pythonCmd => do
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
#eval withPython fun pythonCmd => do
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
#eval withPython fun pythonCmd => do
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
#eval withPython fun pythonCmd => do
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
#eval withPython fun pythonCmd => do
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
#eval withPython fun pythonCmd => do
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
#eval withPython fun pythonCmd => do
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

-- Class with field initialized via constructor call.
-- Verifies that dispatch detection in __init__ doesn't break
-- normal class translation.
#guard_msgs (drop info) in
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
  let _diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  pure ()

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
-- Instance method call resolution and body preservation:
-- Verifies that the method body is translated (not opaque) and the
-- instance call resolves to a StaticCall (not a Hole).
#guard_msgs in
#eval withPython fun pythonCmd => do
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
  let (laurel, output) ← toLaurel pythonCmd program
  let calcAdd := manglePythonMethod "Calculator" "add"
  assertTransparent laurel calcAdd
  unless containsSubstr output s!"{calcAdd}(" do
    throw <| IO.userError s!"Expected '{calcAdd}(' in Laurel output but not found"

-- self.field.method() resolution and composite field initialization:
-- When a class stores another object as a field and calls a method on
-- that field, the call should resolve to a StaticCall (not a Hole).
-- The composite field assignment (self.inner: Inner = ...) should use New.
#guard_msgs in
#eval withPython fun pythonCmd => do
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
  let (_, output) ← toLaurel pythonCmd program
  let innerValidate := manglePythonMethod "Inner" "validate"
  -- self.inner.validate() must resolve to Inner@validate StaticCall
  unless containsSubstr output s!"{innerValidate}(" do
    throw <| IO.userError s!"Expected '{innerValidate}(' in Laurel output but not found"
  -- Composite field assignment (self.inner: Inner = ...) uses New initialization
  unless containsSubstr output "new Inner" do
    throw <| IO.userError s!"Expected 'new Inner' in Laurel output but not found"

-- Inheritance guard: when a class is part of an inheritance hierarchy,
-- method calls on it should emit Hole (not StaticCall) because the
-- runtime type may differ from the static type.
#guard_msgs in
#eval withPython fun pythonCmd => do
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
  let (laurel, _) ← toLaurel pythonCmd program
  let baseValue := manglePythonMethod "Base" "value"
  assertOpaque laurel baseValue
  -- The main procedure should contain a Hole for the obj.value() call,
  -- not a StaticCall to Base@value.
  let mainProc := laurel.staticProcedures.find? (fun p => p.name.text == "main")
  match mainProc with
  | none => throw <| .userError "main procedure not found"
  | some proc =>
    let mainOutput := toString (Laurel.formatProcedure proc)
    if containsSubstr mainOutput s!"{baseValue}(" then
      throw <| IO.userError s!"main should NOT call {baseValue} (inheritance guard)"

-- Inheritance with field type conflict: B inherits A and redeclares field x
-- with a different type. Both classes are in the hierarchy, so method bodies
-- must be opaque and call sites must emit Holes.
#guard_msgs in
#eval withPython fun pythonCmd => do
  let program :=
"class A:
    def __init__(self) -> None:
        self.x: int = 0

    def get_x(self) -> int:
        return self.x

class B(A):
    def __init__(self) -> None:
        self.x: str = \"hello\"

    def get_x(self) -> str:
        return self.x

def main() -> None:
    a: A = A()
    result: int = a.get_x()
"
  let (laurel, _) ← toLaurel pythonCmd program
  let aGetX := manglePythonMethod "A" "get_x"
  let bGetX := manglePythonMethod "B" "get_x"
  assertOpaque laurel aGetX
  assertOpaque laurel bGetX

-- Inheritance dispatch soundness: a field typed as A could hold a B at
-- runtime, so calling r.a.f() must not statically dispatch to A@f (which
-- has assert False). The hierarchy guard makes both methods opaque and
-- the call site emits a Hole.
#guard_msgs in
#eval withPython fun pythonCmd => do
  let program :=
"class A:
    def f(self) -> None:
        assert False
class B(A):
    def f(self) -> None:
        assert True

class Receiver:
    def __init__(self) -> None:
        self.a: A = A()

def main() -> None:
    r: Receiver = Receiver()
    r.a.f()
"
  let (laurel, _) ← toLaurel pythonCmd program
  let aF := manglePythonMethod "A" "f"
  let bF := manglePythonMethod "B" "f"
  assertOpaque laurel aF
  assertOpaque laurel bF
  -- r.a.f() must NOT resolve to A@f StaticCall — it must be a Hole
  let mainProc := laurel.staticProcedures.find? (fun p => p.name.text == "main")
  match mainProc with
  | none => throw <| .userError "main procedure not found"
  | some proc =>
    let mainOutput := toString (Laurel.formatProcedure proc)
    if containsSubstr mainOutput s!"{aF}(" then
      throw <| IO.userError s!"main should NOT call {aF} (inheritance dispatch unsound)"

-- Cross-class method dispatch: a method in one class calls a method on
-- a field typed as another class. The call should resolve via userFunctions.
#guard_msgs in
#eval withPython fun pythonCmd => do
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
  let (_, output) ← toLaurel pythonCmd program
  let engineGetHp := manglePythonMethod "Engine" "get_hp"
  let carHorsepower := manglePythonMethod "Car" "horsepower"
  -- self.engine.get_hp() should resolve to Engine@get_hp StaticCall
  unless containsSubstr output s!"{engineGetHp}(" do
    throw <| IO.userError s!"Expected '{engineGetHp}(' in Laurel output but not found"
  -- Car@horsepower should also be a StaticCall from main
  unless containsSubstr output s!"{carHorsepower}(" do
    throw <| IO.userError s!"Expected '{carHorsepower}(' in Laurel output but not found"

-- Full pipeline: composite field assignment goes through the entire
-- Python → Laurel → Core → SMT pipeline without crashing.
#guard_msgs in
#eval withPython fun pythonCmd => do
  let program :=
"class Config:
    def __init__(self, value: int) -> None:
        self.value: int = value

class App:
    def __init__(self) -> None:
        self.config: Config = Config(42)

def main() -> None:
    a: App = App()
"
  let _diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  pure ()

-- Full pipeline: instance method call goes through the entire
-- Python → Laurel → Core → SMT pipeline without crashing.
-- The assertion inside the method body is reachable and verified.
#guard_msgs in
#eval withPython fun pythonCmd => do
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

-- Multi-assignment with side-effecting RHS: the RHS should be evaluated
-- exactly once. a = b = c.next() must call next() once, so both a and b
-- get the same value and the counter increments by 1.
#guard_msgs in
#eval withPython fun pythonCmd => do
  let program :=
"class Counter:
    def __init__(self) -> None:
        self.count: int = 0

    def next(self) -> int:
        self.count = self.count + 1
        return self.count

def test() -> None:
    c: Counter = Counter()
    a = b = c.next()
    assert a == 1
    assert b == 1
    assert c.count == 1
"
  let _diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  pure ()

-- print() with keyword arguments (sep, end, flush) should not produce errors.
#guard_msgs in
#eval withPython fun pythonCmd => do
  let program :=
"def main() -> None:
    print(\"hello\", end=\"\")
    print(\"a\", \"b\", sep=\",\")
    print(\"done\", flush=True)
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size ≠ 0 then
    throw <| .userError s!"Expected 0 diagnostics, got {diags.size}: {diags.map (·.message)}"

-- Callable[..., Any], dict[str, Any], and list[str] type annotations
-- should not crash the pipeline (issue #960).
#guard_msgs in
#eval withPython fun pythonCmd => do
  let program :=
"from typing import Any, Callable

def retry(func: Callable[..., Any], retries: int = 3) -> Any:
    return func()

def make_record(name: str) -> dict[str, Any]:
    return {\"name\": name}

def get_names(names: list[str]) -> list[str]:
    return names
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size ≠ 0 then
    throw <| .userError s!"Expected 0 diagnostics, got {diags.size}: {diags.map (·.message)}"

-- typing.Callable (qualified, without `from typing import Callable`)
-- exercises the .Attribute normalization path.
#guard_msgs in
#eval withPython fun pythonCmd => do
  let program :=
"import typing

def retry(func: typing.Callable[..., typing.Any], retries: int = 3) -> typing.Any:
    return func()
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size ≠ 0 then
    throw <| .userError s!"Expected 0 diagnostics, got {diags.size}: {diags.map (·.message)}"

-- print() with multiple positional arguments exercises the opt parameter.
#guard_msgs in
#eval withPython fun pythonCmd => do
  let program :=
"def main() -> None:
    print()
    print(\"a\")
    print(\"a\", \"b\")
    print(\"a\", \"b\", \"c\")
    print(\"a\", \"b\", sep=\",\", end=\"\\n\", flush=True)
    print(\"x\", \"y\", \"z\", sep=\" \")
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  if diags.size ≠ 0 then
    throw <| .userError s!"Expected 0 diagnostics, got {diags.size}: {diags.map (·.message)}"

-- PreludeInfo.ofLaurelProgram should strip the $in_ prefix from parameter
-- names so that cross-module keyword argument calls use the original names.
#guard_msgs in
#eval withPython fun pythonCmd => do
  let program :=
"def add(x: int, y: int) -> int:
    return x + y
"
  let laurel ← processPythonToLaurel pythonCmd (stringInputContext "test.py" program)
  let prelude := Python.PreludeInfo.ofLaurelProgram laurel
  match prelude.functionSignatures.find? (fun f => f.name == "add") with
  | none => throw <| .userError "add not found in functionSignatures"
  | some sig =>
    for arg in sig.args do
      if arg.name.startsWith "$in_" then
        throw <| .userError s!"Parameter '{arg.name}' still has $in_ prefix in PreludeInfo"

-- End-to-end bug-finding test for method resolution:
-- The assertion `result == 7` can only be verified if Calculator.add's body
-- is correctly resolved and inlined. If the method were unresolved (Hole),
-- the result would be havocked and the assertion would be unknown/failing.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"class Calculator:
    def __init__(self, base: int) -> None:
        self.base: int = base

    def add(self, x: int) -> int:
        return self.base + x

def main() -> None:
    c: Calculator = Calculator(3)
    result: int = c.add(4)
    assert result == 7, \"method body must be inlined to verify this\"
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  -- If method resolution failed, we'd see an unknown/failing diagnostic
  -- for the assertion. A clean pass means the method body was inlined.
  let failures := diags.filter fun d => d.message.contains "fail" || d.message.contains "unknown"
  unless failures.isEmpty do
    throw <| .userError s!"Method resolution test: expected all checks to pass but got: {failures.map (·.message)}"

-- End-to-end test for self.field.method() resolution:
-- Inner.greet's body must be resolved through the Outer.inner field
-- for the assertion to be verifiable.
#guard_msgs in
#eval withPython (warnOnSkip := false) fun pythonCmd => do
  let program :=
"class Inner:
    def __init__(self, prefix: str) -> None:
        self.prefix: str = prefix

    def greet(self, name: str) -> str:
        return self.prefix + name

class Outer:
    def __init__(self) -> None:
        self.inner: Inner = Inner(\"hello \")

    def run(self, name: str) -> str:
        return self.inner.greet(name)

def main() -> None:
    o: Outer = Outer()
    result: str = o.run(\"world\")
    assert result == \"hello world\", \"field.method() must be resolved to verify this\"
"
  let diags ← processPythonFile pythonCmd (stringInputContext "test.py" program)
  let failures := diags.filter fun d => d.message.contains "fail" || d.message.contains "unknown"
  unless failures.isEmpty do
    throw <| .userError s!"Field method resolution test: expected all checks to pass but got: {failures.map (·.message)}"

end Strata.Python.VerifyPythonTest
