/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPython.Specs
meta import all StrataPython.Specs.DDM
meta import StrataPython.PythonDialect
meta import StrataPythonTest.Util.Python

open StrataDDM (SourceRange)
open StrataPython
open StrataPython.Specs

meta section
def testDir : System.FilePath := "StrataPythonTestExtra/Specs"

def expectedPySpec :=
#strata
program PythonSpecs;
extern "BaseClass" from "basetypes.BaseClass";
function "dict_function" {
  args: [
    x : ident("typing.Dict", ident("builtins.int"), ident("typing.Any")) [default: ]
  ]
  kwonly: [
  ]
  return: ident("typing.Any")
  overload: false
  preconditions: [
  ]
  postconditions: [
  ]
}
function "list_function" {
  args: [
    x : ident("typing.List", ident("builtins.int")) [default: ]
  ]
  kwonly: [
  ]
  return: ident("typing.Any")
  overload: false
  preconditions: [
  ]
  postconditions: [
  ]
}
function "sequence_function" {
  args: [
    x : ident("typing.Sequence", ident("builtins.int")) [default: ]
  ]
  kwonly: [
  ]
  return: ident("typing.Any")
  overload: false
  preconditions: [
  ]
  postconditions: [
  ]
}
function "base_function"{
  args: [
    x : ident("basetypes.BaseClass") [default: ]
  ]
  kwonly: [
  ]
  return: ident("typing.Any")
  overload: false
  preconditions: [
  ]
  postconditions: [
  ]
}
class "MainClass" {
  bases: []
  fields: []
  classVars: []
  subclasses: []
  exhaustive: false
  function "main_method"{
    args: [
      self : ident("main.MainClass") [default: ]
      x : ident("basetypes.BaseClass") [default: ]
    ]
    kwonly: [
    ]
    return: ident("typing.Any")
    overload: false
    preconditions: [
    ]
    postconditions: [
    ]
  }
}
function "main_function"{
  args: [
    x : ident("main.MainClass") [default: ]
  ]
  kwonly: [
  ]
  return: ident("typing.Any")
  overload: false
  preconditions: [
  ]
  postconditions: [
  ]
}
function "kwargs_function"{
  args: [
  ]
  kwonly: [
  ]
  kwargs: kw : ident("builtins.int")
  return: ident("typing.Any")
  overload: false
  preconditions: [
    ensure(isinstance(kw[name], "str"), "Expected name to be str")
    ensure(kw[count] >=_int 1, "Expected count >= 1")
  ]
  postconditions: [
  ]
}
type "TestRequest" = dict(
  Name : ident("builtins.str") [required=true]
  Items : ident("typing.List", ident("builtins.str")) [required=false]
  Tags : ident("typing.Mapping", ident("builtins.str"), ident("builtins.str")) [required=false]
)
function "fstring_and_regex"{
  args: [
  ]
  kwonly: [
  ]
  kwargs: params : dict(
    Name : ident("builtins.str") [required=true]
    Items : ident("typing.List", ident("builtins.str")) [required=false]
    Tags : ident("typing.Mapping", ident("builtins.str"), ident("builtins.str")) [required=false]
  )
  return: ident("_types.NoneType")
  overload: false
  preconditions: [
    ensure(stringLen(params[Name]) >=_int 1, "Expected len(params[\"Name\"]) >= 1, got "{stringLen(params[Name])})
    ensure(stringLen(params[Name]) <=_int 100, "Expected len(params[\"Name\"]) <= 100, got "{stringLen(params[Name])})
    ensure(regex(params[Name], "^[a-zA-Z]+$"), "params[\"Name\"] did not match pattern")
    ensure(Items in params => forall(params[Items], item, stringLen(item) >=_int 1), "Expected len(item) >= 1, got "{stringLen(item)})
    ensure(Items in params => forall(params[Items], item, stringLen(item) <=_int 50), "Expected len(item) <= 50, got "{stringLen(item)})
    ensure(Tags in params => forallDict(params[Tags], tag_key, tag_val, stringLen(tag_key) >=_int 1), "Expected len(tag_key) >= 1, got "{stringLen(tag_key)})
  ]
  postconditions: [
  ]
}
type "FloatRequest" = dict(
  SampleSize : ident("builtins.float") [required=false]
  Score : ident("builtins.float") [required=false]
  Count : ident("builtins.int") [required=false]
)
function "float_and_negative_bounds"{
  args: [
  ]
  kwonly: [
  ]
  kwargs: fp : dict(
    SampleSize : ident("builtins.float") [required=false]
    Score : ident("builtins.float") [required=false]
    Count : ident("builtins.int") [required=false]
  )
  return: ident("_types.NoneType")
  overload: false
  preconditions: [
    ensure(Score in fp => fp[Score] >=_float "0.0", "Expected Score >= 0.0")
    ensure(Score in fp => fp[Score] <=_float "1.0", "Expected Score <= 1.0")
    ensure(not(Score in fp) => fp[SampleSize] >=_float "0", "Expected SampleSize >= 0 when no Score")
    ensure(SampleSize in fp => fp[SampleSize] >=_float "0", "Expected SampleSize >= 0")
    ensure(Score in fp => fp[Score] >=_float "-0.5", "Expected Score >= -0.5")
    ensure(Count in fp => fp[Count] >=_int -1, "Expected Count >= -1")
  ]
  postconditions: [
  ]
}
class "InnerHelper" {
  bases: []
  fields: []
  classVars: []
  subclasses: []
  exhaustive: false
}
class "ClassWithInit" {
  bases: []
  fields: [
    helper : ident("main._InnerHelper") "_InnerHelper()"
  ]
  classVars: []
  subclasses: [
    class "_InnerHelper" {
      bases: ["main.InnerHelper"]
      fields: []
      classVars: []
      subclasses: []
      exhaustive: false
      function "do_work"{
        args: [
          self : ident("main._InnerHelper") [default: ]
        ]
        kwonly: [
        ]
        return: ident("_types.NoneType")
        overload: false
        preconditions: [
        ]
        postconditions: [
        ]
      }
    }
  ]
  exhaustive: false
}
#end

meta def testCase : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "main.py")
          (searchPath := testDir)
          (.ofComponent (.ofString "main"))
          |>.toBaseIO
      match r with
      | .ok (sigs, warnings) =>
        let pgm := toDDMProgram sigs
        let pgmCommands := pgm.commands.map (·.mapAnn (fun _ => ()))
        let expCommands := expectedPySpec.commands.map (·.mapAnn (fun _ => ()))
        if pgmCommands != expCommands then
          -- Find first differing command index
          let mut diffMsg := s!"actual has {pgmCommands.size} commands, expected {expCommands.size}"
          for i in [:pgmCommands.size.max expCommands.size] do
            let actual := pgmCommands[i]?
            let expected := expCommands[i]?
            if actual != expected then
              diffMsg := s!"Command {i} differs."
              break
          throw <| IO.userError s!"PySpec output mismatch. {diffMsg}"
        -- from re import compile resolves via prelude without warnings
        if !warnings.isEmpty then
          let warnStr := warnings.foldl (init := "") fun acc w => s!"{acc}\n  {w}"
          throw <| IO.userError s!"Unexpected warnings:{warnStr}"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval testCase

/-- Native `@requires(lambda …: pred)` populates `FunctionDecl.preconditions`. -/
meta def requiresBasicTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "requires_basic.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.requires_basic")
          |>.toBaseIO
      match r with
      | .ok (sigs, _warnings) =>
        let some f := sigs.findSome?
            (fun | .functionDecl d => if d.name == "f" then some d else none | _ => none)
          | throw <| IO.userError "function `f` not found"
        unless f.preconditions.size == 1 do
          throw <| IO.userError
            s!"expected 1 precondition on `f`, got {f.preconditions.size}"
        -- Content must survive: `x >= 0` ⇒ intGe(var x, intLit 0), not a placeholder.
        let expected : SpecExpr := .intGe (.var "x" .none) (.intLit 0 .none) .none
        unless f.preconditions[0]!.formula.softBEq expected do
          throw <| IO.userError "precondition formula did not match `x >= 0`"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval requiresBasicTest

/-- Native `@ensures(lambda result: pred)` populates `FunctionDecl.postconditions`. -/
meta def ensuresBasicTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "ensures_basic.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.ensures_basic")
          |>.toBaseIO
      match r with
      | .ok (sigs, _warnings) =>
        let some f := sigs.findSome?
            (fun | .functionDecl d => if d.name == "f" then some d else none | _ => none)
          | throw <| IO.userError "function `f` not found"
        unless f.postconditions.size == 1 do
          throw <| IO.userError
            s!"expected 1 postcondition on `f`, got {f.postconditions.size}"
        -- `result >= 0` ⇒ intGe(var result, intLit 0).
        let expected : SpecExpr := .intGe (.var "result" .none) (.intLit 0 .none) .none
        unless f.postconditions[0]!.softBEq expected do
          throw <| IO.userError "postcondition formula did not match `result >= 0`"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval ensuresBasicTest

/-- Native `@ghost(name="g")` populates `FunctionDecl.ghosts`. -/
meta def ghostBasicTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "ghost_basic.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.ghost_basic")
          |>.toBaseIO
      match r with
      | .ok (sigs, _warnings) =>
        let some f := sigs.findSome?
            (fun | .functionDecl d => if d.name == "f" then some d else none | _ => none)
          | throw <| IO.userError "function `f` not found"
        unless f.ghosts.size == 1 do
          throw <| IO.userError s!"expected 1 ghost on `f`, got {f.ghosts.size}"
        unless f.ghosts[0]!.name == "g" do
          throw <| IO.userError s!"expected ghost name `g`, got {f.ghosts[0]!.name}"
        -- Declared with only `name=`, so it carries no type/init.
        unless f.ghosts[0]!.type.isNone && f.ghosts[0]!.init.isNone do
          throw <| IO.userError "ghost `g` should have no type= or init="
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval ghostBasicTest

/-- Native `@modifies(lambda …: target)` populates `FunctionDecl.modifies`. -/
meta def modifiesBasicTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "modifies_basic.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.modifies_basic")
          |>.toBaseIO
      match r with
      | .ok (sigs, _warnings) =>
        let some f := sigs.findSome?
            (fun | .functionDecl d => if d.name == "f" then some d else none | _ => none)
          | throw <| IO.userError "function `f` not found"
        unless f.modifies.size == 1 do
          throw <| IO.userError s!"expected 1 modifies target on `f`, got {f.modifies.size}"
        -- `lambda x: x` ⇒ the frame target is the parameter `x`.
        unless f.modifies[0]!.softBEq (.var "x" .none) do
          throw <| IO.userError "modifies target did not match `x`"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval modifiesBasicTest

/-- Native `@invariant(lambda self: pred)` populates `ClassDef.invariants`. -/
meta def invariantBasicTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "invariant_basic.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.invariant_basic")
          |>.toBaseIO
      match r with
      | .ok (sigs, _warnings) =>
        let some c := sigs.findSome?
            (fun | .classDef d => if d.name == "C" then some d else none | _ => none)
          | throw <| IO.userError "class `C` not found"
        unless c.invariants.size == 1 do
          throw <| IO.userError s!"expected 1 invariant on `C`, got {c.invariants.size}"
        -- `self.x >= 0` ⇒ intGe(getIndex(var self, "x"), intLit 0). This must be
        -- the real translated predicate, NOT a content-free placeholder.
        let expected : SpecExpr :=
          .intGe (.getIndex (.var "self" .none) "x" .none) (.intLit 0 .none) .none
        unless c.invariants[0]!.softBEq expected do
          throw <| IO.userError
            "invariant was not translated to `self.x >= 0` (placeholder or mismatch)"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval invariantBasicTest

/-- Native `@snapshot(lambda …: capture, name="v0")` populates
    `FunctionDecl.snapshots` with the named capture. -/
meta def snapshotBasicTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "snapshot_basic.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.snapshot_basic")
          |>.toBaseIO
      match r with
      | .ok (sigs, _warnings) =>
        let some f := sigs.findSome?
            (fun | .functionDecl d => if d.name == "f" then some d else none | _ => none)
          | throw <| IO.userError "function `f` not found"
        unless f.snapshots.size == 1 do
          throw <| IO.userError s!"expected 1 snapshot on `f`, got {f.snapshots.size}"
        unless f.snapshots[0]!.name == "v0" do
          throw <| IO.userError s!"expected snapshot name `v0`, got {f.snapshots[0]!.name}"
        -- `lambda x: x` ⇒ the captured expression is the parameter `x`.
        unless f.snapshots[0]!.capture.softBEq (.var "x" .none) do
          throw <| IO.userError "snapshot capture did not match `x`"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval snapshotBasicTest

/-- Native `@ghost(name="g", type=int, init=0)` captures the declared type and
    initializer (not just the name). -/
meta def ghostTypedTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "ghost_typed.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.ghost_typed")
          |>.toBaseIO
      match r with
      | .ok (sigs, _warnings) =>
        let some f := sigs.findSome?
            (fun | .functionDecl d => if d.name == "f" then some d else none | _ => none)
          | throw <| IO.userError "function `f` not found"
        unless f.ghosts.size == 1 do
          throw <| IO.userError s!"expected 1 ghost on `f`, got {f.ghosts.size}"
        unless f.ghosts[0]!.name == "g" do
          throw <| IO.userError s!"expected ghost name `g`, got {f.ghosts[0]!.name}"
        unless f.ghosts[0]!.type.isSome do
          throw <| IO.userError "expected ghost `g` to carry a declared type= (int)"
        let some ginit := f.ghosts[0]!.init
          | throw <| IO.userError "expected ghost `g` to carry an init= expression"
        unless ginit.softBEq (.intLit 0 .none) do
          throw <| IO.userError "ghost init= did not match `0`"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval ghostTypedTest

/-- A malformed `@requires` (argument is not a lambda) is a hard error, not a
    silently-dropped contract. -/
meta def requiresMalformedTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "requires_malformed.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.requires_malformed")
          |>.toBaseIO
      match r with
      | .ok _ =>
        throw <| IO.userError "expected `@requires(42)` to be a hard error, but translation succeeded"
      | .error e =>
        unless e.contains "expects a lambda" do
          throw <| IO.userError s!"expected a '@requires expects a lambda' error, got: {e}"

#guard_msgs in
#eval requiresMalformedTest

/-- A qualified `@icontract.requires` is declined by the native scheme (which
    only recognizes unqualified markers); it is therefore not silently absorbed
    as a precondition and is rejected by the downstream decorator-value path. -/
meta def icontractDeclineTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "icontract_decline.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.icontract_decline")
          |>.toBaseIO
      match r with
      | .ok _ =>
        throw <| IO.userError
          "expected qualified `@icontract.requires` to be declined+rejected, but translation succeeded"
      | .error _ =>
        pure ()  -- expected: not recognized as a native precondition

#guard_msgs in
#eval icontractDeclineTest

/-- An extra positional argument after the lambda is warned about, but the
    predicate is still recognized. -/
meta def requiresExtraPositionalTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "requires_extra_positional.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.requires_extra_positional")
          |>.toBaseIO
      match r with
      | .ok (sigs, warnings) =>
        let some f := sigs.findSome?
            (fun | .functionDecl d => if d.name == "f" then some d else none | _ => none)
          | throw <| IO.userError "function `f` not found"
        unless f.preconditions.size == 1 do
          throw <| IO.userError
            s!"expected the predicate to still be recognized (1 precondition), got {f.preconditions.size}"
        unless warnings.any (·.contains "extra positional") do
          throw <| IO.userError "expected a warning about extra positional arguments"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval requiresExtraPositionalTest

/-- Multiple `@requires` on one function accumulate into multiple preconditions. -/
meta def requiresMultipleTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "requires_multiple.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.requires_multiple")
          |>.toBaseIO
      match r with
      | .ok (sigs, _warnings) =>
        let some f := sigs.findSome?
            (fun | .functionDecl d => if d.name == "f" then some d else none | _ => none)
          | throw <| IO.userError "function `f` not found"
        unless f.preconditions.size == 2 do
          throw <| IO.userError s!"expected 2 preconditions on `f`, got {f.preconditions.size}"
        -- Both predicates must be present (order-independent).
        let geExpected : SpecExpr := .intGe (.var "x" .none) (.intLit 0 .none) .none
        let leExpected : SpecExpr := .intLe (.var "x" .none) (.intLit 100 .none) .none
        unless f.preconditions.any (·.formula.softBEq geExpected) do
          throw <| IO.userError "missing precondition `x >= 0`"
        unless f.preconditions.any (·.formula.softBEq leExpected) do
          throw <| IO.userError "missing precondition `x <= 100`"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval requiresMultipleTest

/-- `self.x` inside `@requires` (a lowered contract kind) is unsupported for now:
    the predicate is dropped with a warning, NOT silently stored or hard-errored.
    (Contrast `@invariant`, which is allowed to reference `self.x`.) -/
meta def requiresSelfMethodTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "requires_self_method.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.requires_self_method")
          |>.toBaseIO
      match r with
      | .ok (sigs, warnings) =>
        let some c := sigs.findSome?
            (fun | .classDef d => if d.name == "C" then some d else none | _ => none)
          | throw <| IO.userError "class `C` not found"
        let some m := c.methods.findSome? (fun d => if d.name == "m" then some d else none)
          | throw <| IO.userError "method `m` not found"
        unless m.preconditions.size == 0 do
          throw <| IO.userError
            s!"expected `self.x` @requires to be dropped (0 preconditions), got {m.preconditions.size}"
        unless warnings.any (·.contains "unsupported expression") do
          throw <| IO.userError "expected an unsupported-expression warning for `self.x` in @requires"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval requiresSelfMethodTest

/-- A bare string-literal predicate body is dropped (0 preconditions) WITH a
    diagnostic — it is not stored as a content-free placeholder, and the drop is
    not silent. This isolates the `containsPlaceholder` guard: a buried, no-warning
    placeholder is still rejected. -/
meta def requiresStringBodyTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "requires_string_body.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.requires_string_body")
          |>.toBaseIO
      match r with
      | .ok (sigs, warnings) =>
        let some f := sigs.findSome?
            (fun | .functionDecl d => if d.name == "f" then some d else none | _ => none)
          | throw <| IO.userError "function `f` not found"
        unless f.preconditions.size == 0 do
          throw <| IO.userError
            s!"expected the string-literal predicate to be dropped (0 preconditions), got {f.preconditions.size}"
        unless warnings.any (·.contains "unsupported expression in contract") do
          throw <| IO.userError "expected a diagnostic for the dropped string-literal predicate"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval requiresStringBodyTest

/-- `@modifies(lambda self: self.x)` on a method IS allowed to reference `self.x`
    (field access is enabled for the not-yet-lowered targets); the frame target is
    recognized as `getIndex(self, "x")`. Mirrors `invariantBasicTest`. -/
meta def modifiesSelfTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "modifies_self.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.modifies_self")
          |>.toBaseIO
      match r with
      | .ok (sigs, _warnings) =>
        let some c := sigs.findSome?
            (fun | .classDef d => if d.name == "C" then some d else none | _ => none)
          | throw <| IO.userError "class `C` not found"
        let some m := c.methods.findSome? (fun d => if d.name == "m" then some d else none)
          | throw <| IO.userError "method `m` not found"
        unless m.modifies.size == 1 do
          throw <| IO.userError s!"expected 1 modifies target on `m`, got {m.modifies.size}"
        let expected : SpecExpr := .getIndex (.var "self" .none) "x" .none
        unless m.modifies[0]!.softBEq expected do
          throw <| IO.userError "modifies target did not match `self.x` (getIndex self x)"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval modifiesSelfTest

/-- Duplicate `@ghost(name="g")` on one declaration is a hard error. -/
meta def ghostDupTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "ghost_dup.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.ghost_dup")
          |>.toBaseIO
      match r with
      | .ok _ =>
        throw <| IO.userError "expected duplicate @ghost name= to be a hard error, but translation succeeded"
      | .error e =>
        unless e.contains "duplicate" do
          throw <| IO.userError s!"expected a duplicate-ghost error, got: {e}"

#guard_msgs in
#eval ghostDupTest

/-- A BURIED placeholder (e.g. `len("foo") >= 1` → `intGe(stringLen(placeholder),1)`)
    is dropped by the deep `containsPlaceholder` check (a shallow top-level check
    would store it), with a diagnostic. -/
meta def requiresBuriedPlaceholderTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "requires_buried_placeholder.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.requires_buried_placeholder")
          |>.toBaseIO
      match r with
      | .ok (sigs, warnings) =>
        let some f := sigs.findSome?
            (fun | .functionDecl d => if d.name == "f" then some d else none | _ => none)
          | throw <| IO.userError "function `f` not found"
        unless f.preconditions.size == 0 do
          throw <| IO.userError
            s!"expected the buried-placeholder predicate to be dropped (0 preconditions), got {f.preconditions.size}"
        unless warnings.any (·.contains "unsupported expression in contract") do
          throw <| IO.userError "expected a diagnostic for the dropped buried-placeholder predicate"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval requiresBuriedPlaceholderTest

/-- A contract binder matching the function's `**kwargs` parameter is NOT flagged
    as unbound (functionParamNames includes it), and `kw["a"]` translates. -/
meta def requiresKwargsTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "requires_kwargs.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.requires_kwargs")
          |>.toBaseIO
      match r with
      | .ok (sigs, warnings) =>
        let some f := sigs.findSome?
            (fun | .functionDecl d => if d.name == "f" then some d else none | _ => none)
          | throw <| IO.userError "function `f` not found"
        unless f.preconditions.size == 1 do
          throw <| IO.userError s!"expected 1 precondition on `f`, got {f.preconditions.size}"
        if warnings.any (·.contains "unbound at the use site") then
          throw <| IO.userError "the **kwargs binder was wrongly flagged as unbound"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval requiresKwargsTest

/-- Duplicate `@snapshot` name= on one method is a hard error (mirrors `ghostDupTest`). -/
meta def snapshotDupTest : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "native_cases" / "snapshot_dup.py")
          (searchPath := testDir)
          (StrataPython.ModuleName.ofString! "native_cases.snapshot_dup")
          |>.toBaseIO
      match r with
      | .ok _ =>
        throw <| IO.userError "expected duplicate @snapshot name= to be a hard error, but translation succeeded"
      | .error e =>
        unless e.contains "duplicate" do
          throw <| IO.userError s!"expected a duplicate-snapshot error, got: {e}"

#guard_msgs in
#eval snapshotDupTest

/-- Test that unsupported patterns emit appropriate warnings. -/
def warningTestCase : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "warnings.py")
          (searchPath := testDir)
          (.ofComponent (.ofString "warnings"))
          |>.toBaseIO
      match r with
      | .ok (sigs, warnings) =>
        -- Check that we still produced some output despite warnings
        if sigs.isEmpty then
          throw <| IO.userError "Expected signatures from warnings.py but got none"
        -- Check that we got warnings (not zero)
        if warnings.isEmpty then
          throw <| IO.userError "Expected warnings from warnings.py but got none"
        -- Check for specific expected warning substrings
        let expectedWarnings := #[
          "unsupported comparison",               -- assert kw["x"] == 1
          "unsupported __init__ assignment",   -- self.name = "hello"
          "skipped Assign in function body",   -- x = kw["a"]
          "For: else clause not supported",    -- for/else loop
          "skipped Expr in function body"      -- kw["a"] (bare expression)
        ]
        for expected in expectedWarnings do
          if !warnings.any (·.contains expected) then
            let warnStr := warnings.foldl (init := "") fun acc w => s!"{acc}\n  {w}"
            throw <| IO.userError
              s!"Missing expected warning containing \"{expected}\". Actual warnings:{warnStr}"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval warningTestCase


meta def testNegRoundTrip (v : Nat) : Bool :=
  DDM.Int.ofDDM (.negInt SourceRange.none ⟨.none, v⟩) = Int.negOfNat v

#guard testNegRoundTrip 0
#guard testNegRoundTrip 1

def testIntRoundTrip (v : Int) : Bool :=
  DDM.Int.ofDDM (toDDMInt SourceRange.none v) = v

#guard testIntRoundTrip 0
#guard testIntRoundTrip 1
#guard testIntRoundTrip (-1)
#guard testIntRoundTrip (42)
#guard testIntRoundTrip (-100)

/-- Non-vacuous DDM serialization round-trip regression for the B-recog fields.

    Unlike the six recognition tests above (which only inspect the in-memory
    `Specs` value produced by translation and never cross the DDM boundary),
    this test exercises the `toDDM` → `fromDDM` round-trip directly. It builds a
    `FunctionDecl` carrying one `snapshots`, one `modifies`, and one `ghosts`
    entry, plus a `ClassDef` carrying one `invariants` entry, serializes via
    `FunctionDecl.toDDM` / `ClassDef.toDDMDecl`, deserializes via
    `DDM.FunDecl.fromDDM` / `DDM.ClassDecl.fromDDM` (running the `FromDDM`
    `Except` monad), and asserts the field counts AND key contents survive.

    This is the test that the mutation-testing gap analysis showed was missing:
    breaking a `fromDDM` readback to `#[]` left every recognition test green, so
    a regression dropping a (de)serialization clause would have gone undetected.
    Here, such a regression makes the corresponding `unless` below fire. -/
meta def serdeRoundTripTest : IO Unit := do
  -- A FunctionDecl populated with the three B-recog FunctionDecl fields.
  let fd : Specs.FunctionDecl := {
    loc := .none
    nameLoc := .none
    name := "f"
    args := { args := #[], kwonly := #[] }
    returnType := SpecType.noneType .none
    isOverload := false
    preconditions := #[]
    postconditions := #[]
    snapshots := #[{ name := "v0", capture := .var "x" .none, loc := .none }]
    modifies := #[.var "self_x" .none]
    ghosts := #[{ name := "g", type := some (SpecType.ident .none .builtinsInt),
                  init := some (.intLit 7 .none), loc := .none }]
  }
  -- Serialize then deserialize across the DDM boundary.
  let fd' ← match DDM.FunDecl.fromDDM (FunctionDecl.toDDM fd) with
    | .ok r => pure r
    | .error (_, msg) => throw <| IO.userError s!"FunDecl.fromDDM failed: {msg}"
  -- snapshots: count + name + capture contents must survive the round-trip.
  unless fd'.snapshots.size == 1 do
    throw <| IO.userError
      s!"round-trip dropped snapshots: expected 1, got {fd'.snapshots.size}"
  unless fd'.snapshots[0]!.name == "v0" do
    throw <| IO.userError
      s!"round-trip corrupted snapshot name: expected \"v0\", got \"{fd'.snapshots[0]!.name}\""
  unless fd'.snapshots[0]!.capture.softBEq (.var "x" .none) do
    throw <| IO.userError "round-trip corrupted snapshot capture expression"
  -- modifies: count + target expression contents must survive.
  unless fd'.modifies.size == 1 do
    throw <| IO.userError
      s!"round-trip dropped modifies: expected 1, got {fd'.modifies.size}"
  unless fd'.modifies[0]!.softBEq (.var "self_x" .none) do
    throw <| IO.userError "round-trip corrupted modifies target expression"
  -- ghosts: count + name must survive.
  unless fd'.ghosts.size == 1 do
    throw <| IO.userError
      s!"round-trip dropped ghosts: expected 1, got {fd'.ghosts.size}"
  unless fd'.ghosts[0]!.name == "g" do
    throw <| IO.userError
      s!"round-trip corrupted ghost name: expected \"g\", got \"{fd'.ghosts[0]!.name}\""
  -- ghost type= and init= must also survive (exercises the `Option` clauses of
  -- `mkGhostDecl`'s ghostType/ghostInit).
  unless fd'.ghosts[0]!.type.isSome do
    throw <| IO.userError "round-trip dropped ghost type="
  let some ginit := fd'.ghosts[0]!.init
    | throw <| IO.userError "round-trip dropped ghost init="
  unless ginit.softBEq (.intLit 7 .none) do
    throw <| IO.userError "round-trip corrupted ghost init expression"
  -- A ClassDef populated with the B-recog ClassDef invariants field.
  let cd : Specs.ClassDef := {
    loc := .none
    name := "C"
    methods := #[fd]
    invariants := #[.var "inv" .none]
  }
  let cd' ← match DDM.ClassDecl.fromDDM (ClassDef.toDDMDecl cd) with
    | .ok r => pure r
    | .error (_, msg) => throw <| IO.userError s!"ClassDecl.fromDDM failed: {msg}"
  -- invariants: count + expression contents must survive.
  unless cd'.invariants.size == 1 do
    throw <| IO.userError
      s!"round-trip dropped invariants: expected 1, got {cd'.invariants.size}"
  unless cd'.invariants[0]!.softBEq (.var "inv" .none) do
    throw <| IO.userError "round-trip corrupted invariant expression"
  -- The class's method (itself carrying snapshot/modifies/ghost fields) must
  -- round-trip too, including those nested fields.
  unless cd'.methods.size == 1 do
    throw <| IO.userError
      s!"round-trip dropped class method: expected 1, got {cd'.methods.size}"
  unless cd'.methods[0]!.snapshots.size == 1
          && cd'.methods[0]!.modifies.size == 1
          && cd'.methods[0]!.ghosts.size == 1 do
    throw <| IO.userError "round-trip dropped a class method's snapshot/modifies/ghost fields"

#guard_msgs in
#eval serdeRoundTripTest
end
