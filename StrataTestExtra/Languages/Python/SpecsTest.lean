/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import Strata.Languages.Python.Specs
meta import Strata.Languages.Python.Specs.DDM
import Strata.DDM.Ion
import Strata.Languages.Python.PythonDialect
meta import StrataTest.Util.Python

namespace Strata.Python.Specs

private meta def testDir : System.FilePath :=
  "StrataTestExtra/Languages/Python/Specs"

meta def expectedPySpec :=
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
    ensure(len(params[Name]) >=_int 1, "Expected len(params[\"Name\"]) >= 1, got "{len(params[Name])})
    ensure(len(params[Name]) <=_int 100, "Expected len(params[\"Name\"]) <= 100, got "{len(params[Name])})
    ensure(regex(params[Name], "^[a-zA-Z]+$"), "params[\"Name\"] did not match pattern")
    ensure(Items in params => forall(params[Items], item, len(item) >=_int 1), "Expected len(item) >= 1, got "{len(item)})
    ensure(Items in params => forall(params[Items], item, len(item) <=_int 50), "Expected len(item) <= 50, got "{len(item)})
    ensure(Tags in params => forallDict(params[Tags], tag_key, tag_val, len(tag_key) >=_int 1), "Expected len(tag_key) >= 1, got "{len(tag_key)})
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
    IO.FS.writeBinFile dialectFile Strata.Python.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "main.py")
          (searchPath := testDir)
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

/-- Test that unsupported patterns emit appropriate warnings. -/
meta def warningTestCase : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile Strata.Python.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "warnings.py")
          (searchPath := testDir)
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
          "unrecognized assert pattern",       -- assert kw["x"] == 1
          "unsupported __init__ assignment",   -- self.name = "hello"
          "skipped Assign in function body",   -- x = kw["a"]
          "For: else clause not supported",    -- for/else loop
          "skipped Expr in function body"      -- kw["a"] (bare expression)
        ]
        for expected in expectedWarnings do
          if !warnings.any (containsSubstr · expected) then
            let warnStr := warnings.foldl (init := "") fun acc w => s!"{acc}\n  {w}"
            throw <| IO.userError
              s!"Missing expected warning containing \"{expected}\". Actual warnings:{warnStr}"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval warningTestCase


meta def testNegRoundTrip (v : Nat) : Bool :=
  DDM.Int.ofDDM (.negInt SourceRange.none ⟨.none, v⟩) = .negOfNat v

#guard testNegRoundTrip 0
#guard testNegRoundTrip 1

meta def testIntRoundTrip (v : Int) : Bool :=
  DDM.Int.ofDDM (toDDMInt SourceRange.none v) = v

#guard testIntRoundTrip 0
#guard testIntRoundTrip 1
#guard testIntRoundTrip (-1)
#guard testIntRoundTrip (42)
#guard testIntRoundTrip (-100)

end Strata.Python.Specs
