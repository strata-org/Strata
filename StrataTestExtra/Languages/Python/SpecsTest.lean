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
  snapshots: [
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
  snapshots: [
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
  snapshots: [
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
  snapshots: [
  ]
}
class "MainClass" {
  bases: []
  fields: []
  classVars: []
  subclasses: []
  exhaustive: false
  invariants: [
  ]
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
    snapshots: [
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
  snapshots: [
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
  snapshots: [
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
  snapshots: [
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
  snapshots: [
  ]
}
class "InnerHelper" {
  bases: []
  fields: []
  classVars: []
  subclasses: []
  exhaustive: false
  invariants: [
  ]
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
      invariants: [
      ]
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
        snapshots: [
        ]
      }
    }
  ]
  exhaustive: false
  invariants: [
  ]
  function "__init__"{
    args: [
      self : ident("main.ClassWithInit") [default: ]
    ]
    kwonly: [
    ]
    return: ident("typing.Any")
    overload: false
    preconditions: [
    ]
    postconditions: [
    ]
    snapshots: [
    ]
  }
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
          "unsupported comparison",               -- assert kw["x"] == 1
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

/-! ## icontract decorator tests

Table-driven end-to-end tests for `@icontract.{require,ensure,
invariant,snapshot}` and `OLD.<name>`. Each row pairs a fixture
under `Specs/icontract_cases/` with a check on the translation
result. -/

private meta structure CaseResult where
  sigs     : Array Specs.Signature := #[]
  warnings : Array String := #[]
  error?   : Option String := none

private meta abbrev Check := CaseResult → IO Unit

private meta def fail {α} (msg : String) : IO α := throw (.userError msg)

private meta def CaseResult.expectOk (r : CaseResult) : IO Unit := do
  if let some e := r.error? then fail s!"unexpected translation error: {e}"
  unless r.warnings.isEmpty do
    fail s!"unexpected warnings:\n  {"\n  ".intercalate r.warnings.toList}"

private meta def CaseResult.expectWarn (r : CaseResult) (needle : String) : IO Unit := do
  if let some e := r.error? then fail s!"unexpected translation error: {e}"
  unless r.warnings.any (containsSubstr · needle) do
    fail s!"expected warning containing \"{needle}\", got:\n  {"\n  ".intercalate r.warnings.toList}"

private meta def CaseResult.expectErr (r : CaseResult) (needle : String) : IO Unit := do
  let some e := r.error?
    | fail "expected translation error, but it succeeded"
  unless containsSubstr e needle do
    fail s!"expected error containing \"{needle}\", got:\n{e}"

private meta def CaseResult.fn (r : CaseResult) (name : String) : IO Specs.FunctionDecl :=
  match r.sigs.findSome? (fun | .functionDecl f => if f.name == name then some f else none | _ => none) with
  | some f => pure f
  | none   => fail s!"function `{name}` not found"

private meta def CaseResult.cls (r : CaseResult) (name : String) : IO Specs.ClassDef :=
  match r.sigs.findSome? (fun | .classDef c => if c.name == name then some c else none | _ => none) with
  | some c => pure c
  | none   => fail s!"class `{name}` not found"

private meta def methodOf (c : Specs.ClassDef) (name : String) : IO Specs.FunctionDecl :=
  match c.methods.find? (·.name == name) with
  | some m => pure m
  | none   => fail s!"method `{name}` not found"

/-- `expectSize n what xs`: throw if `xs.size ≠ n`, naming `what` in
    the error. Used for precondition / postcondition / invariant /
    snapshot count assertions. -/
private meta def expectSize {α} (n : Nat) (what : String) (xs : Array α) : IO Unit :=
  unless xs.size = n do
    fail s!"expected {n} {what}, got {xs.size}"

private meta def fnPreCount (name : String) (n : Nat) : Check := fun r => do
  r.expectOk
  expectSize n s!"preconditions on {name}" (← r.fn name).preconditions

private meta def fnPostCount (name : String) (n : Nat) : Check := fun r => do
  r.expectOk
  expectSize n s!"postconditions on {name}" (← r.fn name).postconditions

private meta def clsInvariantCount (name : String) (n : Nat) : Check := fun r => do
  r.expectOk
  expectSize n s!"invariants on class {name}" (← r.cls name).invariants

private meta def methodSnapshotNames (cls method : String) (names : List String) : Check := fun r => do
  r.expectOk
  let m ← methodOf (← r.cls cls) method
  expectSize names.length s!"snapshots on {cls}.{method}" m.snapshots
  let actual := m.snapshots.toList.map (·.name)
  unless names.all actual.contains do
    fail s!"expected snapshots {names}; got {actual}"

private meta def icontractCases : List (String × Check) := [
  ("require_basic.py",            fnPreCount  "f" 1),
  ("require_multiple.py",         fnPreCount  "g" 2),
  ("require_bad_binder.py",       (·.expectWarn "does not match any function parameter")),
  ("ensure_basic.py",             fnPostCount "f" 1),
  ("ensure_multiple.py",          fnPostCount "f" 2),
  ("invariant_basic.py",          clsInvariantCount "C" 1),
  ("invariant_multiple.py",       clsInvariantCount "C" 2),
  ("invariant_bad_binder.py",     fun r => do
      r.expectWarn "lambda binder must be 'self'"
      expectSize 0 "invariants on class C" (← r.cls "C").invariants),
  ("snapshot_basic.py",           methodSnapshotNames "C" "m" ["v0"]),
  ("snapshot_multiple.py",        methodSnapshotNames "C" "step" ["x0", "y0"]),
  ("snapshot_missing_name.py",    (·.expectErr  "requires a name= keyword argument")),
  ("snapshot_duplicate_name.py",  (·.expectErr  "duplicate name=")),
  ("ensure_with_old_ref.py",      fun r => do
      r.expectOk
      let m ← methodOf (← r.cls "C") "grow"
      expectSize 1 "snapshots on C.grow" m.snapshots
      expectSize 1 "postconditions on C.grow" m.postconditions),
  ("old_undeclared.py",           (·.expectWarn "no @icontract.snapshot named")),
  ("init_with_ensure.py",         fun r => do
      r.expectOk
      expectSize 1 "postconditions on C.__init__"
        (← methodOf (← r.cls "C") "__init__").postconditions)
]

private meta def runIcontractCase (pythonCmd : System.FilePath)
    (filename : String) (check : Check) : IO Unit := do
  IO.FS.withTempFile fun _ dialectFile => do
    IO.FS.writeBinFile dialectFile Strata.Python.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ← (translateFile (pythonCmd := toString pythonCmd) (dialectFile := dialectFile)
                (strataDir := strataDir) (pythonFile := testDir / "icontract_cases" / filename)
                (searchPath := testDir)).toBaseIO
      let result : CaseResult := match r with
        | .ok (sigs, warnings) => { sigs, warnings }
        | .error e             => { error? := some e }
      try check result catch e => fail s!"[{filename}] {e}"

meta def icontractCasesTest : IO Unit := withPython fun pythonCmd =>
  icontractCases.forM fun (filename, check) => runIcontractCase pythonCmd filename check
#guard_msgs in
#eval icontractCasesTest


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
