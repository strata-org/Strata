/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Python.SSA.Translate
meta import Strata.Languages.Python.SSA.Format
meta import Strata.Languages.Python.TypeCheck.Propagate
meta import Strata.Languages.Python.TypeCheck.Format
meta import Strata.Languages.Python.ReadPython
meta import Strata.Languages.Python.Specs.DDM
meta import Strata.Util.IO
meta import StrataTest.Util.Python

/-! ## Tests for Python forward type analysis over SSA IR -/

namespace Strata.Python.TypeCheckTest

open Strata.Python.PythonToSSA (translateModule)
open Strata.Python.SSAFormat (fmtModule)
open Strata.Python.TypeCheck
open Strata.Python (withPython)

private meta def testDir : System.FilePath :=
  "StrataTest/Languages/Python/TypeCheck/tests"

private meta def expectedDir : System.FilePath :=
  "StrataTest/Languages/Python/TypeCheck/expected"

/-- Compile a Python source file to Ion. -/
private meta def compilePython
    (pythonCmd : System.FilePath)
    (pyFile : System.FilePath)
    (outDir : System.FilePath) : IO System.FilePath := do
  let some stem := pyFile.fileStem
    | throw <| .userError s!"No stem for {pyFile}"
  let ionPath := outDir / s!"{stem}.python.st.ion"
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile Python.Python.toIon
    let spawnArgs : IO.Process.SpawnArgs := {
      cmd := toString pythonCmd
      args := #["-m", "strata.gen", "py_to_strata",
                "--dialect", dialectFile.toString,
                pyFile.toString, ionPath.toString]
      cwd := none
      inheritEnv := true
      stdin := .null
      stdout := .piped
      stderr := .piped
    }
    let child ← IO.Process.spawn spawnArgs
    let _stdout ← child.stdout.readToEnd
    let stderr ← child.stderr.readToEnd
    let exitCode ← child.wait
    if exitCode ≠ 0 then
      throw <| .userError s!"py_to_strata failed for {pyFile} (exit {exitCode}): {stderr}"
  return ionPath

/-- Run the full pipeline: Ion → SSA → TypeCheck → formatted output. -/
private meta def runTypeCheck (ionPath : System.FilePath) (moduleName : String)
    (specDir : Option System.FilePath := none) : IO String := do
  let bytes ← Strata.Util.readBinInputSource ionPath.toString
  let stmts ← match Strata.Python.readPythonStrataBytes ionPath.toString bytes with
    | .ok stmts => pure stmts
    | .error msg => throw <| .userError s!"Failed to read Ion: {msg}"
  let ssaResult := translateModule moduleName stmts
  let ssaDump := fmtModule ssaResult.module
  let cfg : TypeCheckConfig := { moduleName, specDir }
  let (tcResult, _) ← (TypeCheckM.run cfg (typeCheckModule ssaResult.module) :)
  let tcDump := fmtTypeCheckResult ssaResult.module tcResult
  return s!"{ssaDump}\n--- type check ---\n\n{tcDump}"

/-- Set to `true` to overwrite `.expected` files with actual output. -/
private meta def regenerateTests : Bool := false

/-- Run a single test case. -/
private meta def runTestCase
    (pythonCmd : System.FilePath)
    (tmpDir : System.FilePath)
    (pyFile : System.FilePath)
    (expectedFile : System.FilePath)
    (testName : String)
    : IO (Option String) := do
  let ionPath ← compilePython pythonCmd pyFile tmpDir
  let actual ← runTypeCheck ionPath testName
  IO.FS.createDirAll "/tmp/tc_test_actual"
  IO.FS.writeFile s!"/tmp/tc_test_actual/{testName}.actual" actual
  if regenerateTests then
    IO.FS.createDirAll expectedDir
    IO.FS.writeFile (expectedDir / s!"{testName}.expected") actual
    return none
  let expected ← IO.FS.readFile expectedFile
  if actual.trimAscii.toString == expected.trimAscii.toString then
    return none
  else
    let actualLines := actual.trimAscii.toString.splitOn "\n"
    let expectedLines := expected.trimAscii.toString.splitOn "\n"
    let mut diffMsg := s!"{testName}: output differs from expected\n"
    let maxLines := max actualLines.length expectedLines.length
    for i in [:maxLines] do
      let aLine := actualLines[i]?.getD "<EOF>"
      let eLine := expectedLines[i]?.getD "<EOF>"
      if aLine != eLine then
        diffMsg := diffMsg ++ s!"  first diff at line {i + 1}:\n"
        diffMsg := diffMsg ++ s!"    expected: {eLine}\n"
        diffMsg := diffMsg ++ s!"    actual:   {aLine}\n"
        break
    return some diffMsg

private meta def specDir : System.FilePath :=
  "StrataTest/Languages/Python/TypeCheck/specs"

/-- Generate a .pyspec.st.ion file from an array of Signatures. -/
private meta def writeSpecFile (dir : System.FilePath) (modPath : String)
    (sigs : Array Strata.Python.Specs.Signature) : IO Unit := do
  let parts := modPath.splitOn "/"
  let fileName := parts.getLast!
  let parentDirs := parts.dropLast
  let outDir := parentDirs.foldl (· / ·) dir
  IO.FS.createDirAll outDir
  Strata.Python.Specs.writeDDM (outDir / s!"{fileName}.pyspec.st.ion") sigs

open Strata.Python (PythonIdent) in
/-- Build spec files for tests that exercise spec loading. -/
private meta def buildTestSpecs (dir : System.FilePath) : IO Unit := do
  let sqrtArg : Strata.Python.Specs.Arg :=
    { name := "x", type := .ident default .builtinsFloat }
  let mathSqrt : Strata.Python.Specs.FunctionDecl := {
    loc := default, nameLoc := default
    name := "sqrt"
    args := { args := #[sqrtArg], kwonly := #[] }
    returnType := .ident default .builtinsFloat
    isOverload := false
    preconditions := #[]
    postconditions := #[]
  }
  let mathPi : Strata.Python.Specs.TypeDef := {
    loc := default, nameLoc := default
    name := "pi"
    definition := .ident default .builtinsFloat
  }
  writeSpecFile dir "math" #[.functionDecl mathSqrt, .typeDef mathPi]
  -- myservice spec: a Client class with methods, fields, and exhaustive flag
  let keyArg : Strata.Python.Specs.Arg :=
    { name := "key", type := .ident default .builtinsStr }
  let getItemMethod : Strata.Python.Specs.FunctionDecl := {
    loc := default, nameLoc := default
    name := "get_item"
    args := { args := #[keyArg], kwonly := #[] }
    returnType := .ident default .builtinsDict
    isOverload := false
    preconditions := #[]
    postconditions := #[]
  }
  let serviceNameField : Strata.Python.Specs.ClassField := {
    name := "service_name"
    type := .ident default .builtinsStr
  }
  let clientClass : Strata.Python.Specs.ClassDef := {
    loc := default
    name := "Client"
    fields := #[serviceNameField]
    methods := #[getItemMethod]
    exhaustive := true
  }
  writeSpecFile dir "myservice" #[.classDef clientClass]

/-- Run a test case that uses spec loading. -/
private meta def runSpecTestCase
    (pythonCmd : System.FilePath)
    (tmpDir specTestDir : System.FilePath)
    (pyFile expectedFile : System.FilePath)
    (testName : String) : IO (Option String) := do
  let ionPath ← compilePython pythonCmd pyFile tmpDir
  let actual ← runTypeCheck ionPath testName (specDir := some specTestDir)
  IO.FS.createDirAll "/tmp/tc_test_actual"
  IO.FS.writeFile s!"/tmp/tc_test_actual/{testName}.actual" actual
  if regenerateTests then
    IO.FS.createDirAll expectedDir
    IO.FS.writeFile (expectedDir / s!"{testName}.expected") actual
    return none
  let expected ← IO.FS.readFile expectedFile
  if actual.trimAscii.toString == expected.trimAscii.toString then
    return none
  else
    let actualLines := actual.trimAscii.toString.splitOn "\n"
    let expectedLines := expected.trimAscii.toString.splitOn "\n"
    let mut diffMsg := s!"{testName}: output differs from expected\n"
    let maxLines := max actualLines.length expectedLines.length
    for i in [:maxLines] do
      let aLine := actualLines[i]?.getD "<EOF>"
      let eLine := expectedLines[i]?.getD "<EOF>"
      if aLine != eLine then
        diffMsg := diffMsg ++ s!"  first diff at line {i + 1}:\n"
        diffMsg := diffMsg ++ s!"    expected: {eLine}\n"
        diffMsg := diffMsg ++ s!"    actual:   {aLine}\n"
        break
    return some diffMsg

/-! ## Test list -/

private meta def positiveTests : List String := [
  "tc01_literals",
  "tc02_arithmetic",
  "tc03_string_ops",
  "tc04_comparisons",
  "tc05_unary",
  "tc06_collections",
  "tc07_if_else",
  "tc08_fstring"
]

private meta def specTests : List String := [
  "tc09_import",
  "tc10_class_method",
  "tc11_class_field",
  "tc12_exhaustive",
  "tc13_from_import"
]

#eval withPython fun pythonCmd => do
  IO.FS.createDirAll "/tmp/tc_test_actual"
  IO.FS.withTempDir fun tmpDir => do
    -- Build spec stubs
    IO.FS.withTempDir fun specTmpDir => do
      buildTestSpecs specTmpDir
      let mut tasks : Array (String × Task (Except IO.Error (Option String))) := #[]
      for name in positiveTests do
        let pyFile := testDir / s!"{name}.py"
        let expFile := expectedDir / s!"{name}.expected"
        let task ← IO.asTask (runTestCase pythonCmd tmpDir pyFile expFile name)
        tasks := tasks.push (name, task)
      for name in specTests do
        let pyFile := testDir / s!"{name}.py"
        let expFile := expectedDir / s!"{name}.expected"
        let task ← IO.asTask (runSpecTestCase pythonCmd tmpDir specTmpDir pyFile expFile name)
        tasks := tasks.push (name, task)
      let mut errors : Array String := #[]
      let mut passed : Nat := 0
      for (_, task) in tasks do
        match ← IO.wait task with
        | .ok (some err) => errors := errors.push err
        | .ok none => passed := passed + 1
        | .error e => errors := errors.push s!"Task error: {e}"
      IO.println s!"TypeCheckTest: {passed}/{tasks.size} passed"
      if errors.size > 0 then
        IO.println s!"TypeCheckTest differences ({errors.size}):"
        for err in errors do
          IO.println err

end Strata.Python.TypeCheckTest
