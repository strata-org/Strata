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

/-- Compare actual output against an expected file.  If the expected file
    doesn't exist, generate it and report the test as newly created. -/
private meta def checkOrGenerate (testName : String) (actual : String)
    (expectedFile : System.FilePath) : IO (Option String) := do
  IO.FS.createDirAll "/tmp/tc_test_actual"
  IO.FS.writeFile s!"/tmp/tc_test_actual/{testName}.actual" actual
  if !(← expectedFile.pathExists) then
    IO.FS.createDirAll expectedDir
    IO.FS.writeFile expectedFile actual
    return some s!"{testName}: generated expected file"
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
  checkOrGenerate testName actual expectedFile

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
  -- cloudkit spec: overloaded client() function for dispatch testing
  let dbIdent : PythonIdent := { pythonModule := "cloudkit.database", name := "DatabaseClient" }
  let dbLiteralType : Strata.Python.Specs.SpecType :=
    { atoms := #[.stringLiteral "database"], loc := default }
  let dbArg : Strata.Python.Specs.Arg :=
    { name := "service_name", type := dbLiteralType }
  let clientDb : Strata.Python.Specs.FunctionDecl := {
    loc := default, nameLoc := default
    name := "client"
    args := { args := #[dbArg], kwonly := #[] }
    returnType := .ident default dbIdent
    isOverload := true
    preconditions := #[], postconditions := #[]
  }
  let cacheIdent : PythonIdent := { pythonModule := "cloudkit.cache", name := "CacheClient" }
  let cacheLiteralType : Strata.Python.Specs.SpecType :=
    { atoms := #[.stringLiteral "cache"], loc := default }
  let cacheArg : Strata.Python.Specs.Arg :=
    { name := "service_name", type := cacheLiteralType }
  let clientCache : Strata.Python.Specs.FunctionDecl := {
    loc := default, nameLoc := default
    name := "client"
    args := { args := #[cacheArg], kwonly := #[] }
    returnType := .ident default cacheIdent
    isOverload := true
    preconditions := #[], postconditions := #[]
  }
  let fallbackArg : Strata.Python.Specs.Arg :=
    { name := "service_name", type := .ident default .builtinsStr }
  let clientFallback : Strata.Python.Specs.FunctionDecl := {
    loc := default, nameLoc := default
    name := "client"
    args := { args := #[fallbackArg], kwonly := #[] }
    returnType := .ident default .typingAny
    isOverload := false
    preconditions := #[], postconditions := #[]
  }
  writeSpecFile dir "cloudkit" #[.functionDecl clientDb, .functionDecl clientCache,
                                 .functionDecl clientFallback]
  -- cloudkit.database spec: DatabaseClient class loaded transitively
  let queryArg : Strata.Python.Specs.Arg :=
    { name := "sql", type := .ident default .builtinsStr }
  let queryMethod : Strata.Python.Specs.FunctionDecl := {
    loc := default, nameLoc := default
    name := "query"
    args := { args := #[queryArg], kwonly := #[] }
    returnType := .ident default .builtinsDict
    isOverload := false
    preconditions := #[], postconditions := #[]
  }
  let dbClientClass : Strata.Python.Specs.ClassDef := {
    loc := default
    name := "DatabaseClient"
    methods := #[queryMethod]
  }
  writeSpecFile dir "cloudkit/database" #[.classDef dbClientClass]

/-- Run a test case that uses spec loading. -/
private meta def runSpecTestCase
    (pythonCmd : System.FilePath)
    (tmpDir specTestDir : System.FilePath)
    (pyFile expectedFile : System.FilePath)
    (testName : String) : IO (Option String) := do
  let ionPath ← compilePython pythonCmd pyFile tmpDir
  let actual ← runTypeCheck ionPath testName (specDir := some specTestDir)
  checkOrGenerate testName actual expectedFile

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
  "tc13_from_import",
  "tc14_overload_dispatch",
  "tc15_arg_count",
  "tc16_unknown_attr",
  "tc17_transitive_dispatch"
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
      let mut generated : Array String := #[]
      let mut passed : Nat := 0
      for (_, task) in tasks do
        match ← IO.wait task with
        | .ok (some msg) =>
          if msg.endsWith "generated expected file" then
            generated := generated.push msg
          else
            errors := errors.push msg
        | .ok none => passed := passed + 1
        | .error e => errors := errors.push s!"Task error: {e}"
      IO.println s!"TypeCheckTest: {passed}/{tasks.size} passed"
      if generated.size > 0 then
        IO.println s!"TypeCheckTest generated ({generated.size}):"
        for msg in generated do
          IO.println s!"  {msg}"
      if errors.size > 0 then
        for err in errors do
          IO.println err
        throw <| .userError s!"TypeCheckTest: {errors.size} test(s) failed"

end Strata.Python.TypeCheckTest
