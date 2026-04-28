/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Python.PythonToSSA
meta import Strata.Languages.Python.SSAFormat
meta import Strata.Languages.Python.ReadPython
meta import Strata.Util.IO
meta import StrataTest.Util.Python

/-! ## Tests for Python → SSA translation (strict block-argument SSA)

Dumps actual output to `/tmp/ssa_test_actual/` for comparison.
-/

namespace Strata.Python.SSATest

open Strata.Python.PythonToSSA (translateModule)
open Strata.Python.SSAFormat (fmtModule fmtWarnings)
open Strata.Python (withPython)

private meta def testDir : System.FilePath :=
  "StrataTest/Languages/Python/SSA/tests"

private meta def expectedDir : System.FilePath :=
  "StrataTest/Languages/Python/SSA/expected"

private meta def negativeDir : System.FilePath :=
  "StrataTest/Languages/Python/SSA/negative_tests"

/-- Compile a Python source file to a `.python.st.ion` Ion file. -/
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

/-- Read Python strata from Ion file and run translateModule (v2). -/
private meta def runTranslate (ionPath : System.FilePath) (pyFile : System.FilePath)
    (moduleName : String) : IO String := do
  let bytes ← Strata.Util.readBinInputSource ionPath.toString
  let stmts ← match Strata.Python.readPythonStrataBytes ionPath.toString bytes with
    | .ok stmts => pure stmts
    | .error msg => throw <| .userError s!"Failed to read Ion: {msg}"
  let result := translateModule moduleName stmts
  let fileMap ← do
    try
      let content ← IO.FS.readFile pyFile
      pure (some (Lean.FileMap.ofString content))
    catch _ => pure none
  let warnStr := fmtWarnings result.warnings fileMap
  let modStr := fmtModule result.module
  -- Insert warnings after the module header line
  let lines := modStr.splitOn "\n"
  match lines with
  | hdr :: rest =>
    let warningBlock := if warnStr.isEmpty then "" else "\n" ++ warnStr
    return hdr ++ warningBlock ++ "\n" ++ "\n".intercalate rest
  | [] => return warnStr ++ modStr

/-- Run a single test: compile, translate, dump actual output. -/
private meta def runTestCase
    (pythonCmd : System.FilePath)
    (tmpDir : System.FilePath)
    (pyFile : System.FilePath)
    (expectedFile : System.FilePath)
    (testName : String)
    : IO (Option String) := do
  let ionPath ← compilePython pythonCmd pyFile tmpDir
  let actual ← runTranslate ionPath pyFile testName
  let expected ← IO.FS.readFile expectedFile
  -- Always dump actual output for inspection
  IO.FS.writeFile s!"/tmp/ssa_test_actual/{testName}.actual" actual
  if actual.trimAscii.toString == expected.trimAscii.toString then
    return none
  else
    -- Find first differing line for a useful error message
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

/-! ## Positive tests -/

private meta def positiveTests : List String := [
  "t01_assign",
  "t02_operators",
  "t03_if_else",
  "t04_while",
  "t05_for",
  "t06_function",
  "t07_try_except",
  "t08_try_finally",
  "t09_nested_try",
  "t10_except_type",
  "t11_with",
  "t12_class",
  "t13_fstring",
  "t14_bool_short",
  "t15_ifexp",
  "t16_chained_cmp",
  "t17_import",
  "t18_data_struct",
  "t19_attribute",
  "t20_raise",
  "t21_combined",
  "t22_star_args",
  "t23_kwargs_boto3",
  "t24_assert",
  "t25_tuple_unpack"
]

private meta def negativeTests : List String := [
  "n01_async",
  "n02_listcomp",
  "n03_dictcomp",
  "n04_generator",
  "n05_lambda",
  "n06_yield",
  "n07_walrus",
  "n08_mixed"
]

#eval withPython fun pythonCmd => do
  IO.FS.createDirAll "/tmp/ssa_test_actual"
  IO.FS.withTempDir fun tmpDir => do
    -- Launch all positive tests concurrently
    let mut tasks : Array (String × Task (Except IO.Error (Option String))) := #[]
    for name in positiveTests do
      let pyFile := testDir / s!"{name}.py"
      let expFile := expectedDir / s!"{name}.expected"
      let task ← IO.asTask (runTestCase pythonCmd tmpDir pyFile expFile name)
      tasks := tasks.push (name, task)
    -- Launch all negative tests concurrently
    for name in negativeTests do
      let pyFile := negativeDir / s!"{name}.py"
      let expFile := negativeDir / s!"{name}.expected"
      let task ← IO.asTask (runTestCase pythonCmd tmpDir pyFile expFile name)
      tasks := tasks.push (name, task)
    -- Collect results
    let mut errors : Array String := #[]
    let mut passed : Nat := 0
    for (_, task) in tasks do
      match ← IO.wait task with
      | .ok (some err) => errors := errors.push err
      | .ok none => passed := passed + 1
      | .error e => errors := errors.push s!"Task error: {e}"
    IO.println s!"SSATest: {passed}/{tasks.size} passed"
    if errors.size > 0 then
      IO.println s!"SSATest2 differences ({errors.size}):"
      for err in errors do
        IO.println err

end Strata.Python.SSATest
