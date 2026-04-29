/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.SimpleAPI
meta import Strata.Languages.Python.PySpecPipeline
meta import Strata.Languages.Python.ReadPython
meta import Strata.Languages.Python.PythonToCore
meta import Strata.Languages.Python.Specs.IdentifyOverloads
meta import StrataTest.Util.Python

/-! ## Unit tests for `resolveOverloads`

These tests call `resolveOverloads` directly and assert exact module
sets, ensuring we identify precisely the needed specs — no more, no
fewer.
-/

namespace Strata.Python.Specs.IdentifyOverloadsTest

open Strata (readDispatchOverloads pySpecsDir pySpecOutputPath)
open Strata.Python.Specs.IdentifyOverloads (resolveOverloads)
open Strata.Python (OverloadTable)

private meta def testDir : System.FilePath :=
  "StrataTestExtra/Languages/Python/Specs/dispatch_test"

/-- Compile a Python source file to Ion and return the path. -/
private meta def compilePython
    (pythonCmd : System.FilePath)
    (pyFile : System.FilePath) (outDir : System.FilePath)
    : IO System.FilePath := do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile Python.Python.toIon
    let some stem := pyFile.fileStem
      | throw <| .userError s!"No stem for {pyFile}"
    let ionPath := outDir / s!"{stem}.python.st.ion"
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
      throw <| .userError
        s!"py_to_strata failed for {pyFile} (exit {exitCode}): {stderr}"
    return ionPath

/-- Compile the dispatch pyspec and return the overload table. -/
private meta def buildOverloadTable
    (pythonCmd : System.FilePath)
    (outDir : System.FilePath) : IO OverloadTable := do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile Python.Python.toIon
    -- Compile servicelib dispatch file to pyspec Ion
    let pyFile := testDir / "servicelib" / "__init__.py"
    match ← pySpecsDir testDir outDir dialectFile
        (modules := #["servicelib"])
        (warningOutput := .none)
        (pythonCmd := toString pythonCmd) |>.toBaseIO with
    | .ok () => pure ()
    | .error msg =>
      throw <| .userError s!"pySpecsDir failed for {pyFile}: {msg}"
    let some ionPath := pySpecOutputPath testDir outDir pyFile
      | throw <| .userError s!"Cannot derive output path for {pyFile}"
    match ← readDispatchOverloads #[ionPath.toString] |>.toBaseIO with
    | .ok (tbl, _) => return tbl
    | .error msg =>
      throw <| .userError s!"readDispatchOverloads failed: {msg}"

/-- Parse a user Python Ion file into statements. -/
private meta def parseStmts (ionPath : System.FilePath)
    : IO (Array (Python.stmt SourceRange)) := do
  match ← Strata.Python.readPythonStrata ionPath.toString |>.toBaseIO with
  | .ok stmts =>
    return stmts
  | .error msg =>
    throw <| .userError s!"readPythonStrata failed: {msg}"

/-- Run resolveOverloads on a test file and return the module set. -/
private meta def resolveFile
    (pythonCmd : System.FilePath)
    (tbl : OverloadTable) (pyFile : System.FilePath)
    (outDir : System.FilePath)
    : IO (Std.HashSet String) := do
  let ionPath ← compilePython pythonCmd pyFile outDir
  let stmts ← parseStmts ionPath
  return (resolveOverloads tbl stmts).modules

/-- A test case: Python file and exact expected module set. -/
private structure TestCase where
  file : String
  expected : List String

private meta def testCases : List TestCase := [
  -- Single service at top level
  { file := "test_single_service.py"
    expected := ["servicelib.Storage"] },
  -- Multiple services
  { file := "test_multi_service.py"
    expected := ["servicelib.Storage", "servicelib.Messaging"] },
  -- Dispatch inside a class method
  { file := "test_class_dispatch.py"
    expected := ["servicelib.Storage"] },
  -- Dispatch in both branches of an if/else
  { file := "test_dispatch_in_conditional.py"
    expected := ["servicelib.Storage", "servicelib.Messaging"] },
  -- Dispatch inside a try block
  { file := "test_dispatch_in_try.py"
    expected := ["servicelib.Storage"] },
  -- No dispatch calls at all
  { file := "test_no_dispatch.py"
    expected := [] },
  -- Loop with variable (not string literal) — not resolved
  { file := "test_dispatch_in_loop.py"
    expected := [] }
]

/-- Run a single test case and return an error message on failure. -/
private meta def runTestCase
    (pythonCmd : System.FilePath)
    (tbl : OverloadTable) (outDir : System.FilePath)
    (tc : TestCase) : IO (Option String) := do
  let modules ← resolveFile pythonCmd tbl (testDir / tc.file) outDir
  let expected : Std.HashSet String :=
    tc.expected.foldl (init := {}) fun s m => s.insert m
  if modules == expected then return none
  let got := modules.toList
  let exp := expected.toList
  return some
    s!"{tc.file}: expected modules {exp}, got {got}"

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    let tbl ← buildOverloadTable pythonCmd tmpDir
    -- Launch all tests concurrently
    let mut seen : Std.HashSet String := {}
    let mut tasks : Array (String × Task (Except IO.Error (Option String))) := #[]
    for tc in testCases do
      if tc.file ∈ seen then
        throw <| IO.userError s!"Duplicate test filename: {tc.file}"
      seen := seen.insert tc.file
      let task ← IO.asTask (runTestCase pythonCmd tbl tmpDir tc)
      tasks := tasks.push (tc.file, task)
    -- Collect results
    let mut errors : Array String := #[]
    for (_, task) in tasks do
      match ← IO.wait task with
      | .ok (some err) => errors := errors.push err
      | .ok none => pure ()
      | .error e => errors := errors.push s!"Task error: {e}"
    if errors.size > 0 then
      throw <| IO.userError ("\n".intercalate errors.toList)

end Strata.Python.Specs.IdentifyOverloadsTest
