/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.SimpleAPI
meta import Strata.Languages.Python.PySpecPipeline
meta import StrataTest.Util.Python

/-! ## End-to-end tests for `pyAnalyzeLaurel` with dispatch

These tests exercise the full pipeline: compile mock PySpec Python sources
to Ion, compile a user Python script to Ion, then run `pyAnalyzeLaurel`
with `--dispatch` through the SimpleAPI. The mock services (Storage,
Messaging) are generic and not tied to any cloud provider.
-/

namespace Strata.Python.AnalyzeLaurelTest

open Strata (pyAnalyzeLaurel pySpecs)

private meta def testDir : System.FilePath :=
  "StrataTest/Languages/Python/Specs/dispatch_test"

/-- Compile a Python source file to a `.pyspec.st.ion` Ion file using `pySpecs`.
    Returns the path to the generated Ion file. -/
private meta def compilePySpec
    (dialectFile : System.FilePath) (pyFile : System.FilePath)
    (outDir : System.FilePath) : IO System.FilePath := do
  match ← pySpecs pyFile outDir dialectFile
      (warningOutput := .none) |>.toBaseIO with
  | .ok () => pure ()
  | .error msg => throw <| .userError s!"pySpecs failed for {pyFile}: {msg}"
  let some stem := pyFile.fileStem
    | throw <| .userError s!"No stem for {pyFile}"
  return outDir / s!"{stem}.pyspec.st.ion"

/-- Compile a Python source file to a `.python.st.ion` Ion file.
    Returns the path to the generated Ion file. -/
private meta def compilePython
    (dialectFile : System.FilePath) (pyFile : System.FilePath)
    (outDir : System.FilePath) : IO System.FilePath := do
  let some stem := pyFile.fileStem
    | throw <| .userError s!"No stem for {pyFile}"
  let ionPath := outDir / s!"{stem}.python.st.ion"
  let spawnArgs : IO.Process.SpawnArgs := {
    cmd := "python"
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

/-- Set up the test fixture: compile all pyspec files and the dispatch file.
    Returns (dispatchIonPath, pyspecDir). -/
private meta def setupFixture (_pythonCmd : System.FilePath)
    (outDir : System.FilePath) : IO System.FilePath := do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile Python.Python.toIon
    -- Compile service specs
    let _ ← compilePySpec dialectFile (testDir / "Storage.py") outDir
    let _ ← compilePySpec dialectFile (testDir / "Messaging.py") outDir
    -- Compile dispatch file
    compilePySpec dialectFile (testDir / "servicelib.py") outDir

/-- Compile a test Python file to Ion format. -/
private meta def compileTestScript (pyFile : System.FilePath)
    (outDir : System.FilePath) : IO System.FilePath := do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile Python.Python.toIon
    compilePython dialectFile pyFile outDir

/-- Run pyAnalyzeLaurel on a test script within the shared fixture. -/
private meta def runAnalyze (dispatchIon : System.FilePath)
    (tmpDir : System.FilePath) (scriptName : String)
    : IO (Except String Core.Program) := do
  let testIon ← compileTestScript (testDir / scriptName) tmpDir
  let laurel ←
    match ← Strata.pyAnalyzeLaurel testIon.toString
        (dispatchPaths := #[dispatchIon.toString]) |>.toBaseIO with
    | .ok r => pure r
    | .error err => return .error (toString err)
  match Strata.translateCombinedLaurel laurel with
  | (some core, []) =>
    -- Also run Core type checking to catch semantic errors (e.g. Heap vs Any)
    match Core.typeCheck Core.VerifyOptions.quiet core with
    | .error diag => return .error s!"Core type checking failed: {diag}"
    | .ok _ => return .ok core
  | (_, errors) => return .error s!"Laurel to Core translation failed: {errors}"

/-- Expected outcome for a test case. -/
private inductive Expected where
  | success
  | fail (msg : String)

/-- All dispatch test cases: (filename, expected outcome). -/
private meta def testCases : List (String × Expected) := [
  -- Positive tests
  .mk "test_single_service.py" .success,
  .mk "test_multi_service.py" .success,
  .mk "test_annotation_fallback.py" .success,
  .mk "test_required_with_optional.py" .success,
  .mk "test_heap_return.py" .success,
  .mk "test_list_str.py" .success,
  .mk "test_nested_try.py" .success,
  .mk "test_try_scope.py" .success,
  -- Negative tests
  .mk "test_invalid_service.py" $
    .fail "User code error: 'connect' called with unknown string \"invalid\"; known services: #[messaging, storage]",
  .mk "test_invalid_method.py" $
    .fail "User code error: Unknown method 'nonexistent_method'",
  .mk "test_invalid_args.py" $
    .fail "User code error: 'put_item' called with unknown keyword arguments: [Wrong]",
  .mk "test_missing_required.py" $
    .fail "User code error: 'put_item' called with missing required arguments: [Key, Data]",
  .mk "test_extra_kwarg.py" $
    .fail "User code error: 'get_item' called with unknown keyword arguments: [Bogus]",
  .mk "test_no_args.py" $
    .fail "User code error: 'put_item' called with missing required arguments: [Bucket, Key, Data]",
  .mk "test_optional_missing_required.py" $
    .fail "User code error: 'list_items' called with missing required arguments: [Bucket]",
  .mk "test_positional_missing.py" $
    .fail "User code error: 'delete_item' called with missing required arguments: [Key]"
]

/-- Run a single test case and return an error message on failure, or `none` on success. -/
private meta def runTestCase (dispatchIon tmpDir : System.FilePath)
    (scriptName : String) (expected : Expected) : IO (Option String) := do
  let result ← runAnalyze dispatchIon tmpDir scriptName
  match expected, result with
  | .success, .ok _ => return none
  | .success, .error msg =>
    return some s!"pyAnalyzeLaurel failed on {scriptName}: {msg}"
  | .fail _, .ok _ =>
    return some s!"pyAnalyzeLaurel succeeded on {scriptName} but was expected to fail"
  | .fail exp, .error msg =>
    if msg == exp then return none
    else return some s!"{scriptName}: Expected error:\n  {exp}\nGot:\n  {msg}"

#eval withPython fun _pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    let dispatchIon ← setupFixture _pythonCmd tmpDir
    -- Launch all tests concurrently, checking for duplicate filenames
    let mut seen : Std.HashSet String := {}
    let mut tasks : Array (String × Task (Except IO.Error (Option String))) := #[]
    for (scriptName, expected) in testCases do
      if scriptName ∈ seen then
        throw <| IO.userError s!"Duplicate test filename: {scriptName}"
      seen := seen.insert scriptName
      let task ← IO.asTask (runTestCase dispatchIon tmpDir scriptName expected)
      tasks := tasks.push (scriptName, task)
    -- Collect results
    let mut errors : Array String := #[]
    for (_, task) in tasks do
      match ← IO.wait task with
      | .ok (some err) => errors := errors.push err
      | .ok none => pure ()
      | .error e => errors := errors.push s!"Task error: {e}"
    if errors.size > 0 then
      throw <| IO.userError ("\n".intercalate errors.toList)

end Strata.Python.AnalyzeLaurelTest
