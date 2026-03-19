/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.SimpleAPI
meta import Strata.Languages.Python.PySpecPipeline
meta import StrataTest.Util.Python

/-! ## End-to-end tests for PySpec precondition assertion translation

These tests verify that PySpec `assert` preconditions are translated into
Core assertions. The pyspec file `MessageService.py` defines `send()` with
three `len` preconditions. The test checks that the generated Core program
contains assert statements from the pyspec procedure.
-/

namespace Strata.Python.PreconditionTest

open Strata (pyAnalyzeLaurel pySpecs)

private meta def testDir : System.FilePath :=
  "StrataTest/Languages/Python/Specs/precondition_test"

/-- Compile a Python source file to a `.pyspec.st.ion` Ion file. -/
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

/-- Compile a Python source file to a `.python.st.ion` Ion file. -/
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

#eval! Strata.Python.withPython fun _pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    IO.FS.withTempFile fun _handle dialectFile => do
      IO.FS.writeBinFile dialectFile Python.Python.toIon
      let pyspecIon ← compilePySpec dialectFile (testDir / "MessageService.py") tmpDir
      let testIon ← compilePython dialectFile (testDir / "test_precondition_pass.py") tmpDir

      -- Run pipeline up to Core translation
      let laurel ←
        match ← pyAnalyzeLaurel testIon.toString
            (pyspecPaths := #[pyspecIon.toString]) |>.toBaseIO with
        | .ok r => pure r
        | .error err => throw <| .userError s!"pyAnalyzeLaurel failed: {err}"
      let translateResult := Strata.translateCombinedLaurel laurel
      let coreProgram ← match translateResult with
        | .ok (core, _) => pure core
        | .error _ => throw <| .userError "Laurel→Core translation failed"

      -- Check that the Core program contains assert statements from pyspec
      -- by printing the program and checking the output
      let coreStr := toString (Std.format coreProgram)
      let hasAssert := (coreStr.splitOn "assert [").length > 1
      let hasSendProc := (coreStr.splitOn "MessageService_send").length > 1
      let hasStrLen := (coreStr.splitOn "str.len").length > 1
      if !hasSendProc then
        throw <| .userError "Expected MessageService_send procedure in Core program"
      if !hasAssert then
        throw <| .userError "Expected assert statements in Core program"
      if !hasStrLen then
        throw <| .userError "Expected str.len in Core assertions"
      -- Count assert statements in the send procedure
      let assertCount := (coreStr.splitOn "assert [").length - 1
      IO.println s!"✅ PySpec preconditions: Core program contains {assertCount} assert statement(s) with str.len checks"

end Strata.Python.PreconditionTest
