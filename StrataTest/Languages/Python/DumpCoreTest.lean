/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.SimpleAPI
meta import Strata.Languages.Python.PySpecPipeline
meta import Strata.Languages.Laurel.LaurelFormat
meta import StrataTest.Util.Python

/-! ## Core IR dump for debugging type checking failures

Run with: `lake build StrataTest.Languages.Python.DumpCoreTest`
-/

namespace Strata.Python.DumpCoreTest

open Strata (pyAnalyzeLaurel pySpecs)

private meta def testDir : System.FilePath :=
  "StrataTest/Languages/Python/Specs/dispatch_test"

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

-- *** CHANGE THIS to investigate a different test ***
private def scriptName : String := "test_class_init_kwargs.py"

#eval withPython fun _pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    IO.FS.withTempFile fun _handle dialectFile => do
      IO.FS.writeBinFile dialectFile Python.Python.toIon
      let _ ← compilePySpec dialectFile (testDir / "Storage.py") tmpDir
      let _ ← compilePySpec dialectFile (testDir / "Messaging.py") tmpDir
      let dispatchIon ← compilePySpec dialectFile (testDir / "servicelib.py") tmpDir

      let testIon ← compilePython dialectFile (testDir / scriptName) tmpDir

      -- Run pyAnalyzeLaurel
      let laurel ←
        match ← Strata.pyAnalyzeLaurel testIon.toString
            (dispatchPaths := #[dispatchIon.toString]) |>.toBaseIO with
        | .ok r => pure r
        | .error err =>
          IO.eprintln s!"pyAnalyzeLaurel failed: {err}"
          return

      -- Dump Laurel IR
      IO.println "=== Laurel Program ==="
      IO.println s!"{Strata.Laurel.formatProgram laurel}"
      IO.println ""

      -- Translate to Core
      match Strata.translateCombinedLaurel laurel with
      | (none, diagnostics) =>
        IO.eprintln s!"Laurel to Core translation failed: {diagnostics}"
        return
      | (some core, _) =>
        -- Dump Core IR
        IO.println "=== Core Program ==="
        IO.println s!"{Core.Program.formatWithMetaData core}"
        IO.println ""

        -- Try type checking and report error with context
        match Core.typeCheck Core.VerifyOptions.quiet core with
        | .error diag =>
          IO.eprintln "=== Type Checking Error ==="
          IO.eprintln s!"{diag}"
        | .ok _ =>
          IO.println "=== Type checking succeeded ==="

end Strata.Python.DumpCoreTest
