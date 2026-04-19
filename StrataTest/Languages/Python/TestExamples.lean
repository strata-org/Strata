/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Util.Python
import Strata.Languages.Python.PySpecPipeline
import Strata.Languages.Python.PyFactory
import Strata.Languages.Laurel.LaurelToCoreTranslator

open StrataTest.Util
open Strata
open Lean.Parser (InputContext)

namespace Strata.Python

/-- Run the Python → Ion → Laurel pipeline inside a temp directory and pass
    the resulting Laurel program and the temp source path to a continuation. -/
def withPythonToLaurel (pythonCmd : System.FilePath) (input : InputContext)
    (k : Laurel.Program → System.FilePath → IO α) : IO α := do
  IO.FS.withTempDir fun tmpDir => do
    let pyFile := tmpDir / "test.py"
    IO.FS.writeFile pyFile input.inputString
    let dialectFile := tmpDir / "dialect.ion"
    IO.FS.writeBinFile dialectFile Python.Python.toIon
    let ionFile := tmpDir / "test.python.st.ion"
    let child ← IO.Process.spawn {
      cmd := pythonCmd.toString
      args := #["-m", "strata.gen", "py_to_strata",
                "--dialect", dialectFile.toString,
                pyFile.toString, ionFile.toString]
      inheritEnv := true
      stdin := .null, stdout := .null, stderr := .piped
    }
    let stderr ← child.stderr.readToEnd
    let exitCode ← child.wait
    if exitCode ≠ 0 then
      throw <| .userError s!"py_to_strata failed (exit code {exitCode}): {stderr}"
    match ← pythonAndSpecToLaurel ionFile.toString
        (sourcePath := some pyFile.toString) |>.toBaseIO with
    | .ok r => k r pyFile
    | .error err => throw <| .userError s!"pythonAndSpecToLaurel failed: {err}"

/-- Run the Python → Ion → Laurel pipeline and return the Laurel program.
    The caller can inspect the Laurel IR directly or continue to Core/SMT. -/
def processPythonToLaurel (pythonCmd : System.FilePath) (input : InputContext)
    : IO Laurel.Program :=
  withPythonToLaurel pythonCmd input fun laurel _ => pure laurel

/-- Process a Python source file through the full verification pipeline
    (Python → Ion → Laurel → Core → verify) and return diagnostics.

    The `input` should contain raw Python source code. The `pythonCmd`
    must point to a Python 3 interpreter with `strata.gen` installed. -/
def processPythonFile (pythonCmd : System.FilePath) (input : InputContext)
    : IO (Array Diagnostic) := do
  withPythonToLaurel pythonCmd input fun laurel pyFile => do
    let (coreOpt, translateDiags) ← translateCombinedLaurel laurel
    let uri := Uri.file pyFile.toString
    let files := Map.insert Map.empty uri input.fileMap
    match coreOpt with
    | none =>
      pure (translateDiags.map (·.toDiagnostic files)).toArray
    | some core =>
      let options : Core.VerifyOptions :=
        { Core.VerifyOptions.quiet with removeIrrelevantAxioms := .Precise }
      let vcResults ← IO.FS.withTempDir fun vcDir =>
        EIO.toIO (fun f => IO.Error.userError (toString f))
          (Core.verify core vcDir .none options
            (moreFns := Strata.Python.ReFactory)
            (externalPhases := [Strata.frontEndPhase]))
      let vcDiags := vcResults.toList.filterMap (fun vcr => vcr.toDiagnostic files Core.coreAbstractedPhases)
      pure ((translateDiags.map (·.toDiagnostic files)) ++ vcDiags).toArray

end Strata.Python
