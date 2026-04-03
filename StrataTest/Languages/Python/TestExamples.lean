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

/-- Process a Python source file through the full verification pipeline
    (Python → Ion → Laurel → Core → verify) and return diagnostics.

    The `input` should contain raw Python source code. The `pythonCmd`
    must point to a Python 3 interpreter with `strata.gen` installed. -/
def processPythonFile (pythonCmd : System.FilePath) (input : InputContext)
    : IO (Array Diagnostic) := do
  IO.FS.withTempDir fun tmpDir => do
    -- Write Python source (temp filename is irrelevant; the temp dir is ephemeral
    -- and the URI for diagnostic mapping comes from input.fileMap, not this path)
    let pyFile := tmpDir / "test.py"
    IO.FS.writeFile pyFile input.inputString

    -- Write dialect file
    let dialectFile := tmpDir / "dialect.ion"
    IO.FS.writeBinFile dialectFile Python.Python.toIon

    -- Compile to Ion
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

    -- Translate Python Ion → Laurel
    let laurel ←
      match ← pyAnalyzeLaurel ionFile.toString
          (sourcePath := some pyFile.toString) |>.toBaseIO with
      | .ok r => pure r
      | .error err => throw <| .userError s!"pyAnalyzeLaurel failed: {err}"

    -- Translate Laurel → Core (using Python-specific translateCombinedLaurel)
    let (coreOpt, translateDiags) := translateCombinedLaurel laurel

    let uri := Uri.file pyFile.toString
    let files := Map.insert Map.empty uri input.fileMap

    match coreOpt with
    | none =>
      pure (translateDiags.map (·.toDiagnostic files)).toArray
    | some core =>
      -- Verify Core with Python-specific factory functions
      let options : Core.VerifyOptions :=
        { Core.VerifyOptions.quiet with removeIrrelevantAxioms := .Precise }
      let vcResults ← IO.FS.withTempDir fun vcDir =>
        EIO.toIO (fun f => IO.Error.userError (toString f))
          (Core.verify core vcDir .none options
            (moreFns := Strata.Python.ReFactory)
            (externalPhases := [Strata.frontEndPhase]))
      let vcDiags := vcResults.toList.filterMap (fun vcr => vcr.toDiagnostic files)
      pure ((translateDiags.map (·.toDiagnostic files)) ++ vcDiags).toArray

end Strata.Python
