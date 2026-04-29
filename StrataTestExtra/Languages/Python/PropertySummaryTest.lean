/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.Python
import Strata.SimpleAPI
import Strata.Languages.Python.PyFactory

/-! ## Test: Python assert messages propagate as property summaries

Verifies that `assert cond, "message"` in Python flows through as a
property summary in the Core verification results.
-/

namespace Strata.Python.PropertySummaryTest

open Strata (pyTranslateLaurel)

/-- Compile a Python string to Ion, translate to Core, verify, and return
    the property summaries from the VCResults. -/
private def getPropertySummaries (pythonCmd : System.FilePath) (source : String)
    : IO (Array String) := do
  IO.FS.withTempDir fun tmpDir => do
    let pyFile := tmpDir / "test.py"
    IO.FS.writeFile pyFile source
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
    let (core, _diags) ← match ← pyTranslateLaurel ionFile.toString |>.toBaseIO with
      | .ok r => pure r
      | .error msg => throw <| .userError s!"pyTranslateLaurel failed: {msg}"
    let results ← match ← Core.verifyProgram core Core.VerifyOptions.quiet
        (moreFns := Strata.Python.ReFactory) |>.toBaseIO with
      | .ok r => pure r
      | .error msg => throw <| .userError s!"verifyCore failed: {msg}"
    return results.filterMap fun vcr =>
      vcr.obligation.metadata.getPropertySummary

#guard_msgs in
#eval withPython fun pythonCmd => do
  let summaries ← getPropertySummaries pythonCmd
    "def main(x: int) -> None:\n    assert x == x, \"reflexivity\"\n    assert x + 0 == x, \"additive identity\"\n"
  let expected := #["reflexivity", "additive identity"]
  for msg in expected do
    unless summaries.any (· == msg) do
      throw <| .userError s!"FAIL: \"{msg}\" not found in summaries: {summaries}"

end Strata.Python.PropertySummaryTest
