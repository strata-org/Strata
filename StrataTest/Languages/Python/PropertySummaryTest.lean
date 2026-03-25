/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

meta import Strata.SimpleAPI
meta import StrataTest.Util.Python

/-! ## Test: Python assert messages propagate as property summaries

Verifies that `assert cond, "message"` in Python flows through as a
property summary in the Core verification results.
-/

namespace Strata.Python.PropertySummaryTest

open Strata (pyTranslateLaurel verifyCore)

private meta def testPy : String :=
"def main(x: int) -> None:
    assert x == x, \"reflexivity\"
    assert x + 0 == x, \"additive identity\"
"

/-- Compile a Python string to Ion, translate to Core, verify, and return
    the property summaries from the VCResults. -/
private meta def getPropertySummaries (pythonCmd : System.FilePath) : IO (Array String) := do
  IO.FS.withTempDir fun tmpDir => do
    -- Write Python source
    let pyFile := tmpDir / "test.py"
    IO.FS.writeFile pyFile testPy
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
      stdin := .null, stdout := .piped, stderr := .piped
    }
    let stderr ← child.stderr.readToEnd
    let exitCode ← child.wait
    if exitCode ≠ 0 then
      throw <| .userError s!"py_to_strata failed: {stderr}"
    -- Translate to Core
    let (core, _diags) ← match ← pyTranslateLaurel ionFile.toString |>.toBaseIO with
      | .ok r => pure r
      | .error msg => throw <| .userError s!"pyTranslateLaurel failed: {msg}"
    -- Verify
    let results ← match ← verifyCore core Core.VerifyOptions.quiet |>.toBaseIO with
      | .ok r => pure r
      | .error msg => throw <| .userError s!"verifyCore failed: {msg}"
    -- Extract property summaries
    return results.filterMap fun vcr =>
      vcr.obligation.metadata.getPropertySummary

#eval withPython fun pythonCmd => do
  let summaries ← getPropertySummaries pythonCmd
  let expected := #["reflexivity", "additive identity"]
  for msg in expected do
    unless summaries.any (· == msg) do
      throw <| .userError s!"FAIL: \"{msg}\" not found in summaries: {summaries}"
  IO.println "PASS: Python assert messages propagate as property summaries"

end Strata.Python.PropertySummaryTest
