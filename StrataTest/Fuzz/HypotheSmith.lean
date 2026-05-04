/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.Python

/-!
# Lightweight fuzz test via hypothesmith

Runs a small deterministic batch of fuzz tests when the Python tooling
is available. Skips gracefully otherwise. The full random-seed fuzzing
lives in `.github/workflows/python-fuzz.yml`.
-/

open Strata.Python in
#eval do
  -- Skip gracefully when Python or strata.gen is not available (e.g. in the
  -- "Build and test Lean" CI job which doesn't install Python libraries).
  let pythonCmd ← try findPython3 (minVersion := 11) (maxVersion := 14)
    catch _ => IO.eprintln "⚠ Fuzz test skipped: Python 3 not found"; return
  unless ← pythonCheckModule pythonCmd "strata.gen" do
    IO.eprintln "⚠ Fuzz test skipped: strata.gen not installed"; return
  unless ← pythonCheckModule pythonCmd "hypothesmith" do
    IO.eprintln "⚠ Fuzz test skipped: hypothesmith not installed"; return

  -- Run a small deterministic batch (3 tests, fixed seed, both modes)
  let script := "Tools/Python/scripts/hypothesmith.sh"
  let result ← IO.Process.output {
    cmd := "bash"
    args := #[script, "3", "20260423", "both"]
    env := #[("PYTHON", pythonCmd.toString)]
    inheritEnv := true
  }
  IO.print result.stdout
  if result.exitCode != 0 then
    IO.eprint result.stderr
    throw <| IO.userError s!"Fuzz test failed (exit code {result.exitCode})"
