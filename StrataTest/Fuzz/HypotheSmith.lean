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
#eval withPython fun pythonCmd => do
  -- Check that hypothesmith is installed
  unless ← pythonCheckModule pythonCmd "hypothesmith" do
    IO.eprintln "⚠ Fuzz test skipped: hypothesmith not installed"
    return

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
    throw <| .userError s!"Fuzz test failed (exit code {result.exitCode})"
