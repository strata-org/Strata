/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-! ## CBMC tests under `lake test`

Runs `StrataTest/Backends/CBMC/run_cbmc_tests.sh` and fails if any suite
fails. With `CBMC_TESTS_REQUIRED` set (the Brazil build sets it, since its
`Config` declares CBMC) a missing CBMC tool fails the test; otherwise the
script prints `SKIP` and this test passes. See `StrataTest/Backends/CBMC/README.md`.
-/

#eval show IO Unit from do
  let required := (← IO.getEnv "CBMC_TESTS_REQUIRED").isSome
  let env : Array (String × Option String) :=
    if required then #[] else #[("CBMC_TESTS_SKIP_IF_MISSING", some "1")]
  let child ← IO.Process.spawn {
    cmd := "bash"
    args := #["StrataTest/Backends/CBMC/run_cbmc_tests.sh"]
    env
  }
  let code ← child.wait
  if code != 0 then
    throw (IO.userError s!"CBMC tests failed (exit code {code})")
