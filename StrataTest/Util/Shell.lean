/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-! # Shell command runner

Provides `runShell` for running shell scripts. Used by test files to wrap
CI shell scripts as Lean build targets so that `lake test` exercises them.

Usage in test files:
```
#eval runShell "path/to/script.sh"
```
-/

/-- Run a shell script via bash. Throws on non-zero exit. -/
def runShell (script : String) : IO Unit := do
  let result ← IO.Process.output {
    cmd := "bash"
    args := #[script]
  }
  unless result.stdout.isEmpty do
    IO.println result.stdout
  unless result.stderr.isEmpty do
    IO.eprintln result.stderr
  if result.exitCode != 0 then
    throw <| .userError s!"Shell script failed (exit {result.exitCode}): {script}"
