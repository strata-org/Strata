/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-! ## Axiom pruning on many obligations that share a long path condition

`sharedPathProg k n` is the program of `Examples/AxiomRelevancePaths.core.st`
with `k` functions and `n` assertions: `k` uninterpreted functions with one
axiom each, one assumption about every function, then `n` assertions that all
share that path condition. Under `--remove-irrelevant-axioms precise` the
relevance query of every assertion is seeded with the function names of the
whole path condition. Pruning that deduplicates those names in quadratic time,
walks every path expression again for each obligation, or recomputes each
function's call-graph closure per obligation is slow here.

The test runs the compiled `strataLaurel` executable on the program with 800
functions and 40 assertions, with `--no-solve` (the pruning runs before any
solver call), and reads the time of the `evalDischarge` phase, where the
pruning happens, from `--profile`, keeping the fastest of three runs. `#eval`
would interpret the pruning, which hides most of the difference between linear
and super-linear code. The pruning is linear per obligation: about 0.15 s for the
whole phase here. A quadratic deduplication of the seeds, a per-obligation walk
of the shared path, or a per-obligation call-graph closure takes seconds here, so
the 1.5 s bound (about ten times the linear cost) catches it. The test reads the
clock, so it runs under `lake test` rather than `lake build`, where host load
could fail the build. -/

namespace Strata.IrrelevantAxiomsScaling

/-- Built by `lake`; listed in `StrataTestMain`'s `needs`. -/
def strataLaurelExe : System.FilePath := ".lake/build/bin/strataLaurel"

/-- The program of `Examples/AxiomRelevancePaths.core.st`, with `k` functions and `n`
    assertions (`n ≤ k`). -/
def sharedPathProg (k n : Nat) : String := Id.run do
  let mut lines := #["program Core;"]
  for i in [0:k] do
    lines := lines.push s!"function f{i}(x : int) : int; \
      axiom [f{i}_pos]: forall x : int :: int.gt(f{i}(x), 0);"
  lines := lines ++ #["procedure SharedPath()", "{"]
  for i in [0:k] do
    let arg := (List.range 8).foldl (fun t c => s!"int.add({t}, {c + 1})") s!"v{i}"
    lines := lines.push s!"  var v{i} : int; assume [h{i}]: int.gt(f{i}({arg}), {i});"
  for j in [0:n] do
    lines := lines.push s!"  assert [g{j}]: int.gt(f{j}({j}), 0);"
  lines := lines.push "};"
  return "\n".intercalate lines.toList

/-- The milliseconds `--profile` reports for the `evalDischarge` phase. -/
def evalDischargeMillis (out : String) : Option Nat := do
  let line ← (out.splitOn "\n").find? (·.contains "[profile] evalDischarge ")
  let after ← (line.splitOn "total: ")[1]?
  (after.takeWhile Char.isDigit).toString.toNat?

/-- Runs `strataLaurel verify --profile --no-solve --remove-irrelevant-axioms precise` on
    `sharedPathProg k n` three times, returning the number of SMT files the last run wrote
    and the fastest `evalDischarge` time in milliseconds. -/
def timedPruning (k n : Nat) : IO (Nat × Nat) := do
  unless ← strataLaurelExe.pathExists do
    throw <| IO.userError s!"{strataLaurelExe} has not been built; run `lake build`."
  let dir ← IO.FS.createTempDir
  let file := dir / "SharedPath.core.st"
  IO.FS.writeFile file (sharedPathProg k n)
  let mut best := 0
  let mut smtFiles := 0
  for i in [0:3] do
    let vcDir := dir / s!"vc{i}"
    let r ← IO.Process.output
      { cmd := strataLaurelExe.toString,
        args := #["verify", "--profile", "--no-solve", "--vc-directory", vcDir.toString,
          "--remove-irrelevant-axioms", "precise", file.toString] }
    let some ms := evalDischargeMillis r.stdout
      | IO.FS.removeDirAll dir
        throw <| IO.userError s!"no evalDischarge time (exit {r.exitCode}):\n{r.stdout}\n{r.stderr}"
    smtFiles := (← vcDir.readDir).size
    best := if i == 0 then ms else min best ms
  IO.FS.removeDirAll dir
  return (smtFiles, best)

/-- info: SMT files: 40, within the time bound: true -/
#guard_msgs in
#eval show IO Unit from do
  let (smtFiles, ms) ← timedPruning 800 40
  IO.println s!"SMT files: {smtFiles}, within the time bound: {decide (ms < 1500)}"

end Strata.IrrelevantAxiomsScaling
