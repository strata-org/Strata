/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-! ## Common subexpression elimination on many sequential path splits

`branchesProg n` is the program of `Examples/CSEPathSplits.core.st` with `n`
branches: a shared term `y` built by four steps of `y := y * y + y`, then `n`
sequential branches that each assume a fact about `y`, check `r == y` and leave
the block. Symbolic evaluation nests a block per branch, and every resulting
path repeats `y`. A CSE pass that is quadratic in the nesting depth, or that
rewrites shared subterms once per statement, is slow here.

The test verifies the program with 400 branches using the compiled
`strataLaurel` executable, and reads the time of the `commonSubexprElim` phase
from `--profile`, keeping the fastest of three runs. `#eval` would interpret
CSE, which hides most of the difference between linear and super-linear code.
On one loaded host CSE took 0.65 to 0.9 s here, and 19 to 25 s before it was
made linear per round, so the 9 s bound is ten times the current cost and two to
three times below the old one. The test reads the clock, so it runs under
`lake test` rather than `lake build`, where host load could fail the build. -/

namespace Strata.CSEScaling

/-- Built by `lake`; listed in `StrataTestMain`'s `needs`. -/
def strataLaurelExe : System.FilePath := ".lake/build/bin/strataLaurel"

/-- The program of `Examples/CSEPathSplits.core.st`, with `n` branches. -/
def branchesProg (n : Nat) : String := Id.run do
  let mut lines := #["program Core;",
    "procedure Dispatch(x : int, out y : int, out r : int)",
    "spec { ensures [r_is_y]: r == y; }",
    "{", "  y := x;"]
  for _ in [0:4] do
    lines := lines.push "  y := int.add(int.mul(y, y), y);"
  lines := lines.push "  done: {"
  for i in [0:n] do
    lines := lines.push s!"    if (x == {i}) \{ assume [a{i}]: int.ge(int.add(y, {i}), 0); \
      r := y; assert [b{i}]: r == y; exit done; }"
  lines := lines ++ #["    r := y;", "  }", "};"]
  return "\n".intercalate lines.toList

/-- The milliseconds `--profile` reports for the `commonSubexprElim` phase. -/
def cseMillis (out : String) : Option Nat := do
  let line ← (out.splitOn "\n").find? (·.contains "[profile] commonSubexprElim ")
  let after ← (line.splitOn "total: ")[1]?
  (after.takeWhile Char.isDigit).toString.toNat?

/-- Verifies `branchesProg n` three times, returning the last run's verdict line and the
    fastest `commonSubexprElim` time in milliseconds. -/
def timedCse (n : Nat) : IO (String × Nat) := do
  unless ← strataLaurelExe.pathExists do
    throw <| IO.userError s!"{strataLaurelExe} has not been built; run `lake build`."
  let dir ← IO.FS.createTempDir
  let file := dir / "CSEScaling.core.st"
  IO.FS.writeFile file (branchesProg n)
  let mut best := 0
  let mut verdict := ""
  for i in [0:3] do
    let r ← IO.Process.output
      { cmd := strataLaurelExe.toString, args := #["verify", "--profile", file.toString] }
    let some ms := cseMillis r.stdout
      | IO.FS.removeDirAll dir
        throw <| IO.userError s!"no commonSubexprElim time (exit {r.exitCode}):\n{r.stdout}\n{r.stderr}"
    verdict := ((r.stdout.trimAscii.toString.splitOn "\n").getLast?.getD "")
    best := if i == 0 then ms else min best ms
  IO.FS.removeDirAll dir
  return (verdict, best)

/-- info: All 401 goals passed., within the time bound: true -/
#guard_msgs in
#eval show IO Unit from do
  let (verdict, ms) ← timedCse 400
  IO.println s!"{verdict}, within the time bound: {decide (ms < 9000)}"

end Strata.CSEScaling
