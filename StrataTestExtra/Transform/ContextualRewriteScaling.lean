/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-! ## Contextual rewriting on a value that copies itself

`selfCopyProg k` repeats `r := int.add(r, r)` `k` times and asserts `int.ge(r, r)`.
Symbolic execution inlines each assignment, so the goal is a term that shares its
subterms: small in memory, but with a tree of about `2^(k+3)` nodes. Rewriting walks the
tree, so the `contextualRewrite` phase leaves a goal with more than
`maxTreeSize` nodes alone, and counts it in `ContextualRewrite.skippedLarge`; the
solver proves it.

The test verifies the program with 24 copies under `--vcgen symexec:per-path`, with the phase
after `betaReduce` in the default order (`--phases`), using the compiled `strataLaurel`
executable (in that mode
common-subexpression elimination runs on so large a tree, and names its shared parts for the
solver), and reads the time of the `contextualRewrite` phase from `--profile`, keeping the
fastest of three runs. The phase takes milliseconds when it skips the goal and many seconds
when it rewrites it, so the 1 s bound catches a rewrite of the goal without flaking on a
loaded host. The test reads the clock, so it runs under `lake test` rather than `lake build`,
where host load could fail the build. -/

namespace Strata.ContextualRewriteScaling

/-- Built by `lake`; listed in `StrataTestMain`'s `needs`. -/
def strataLaurelExe : System.FilePath := ".lake/build/bin/strataLaurel"

/-- `r := int.add(r, r)` repeated `k` times, then an assert. -/
def selfCopyProg (k : Nat) : String := Id.run do
  let mut lines := #["program Core;", "procedure P(x : int, out r : int) {",
    "  assume int.gt(x, 0);", "  r := x;"]
  for _ in [0:k] do
    lines := lines.push "  r := int.add(r, r);"
  lines := lines ++ #["  assert [pos]: int.ge(r, r);", "};"]
  return "\n".intercalate lines.toList

/-- The milliseconds `--profile` reports for the `contextualRewrite` phase. -/
def phaseMillis (out : String) : Option Nat := do
  let line ← (out.splitOn "\n").find? (·.contains "[profile] contextualRewrite ")
  let after ← (line.splitOn "total: ")[1]?
  (after.takeWhile Char.isDigit).toString.toNat?

/-- The default order of `--vcgen vcgen`, which `--display-phases` prints, with the
    `contextualRewrite` phase after `betaReduce`, as an argument of `--phases`. -/
def rewriteOrder (vcgen : String) : IO String := do
  let r ← IO.Process.output
    { cmd := strataLaurelExe.toString, args := #["verify", "--vcgen", vcgen, "--display-phases"] }
  let some line := (r.stdout.splitOn "\n").find? (·.trimAscii.startsWith "--phases ")
    | throw <| IO.userError s!"no default order (exit {r.exitCode}):\n{r.stdout}\n{r.stderr}"
  let some names := (line.trimAscii.toString.splitOn " ")[1]?
    | throw <| IO.userError s!"no phase names in {line}"
  return ",".intercalate ((names.splitOn ",").flatMap fun n =>
    if n == "betaReduce" then [n, "contextualRewrite"] else [n])

/-- Verifies `src` three times under `--vcgen vcgen` with the phase after `betaReduce`
    (`rewriteOrder`), returning the last run's verdict line,
    its `ContextualRewrite.skippedLarge` statistic line, and the fastest `contextualRewrite`
    time in milliseconds. -/
def timedPhase (src : String) (vcgen : String := "symexec") : IO (String × String × Nat) := do
  unless ← strataLaurelExe.pathExists do
    throw <| IO.userError s!"{strataLaurelExe} has not been built; run `lake build`."
  let phases ← rewriteOrder vcgen
  let dir ← IO.FS.createTempDir
  let file := dir / "ContextualRewriteScaling.core.st"
  IO.FS.writeFile file src
  let mut best := 0
  let mut verdict := ""
  let mut skipped := ""
  for i in [0:3] do
    let r ← IO.Process.output
      { cmd := strataLaurelExe.toString,
        args := #["verify", "--vcgen", vcgen, "--phases", phases, "--profile",
          file.toString] }
    let some ms := phaseMillis r.stdout
      | IO.FS.removeDirAll dir
        throw <| IO.userError
          s!"no contextualRewrite time (exit {r.exitCode}):\n{r.stdout}\n{r.stderr}"
    let lines := r.stdout.trimAscii.toString.splitOn "\n"
    verdict := lines.getLast?.getD ""
    skipped := (lines.find? (·.contains "ContextualRewrite.skippedLarge")).getD ""
    best := if i == 0 then ms else min best ms
  IO.FS.removeDirAll dir
  return (verdict, skipped, best)

/--
info: All 1 goals passed.
[statistics] ContextualRewrite.skippedLarge: 1
within the time bound: true
-/
#guard_msgs in
#eval show IO Unit from do
  let (verdict, skipped, ms) ← timedPhase (selfCopyProg 24) (vcgen := "symexec:per-path")
  IO.println s!"{verdict}\n{skipped}\nwithin the time bound: {decide (ms < 1000)}"

/-! ## Contextual rewriting on chained joins

`diamondProg k` updates an `IntOpt` value `r` in one branch of each of `k` conditionals and
asserts `IntOpt..isSome(r)` after them, or after each one. Symbolic execution defines a join
symbol after each conditional,
`r_i == ite(b_i, Some(val(r_{i-1}) + val(r_{i-1})), r_{i-1})`, which reads its predecessor three
times, so the definitions expanded into one another grow as `3^i`. The phase
reads through a definition only while the expanded size of what it reads stays within its
allowance, so it gives up on the later goals quickly; the solver proves them. -/

/-- The diamond program with `k` conditionals, asserting `IntOpt..isSome(r)` at the end, or,
    with `each`, after every conditional. -/
def diamondProg (k : Nat) (each : Bool := false) : String := Id.run do
  let bs := ", ".intercalate ((List.range k).map fun i => s!"b{i} : bool")
  let mut lines := #["program Core;", "datatype IntOpt { None(), Some(val: int) };",
    s!"procedure P(i : int, {bs}, out r : IntOpt) \{", "  r := Some(i);"]
  for i in [0:k] do
    lines := lines.push
      s!"  if (b{i}) \{ r := Some(int.add(IntOpt..val(r), IntOpt..val(r))); } else \{ r := r; }"
    if each then lines := lines.push s!"  assert [s{i}]: IntOpt..isSome(r);"
  lines := lines ++ #["  assert [s]: IntOpt..isSome(r);", "};"]
  return "\n".intercalate lines.toList

/--
info: All 41 goals passed.
within the time bound: true
-/
#guard_msgs in
#eval show IO Unit from do
  let (verdict, _, ms) ← timedPhase (diamondProg 20)
  IO.println s!"{verdict}\nwithin the time bound: {decide (ms < 1000)}"

/--
info: All 61 goals passed.
within the time bound: true
-/
#guard_msgs in
#eval show IO Unit from do
  let (verdict, _, ms) ← timedPhase (diamondProg 20 (each := true))
  IO.println s!"{verdict}\nwithin the time bound: {decide (ms < 1000)}"

/-! ## Contextual rewriting on a long straight-line program under `--vcgen wp`

`straightProg n` declares `n` variables in a row, each followed by an assumption about it and
an assertion of the same fact. The WP phase writes its obligation as a chain of `if *`
statements, one per assertion, each the last statement of the `else` branch of the one before,
so the walk reaches a depth of `n`. The facts grow by one variable at each level; the walk
neither joins nor copies them there, nor forgets anything at a declaration, so its time grows
about linearly with `n`; the 1 s bound catches a walk whose time grows with the square of `n`.
The phase proves every goal. -/

/-- `n` declarations, each followed by an assumption and an assertion of the same fact. -/
def straightProg (n : Nat) : String := Id.run do
  let mut lines := #["program Core;", "procedure P(x : int, y : int) {"]
  for i in [0:n] do
    lines := lines ++ #[s!"  var v{i} : int := int.add(x, {i});",
      s!"  assume int.gt(v{i}, y);", s!"  assert [a{i}]: int.gt(v{i}, y);"]
  lines := lines.push "};"
  return "\n".intercalate lines.toList

/--
info: All 2000 goals passed.
within the time bound: true
-/
#guard_msgs in
#eval show IO Unit from do
  let (verdict, _, ms) ← timedPhase (straightProg 2000) (vcgen := "wp")
  IO.println s!"{verdict}\nwithin the time bound: {decide (ms < 1000)}"

end Strata.ContextualRewriteScaling
