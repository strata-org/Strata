/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import StrataTest.Transform.SimplifyTests

meta section

/-! ## Deep and long branch structures are simplified in linear time

On the two chains of `StrataTest/Transform/SimplifyTests.lean` (`elseIfChain`, whose every
level writes `x`, and `freshVarChain`, whose every level also declares a fresh variable),
`simpStmts` and `dropDeadDefs` cost time linear in the depth. Each branch reads the write
and read sets of its arms from their own traversal, and the join tests membership in hash
sets. On `writeFreeIfs`, branches in sequence that write nothing, they cost time linear
in the length: the sweep updates one live set in place across both arms of a branch.

The test times each chain at depths 125 and 1000, and the sequence at lengths 500 and
4000, keeping the fastest of five runs, and checks that the larger input takes less than
32 times as long. Linear cost gives a ratio near 8, quadratic cost near 64, cubic cost
near 512, so the bound leaves a factor of four of slack above linear cost and rejects
quadratic cost. A ratio does not depend on the speed of the host, and `maxHeartbeats`
does not limit `#eval`. The test reads the clock, so it runs under `lake test` rather
than `lake build`, where host load could fail the build. -/

namespace Core.Simplify.Tests

/-- Runs `simplifiesUnchanged ss` five times, returning whether every run left `ss`
    unchanged and the fastest run's time in nanoseconds. The work sits in
    `IO.lazyPure`, so it runs between the two clock reads. -/
private def timedChain (ss : List Statement) : IO (Bool × Nat) := do
  let mut ok := true
  let mut best := 0
  for i in [0:5] do
    let t0 ← IO.monoNanosNow
    let same ← IO.lazyPure fun _ => simplifiesUnchanged ss
    let t1 ← IO.monoNanosNow
    ok := ok && same
    best := if i == 0 then t1 - t0 else min best (t1 - t0)
  return (ok, best)

/-- Whether `chain n` and `chain (8 * n)` come back unchanged, and whether the second
    takes less than 32 times as long as the first. -/
private def scalesLinearly (chain : Nat → List Statement) (n : Nat := 125) :
    IO (Bool × Bool) := do
  let (ok₁, t₁) ← timedChain (chain n)
  let (ok₂, t₂) ← timedChain (chain (8 * n))
  return (ok₁ && ok₂, decide (t₂ < 32 * t₁))

/-- info: (true, true) -/
#guard_msgs in
#eval scalesLinearly elseIfChain

/-- info: (true, true) -/
#guard_msgs in
#eval scalesLinearly freshVarChain

/-- info: (true, true) -/
#guard_msgs in
#eval scalesLinearly writeFreeIfs 500

end Core.Simplify.Tests
