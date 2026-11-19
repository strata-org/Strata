/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-! # Timing helpers for scaling tests

A scaling test times a computation at two sizes and checks the ratio, which does not depend
on the speed of the host. `fastestOf n work` runs `work ()` `n` times and returns whether
every run returned `true` and the fastest run's time in nanoseconds; keeping the fastest run
filters out the slowdowns a loaded host adds. Each run sits in `IO.lazyPure`, so it runs
between the two clock reads. `scalesUnder` compares two such measurements.

A thunk with no free variables, such as `fun _ => f (input 4000)`, may be compiled into a
constant computed once, so that only the first run does the work. `scalesUnder` therefore
takes the inputs as values, built before the clock starts, and times `f` applied to each. -/

meta section
public section

namespace StrataTest.Scaling

/-- Runs `work ()` `n` times, returning whether every run returned `true` and the fastest
    run's time in nanoseconds. -/
def fastestOf (n : Nat) (work : Unit → Bool) : IO (Bool × Nat) := do
  let mut ok := true
  let mut best := 0
  for i in [0:n] do
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure work
    let t1 ← IO.monoNanosNow
    ok := ok && r
    best := if i == 0 then t1 - t0 else min best (t1 - t0)
  return (ok, best)

/-- Whether `f` returned `true` on both inputs and took less than `bound` times as long on
    `large` as on `small`, each the fastest of five runs. -/
def scalesUnder {α : Type} (bound : Nat) (f : α → Bool) (small large : α) : IO Bool := do
  let (ok₁, t₁) ← fastestOf 5 fun _ => f small
  let (ok₂, t₂) ← fastestOf 5 fun _ => f large
  return ok₁ && ok₂ && t₂ < bound * t₁

end StrataTest.Scaling

end
end
