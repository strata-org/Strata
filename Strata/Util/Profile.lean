/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

@[inline] public def nsToMs (ns : Nat) : Nat := (ns + 500000) / 1000000

/-- Measure the wall-clock nanoseconds taken by a pure expression.
    Takes a thunk to ensure the expression is not evaluated before timing starts.
    The `t1 == 0` trick creates a data dependency preventing reordering. -/
@[inline] public def measureNanos [Inhabited α] (expr : Unit → α) : BaseIO (α × Nat) := do
  let t1 ← IO.monoNanosNow
  let result := if t1 == 0 then default else expr ()
  let t2 ← IO.monoNanosNow
  pure (result, t2 - t1)

/-- Run an action, printing its elapsed time in milliseconds to stdout when `profile` is true. -/
public def profileStep {m α} [Monad m] [MonadLiftT BaseIO m]
    (profile : Bool) (name : String) (action : m α) : m α := do
  if !profile then return ← action
  let start ← IO.monoNanosNow
  let result ← action
  let elapsed := (← IO.monoNanosNow) - start
  let _ ← (IO.println s!"[profile] {name}: {nsToMs elapsed}ms" |>.toBaseIO)
  pure result
