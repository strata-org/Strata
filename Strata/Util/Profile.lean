/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Std.Data.HashMap.Basic

@[inline] public def nsToMs (ns : Nat) : Nat := (ns + 500000) / 1000000

/-- Measure the wall-clock nanoseconds taken by a pure expression.
    Takes a thunk to ensure the expression is not evaluated before timing starts.
    The `t1 == 0` trick prevents hoisting `result` above t1.
    Writing `result` to an `IO.Ref` forces its evaluation before t2 is read. -/
public def measureNanos [Inhabited α] (expr : Unit → α) : BaseIO (α × Nat) := do
  let ref ← IO.mkRef (default : α)
  let t1 ← IO.monoNanosNow
  let result := if t1 == 0 then default else expr ()
  ref.set result
  let t2 ← IO.monoNanosNow
  pure (result, t2 - t1)

/-- Run an action and return its result along with the elapsed nanoseconds. -/
@[inline] public def recordNanos {m α} [Monad m] [MonadLiftT BaseIO m]
    (key : String) (timing : Std.HashMap String Nat) (action : m α) : m (α × Std.HashMap String Nat) := do
  let t0 ← IO.monoNanosNow
  let result ← action
  let t1 ← IO.monoNanosNow
  pure (result, timing.insert key (t1 - t0))

/-- Run an action, printing its elapsed time in milliseconds to stdout when `profile` is true. -/
public def profileStep {m α} [Monad m] [MonadLiftT BaseIO m]
    (profile : Bool) (name : String) (action : m α) : m α := do
  if !profile then return ← action
  let start ← IO.monoNanosNow
  let result ← action
  let elapsed := (← IO.monoNanosNow) - start
  let _ ← (IO.println s!"[profile] {name}: {nsToMs elapsed}ms" |>.toBaseIO)
  pure result
