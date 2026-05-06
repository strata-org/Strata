/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Std.Data.HashMap.Basic

/-- A map from timing label to elapsed nanoseconds. -/
public abbrev TimingInfo := Std.HashMap String Nat

@[inline] public def nsToMs (ns : Nat) : Nat := (ns + 500000) / 1000000

/-- Measure the wall-clock nanoseconds taken by a pure expression.
    The `@[noinline]` prevents the compiler from hoisting `expr ()` out of
    this function. The `IO.Ref.set` forces evaluation of `expr ()` between
    the two timestamp reads (IO actions are sequenced). -/
@[noinline] public def measureNanos [Inhabited α] (expr : Unit → α) : BaseIO (α × Nat) := do
  let ref ← IO.mkRef (default : α)
  let t1 ← IO.monoNanosNow
  ref.set (expr ())
  let t2 ← IO.monoNanosNow
  let result ← ref.get
  pure (result, t2 - t1)

/-- Run an action and record its elapsed nanoseconds into a `TimingInfo` under the given key. -/
@[inline] public def recordNanos {m α} [Monad m] [MonadLiftT BaseIO m]
    (key : String) (timing : TimingInfo) (action : m α) : m (α × TimingInfo) := do
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
