/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas

/-- A map from timing label to elapsed nanoseconds. -/
public abbrev TimingInfo := Std.HashMap String Nat

/-- Accumulate nanoseconds into an existing key (defaulting to 0). -/
@[inline] public def TimingInfo.add (t : TimingInfo) (key : String) (ns : Nat) : TimingInfo :=
  t.insert key (t.getD key 0 + ns)

/-- Merge `b` into `a` by summing values for overlapping keys. -/
@[inline] public def TimingInfo.mergeAdd (a b : TimingInfo) : TimingInfo :=
  b.fold (init := a) fun acc k v => acc.add k v

theorem TimingInfo.add_getD_self (t : TimingInfo) (k : String) (v : Nat) :
    (t.add k v).getD k 0 = t.getD k 0 + v := by
  simp [TimingInfo.add]

theorem TimingInfo.add_getD_of_ne (t : TimingInfo) (k k' : String) (v : Nat)
    (h : k ≠ k') : (t.add k v).getD k' 0 = t.getD k' 0 := by
  simp [TimingInfo.add, Std.HashMap.getD_insert, h]


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

/-- Run an action and record its elapsed nanoseconds into a `TimingInfo` under
    the given key. The measurement is accumulated via `TimingInfo.add`, so
    repeated calls with the same key sum their durations.

    Unlike `measureNanos`, this does not need `@[noinline]`: `action` is a
    monadic computation, so its IO primitives are sequenced by `>>=` and cannot
    be reordered across `IO.monoNanosNow`.

    Caveat: if the `α` returned by `action` is a lazy pure value (e.g.
    `pure (expensivePureComputation)`), the thunk is not forced here, and the
    recorded time will reflect only the IO sequencing, not the pure work. For
    timing pure computations, use `measureNanos` (which forces via `IO.Ref`). -/
public def recordNanos {m α} [Monad m] [MonadLiftT BaseIO m]
    (key : String) (timing : TimingInfo) (action : m α) : m (α × TimingInfo) := do
  let t0 ← IO.monoNanosNow
  let result ← action
  let t1 ← IO.monoNanosNow
  pure (result, timing.add key (t1 - t0))

/-- Run an action, printing its elapsed time in milliseconds to stdout when `profile` is true. -/
public def profileStep {m α} [Monad m] [MonadLiftT BaseIO m]
    (profile : Bool) (name : String) (action : m α) : m α := do
  if !profile then return ← action
  let start ← IO.monoNanosNow
  let result ← action
  let elapsed := (← IO.monoNanosNow) - start
  let _ ← (IO.println s!"[profile] {name}: {nsToMs elapsed}ms" |>.toBaseIO)
  pure result
