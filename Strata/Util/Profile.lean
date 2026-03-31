/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-- Run an action, printing its elapsed time in milliseconds to stdout when `profile` is true. -/
public def profileStep {m α} [Monad m] [MonadLiftT BaseIO m]
    (profile : Bool) (name : String) (action : m α) : m α := do
  if !profile then return ← action
  let start ← (IO.monoNanosNow : BaseIO Nat)
  let result ← action
  let elapsed := (← (IO.monoNanosNow : BaseIO Nat)) - start
  let _ ← (IO.println s!"[profile] {name}: {elapsed / 1000000}ms" |>.toBaseIO : BaseIO _)
  pure result
