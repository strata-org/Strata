/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-! # Time-bounded evaluation for regression tests

`withinMs ms f` runs `f ()` on a dedicated thread and returns its value if it finishes
within `ms` milliseconds, and `none` otherwise, abandoning the computation; `withinMsIO`
does the same for an `IO` action and raises the action's error again.  A test of a
computation that has become too slow then fails its `#guard_msgs` after `ms` milliseconds
instead of stalling the build.  An abandoned computation keeps its thread busy until the
`lean` process exits. -/

meta section
public section

namespace StrataTest.TimeBound

/-- `some (f ())` when `f ()` finishes within `ms` milliseconds, else `none`. -/
def withinMs {α : Type} (ms : UInt32) (f : Unit → α) : IO (Option α) := do
  let t := (Task.spawn (prio := .dedicated) f).map (prio := .dedicated) some
  let s ← IO.asTask (prio := .dedicated) (IO.sleep ms)
  IO.waitAny [t, s.map fun _ => none]

/-- `some a` when `act` returns `a` within `ms` milliseconds, `none` when it has not finished
    by then; an error `act` raises within `ms` milliseconds is raised again. -/
def withinMsIO {α : Type} (ms : UInt32) (act : IO α) : IO (Option α) := do
  let t ← IO.asTask (prio := .dedicated) act
  let s ← IO.asTask (prio := .dedicated) (IO.sleep ms)
  match ← IO.waitAny [t.map some, s.map fun _ => none] with
  | some (.ok a) => pure (some a)
  | some (.error e) => throw e
  | none => pure none

end StrataTest.TimeBound

end
end
