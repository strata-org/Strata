/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

@[inline] public def nsToMs (ns : Nat) : Nat := (ns + 500000) / 1000000

/-- Run an action, printing its elapsed time in milliseconds to stdout when `profile` is true. -/
public def profileStep {m α} [Monad m] [MonadLiftT BaseIO m]
    (profile : Bool) (name : String) (action : m α) : m α := do
  if !profile then return ← action
  let start ← IO.monoNanosNow
  let result ← action
  let elapsed := (← IO.monoNanosNow) - start
  let _ ← (IO.println s!"[profile] {name}: {nsToMs elapsed}ms" |>.toBaseIO)
  pure result

/-! # Debug Statistics Counters (FFI)

Lightweight global counters for debugging / profiling.
The counters live in C (via FFI) so they survive across pure and IO code
without threading state.

## Usage

```lean
import Strata.Util.Profile

increment_stat "myCounter";       -- increment by 1
increment_stat "myCounter" 5;     -- increment by 5
get_stat "myCounter" v;           -- read current value into v
get_stat_keys keys;               -- get all stat key names
print_stat "myCounter";           -- print one counter
print_stat_all;                   -- print all counters

start_timer "myOp";               -- push timer onto stack
-- ... computation ...
finish_timer;                     -- pop & print elapsed ms
```

**Note**: These use C FFI, so they only work in compiled code (not `#eval` / `#guard`).
Tests live in `StrataTest/Util/Profile.lean` and run via:

    lake build TestProfile && .lake/build/bin/TestProfile
-/

-- FFI primitives (CPS style, declared opaque so the compiler must call the extern)

/-- Increment the counter for `statId` by `i`. -/
@[extern "strata_increment_statistics_pure"]
public opaque incrementStatisticsPure {α : Type} [Inhabited α] (statId : String) (i : Nat) (f : Unit → α) : α

/-- Get the current value of counter `statId`. Returns 0 if not found. -/
@[extern "strata_get_statistics_pure"]
public opaque getStatisticsPure {α : Type} [Inhabited α] (statId : String) (f : Nat → α) : α

/-- Get all stat key names as an array. -/
@[extern "strata_get_stat_keys_pure"]
public opaque getStatKeysPure {α : Type} [Inhabited α] (f : Array String → α) : α

/-- Push a named timer onto the timer stack. -/
@[extern "strata_start_timer_pure"]
public opaque startTimerPure {α : Type} [Inhabited α] (label : String) (f : Unit → α) : α

/-- Pop the top timer from the stack and print its elapsed time to stdout. -/
@[extern "strata_finish_timer_pure"]
public opaque finishTimerPure {α : Type} [Inhabited α] (f : Unit → α) : α

-- Print helpers (pure Lean, built on FFI primitives)

/-- Print a single counter to stderr. -/
public def printStatPure {α : Type} [Inhabited α] (statId : String) (f : Unit → α) : α :=
  getStatisticsPure statId fun v =>
  dbgTrace s!"[stat] {statId}: {v}" fun () =>
  f ()

/-- Print all statistics counters to stderr. -/
public def printStatAllPure {α : Type} [Inhabited α] (f : Unit → α) : α :=
  getStatKeysPure fun keys =>
  if keys.isEmpty then
    dbgTrace "[statistics] (no counters recorded)" fun () => f ()
  else
    let go (acc : Unit → α) (k : String) : Unit → α := fun () =>
      getStatisticsPure k fun v =>
      dbgTrace s!"  {k}: {v}" fun () =>
      acc ()
    let body := keys.foldl go f
    dbgTrace s!"=== Statistics ({keys.size} counters) ===" fun () =>
    body ()

-- Macros (analogous to `dbg_trace`; the trailing `term` captures the CPS continuation body)

/-- `increment_stat "id"; body` increments counter `"id"` by 1 then evaluates `body`.
    `increment_stat "id" n; body` increments by `n`. -/
syntax (name := incrementStatStx) "increment_stat " str (num)? "; " term : term

@[macro incrementStatStx] public meta def expandIncrementStat : Lean.Macro
  | `(increment_stat $arg:str $n:num; $body) =>
    `(incrementStatisticsPure $arg $n fun () => $body)
  | `(increment_stat $arg:str; $body) =>
    `(incrementStatisticsPure $arg 1 fun () => $body)
  | _ => Lean.Macro.throwUnsupported

/-- `get_stat "id" v; body` binds the current value of counter `"id"` to `v`. -/
syntax (name := getStatStx) "get_stat " str ident "; " term : term

@[macro getStatStx] public meta def expandGetStat : Lean.Macro
  | `(get_stat $arg:str $v:ident; $body) => `(getStatisticsPure $arg fun $v => $body)
  | _ => Lean.Macro.throwUnsupported

/-- `get_stat_keys v; body` binds all stat key names to `v : Array String`. -/
syntax (name := getStatKeysStx) "get_stat_keys " ident "; " term : term

@[macro getStatKeysStx] public meta def expandGetStatKeys : Lean.Macro
  | `(get_stat_keys $v:ident; $body) => `(getStatKeysPure fun $v => $body)
  | _ => Lean.Macro.throwUnsupported

/-- `print_stat "id"; body` prints counter `"id"` to stderr then evaluates `body`. -/
syntax (name := printStatStx) "print_stat " str "; " term : term

@[macro printStatStx] public meta def expandPrintStat : Lean.Macro
  | `(print_stat $arg:str; $body) => `(printStatPure $arg fun () => $body)
  | _ => Lean.Macro.throwUnsupported

/-- `print_stat_all; body` prints all statistics then evaluates `body`. -/
syntax (name := printStatAllStx) "print_stat_all" "; " term : term

@[macro printStatAllStx] public meta def expandPrintStatAll : Lean.Macro
  | `(print_stat_all; $body) => `(printStatAllPure fun () => $body)
  | _ => Lean.Macro.throwUnsupported

/-- `start_timer "label"; body` pushes a timer then evaluates `body`. -/
syntax (name := startTimerStx) "start_timer " str "; " term : term

@[macro startTimerStx] public meta def expandStartTimer : Lean.Macro
  | `(start_timer $arg:str; $body) => `(startTimerPure $arg fun () => $body)
  | _ => Lean.Macro.throwUnsupported

/-- `finish_timer; body` pops the top timer, prints elapsed ms, then evaluates `body`. -/
syntax (name := finishTimerStx) "finish_timer" "; " term : term

@[macro finishTimerStx] public meta def expandFinishTimer : Lean.Macro
  | `(finish_timer; $body) => `(finishTimerPure fun () => $body)
  | _ => Lean.Macro.throwUnsupported
