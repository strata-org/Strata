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

/-! # Debug Statistics Counters

Lightweight global counters for debugging / profiling.
The counters live in global `IO.Ref`s so they survive across pure and IO code
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

Tests live in `StrataTest/Util/Profile.lean`.
-/

-- Global mutable state (initialized at module load time)
private initialize statsRef : IO.Ref (Array (String × Nat)) ← IO.mkRef #[]
private initialize timerStackRef : IO.Ref (Array (String × Nat)) ← IO.mkRef #[]

-- Helper: update existing entry or push a new one
private def upsertStat (key : String) (delta : Nat) (arr : Array (String × Nat))
    : Array (String × Nat) :=
  if arr.any (·.1 == key) then
    arr.map fun (k, v) => if k == key then (k, v + delta) else (k, v)
  else
    arr.push (key, delta)

-- Implementations (private, unsafe — callers only see the `opaque` below)

private unsafe def resetStatsPureImpl {α : Type} [Inhabited α]
    (f : Unit → α) : α :=
  unsafeBaseIO do
    statsRef.set #[]
    timerStackRef.set #[]
    return f ()

private unsafe def incrementStatisticsPureImpl {α : Type} [Inhabited α]
    (statId : String) (i : Nat) (f : Unit → α) : α :=
  unsafeBaseIO do
    statsRef.modify (upsertStat statId i)
    return f ()

private unsafe def getStatisticsPureImpl {α : Type} [Inhabited α]
    (statId : String) (f : Nat → α) : α :=
  unsafeBaseIO do
    let arr ← statsRef.get
    let val := match arr.find? (·.1 == statId) with
      | some (_, v) => v
      | none => 0
    return f val

private unsafe def getStatKeysPureImpl {α : Type} [Inhabited α]
    (f : Array String → α) : α :=
  unsafeBaseIO do
    let arr ← statsRef.get
    return f (arr.map (·.1))

private unsafe def startTimerPureImpl {α : Type} [Inhabited α]
    (label : String) (f : Unit → α) : α :=
  unsafeBaseIO do
    let now ← IO.monoNanosNow
    timerStackRef.modify (·.push (label, now))
    return f ()

private unsafe def finishTimerPureImpl {α : Type} [Inhabited α]
    (f : Unit → α) : α :=
  unsafeBaseIO do
    let now ← IO.monoNanosNow
    let stack ← timerStackRef.get
    if stack.isEmpty then
      let _ ← (IO.println "[timer] WARNING: finish_timer with no active timer").toBaseIO
    else
      let entry := stack.back!
      timerStackRef.set stack.pop
      let elapsedMs := nsToMs (now - entry.2)
      let _ ← (IO.println s!"[timer] {entry.1}: {elapsedMs}ms").toBaseIO
    return f ()

-- Public interface (CPS, pure — callers never need `unsafe`)

/-- Reset all statistics counters and timers. -/
@[implemented_by resetStatsPureImpl]
public opaque resetStatsPure {α : Type} [Inhabited α] (f : Unit → α) : α

/-- Increment the counter for `statId` by `i`. -/
@[implemented_by incrementStatisticsPureImpl]
public opaque incrementStatisticsPure {α : Type} [Inhabited α] (statId : String) (i : Nat) (f : Unit → α) : α

/-- Get the current value of counter `statId`. Returns 0 if not found. -/
@[implemented_by getStatisticsPureImpl]
public opaque getStatisticsPure {α : Type} [Inhabited α] (statId : String) (f : Nat → α) : α

/-- Get all stat key names as an array. -/
@[implemented_by getStatKeysPureImpl]
public opaque getStatKeysPure {α : Type} [Inhabited α] (f : Array String → α) : α

/-- Push a named timer onto the timer stack. -/
@[implemented_by startTimerPureImpl]
public opaque startTimerPure {α : Type} [Inhabited α] (label : String) (f : Unit → α) : α

/-- Pop the top timer from the stack and print its elapsed time to stdout. -/
@[implemented_by finishTimerPureImpl]
public opaque finishTimerPure {α : Type} [Inhabited α] (f : Unit → α) : α

-- Direct-return wrappers

/-- Get the current value of counter `statId`. Returns 0 if not found. -/
@[inline] public def getStatistics (statId : String) : Nat :=
  getStatisticsPure statId id

/-- Get all stat key names as an array. -/
@[inline] public def getStatKeys (_ : Unit := ()) : Array String :=
  getStatKeysPure id

-- Print helpers (opaque + @[implemented_by], same pattern as the rest)

private unsafe def printStatPureImpl {α : Type} [Inhabited α]
    (statId : String) (f : Unit → α) : α :=
  unsafeBaseIO do
    let v := getStatistics statId
    let _ ← (IO.eprintln s!"[stat] {statId}: {v}").toBaseIO
    return f ()

private unsafe def printStatAllPureImpl {α : Type} [Inhabited α]
    (f : Unit → α) : α :=
  unsafeBaseIO do
    let keys := getStatKeys ()
    if keys.isEmpty then
      let _ ← (IO.eprintln "[statistics] (no counters recorded)").toBaseIO
    else
      let _ ← (IO.eprintln s!"=== Statistics ({keys.size} counters) ===").toBaseIO
      for k in keys do
        let v := getStatistics k
        let _ ← (IO.eprintln s!"  {k}: {v}").toBaseIO
    return f ()

/-- Print a single counter to stderr. -/
@[implemented_by printStatPureImpl]
public opaque printStatPure {α : Type} [Inhabited α] (statId : String) (f : Unit → α) : α

/-- Print all statistics counters to stderr. -/
@[implemented_by printStatAllPureImpl]
public opaque printStatAllPure {α : Type} [Inhabited α] (f : Unit → α) : α

-- Term macros (CPS style: `increment_stat "id"; body`)

syntax (name := resetStatsStx) "reset_stats" "; " term : term
@[macro resetStatsStx] public meta def expandResetStats : Lean.Macro
  | `(reset_stats; $body) => `(resetStatsPure fun () => $body)
  | _ => Lean.Macro.throwUnsupported

syntax (name := incrementStatStx) "increment_stat " str (num)? "; " term : term
@[macro incrementStatStx] public meta def expandIncrementStat : Lean.Macro
  | `(increment_stat $arg:str $n:num; $body) =>
    `(incrementStatisticsPure $arg $n fun () => $body)
  | `(increment_stat $arg:str; $body) =>
    `(incrementStatisticsPure $arg 1 fun () => $body)
  | _ => Lean.Macro.throwUnsupported

syntax (name := getStatStx) "get_stat " str ident "; " term : term
@[macro getStatStx] public meta def expandGetStat : Lean.Macro
  | `(get_stat $arg:str $v:ident; $body) => `(getStatisticsPure $arg fun $v => $body)
  | _ => Lean.Macro.throwUnsupported

syntax (name := getStatKeysStx) "get_stat_keys " ident "; " term : term
@[macro getStatKeysStx] public meta def expandGetStatKeys : Lean.Macro
  | `(get_stat_keys $v:ident; $body) => `(getStatKeysPure fun $v => $body)
  | _ => Lean.Macro.throwUnsupported

syntax (name := printStatStx) "print_stat " str "; " term : term
@[macro printStatStx] public meta def expandPrintStat : Lean.Macro
  | `(print_stat $arg:str; $body) => `(printStatPure $arg fun () => $body)
  | _ => Lean.Macro.throwUnsupported

syntax (name := printStatAllStx) "print_stat_all" "; " term : term
@[macro printStatAllStx] public meta def expandPrintStatAll : Lean.Macro
  | `(print_stat_all; $body) => `(printStatAllPure fun () => $body)
  | _ => Lean.Macro.throwUnsupported

syntax (name := startTimerStx) "start_timer " str "; " term : term
@[macro startTimerStx] public meta def expandStartTimer : Lean.Macro
  | `(start_timer $arg:str; $body) => `(startTimerPure $arg fun () => $body)
  | _ => Lean.Macro.throwUnsupported

syntax (name := finishTimerStx) "finish_timer" "; " term : term
@[macro finishTimerStx] public meta def expandFinishTimer : Lean.Macro
  | `(finish_timer; $body) => `(finishTimerPure fun () => $body)
  | _ => Lean.Macro.throwUnsupported

-- Do-element macros (standalone in `do` blocks, like `dbg_trace`)

syntax (name := resetStatsDoStx) "reset_stats" : doElem
@[macro resetStatsDoStx] public meta def expandResetStatsDo : Lean.Macro
  | `(doElem| reset_stats) => `(doElem| let _ : Unit := resetStatsPure fun () => ())
  | _ => Lean.Macro.throwUnsupported

syntax (name := incrementStatDoStx) "increment_stat " str (num)? : doElem
@[macro incrementStatDoStx] public meta def expandIncrementStatDo : Lean.Macro
  | `(doElem| increment_stat $arg:str $n:num) =>
    `(doElem| let _ : Unit := incrementStatisticsPure $arg $n fun () => ())
  | `(doElem| increment_stat $arg:str) =>
    `(doElem| let _ : Unit := incrementStatisticsPure $arg 1 fun () => ())
  | _ => Lean.Macro.throwUnsupported

syntax (name := getStatDoStx) "get_stat " str ident : doElem
@[macro getStatDoStx] public meta def expandGetStatDo : Lean.Macro
  | `(doElem| get_stat $arg:str $v:ident) =>
    `(doElem| let $v := getStatistics $arg)
  | _ => Lean.Macro.throwUnsupported

syntax (name := getStatKeysDoStx) "get_stat_keys " ident : doElem
@[macro getStatKeysDoStx] public meta def expandGetStatKeysDo : Lean.Macro
  | `(doElem| get_stat_keys $v:ident) =>
    `(doElem| let $v := getStatKeys)
  | _ => Lean.Macro.throwUnsupported

syntax (name := printStatDoStx) "print_stat " str : doElem
@[macro printStatDoStx] public meta def expandPrintStatDo : Lean.Macro
  | `(doElem| print_stat $arg:str) =>
    `(doElem| let _ : Unit := printStatPure $arg fun () => ())
  | _ => Lean.Macro.throwUnsupported

syntax (name := printStatAllDoStx) "print_stat_all" : doElem
@[macro printStatAllDoStx] public meta def expandPrintStatAllDo : Lean.Macro
  | `(doElem| print_stat_all) =>
    `(doElem| let _ : Unit := printStatAllPure fun () => ())
  | _ => Lean.Macro.throwUnsupported

syntax (name := startTimerDoStx) "start_timer " str : doElem
@[macro startTimerDoStx] public meta def expandStartTimerDo : Lean.Macro
  | `(doElem| start_timer $arg:str) =>
    `(doElem| let _ : Unit := startTimerPure $arg fun () => ())
  | _ => Lean.Macro.throwUnsupported

syntax (name := finishTimerDoStx) "finish_timer" : doElem
@[macro finishTimerDoStx] public meta def expandFinishTimerDo : Lean.Macro
  | `(doElem| finish_timer) =>
    `(doElem| let _ : Unit := finishTimerPure fun () => ())
  | _ => Lean.Macro.throwUnsupported
