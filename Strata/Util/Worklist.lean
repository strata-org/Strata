/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Std.Data.HashSet.Basic

/-! # Generic worklist algorithm

A monad-agnostic worklist driver: seed a set of items, dequeue one at a time,
run a user-supplied `process` to discover new items, and re-enqueue only those
not seen before.  Dedup is by structural `BEq`/`Hashable` on the item type.

The public entry point is `run`. -/

namespace Strata.Worklist

public section

/-- Worklist state: the FIFO item queue and the seen-set. -/
private abbrev State (α : Type) [BEq α] [Hashable α] := Std.Queue α × Std.HashSet α

/-- One iteration: dequeue the next item, `process` it, and enqueue any newly
    discovered items not already seen.  Returns `none` if the queue is drained
    (no more work), `some state'` after one item was processed. -/
private def runOneIter {m : Type → Type} [Monad m] {α : Type} [BEq α] [Hashable α]
    (process : α → m (List α)) (state : State α) : m (Option (State α)) := do
  let (pending, seen) := state
  let some (a, pending) := pending.dequeue? | return none
  let news ← process a
  let (pending, seen) ← news.foldlM (init := (pending, seen)) fun (pending, seen) b =>
    if seen.contains b then pure (pending, seen)
    else pure (pending.enqueue b, seen.insert b)
  return some (pending, seen)

/-- Structural recursion on `remaining` fuel.

    * `0` — the cap is reached; report whether the queue happens to be empty
      at that boundary.  This fixes a subtle off-by-one: a worklist that
      drains in exactly `cap` items would otherwise report
      `finished = false` (rejecting a well-formed program).  A drained
      queue is `true` regardless of whether fuel ran out simultaneously.
    * `n+1` — dequeue and `process` one item; recurse with `n` fuel remaining.

    Returns `true` iff the worklist drained; `false` otherwise (cap hit with
    items still pending). -/
private def runIterations {m : Type → Type} [Monad m] {α : Type} [BEq α] [Hashable α]
    (process : α → m (List α)) : Nat → State α → m Bool
  | 0, (pending, _) => pure pending.isEmpty
  | n+1, s => do
    match ← runOneIter process s with
    | none => pure true
    | some s' => runIterations process n s'

/-- Run a worklist algorithm over items of type `α`.

    * `initial` — seed items (deduplicated on entry).
    * `process` — for each dequeued item, returns newly-discovered items; each
      is enqueued iff not already seen.  `process` may do arbitrary work in
      `m` (e.g. update state via `StateT`, raise errors, log, etc.).
    * `maxIterations` — cap on total items processed.

    Returns `false` if the cap is reached with items still pending, `true` if the
    worklist drained. -/
def run {m : Type → Type} [Monad m] {α : Type} [BEq α] [Hashable α]
    (initial : List α) (process : α → m (List α))
    (maxIterations : Nat) : m Bool := do
  let mut seen : Std.HashSet α := {}
  let mut pending : Std.Queue α := ∅
  for a in initial do
    if !(seen.contains a) then
      seen := seen.insert a
      pending := pending.enqueue a
  runIterations process maxIterations (pending, seen)

end -- public section

end Strata.Worklist
