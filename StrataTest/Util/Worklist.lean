/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Util.Worklist

/-! # `Strata.Worklist.run` unit tests -/

meta section

namespace Strata.Worklist.Test

/-- No item discovers anything new: the queue only ever shrinks. -/
private def noDiscovery : Nat → Id (List Nat) := fun _ => pure []

/-- Run the worklist at the identity monad and project to `Bool` . -/
private def runId (init : List Nat) (process : Nat → Id (List Nat)) (cap : Nat) : Bool :=
  Id.run (Strata.Worklist.run init process cap)

-- Empty seed set: the worklist drains immediately, regardless of the cap.
#guard runId [] noDiscovery 0 == true

-- Drains in *exactly* `maxIterations` steps: 3 seeds, no discoveries, cap 3.
-- Processing the third item empties the queue exactly as the fuel reaches 0, so
-- the `remaining = 0` branch observes an empty queue and reports `true`.
#guard runId [1, 2, 3] noDiscovery 3 == true

-- Cap reached with items still pending: 3 seeds, cap 2 — after two steps one
-- item remains, so the `remaining = 0` branch observes a non-empty queue and
-- reports `false`.
#guard runId [1, 2, 3] noDiscovery 2 == false

-- Drains strictly before the cap: the driver stops via the empty-queue exit
-- (`runOneIter` returns `none`), independent of the `remaining = 0` branch.
#guard runId [1, 2] noDiscovery 5 == true

-- Duplicate seeds are deduplicated on entry, so two `1`s count as one item and
-- the worklist drains within the cap.
#guard runId [1, 1] noDiscovery 1 == true

-- A discovery is enqueued and processed: seed `1` discovers `2`, then `2`
-- discovers nothing.  With cap 2 the two items drain exactly at the fuel
-- boundary, again exercising the `remaining = 0`/empty-queue `true` path.
#guard runId [1] (fun n => pure (if n == 1 then [2] else [])) 2 == true

-- Dedup within discoveries: `process` re-returns already-seen items, so the
-- `seen.contains` guard in `runOneIter` drops them and the queue still drains.
#guard runId [1, 2] (fun _ => pure [1, 2]) 3 == true

-- Unbounded discovery: every item discovers a fresh successor, so the queue
-- never empties and the cap is hit with work pending — `false`.
#guard runId [0] (fun n => pure [n + 1]) 5 == false

end Strata.Worklist.Test

end
