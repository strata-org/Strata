/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.EvalContext

/-! # Incremental fold over `PathConditions`

Folds a step function over a sequence of `PathConditions` values, processing
each `PathConditionEntry` once even when the values repeat across other
`PathConditions`. Consecutive `PathConditions` (e.g. the `assumptions` of
successive `ProofObligation`s) typically agree on a prefix of their
`PathCondition`s. Therefore, this fold reuses the results computed for that
prefix and processes only the remainder.

The fold state (`FoldState`) holds the current checkpoint of the folded state
(`current : σ`) and a stack of `PathConditionFrame`s, one per
`PathCondition` processed. Each frame records its `PathConditionEntry`s, its
output `ω`, and the checkpoint at which it was opened.
Given the next `PathConditions`, `computeReusePlan` compares them against the
frame stack and returns a `ReusePlan`. This tells us how many frames match the
corresponding target `PathCondition` exactly (`keep`), the entries by which
the target extends the last kept frame (`topDelta`), and the target's
remaining `PathCondition`s (`newPathConditions`).
`applyReusePlan` pops the frames above `keep` — restoring `current` from the oldest popped frame's
saved checkpoint — then processes exactly `topDelta` and `newPathConditions`.

For example, the four assertions in
```
procedure Demo(x : int, y : int) {
  assume [h0]: int.ge(x, 0);
  assert [A1]: int.ge(x, 0);
  assume [h1]: int.ge(y, 0);
  assert [A2]: int.ge(int.add(x, y), 0);
  if (int.ge(x, y)) { assert [A3]: int.ge(x, y); }
  else              { assert [A4]: int.lt(x, y); }
};
```
yield four proof obligations whose `assumptions` (oldest `PathCondition`
first, with `c` the branch condition `x ≥ y`) share prefixes:
```
A1: [ [h0] ]
A2: [ [h0, h1] ]
A3: [ [h0, h1], [c]  ]
A4: [ [h0, h1], [¬c] ]
```
Folding them in order, each `advance` processes only what is new:
* A1 — initial fill: no frames yet, all of A1's `assumptions` are processed.
* A2 — extension: `[h0]` is a prefix of the top frame's target, so the plan is
  `{keep := 1, topDelta := [h1]}`; only `h1` is processed.
* A3 — new frame: all frames match exactly; `{keep := 1, newPathConditions :=
  [[c]]}` opens one frame for the branch condition.
* A4 — rewind: `[c]` vs `[¬c]` diverges; `{keep := 1, newPathConditions :=
  [[¬c]]}` pops the branch frame — restoring the checkpoint captured when it
  opened — and processes only `¬c`.

Across the run, `h0` and `h1` are processed exactly once instead of four and
three times.

See `PathConditionsFoldProps.lean` for the faithfulness theorem:
`(f.advance target).exec st` equals the from-scratch fold of `target`, so
`advance`'s result does not depend on the sequence of `advance` calls that
produced the state. -/

namespace Imperative

namespace PathConditions

public section

/- The fold is generic over three types, instantiated identically throughout
   this file:

   * `E` — the error type a `stepEntry` can fail with;
   * `σ` — the checkpoint: the folded state that `stepEntry` transforms;
   * `ω` — the per-frame output that `stepEntry` accumulates;

   plus `P`, the `PureExpr` the `PathConditionEntry`s range over. -/
variable (E σ ω : Type) (P : PureExpr)

/-- What a caller supplies to the fold: how one `PathConditionEntry`
    transforms the checkpoint `σ` and extends the per-frame output `ω`.

    `stepEntry` is a pure function, so processing an entry twice from the
    same checkpoint gives the same result. -/
structure Fold where
  /-- Process one entry against the checkpoint, extending the frame output. -/
  stepEntry : σ → ω → PathConditionEntry P → Except E (σ × ω)
  /-- The output a freshly opened frame starts from. -/
  emptyOutput : ω

/-- The engine's record for one processed `PathCondition`: the entries
    processed into it so far (oldest first, matching program order), the
    checkpoint at its start (the rewind point for branch switches), and its
    accumulated output. -/
structure PathConditionFrame where
  entries : Array (PathConditionEntry P)
  baseCheckpoint : σ
  output : ω

/-- The fold state: the current checkpoint and the frames of the processed
    `PathCondition`s (newest first, mirroring `PathConditions`). -/
structure FoldState where
  current : σ
  /-- Newest frame first, mirroring `PathConditions`. -/
  frames : List (PathConditionFrame σ ω P) := []

/-- The fold's monad: threads a `FoldState` and fails with `E`. A failing
    `stepEntry` aborts the whole action and discards the state. -/
abbrev FoldM (α : Type) : Type :=
  StateT (FoldState σ ω P) (Except E) α

variable {E σ ω P}

/-- A fresh state at checkpoint `s`: nothing processed, no frames. -/
def FoldState.init (s : σ) : FoldState σ ω P :=
  { current := s }

/-- Run an action for its final state. -/
def FoldM.exec (x : FoldM E σ ω P Unit) (st : FoldState σ ω P) :
    Except E (FoldState σ ω P) :=
  (StateT.run x st).map (·.2)

/-- Process one entry against the current checkpoint, appending it to the top
    frame (opening one at the current checkpoint if no frame is open). -/
def Fold.appendEntry (f : Fold E σ ω P) (e : PathConditionEntry P) :
    FoldM E σ ω P Unit := fun st => do
  let (top, rest) : PathConditionFrame σ ω P × List (PathConditionFrame σ ω P) :=
    match st.frames with
    | [] => ({ entries := #[], baseCheckpoint := st.current, output := f.emptyOutput }, [])
    | t :: r => (t, r)
  let (current', output) ← f.stepEntry st.current top.output e
  .ok ((), { current := current',
             frames := { top with entries := top.entries.push e, output } :: rest })

/-- Open a new empty frame at the current checkpoint. -/
def Fold.pushEmptyFrame (f : Fold E σ ω P) : FoldM E σ ω P Unit :=
  modify fun st =>
    { st with frames :=
        { entries := #[], baseCheckpoint := st.current, output := f.emptyOutput } :: st.frames }

/-- Push one `PathCondition` onto the state's stack: open a frame at the
    current checkpoint and process its entries, oldest first. -/
def Fold.pushPathCondition (f : Fold E σ ω P) (pc : PathCondition P) :
    FoldM E σ ω P Unit := do
  f.pushEmptyFrame
  pc.forM f.appendEntry

/-- How a target `PathConditions` relates to the state's frames:
    keep the first `keep` complete frames, append `topDelta` to
    the kept top frame, then push `newPathConditions`. -/
structure ReusePlan (P : PureExpr) where
  /-- Complete frames to keep (the rest are popped). -/
  keep : Nat
  /-- Entries to append to the kept top frame. -/
  topDelta : PathCondition P
  /-- Further `PathCondition`s to push and fill, oldest first. -/
  newPathConditions : PathConditions P

/-- If `candidate` is a prefix of `target`, return the remaining entries;
    otherwise return `none`. -/
def stripPathConditionPrefixGo
    [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr] :
    (candidate target : PathCondition P) → Option (PathCondition P)
  -- The whole candidate matched: whatever is left of `target` is the remainder.
  | [], target => some target
  -- The candidate still has entries but `target` is exhausted: not a prefix.
  | _ :: _, [] => none
  -- Heads must match; if so, continue on both tails, otherwise fail.
  | c :: candidate, e :: target =>
    if c.fastEq e then stripPathConditionPrefixGo candidate target else none

/-- If the processed entries `candidate` are a prefix of the target
    `PathCondition`, return the remaining entries; otherwise `none`. -/
@[inline] def stripPathConditionPrefix
    [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr]
    (candidate : Array (PathConditionEntry P)) (target : PathCondition P) :
    Option (PathCondition P) :=
  stripPathConditionPrefixGo candidate.toList target

/-- Worker for `computeReusePlan`: current frames' entries and target
    `PathCondition`s, both oldest first. `keep` counts the fully-matched
    frames. -/
def computeReusePlanGo
    [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr] :
    List (Array (PathConditionEntry P)) →
    PathConditions P → ReusePlan P
  | [], targetRest =>
    -- All current frames consumed (or none open): keep them all, everything
    -- remaining is new.
    { keep := 0, topDelta := [], newPathConditions := targetRest }
  | _ :: _, [] =>
    -- Target exhausted but frames remain (e.g. the next target sits above
    -- a branch a previous target descended into): keep the matched frames
    -- and pop the deeper ones.
    { keep := 0, topDelta := [], newPathConditions := [] }
  | ws :: wrest, t :: trest =>
    match stripPathConditionPrefix ws t with
    | some leftover =>
      if wrest.isEmpty then
        -- ws is the top frame: so the current frames are a prefix of the
        -- target; the leftover extends this top frame, and remaining
        -- target `PathCondition`s are new.
        { keep := 1, topDelta := leftover, newPathConditions := trest }
      else if leftover.isEmpty then
        -- ws is a closed frame that matches the target `PathCondition`
        -- exactly: it is fully shared, so count it and match the next pair.
        let r := computeReusePlanGo wrest trest
        { r with keep := r.keep + 1 }
      else
        -- A closed frame only partially matches: keep below it, rebuild.
        { keep := 0, topDelta := [], newPathConditions := t :: trest }
    | none =>
      -- ws is not a prefix of its target: they diverge. Nothing here is
      -- reusable, so keep the frames below and rebuild from here on.
      { keep := 0, topDelta := [], newPathConditions := t :: trest }

/-- Compare the state's frames against a target `PathConditions`
    (`PathCondition`s oldest first), producing a `ReusePlan`. When every
    already-processed `PathConditionEntry` matches, `keep` covers all frames
    and `topDelta` is the extra entries of the target's corresponding
    `PathCondition`; otherwise `keep` is the deepest fully-matched frame
    count and `newPathConditions` is the divergent tail to reprocess. -/
def FoldState.computeReusePlan
    [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr]
    (st : FoldState σ ω P) (target : PathConditions P) : ReusePlan P :=
  computeReusePlanGo (st.frames.reverse.map (·.entries)) target

/-- Pop the top frame, restoring `current` to the checkpoint at which that
    frame was opened. Identity on a frameless state. -/
def FoldState.popFrame (st : FoldState σ ω P) : FoldState σ ω P :=
  match st.frames with
  | [] => st
  | f :: rest => { current := f.baseCheckpoint, frames := rest }

/-- Pop `n` frames, one at a time. -/
def FoldState.popFrames (st : FoldState σ ω P) : Nat → FoldState σ ω P
  | 0 => st
  | n + 1 =>
    let popped := st.popFrame
    popped.popFrames n

/-- Truncate the state to its oldest `k` frames. Each pop restores `current`
    to the popped frame's `baseCheckpoint`, so the survivor is the checkpoint
    at which the oldest dropped frame opened — where processing restarts
    after a rewind. -/
def FoldState.keepFrames (st : FoldState σ ω P) (k : Nat) : FoldState σ ω P :=
  st.popFrames (st.frames.length - k)

/-- Execute a reuse plan: keep the matched frames (no-op when `keep` =
    depth), grow the kept top frame by `topDelta`, then push and fill the
    new `PathCondition`s. -/
def Fold.applyReusePlan (f : Fold E σ ω P) (plan : ReusePlan P) :
    FoldM E σ ω P Unit := do
  modify (·.keepFrames plan.keep)
  plan.topDelta.forM f.appendEntry
  plan.newPathConditions.forM f.pushPathCondition

/-- Advance the state so that its frames record exactly `target`
    (`PathCondition`s oldest first): compute how `target` relates to the
    frames (`computeReusePlan`), then process only what the plan says is new
    (`applyReusePlan`). -/
def Fold.advance
    [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr]
    (f : Fold E σ ω P) (target : PathConditions P) :
    FoldM E σ ω P Unit := do
  let st ← get
  f.applyReusePlan (st.computeReusePlan target)

/-- Accumulate the frame outputs, newest frame first, starting from `init`. -/
def FoldState.collectOutputs (st : FoldState σ ω P)
    (combine : ω → ω → ω) (init : ω) : ω :=
  st.frames.foldr (fun f acc => combine f.output acc) init

end -- public section

end PathConditions

end Imperative
