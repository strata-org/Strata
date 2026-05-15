/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Pipeline.Messages

/-! ## Phase timing tests

Exercises nesting of `withPhase` and `withRepeatedPhase` to validate that:
1. Nested `withPhase` inside `withRepeatedPhase` aggregates child timing.
2. Messages emitted inside nested phases get the correct phase path.
3. Nested `withRepeatedPhase` inside `withRepeatedPhase` does not corrupt
   the parent's aggregation map.
-/

open Strata.Pipeline

meta def mkCtx : BaseIO PipelineContext :=
  PipelineContext.create (outputMode := .quiet) (skipTiming := true)

meta def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

/-! ### Test 1: withRepeatedPhase aggregates count and total -/

#eval show IO Unit from do
  let ctx ← mkCtx
  ctx.withPhase "outer" (m := IO) do
    for _ in List.range 5 do
      ctx.withRepeatedPhase "iter" (m := IO) do
        pure ()
  let entries ← ctx.getTimingEntries
  let iterPhase := Phase.base "outer" |>.subphase "iter"
  let iterEntries := entries.filter (fun e => e.phase == iterPhase)
  check (iterEntries.size == 1)
    s!"Expected 1 aggregated iter entry, got {iterEntries.size}"
  match iterEntries[0]? with
  | some e => check (e.count == 5) s!"Expected count 5, got {e.count}"
  | none => throw <| IO.userError "unreachable"

/-! ### Test 2: withPhase nested inside withRepeatedPhase records timing -/

#eval show IO Unit from do
  let ctx ← mkCtx
  ctx.withPhase "outer" (m := IO) do
    for _ in List.range 3 do
      ctx.withRepeatedPhase "iter" (m := IO) do
        ctx.withPhase "inner" (m := IO) do
          pure ()
  let entries ← ctx.getTimingEntries
  let iterPhase := Phase.base "outer" |>.subphase "iter"
  let iterEntries := entries.filter (fun e => e.phase == iterPhase)
  check (iterEntries.size == 1)
    s!"Expected 1 aggregated iter entry, got {iterEntries.size}"
  match iterEntries[0]? with
  | some e => check (e.count == 3) s!"Expected count 3, got {e.count}"
  | none => throw <| IO.userError "unreachable"
  let innerPhase := Phase.base "outer" |>.subphase "iter" |>.subphase "inner"
  let innerEntries := entries.filter (fun e => e.phase == innerPhase)
  check (innerEntries.size == 1)
    s!"Expected 1 aggregated inner entry, got {innerEntries.size}"
  match innerEntries[0]? with
  | some e => check (e.count == 3) s!"Expected inner count 3, got {e.count}"
  | none => throw <| IO.userError "unreachable"

/-! ### Test 3: Messages inside withRepeatedPhase get correct phase tag -/

#eval show IO Unit from do
  let ctx ← mkCtx
  let pipelineAction : PipelineM Unit := do
    Strata.Pipeline.withPhase "outer" do
      for _ in List.range 2 do
        let ctx ← read
        ctx.withRepeatedPhase "iter" do
          emitMessage .laurelLoweringWarning "test warning"
  let _ ← pipelineAction.run ctx |>.toBaseIO
  let msgs ← ctx.getMessages
  check (msgs.size == 2) s!"Expected 2 messages, got {msgs.size}"
  let expectedPhase := Phase.base "outer" |>.subphase "iter"
  for msg in msgs do
    check (msg.phase == expectedPhase)
      s!"Expected phase '{expectedPhase}', got '{msg.phase}'"

/-! ### Test 4: Nested withRepeatedPhase does not corrupt parent -/

#eval show IO Unit from do
  let ctx ← mkCtx
  ctx.withPhase "outer" (m := IO) do
    for _ in List.range 4 do
      ctx.withRepeatedPhase "a" (m := IO) do
        for _ in List.range 2 do
          ctx.withRepeatedPhase "b" (m := IO) do
            pure ()
  let entries ← ctx.getTimingEntries
  let aPhase := Phase.base "outer" |>.subphase "a"
  let aEntries := entries.filter (fun e => e.phase == aPhase)
  check (aEntries.size == 1)
    s!"Expected 1 aggregated 'a' entry, got {aEntries.size}"
  match aEntries[0]? with
  | some e => check (e.count == 4) s!"Expected 'a' count 4, got {e.count}"
  | none => throw <| IO.userError "unreachable"
  let bPhase := Phase.base "outer" |>.subphase "a" |>.subphase "b"
  let bEntries := entries.filter (fun e => e.phase == bPhase)
  check (bEntries.size == 1)
    s!"Expected 1 aggregated 'b' entry, got {bEntries.size}"
  match bEntries[0]? with
  | some e => check (e.count == 8) s!"Expected 'b' count 8, got {e.count}"
  | none => throw <| IO.userError "unreachable"

/-! ### Test 5: Multiple distinct withPhase inside withRepeatedPhase -/

#eval show IO Unit from do
  let ctx ← mkCtx
  ctx.withPhase "outer" (m := IO) do
    for _ in List.range 3 do
      ctx.withRepeatedPhase "iter" (m := IO) do
        ctx.withPhase "preprocess" (m := IO) do pure ()
        ctx.withPhase "solve" (m := IO) do pure ()
  let entries ← ctx.getTimingEntries
  let iterPhase := Phase.base "outer" |>.subphase "iter"
  let iterEntries := entries.filter (fun e => e.phase == iterPhase)
  check (iterEntries.size == 1)
    s!"Expected 1 aggregated iter entry, got {iterEntries.size}"
  let prepPhase := iterPhase.subphase "preprocess"
  let prepEntries := entries.filter (fun e => e.phase == prepPhase)
  check (prepEntries.size == 1)
    s!"Expected 1 aggregated preprocess entry, got {prepEntries.size}"
  match prepEntries[0]? with
  | some e => check (e.count == 3) s!"Expected preprocess count 3, got {e.count}"
  | none => throw <| IO.userError "unreachable"
  let solvePhase := iterPhase.subphase "solve"
  let solveEntries := entries.filter (fun e => e.phase == solvePhase)
  check (solveEntries.size == 1)
    s!"Expected 1 aggregated solve entry, got {solveEntries.size}"
  match solveEntries[0]? with
  | some e => check (e.count == 3) s!"Expected solve count 3, got {e.count}"
  | none => throw <| IO.userError "unreachable"

/-! ### Test 6: Parent timing entry gets correct end_ns with repeated children -/

#eval show IO Unit from do
  let ctx ← mkCtx
  ctx.withPhase "parent" (m := IO) do
    for _ in List.range 3 do
      ctx.withRepeatedPhase "child" (m := IO) do
        pure ()
  let entries ← ctx.getTimingEntries
  let parentPhase := Phase.base "parent"
  let parentEntries := entries.filter (fun e => e.phase == parentPhase)
  check (parentEntries.size == 1)
    s!"Expected 1 parent entry, got {parentEntries.size}"
  match parentEntries[0]? with
  | some e =>
    check e.end_ns.isSome s!"Parent entry should have end_ns set"
    check (e.count == 1) s!"Parent count should be 1, got {e.count}"
  | none => throw <| IO.userError "unreachable"
