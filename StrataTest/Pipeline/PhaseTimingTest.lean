/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Pipeline.Context

/-! ## Phase timing tests

Exercises nesting of `withPhase` and `withRepeatedPhase` to validate that:
1. Repeated phases aggregate without crashing.
2. Messages emitted inside nested phases get the correct phase path.
3. Nested `withRepeatedPhase` inside `withRepeatedPhase` does not corrupt
   the parent's aggregation map.
4. `withRepeatedPhasePure` evaluates its expression.
-/

open Strata.Pipeline

meta def mkCtx : BaseIO PipelineContext :=
  PipelineContext.create (outputMode := .quiet) (profilePipeline := false)

meta def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

/-! ### Test 1: withRepeatedPhase aggregates without error -/

#guard_msgs in
#eval show IO Unit from do
  let ctx ← mkCtx
  ctx.withPhase "outer" (m := IO) do
    for _ in List.range 5 do
      ctx.withRepeatedPhase "iter" (m := IO) do
        pure ()

/-! ### Test 2: withPhase nested inside withRepeatedPhase runs correctly -/

#guard_msgs in
#eval show IO Unit from do
  let ctx ← mkCtx
  ctx.withPhase "outer" (m := IO) do
    for _ in List.range 3 do
      ctx.withRepeatedPhase "iter" (m := IO) do
        ctx.withPhase "inner" (m := IO) do
          pure ()

/-! ### Test 3: Messages inside withRepeatedPhase get correct phase tag -/

#guard_msgs in
#eval show IO Unit from do
  let ctx ← mkCtx
  let pipelineAction : PipelineM Unit := do
    Strata.Pipeline.withPhase "outer" do
      for _ in List.range 2 do
        let ctx ← read
        ctx.withRepeatedPhase "iter" do
          emitMessage .laurelLoweringNotImpl "test warning"
  let _ ← pipelineAction.run ctx |>.toBaseIO
  let msgs ← ctx.getMessages
  check (msgs.size == 2) s!"Expected 2 messages, got {msgs.size}"
  let expectedPhase := Phase.base "outer" |>.subphase "iter"
  for msg in msgs do
    check (msg.phase == expectedPhase)
      s!"Expected phase '{expectedPhase}', got '{msg.phase}'"

/-! ### Test 4: Nested withRepeatedPhase does not corrupt parent -/

#guard_msgs in
#eval show IO Unit from do
  let ctx ← mkCtx
  ctx.withPhase "outer" (m := IO) do
    for _ in List.range 4 do
      ctx.withRepeatedPhase "a" (m := IO) do
        for _ in List.range 2 do
          ctx.withRepeatedPhase "b" (m := IO) do
            pure ()

/-! ### Test 5: Multiple distinct withPhase inside withRepeatedPhase -/

#guard_msgs in
#eval show IO Unit from do
  let ctx ← mkCtx
  ctx.withPhase "outer" (m := IO) do
    for _ in List.range 3 do
      ctx.withRepeatedPhase "iter" (m := IO) do
        ctx.withPhase "preprocess" (m := IO) do pure ()
        ctx.withPhase "solve" (m := IO) do pure ()

/-! ### Test 6: Messages inside nested withPhase get deepest phase path -/

#guard_msgs in
#eval show IO Unit from do
  let ctx ← mkCtx
  let pipelineAction : PipelineM Unit := do
    Strata.Pipeline.withPhase "parent" do
      let ctx ← read
      ctx.withRepeatedPhase "iter" do
        Strata.Pipeline.withPhase "child" do
          emitMessage .laurelLoweringNotImpl "deep msg"
  let _ ← pipelineAction.run ctx |>.toBaseIO
  let msgs ← ctx.getMessages
  check (msgs.size == 1) s!"Expected 1 message, got {msgs.size}"
  let expectedPhase := Phase.base "parent" |>.subphase "iter" |>.subphase "child"
  match msgs[0]? with
  | some msg =>
    check (msg.phase == expectedPhase)
      s!"Expected phase '{expectedPhase}', got '{msg.phase}'"
  | none => throw <| IO.userError "unreachable"

/-! ### Test 7: withRepeatedPhasePure evaluates expression -/

/--
info: withRepeatedPhasePure: evaluating
withRepeatedPhasePure: evaluating
withRepeatedPhasePure: evaluating
withRepeatedPhasePure: evaluating
-/
#guard_msgs in
#eval show IO Unit from do
  let ctx ← mkCtx
  let evalRef ← IO.mkRef (0 : Nat)
  ctx.withPhase "outer" (m := IO) do
    for _ in List.range 4 do
      let _ ← ctx.withRepeatedPhasePure "compute" fun () =>
        dbg_trace "withRepeatedPhasePure: evaluating"
        42
      evalRef.modify (· + 1)
  let count ← evalRef.get
  check (count == 4) s!"Expected 4 evaluations, got {count}"
