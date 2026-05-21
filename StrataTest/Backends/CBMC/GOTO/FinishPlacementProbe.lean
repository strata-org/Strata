/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline
import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOInvariants

/-! # Regression: `coreCFGToGotoTransform` handles multiple `.finish` blocks correctly

This file probes `coreCFGToGotoTransform` on a `Core.DetCFG` with two
`.finish` blocks and confirms each emits its own `END_FUNCTION`
instruction inline.

Before the fix (Option 1 in
`docs/CoreToGOTO_CorrectnessAnalysis.md`), the `.finish` case in
`coreCFGToGotoTransform` did `pure ()` (no instruction emitted), and
`procedureToGotoCtxViaCFG` appended a single trailing `END_FUNCTION`
at the end of the program. With multiple `.finish` blocks, only the
last block's fall-through reached the trailing `END_FUNCTION`;
intermediate blocks silently fell into the next block's `LOCATION`.
This violates `WellFormedTranslation.layout_finish` (which demands an
`END_FUNCTION` at `pc + 1 + body_length` for **every** `.finish`
block) and is a real soundness hazard: source-level "stop" became
target-level "keep going through unrelated code". -/

namespace CProverGOTOFinishProbe

open Imperative CProverGOTO

/-- A two-block CFG: B1 finishes early, B2 follows with another finish.
Each block has an empty body to keep instruction counts trivial. -/
def twoFinishCfg : Core.DetCFG :=
  { entry := "B1"
    blocks := [
      ("B1", { cmds := [], transfer := .finish .empty }),
      ("B2", { cmds := [], transfer := .finish .empty })
    ] }

/-- Run the translator core on the two-finish CFG and report each
emitted instruction's index and type. The wrapper that appends a
trailing `END_FUNCTION` is *not* invoked here so the output reflects
the per-block translation alone. -/
def probeInstructions :
    Except Std.Format (Array (Nat × InstructionType)) := do
  let initEnv : Core.Expression.TyEnv := default
  let initTrans : Imperative.GotoTransform Core.Expression.TyEnv :=
    { instructions := #[], nextLoc := 0, T := initEnv, sourceText := none }
  let ans ← Strata.coreCFGToGotoTransform initEnv "probe" twoFinishCfg initTrans
  return ans.instructions.mapIdx (fun i instr => (i, instr.type))

#eval probeInstructions

/-- Each `.finish` block emits its own `END_FUNCTION` at the PC
immediately past its (empty) body. This is the form
`WellFormedTranslation.layout_finish` requires.

Cast through `Except.toOption` and `BEq` because the full `Except`
inductive does not have a `DecidableEq` instance. -/
def expected : List (Nat × InstructionType) :=
  [(0, .LOCATION), (1, .END_FUNCTION), (2, .LOCATION), (3, .END_FUNCTION)]

#eval (probeInstructions.toOption.map Array.toList = some expected : Bool)

example : probeInstructions.toOption.map Array.toList = some expected := by
  native_decide

end CProverGOTOFinishProbe
