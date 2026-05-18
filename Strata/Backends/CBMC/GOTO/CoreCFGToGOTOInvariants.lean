/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.Semantics
public import Strata.Languages.Core.Procedure
public import Strata.DL.Imperative.BasicBlock
public import Strata.DL.Imperative.Cmd

public section

/-! # Structural well-formedness of `coreCFGToGotoTransform` outputs

This module defines a `WellFormedTranslation` predicate capturing the
structural relationship between a `Core.DetCFG` and a GOTO `Program` that
purports to be its translation via `coreCFGToGotoTransform`.

The predicate is exactly what the simulation proof in
`CoreCFGToGOTOCorrect.lean` consumes about the translator output:

* every CFG block label resolves to a known `pc` in the program,
* the `pc` for label `l` holds a `LOCATION` instruction,
* a block ending in `condGoto` is followed by two `GOTO` instructions
  (the conditional negated guard and the unconditional true-target jump),
* a block ending in `finish` is followed by `END_FUNCTION`.

The simulation theorem assumes a `WellFormedTranslation` value as a
hypothesis. Discharging it for the actual `coreCFGToGotoTransform` output
(by induction over the imperative `for`-loop in
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOPipeline.lean`) is left as a
separate proof obligation, intentionally not imported here so this
module's build is independent of the translator file. -/

/-! ## Per-command instruction layout

How many GOTO instructions does each `Imperative.Cmd` translate to?

Reading `Cmd.toGotoInstructions` in
`Strata/DL/Imperative/ToCProverGOTO.lean`:

* `.init _ _ (.det _) _`  → 2 instructions (`DECL`, `ASSIGN`)
* `.init _ _ .nondet _`   → 1 instruction  (`DECL`)
* `.set _ _ _`            → 1 instruction  (`ASSIGN`)
* `.assert _ _ _`         → 1 instruction  (`ASSERT`)
* `.assume _ _ _`         → 1 instruction  (`ASSUME`)
* `.cover  _ _ _`         → 1 instruction  (`ASSERT`)

The call-free fragment we are proving correct admits only `CmdExt.cmd`,
not `CmdExt.call`. -/
def Imperative.Cmd.gotoInstrCount {P : Imperative.PureExpr} :
    Imperative.Cmd P → Nat
  | .init _ _ (.det _) _   => 2
  | .init _ _ .nondet _    => 1
  | .set _ _ _             => 1
  | .assert _ _ _          => 1
  | .assume _ _ _          => 1
  | .cover  _ _ _          => 1

/-- Total number of GOTO instructions emitted for a `Core.Command`. The call
case yields `0` so we can state predicates uniformly; the simulation
theorem rules out calls via a separate hypothesis (`isPlainCmd`). -/
def Core.CmdExt.gotoInstrCount : Core.Command → Nat
  | .cmd c => Imperative.Cmd.gotoInstrCount c
  | .call _ _ _ => 0

/-- Discriminator: is this a non-call command? -/
def Core.CmdExt.isPlainCmd : Core.Command → Bool
  | .cmd _ => true
  | .call _ _ _ => false

namespace CProverGOTO

open Imperative

/-- Total instructions emitted for the body of a single block, *not* counting
the leading `LOCATION` or trailing transfer instructions. -/
@[expose] def DetBlockBodyInstrCount
    (blk : Imperative.DetBlock String Core.Command Core.Expression) : Nat :=
  blk.cmds.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0

/-- Number of trailing transfer instructions emitted for a block:

  * `condGoto _ _ _` → 2 (`GOTO [¬cond] lf`, `GOTO lt`)
  * `finish _`       → 0 (the procedure-final `END_FUNCTION` is appended by
                          the pipeline wrapper, not the per-block code) -/
def DetBlockTransferInstrCount
    (blk : Imperative.DetBlock String Core.Command Core.Expression) : Nat :=
  match blk.transfer with
  | .condGoto _ _ _ _ => 2
  | .finish _ => 0

/-- Total instructions for a block, including its leading `LOCATION`
(`+1`) and trailing transfer. -/
def DetBlockTotalInstrCount
    (blk : Imperative.DetBlock String Core.Command Core.Expression) : Nat :=
  1 + DetBlockBodyInstrCount blk + DetBlockTransferInstrCount blk

/-! ## Well-formedness predicate

A `WellFormedTranslation` value witnesses that a `Program` is a structurally
faithful translation of a `Core.DetCFG`. The simulation theorem in
`CoreCFGToGOTOCorrect.lean` consumes this as a hypothesis. -/

/-- Map from CFG block labels to the `pc` of the `LOCATION` instruction that
the translator emits for that block. -/
@[expose] abbrev LabelMap := String → Option Nat

/-- The structural relationship between a `Core.DetCFG` and a `Program`. -/
structure WellFormedTranslation
    (cfg : Core.DetCFG) (pgm : Program) where
  /-- Lookup from CFG label to `pc` in `pgm.instructions`. -/
  labelMap : LabelMap
  /-- Every CFG block label has a `pc` in `labelMap`. -/
  labelMap_total :
    ∀ l, l ∈ cfg.blocks.map Prod.fst → (labelMap l).isSome
  /-- Distinct labels map to distinct `pc`s. -/
  labelMap_inj :
    ∀ l₁ l₂ pc, labelMap l₁ = some pc → labelMap l₂ = some pc → l₁ = l₂
  /-- For each block `(l, blk)` of the CFG, `pgm.instructions[labelMap[l]]`
  is a `LOCATION` instruction. -/
  layout_location :
    ∀ l blk pc,
      (l, blk) ∈ cfg.blocks → labelMap l = some pc →
      ∃ instr, pgm.instrAt pc = some instr ∧ instr.type = .LOCATION
  /-- For each `condGoto` transfer in block `(l, blk)`, two `GOTO`
  instructions appear at the end of the block's instruction range:
  the first is conditional (guard = `¬cond`) and targets `lf`; the
  second is unconditional (guard = `Expr.true`) and targets `lt`. -/
  layout_cond_goto :
    ∀ l blk pc cond lt lf md, (l, blk) ∈ cfg.blocks →
      labelMap l = some pc →
      blk.transfer = .condGoto cond lt lf md →
      ∃ pc_neg pc_uncond pc_lf pc_lt instr_neg instr_uncond,
        pc_neg = pc + 1 + DetBlockBodyInstrCount blk ∧
        pc_uncond = pc_neg + 1 ∧
        pgm.instrAt pc_neg = some instr_neg ∧
        instr_neg.type = .GOTO ∧
        instr_neg.target = some pc_lf ∧
        labelMap lf = some pc_lf ∧
        pgm.instrAt pc_uncond = some instr_uncond ∧
        instr_uncond.type = .GOTO ∧
        instr_uncond.target = some pc_lt ∧
        labelMap lt = some pc_lt
  /-- A `finish` block has no transfer instructions; the next instruction
  beyond the block body must be `END_FUNCTION`. -/
  layout_finish :
    ∀ l blk pc md, (l, blk) ∈ cfg.blocks →
      labelMap l = some pc →
      blk.transfer = .finish md →
      ∃ pc_end instr_end,
        pc_end = pc + 1 + DetBlockBodyInstrCount blk ∧
        pgm.instrAt pc_end = some instr_end ∧
        instr_end.type = .END_FUNCTION
  /-- The CFG's entry label is in the label map. -/
  entry_in_map :
    ∃ pc, labelMap cfg.entry = some pc

end CProverGOTO
