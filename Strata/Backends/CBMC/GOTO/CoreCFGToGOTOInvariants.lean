/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.Semantics
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.StatementSemantics
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
@[expose] def Imperative.Cmd.gotoInstrCount {P : Imperative.PureExpr} :
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
@[expose] def Core.CmdExt.gotoInstrCount : Core.Command → Nat
  | .cmd c => Imperative.Cmd.gotoInstrCount c
  -- `.call` is excluded by `isPlainCmd` in the call-free fragment we are
  -- proving correct. The actual translator emits 1 FUNCTION_CALL
  -- instruction for a call; updating to `1` is a follow-up when calls are
  -- admitted into the proof.
  | .call _ _ _ => 0

/-- Discriminator: is this a non-call command? -/
def Core.CmdExt.isPlainCmd : Core.Command → Bool
  | .cmd _ => true
  | .call _ _ _ => false

/-- A `Core.Command` is admitted by the simulation theorem when it is a
plain `CmdExt.cmd` whose inner `Imperative.Cmd` is *not* a `cover` and
*not* a non-deterministic initialization. The two excluded shapes
correspond to known semantic asymmetries:
- cover is a no-op in source but emits an ASSERT in GOTO (per-trace
  divergence; documented in
  `docs/superpowers/2026-05-19-cover-semantics-discussion.md`);
- nondet `init` binds a value in source but emits a single DECL in
  GOTO (precision mismatch; tracked at
  https://github.com/strata-org/Strata/issues/1186). -/
@[expose] def Core.CmdExt.isAdmittedCmd : Core.Command → Bool
  | .cmd (.cover _ _ _)         => false
  | .cmd (.init _ _ .nondet _)  => false
  | .cmd _                      => true
  | .call _ _ _                 => false

namespace CProverGOTO

open Imperative

/-- Total instructions emitted for the body of a single block, *not* counting
the leading `LOCATION` or trailing transfer instructions. -/
@[expose] def DetBlockBodyInstrCount
    (blk : Imperative.DetBlock String Core.Command Core.Expression) : Nat :=
  blk.cmds.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0

/-- Number of GOTO instructions emitted for the first `k` commands of a
block body. Used by `layout_block_body` to address the position of the
`k`-th command's translation in `pgm.instructions`. -/
@[expose] def cmdsPrefixInstrCount
    (cmds : List Core.Command) (k : Nat) : Nat :=
  (cmds.take k).foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0

/-! ## Expression-translation predicate

This predicate is used both here (by `CmdEmittedAt`) and by
`CoreCFGToGOTOCorrect.lean` (by `ExprTranslationPreservesEval`). It lives
here because `CmdEmittedAt` references it and `Correct.lean` already
imports `Invariants.lean`. -/

/-- Predicate stating that a Core expression and a GOTO expression are
"translation-equivalent" under the given evaluators: bidirectionally agree
on values, and bidirectionally agree on boolean truth. -/
structure ExprTranslated
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (e_core : Core.Expression.Expr) (e_goto : Expr) : Prop where
  /-- The evaluators agree on values bidirectionally. -/
  value_agree : ∀ σ v, δ σ e_core = some v ↔ δ_goto σ e_goto = some v
  /-- The boolean evaluators agree on `true` bidirectionally. -/
  bool_tt_agree : ∀ σ,
    δ σ e_core = some (HasBool.tt (P := Core.Expression)) ↔
    δ_goto_bool σ e_goto = some true
  /-- The boolean evaluators agree on `false` bidirectionally. -/
  bool_ff_agree : ∀ σ,
    δ σ e_core = some (HasBool.ff (P := Core.Expression)) ↔
    δ_goto_bool σ e_goto = some false

/-! ## Per-command layout predicate

`CmdEmittedAt pgm pc c` witnesses that the GOTO program `pgm` contains, at
instruction-array index `pc`, the GOTO instruction(s) that
`Cmd.toGotoInstructions` emits for the Core command `c`. There is one
constructor per `Imperative.Cmd` shape, mirroring the cases of
`Cmd.toGotoInstructions` in `Strata/DL/Imperative/ToCProverGOTO.lean`.

Each constructor that translates a Core expression carries an
`ExprTranslated` witness for its translation, decoupling layout from the
specific `tx` function used by the global hypothesis. -/
inductive CmdEmittedAt
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (pgm : Program) :
    Nat → Imperative.Cmd Core.Expression → Prop where
  /-- `.init v ty (.det e_core) md` → DECL at `pc`, ASSIGN at `pc + 1`. -/
  | init_det
    (pc : Nat)
    (v : Core.Expression.Ident) (ty : Core.Expression.Ty)
    (e_core : Core.Expression.Expr) (md : Imperative.MetaData Core.Expression)
    (i_decl i_assn : Instruction)
    (h_decl_at : pgm.instrAt pc = some i_decl)
    (h_decl_ty : i_decl.type = .DECL)
    (h_assn_at : pgm.instrAt (pc + 1) = some i_assn)
    (h_assn_ty : i_assn.type = .ASSIGN)
    (e_goto : Expr)
    (h_assn_code : ∃ lhs, i_assn.code = Code.assign lhs e_goto)
    (h_translated : ExprTranslated δ δ_goto δ_goto_bool e_core e_goto) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.init v ty (.det e_core) md)
  /-- `.init v ty .nondet md` → DECL at `pc` only. -/
  | init_nondet
    (pc : Nat)
    (v : Core.Expression.Ident) (ty : Core.Expression.Ty)
    (md : Imperative.MetaData Core.Expression)
    (i_decl : Instruction)
    (h_decl_at : pgm.instrAt pc = some i_decl)
    (h_decl_ty : i_decl.type = .DECL) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.init v ty .nondet md)
  /-- `.set v (.det e_core) md` → ASSIGN at `pc` with translated rhs. -/
  | set_det
    (pc : Nat)
    (v : Core.Expression.Ident) (e_core : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (i_assn : Instruction)
    (h_assn_at : pgm.instrAt pc = some i_assn)
    (h_assn_ty : i_assn.type = .ASSIGN)
    (e_goto : Expr)
    (h_assn_code : ∃ lhs, i_assn.code = Code.assign lhs e_goto)
    (h_translated : ExprTranslated δ δ_goto δ_goto_bool e_core e_goto) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.set v (.det e_core) md)
  /-- `.set v .nondet md` → ASSIGN at `pc` with side-effect Nondet rhs. -/
  | set_nondet
    (pc : Nat)
    (v : Core.Expression.Ident)
    (md : Imperative.MetaData Core.Expression)
    (i_assn : Instruction)
    (h_assn_at : pgm.instrAt pc = some i_assn)
    (h_assn_ty : i_assn.type = .ASSIGN)
    (h_assn_code : ∃ lhs e_nondet, i_assn.code = Code.assign lhs e_nondet) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.set v .nondet md)
  /-- `.assert label e_core md` → ASSERT at `pc` with translated guard. -/
  | assert_emit
    (pc : Nat)
    (label : String) (e_core : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (i : Instruction)
    (h_at : pgm.instrAt pc = some i)
    (h_ty : i.type = .ASSERT)
    (e_goto : Expr)
    (h_guard : i.guard = e_goto)
    (h_translated : ExprTranslated δ δ_goto δ_goto_bool e_core e_goto) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.assert label e_core md)
  /-- `.assume label e_core md` → ASSUME at `pc` with translated guard. -/
  | assume_emit
    (pc : Nat)
    (label : String) (e_core : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (i : Instruction)
    (h_at : pgm.instrAt pc = some i)
    (h_ty : i.type = .ASSUME)
    (e_goto : Expr)
    (h_guard : i.guard = e_goto)
    (h_translated : ExprTranslated δ δ_goto δ_goto_bool e_core e_goto) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.assume label e_core md)
  /-- `.cover label e_core md` → ASSERT (dual of assume) at `pc`. -/
  | cover_emit
    (pc : Nat)
    (label : String) (e_core : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (i : Instruction)
    (h_at : pgm.instrAt pc = some i)
    (h_ty : i.type = .ASSERT)
    (e_goto : Expr)
    (h_guard : i.guard = e_goto)
    (h_translated : ExprTranslated δ δ_goto δ_goto_bool e_core e_goto) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm pc (.cover label e_core md)

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
    (cfg : Core.DetCFG) (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression) where
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
  instructions appear at the end of the block's instruction range. -/
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
  /-- The two transfer GOTOs for a `condGoto` block carry specific guards:
  the first is `e_goto.not` (where `e_goto` is the GOTO translation of
  `cond`) and the second is the GOTO constant `Expr.true`. The instruction
  witnesses come from `layout_cond_goto`; this field constrains only the
  guard contents. -/
  layout_cond_goto_guards :
    ∀ l blk pc cond lt lf md instr_neg instr_uncond,
      (l, blk) ∈ cfg.blocks →
      labelMap l = some pc →
      blk.transfer = .condGoto cond lt lf md →
      pgm.instrAt (pc + 1 + DetBlockBodyInstrCount blk) = some instr_neg →
      pgm.instrAt (pc + 1 + DetBlockBodyInstrCount blk + 1) = some instr_uncond →
      ∃ e_goto,
        instr_neg.guard = e_goto.not ∧
        ExprTranslated δ δ_goto δ_goto_bool cond e_goto ∧
        instr_uncond.guard = CProverGOTO.Expr.true
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
  /-- For each block, every plain (`CmdExt.cmd`) command in the body has
  the right `CmdEmittedAt` layout at the corresponding `pc` offset. -/
  layout_block_body :
    ∀ l blk pc, (l, blk) ∈ cfg.blocks → labelMap l = some pc →
    ∀ k inner,
      (h : k < blk.cmds.length) →
      blk.cmds[k]'h = .cmd inner →
      CmdEmittedAt δ δ_goto δ_goto_bool pgm
        (pc + 1 + cmdsPrefixInstrCount blk.cmds k)
        inner
  /-- The CFG's entry label is in the label map. -/
  entry_in_map :
    ∃ pc, labelMap cfg.entry = some pc

end CProverGOTO
