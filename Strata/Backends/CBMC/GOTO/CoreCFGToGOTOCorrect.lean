/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.Semantics
public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOInvariants
public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Util.Relations
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.StatementSemantics

public section

/-! # Forward simulation: Core DetCFG → CBMC GOTO

This module states and proves (modulo well-marked obligations) the main
correctness theorem for the `coreCFGToGotoTransform` translation pipeline:

> If a `Core.DetCFG` run terminates in store `σ'` with failure flag `b`,
> then the translated GOTO program reaches the same final `(σ', b)`.

## Scope

* **Source language**: `Core.DetCFG` with `EvalDetBlock` step relation,
  restricted to the call-free fragment (`CmdExt.cmd` only — see
  `Core.Command.isPlainCmd`).
* **Target language**: GOTO `Program`s under the small-step
  `StepGoto`/`StepGotoStar` semantics defined in `Semantics.lean`.
* **Theorem shape**: forward simulation for terminating runs, mirroring
  the existing pattern in `Strata.Transform.DetToKleeneCorrect`.

## Hypotheses (axiomatized)

* **Expression-translation correctness** — the GOTO evaluator agrees with
  Core's evaluator on every translated expression. Captured as
  `ExprTranslationPreservesEval`.
* **Translator well-formedness** — the program output by
  `coreCFGToGotoTransform` is a `WellFormedTranslation` of its input CFG.
  Consumed as a hypothesis; discharging it is a separate proof obligation
  (see `CoreCFGToGOTOInvariants.lean`).

## Proof outline

1. **Simulation relation `Sim`** — relates a `CFGConfig` to a `GotoConfig`
   via the well-formedness predicate's `labelMap`.
2. **Block simulation lemma** — one `EvalDetBlock` derivation translates to
   a `StepGotoStar` covering the corresponding GOTO instruction range.
   Internally inducts on the command list (commands map to 1–2 GOTO steps),
   then handles the transfer.
3. **Transfer simulation** — `condGoto` corresponds to the two-`GOTO`
   pattern (one conditional + one unconditional); `finish` corresponds to
   reaching `END_FUNCTION` via fall-through.
4. **Main theorem** — induction on `ReflTrans` length, using block
   simulation at each step. -/

namespace CProverGOTO

open Imperative

/-! ## Hypothesis: expression-translation correctness

We axiomatize the relationship between Core's expression evaluator (`δ`) and
the GOTO expression evaluator (`δ_goto`) used by `StepGoto`. The translator
`Lambda.LExpr.toGotoExprCtx` should preserve evaluation; this hypothesis
states that explicitly without the proof. Discharging it is a separate
project — its proof involves a mutual induction over the expression
language tying GOTO operator semantics to Core's. -/

/-- Predicate stating that a Core expression and a GOTO expression are
"translation-equivalent" under the given evaluators: bidirectionally agree
on values, and bidirectionally agree on boolean truth. -/
structure ExprTranslated
    (δ : SemanticEval Core.Expression)
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

/-- Expression-translation correctness as a global property: there is a
*function* `tx` (the expression translator, e.g. `Lambda.LExpr.toGotoExprCtx`
specialized to the success path) such that every Core expression and its
GOTO translation are `ExprTranslated`-equivalent under the given evaluators.

The simulation theorem takes a value of this type as a hypothesis. The
function form (rather than per-expression existentials) lets us name the
specific GOTO expression for any given Core source — needed when relating
a `condGoto cond _ _` transfer in DetCFG to the emitted GOTO instruction
whose guard is the translation of `cond`. -/
structure ExprTranslationPreservesEval
    (δ : SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression) where
  /-- The expression translator. -/
  tx : Core.Expression.Expr → Expr
  /-- For every Core expression, the translator produces an evaluation-
  equivalent GOTO expression. -/
  tx_correct : ∀ e_core,
    ExprTranslated δ δ_goto δ_goto_bool e_core (tx e_core)
  /-- The translator commutes with negation, up to translation: the GOTO
  side's `Expr.not` of a translated expression is the translation of
  Core's `HasNot.not` of the source. (The CFG-to-GOTO translator emits
  `Expr.not (tx cond)` for `condGoto cond _ _`, while the DetCFG step
  relation evaluates `δ σ cond`. Combined with `WellFormedSemanticEvalBool`
  and `WellFormedSemanticEvalGotoBool`, this lets us bridge the two sides
  on conditional transfers.) -/
  tx_commutes_not :
    ∀ e_core,
      tx (HasNot.not (P := Core.Expression) e_core) = (tx e_core).not

/-! ## Simulation relation

Relates DetCFG configurations to GOTO configurations under a
`WellFormedTranslation` witness. -/

/-- The simulation invariant.

* A `cont l σ failed` configuration corresponds to running at the `pc` for
  `l`'s `LOCATION` instruction with the same store and failure flag.
* A `terminal σ failed` configuration corresponds to a GOTO `terminal`
  configuration with the same store and failure flag. -/
inductive Sim (cfg : Core.DetCFG) (pgm : Program)
    (wf : WellFormedTranslation cfg pgm) :
    CFGConfig String Core.Expression → GotoConfig Core.Expression → Prop where
  | sim_cont :
    wf.labelMap l = some pc →
    Sim cfg pgm wf (.cont l σ failed) (.running pc σ failed)
  | sim_terminal :
    Sim cfg pgm wf (.terminal σ failed) (.terminal σ failed)

/-! ## Block simulation lemma

The crux: a single `EvalDetBlock` derivation corresponds to a sequence of
`StepGoto` steps over the GOTO instruction range for that block.

Proof strategy: induct on the `EvalDetBlock` derivation. Each `cmd`
constructor consumes one command and produces one or two GOTO steps via
`Cmd.toGotoInstructions`. The transfer constructors (`goto_true`,
`goto_false`, `terminal`) handle the trailing instructions. -/

/-! ### Concrete sub-lemma: empty-body `finish` block

This is the simplest possible case: a block with no commands and a `finish`
transfer. It exercises the proof skeleton end-to-end and validates that
the `WellFormedTranslation` predicate is shaped correctly for the
`finish` case.

A real `block_simulation` proof would handle this case as one of several
in an induction; we prove it standalone as a sanity check. -/

/-- An empty-body `finish` block simulates: from `(.running pc σ failed)`
where `pc` points at the block's `LOCATION` instruction, two GOTO steps
(`LOCATION` then `END_FUNCTION`, with `DetBlockBodyInstrCount blk = 0`)
reach the corresponding GOTO terminal config. -/
theorem block_simulation_empty_finish
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (cfg : Core.DetCFG) (pgm : Program)
    (wf : WellFormedTranslation cfg pgm)
    (l : String) (md : MetaData Core.Expression)
    (blk : Imperative.DetBlock String Core.Command Core.Expression)
    (h_blk_cmds : blk.cmds = [])
    (h_blk_xfer : blk.transfer = .finish md)
    (h_block : (l, blk) ∈ cfg.blocks)
    (σ : Imperative.SemanticStore Core.Expression) (failed : Bool)
    (pc : Nat) (h_pc : wf.labelMap l = some pc)
    : StepGotoStar Core.Expression δ_goto δ_goto_bool pgm
        (.running pc σ failed) (.terminal σ failed) := by
  -- Step 1: at `pc`, the LOCATION instruction is present (from `wf`).
  obtain ⟨instr_loc, h_loc_at, h_loc_ty⟩ :=
    wf.layout_location l blk pc h_block h_pc
  -- Step 2: at `pc + 1 + 0`, an END_FUNCTION instruction is present.
  obtain ⟨pc_end, instr_end, h_pc_end_eq, h_end_at, h_end_ty⟩ :=
    wf.layout_finish l blk pc md h_block h_pc h_blk_xfer
  -- The body instruction count is 0 since `blk.cmds = []`.
  have h_body : DetBlockBodyInstrCount blk = 0 := by
    unfold DetBlockBodyInstrCount; rw [h_blk_cmds]; rfl
  -- So `pc_end = pc + 1`.
  have h_pc_end : pc_end = pc + 1 := by
    rw [h_pc_end_eq, h_body]
  -- Build the two-step trace: LOCATION, then END_FUNCTION, via `ReflTrans`.
  unfold StepGotoStar
  rw [h_pc_end] at h_end_at
  exact ReflTrans.step
    (GotoConfig.running pc σ failed)
    (GotoConfig.running (pc + 1) σ failed)
    (GotoConfig.terminal σ failed)
    (StepGoto.step_location h_loc_at h_loc_ty)
    (ReflTrans.step _ _ _
      (StepGoto.step_end_function h_end_at h_end_ty)
      (ReflTrans.refl _))

/-- One block's `EvalDetBlock` derivation translates to a `StepGotoStar`
covering the block's GOTO instruction range.

The full proof requires:

1. Induction on the `EvalDetBlock` derivation,
2. Per-command instruction-emission lemmas (each `Imperative.Cmd` matches
   the count in `Cmd.gotoInstrCount`),
3. Use of `WellFormedTranslation` to locate the next block's `pc` after a
   transfer.

For the call-free fragment, `EvalCmd` for each `Cmd P` constructor maps
1-to-1 onto the GOTO `step_*` constructors with the same names. -/
theorem block_simulation
    (δ : SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool)
    (π : String → Option Core.Procedure)
    (φ : Core.CoreEval → Imperative.PureFunc Core.Expression → Core.CoreEval)
    (cfg : Core.DetCFG) (pgm : Program)
    (wf : WellFormedTranslation cfg pgm)
    (l : String) (blk : Imperative.DetBlock String Core.Command Core.Expression)
    (h_block : (l, blk) ∈ cfg.blocks)
    (h_call_free : ∀ c ∈ blk.cmds, c.isPlainCmd = true)
    (σ : Imperative.SemanticStore Core.Expression) (failed : Bool)
    (c_after : Imperative.CFGConfig String Core.Expression)
    (h_step :
      Imperative.EvalDetBlock Core.Expression
        (Core.EvalCommand π φ) (Core.EvalPureFunc φ) σ blk c_after)
    (pc : Nat) (h_pc : wf.labelMap l = some pc)
    : ∃ c_after_goto,
        StepGotoStar Core.Expression δ_goto δ_goto_bool pgm
          (.running pc σ failed) c_after_goto ∧
        Sim cfg pgm wf
          (Imperative.updateFailure c_after failed) c_after_goto := by
  -- This is the principal proof obligation. It requires:
  --   (a) Induction on the `EvalDetBlock` derivation,
  --   (b) Per-command lemmas matching each `Imperative.Cmd` constructor
  --       to its `StepGoto` counterpart, using `h_expr` to bridge
  --       expression evaluation between Core and GOTO,
  --   (c) Transfer-case lemmas using `wf.layout_cond_goto` /
  --       `wf.layout_finish` to step through the trailing
  --       GOTO/END_FUNCTION instructions,
  --   (d) `h_call_free` ensures every command in the block is `CmdExt.cmd`
  --       (not `CmdExt.call`), so `EvalCommand` reduces to `EvalCmd`.
  sorry

/-! ## Main forward-simulation theorem

The end-to-end statement: a successful DetCFG run is matched by a successful
GOTO run reaching the same final configuration.

This wraps `block_simulation` with a `ReflTrans`-length induction, mirroring
the pattern in `Strata.Transform.DetToKleeneCorrect`. -/

/-- Forward simulation: any terminating DetCFG run is matched by a
terminating GOTO run with the same final store and failure flag.

Hypotheses:

* `h_expr` — every Core expression has a GOTO translation that the
  evaluators agree on.
* `h_wf_bool` — the GOTO boolean evaluator is well-formed under negation.
* `wf` — a `WellFormedTranslation` witness for `pgm` against `cfg`.
* `h_run` — a multi-step DetCFG run from the entry to a terminal config.
* (Implicit: the CFG's blocks are call-free; the proof obligation above
  takes this as a per-block hypothesis.)

Conclusion: there is a `StepGotoStar` from the GOTO program's entry
configuration to a `terminal` configuration with the same `(σ', b)`. -/
theorem coreCFGToGoto_forward_simulation
    (δ : SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool)
    (π : String → Option Core.Procedure)
    (φ : Core.CoreEval → Imperative.PureFunc Core.Expression → Core.CoreEval)
    (cfg : Core.DetCFG) (pgm : Program)
    (wf : WellFormedTranslation cfg pgm)
    (h_call_free :
      ∀ p ∈ cfg.blocks, ∀ c ∈ p.2.cmds, c.isPlainCmd = true)
    (σ σ' : Imperative.SemanticStore Core.Expression) (b : Bool)
    (h_run :
      Core.CoreCFGStepStar π φ cfg
        (.cont cfg.entry σ false)
        (.terminal σ' b))
    : ∃ pc_entry,
        wf.labelMap cfg.entry = some pc_entry ∧
        StepGotoStar Core.Expression δ_goto δ_goto_bool pgm
          (.running pc_entry σ false)
          (.terminal σ' b) := by
  -- Proof outline (deferred):
  -- 1. From `wf.entry_in_map`, obtain `pc_entry` such that
  --    `wf.labelMap cfg.entry = some pc_entry`.
  -- 2. Induct on `h_run : CoreCFGStepStar …` (which has its own `refl` /
  --    `step` constructors, mutually defined with `EvalCommand`).
  --    For each `step` case, apply `block_simulation` to get a
  --    corresponding `StepGotoStar` segment, then concatenate with the
  --    induction hypothesis via `ReflTrans_Transitive`.
  -- 3. The `refl` case is impossible here because the start config
  --    `(.cont cfg.entry σ false)` is not equal to a terminal config —
  --    it's discharged by `cases` / `injection`.
  -- 4. The `terminal` case lifts via `Sim.sim_terminal`.
  --
  -- Mirrors the structure of `detToKleene_overapproximates` in
  -- `Strata/Transform/DetToKleeneCorrect.lean`.
  sorry

end CProverGOTO
