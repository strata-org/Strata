# Core DetCFG → CBMC GOTO: Proof Progress

This document records the state of the forward-simulation correctness proof
for the unstructured (CFG) Core → CProver GOTO translation pipeline. It
covers what is proved, what remains axiomatized, and what would extend the
result.

The proof lives under `Strata/Backends/CBMC/GOTO/`. As of this branch
(`htd/unstructured-to-goto`), the chain is sorry-free modulo two
documented hypotheses; `#print axioms` of the top-level theorem reports
only `[propext, Classical.choice, Quot.sound]`.

## Theorem

`coreCFGToGoto_forward_simulation` in
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrect.lean` (line 849):

> Given a `Core.DetCFG` and a GOTO `Program`, plus a `WellFormedTranslation`
> witness relating them, every terminating CFG run from `cfg.entry` is
> matched by a GOTO run from `pc_entry` to a terminal config with the
> same final store and failure flag.

```
∀ δ δ_goto δ_goto_bool h_expr h_wf_bool π φ cfg pgm wf h_call_free
  σ σ' b,
  CoreCFGStepStar π φ δ cfg (.cont cfg.entry σ false) (.terminal σ' b) →
  ∃ pc_entry,
    wf.labelMap cfg.entry = some pc_entry ∧
    StepGotoStar Core.Expression δ_goto δ_goto_bool pgm
      (.running pc_entry σ false) (.terminal σ' b)
```

## Soundness story

CBMC explores all GOTO runs. Forward simulation Core → GOTO with
failure-flag preservation gives: *if some Core run reaches a failed
assertion, then some GOTO run does too.* Contrapositively: if CBMC
verifies the GOTO program, no Core run fails. That's the soundness
argument for using CBMC on Core programs via this pipeline, modulo the
hypotheses below.

## Proof chain

The chain is bottom-up. Each layer takes the previous as a black box.

| # | Theorem | Line | Role |
|---|---|---|---|
| 1 | `evalCommand_cmd_iff_evalCmd` | 135 | Inversion: `EvalCommand` on `.cmd c` collapses to `EvalCmd c`. |
| 2 | `UpdateState_self` (private) | 154 | `σ x = some v → UpdateState … σ x v σ`; rewriting a var to its current value is a fixed point. |
| 3 | `single_cmd_simulation` | 172 | One `EvalCmd` step on a plain command corresponds to a `StepGotoStar` of length `c.gotoInstrCount`. |
| 4 | `cmdsPrefixInstrCount_at_blk_length` (private) | 279 | When `k ≥ blk.cmds.length`, the prefix instruction count saturates at `DetBlockBodyInstrCount blk`. |
| 5 | `block_body_cmds_simulation` | 298 | A `k`-suffix of a block's commands plus its transfer simulates a GOTO trace from the appropriate offset. Strong induction on suffix length. |
| 6 | `block_body_simulation` | 555 | Specialization of (5) at `k = 0`; one `EvalDetBlock` derivation simulates the GOTO range past the leading `LOCATION`. |
| 7 | `block_simulation_empty_finish` | 623 | Sanity-check standalone: empty-body `finish` block → 2-step GOTO trace (`LOCATION`, `END_FUNCTION`). |
| 8 | `block_simulation` | 675 | Wraps (6) with one `step_location` for the leading `LOCATION` instruction. |
| 9 | `cfgStepStar_to_gotoStar` (private) | 730 | Induction over `CoreCFGStepStar` via the manual recursor, glueing block traces with `ReflTrans_Transitive`. |
| 10 | `coreCFGToGoto_forward_simulation` | 849 | Wrapper: pulls `pc_entry` from `wf.entry_in_map`, instantiates (9) at `(cfg.entry, σ, false)`. |

## Supporting infrastructure

### `Strata/Backends/CBMC/GOTO/Semantics.lean`

A small-step `StepGoto` relation over `GotoConfig P = .running pc σ failed | .terminal σ failed`,
parameterized by:

- `δ_goto : SemanticEvalGoto P` — abstract evaluator for GOTO `Expr` against `Imperative.SemanticStore P`.
- `δ_goto_bool : SemanticEvalGotoBool P` — boolean projection.

Constructors cover the seven instruction types emitted by
`coreCFGToGotoTransform`: `LOCATION`, `DECL`, `ASSIGN`, `ASSERT`,
`ASSUME`, `GOTO`, `END_FUNCTION`. `FUNCTION_CALL` is intentionally not
modeled (call-free fragment). `step_assign_nondet` is a separate rule
for ASSIGN with a Nondet RHS, used by the `set_nondet` and
`init_unconstrained` cases of `single_cmd_simulation`.

`StepGotoStar` is `ReflTrans (StepGoto …)`, mirroring `StepCFGStar` on
the source side.

`WellFormedSemanticEvalGotoBool` says the boolean evaluator is closed
under negation and `Expr.true` evaluates to `true`. This is the only
axiomatized property of the GOTO boolean evaluator the proof needs.

### `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOInvariants.lean`

Defines the per-block layout language the simulation consumes:

- `Core.CmdExt.isAdmittedCmd` excludes `.call`, `.cover`, and nondet
  `.init` from the proven fragment. The asymmetries are documented
  inline (cover is a no-op in source but emits ASSERT in GOTO; nondet
  init binds in source but emits a single DECL in GOTO).
- `CmdEmittedAt δ δ_goto δ_goto_bool pgm pc c` — witness that program
  `pgm` contains the GOTO instruction(s) for command `c` at index `pc`,
  with `ExprTranslated` evidence for any translated subexpression.
- `DetBlockBodyInstrCount`, `DetBlockTransferInstrCount`,
  `DetBlockTotalInstrCount`, `cmdsPrefixInstrCount` — instruction-count
  arithmetic.
- `WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool` — the structural
  predicate consumed by the simulation theorem. Has 8 fields:
  `labelMap`, `labelMap_total`, `labelMap_inj`, `layout_location`,
  `layout_cond_goto`, `layout_cond_goto_guards`, `layout_finish`,
  `layout_block_body`, `entry_in_map`.

### `Strata/Languages/Core/StatementSemanticsProps.lean`

Adds the manual induction principle `Core.CoreCFGStepStar_rec`
(commit `6e94a20cb`) because `CoreCFGStepStar` is part of a `mutual`
inductive bundle (alongside `CoreStepStar`, `CoreBodyExec`,
`EvalCommand`), so Lean's `induction` tactic does not apply directly.
Three lemmas mirror the existing `CoreStepStar_rec` pattern:

- `CoreCFGStepStar_to_StepCFGStar` — converts the mutual relation to
  the non-mutual `ReflTrans (StepCFG (CoreEvalDetBlock π φ δ) cfg)`.
- `StepCFGStar_to_CoreCFGStepStar` — the reverse conversion.
- `CoreCFGStepStar_rec` — composes the two: induct on the non-mutual
  form, convert sub-derivations back at each step, expose a clean
  `motive` interface to callers.

`CoreEvalDetBlock` is the auxiliary block-evaluator definition needed
to instantiate `StepCFG` for Core's deterministic CFGs.

## Hypotheses (axiomatized inputs)

The proof takes two hypotheses and does not discharge them:

### 1. `WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool`

Witnesses that `pgm` is a structurally faithful translation of `cfg`.
Eight fields total (see above). The actual translator
`coreCFGToGotoTransform` (in
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOPipeline.lean`) almost
certainly produces such a witness, but **discharging this is a
separate proof obligation** — it requires inducting over the
imperative `for`-loop in the pipeline, threading instruction-position
arithmetic through each block.

### 2. `ExprTranslationPreservesEval δ δ_goto δ_goto_bool`

A structure with three fields:

- `tx : Core.Expression.Expr → Expr` — the expression translator (in
  practice `Lambda.LExpr.toGotoExprCtx` specialized to the success path).
- `tx_correct : ∀ e_core, ExprTranslated δ δ_goto δ_goto_bool e_core (tx e_core)` —
  every translated expression evaluates equivalently to its source.
- `tx_commutes_not : ∀ e_core, tx (¬ e_core) = (tx e_core).not` —
  the translator commutes with negation.

Discharging this requires a mutual induction over the expression
language, tying every GOTO operator's semantics to Core's. **It is not
attempted here.**

### Note: `h_expr` parameter is currently unused inside the proof

`block_simulation`, `cfgStepStar_to_gotoStar`, and
`coreCFGToGoto_forward_simulation` all carry `h_expr` as a parameter,
but the proof body never destructs it. The `ExprTranslated` evidence
flows in through the `WellFormedTranslation.layout_*` fields instead.
This is a stylistic choice: keeping `h_expr` in the signature makes
the dependency surface explicit and prepares the API for callers that
will eventually instantiate both hypotheses together. Removing it from
all three sites is a separate cleanup PR.

## Restricted fragment

The proof is restricted to the fragment defined by
`Core.CmdExt.isAdmittedCmd`:

- **No `.call`** — function calls are excluded; the `step_function_call`
  semantics is not modeled, the `WellFormedTranslation.layout_block_body`
  field requires every block command to be `.cmd inner` for some
  `Imperative.Cmd inner`.
- **No `.cover`** — cover is a per-trace divergence: a no-op in Core
  source, but emits an `ASSERT` in GOTO. See
  `docs/superpowers/2026-05-19-cover-semantics-discussion.md`.
- **No nondet `.init`** — nondet init binds a value in source but emits
  a single `DECL` in GOTO. Tracked at
  https://github.com/strata-org/Strata/issues/1186.

The hypothesis `h_call_free : ∀ p ∈ cfg.blocks, ∀ c ∈ p.2.cmds, c.isAdmittedCmd = true`
is consumed at the top level; its content threads down through
`single_cmd_simulation` via the `eval_cover` case being unreachable.

## What would extend this

In rough order of effort, ascending:

1. **Drop the unused `h_expr` parameter** from `block_simulation`,
   `cfgStepStar_to_gotoStar`, and `coreCFGToGoto_forward_simulation`.
   Tiny cleanup, currently noted as out-of-scope for the last PR.
2. **Discharge `WellFormedTranslation`** for the actual
   `coreCFGToGotoTransform` output. Requires a structural induction
   over the imperative `for`-loop in
   `CoreCFGToGOTOPipeline.lean:coreCFGToGotoTransform`, threading
   per-block instruction-count arithmetic and label-map invariants.
   Estimated effort: medium-large; the hardest cases are
   `layout_cond_goto_guards` (which constrains the shape of the two
   transfer instructions) and `layout_block_body` (which addresses each
   command's emitted instructions at the right offset).
3. **Discharge `ExprTranslationPreservesEval`** for
   `Lambda.LExpr.toGotoExprCtx`. Requires a mutual induction over
   `LExpr` and the GOTO `Expr` language, with one case per operator.
   Largest of the three; estimated effort: large.
4. **Admit `.cover` into the proof.** Either tighten the source
   semantics so that `cover` matches GOTO's per-trace failure flag, or
   weaken the simulation conclusion to a per-trace correspondence.
   Conceptual work first, then proof.
5. **Admit nondet `.init` into the proof.** The asymmetry is:
   source `.init x ty .nondet md` *binds* x to an arbitrary value; GOTO
   emits a single `DECL` (an unconstrained store update). The fix is
   either to add a `step_decl_nondet` rule that nondeterministically
   updates the store, or to translate nondet init as `DECL + ASSIGN(nondet)`.
   Tracked at issue #1186.
6. **Admit `.call`.** Significant: requires modeling
   `step_function_call`, threading the call-stack semantics through
   `StepGoto`, and proving that `coreCFGToGotoTransform`'s call lowering
   matches. Estimated effort: very large.

## Build artifacts

- The `#print axioms CProverGOTO.coreCFGToGoto_forward_simulation`
  output (in `StrataTest/Backends/CBMC/GOTO/SemanticsTests.lean`)
  reports `[propext, Classical.choice, Quot.sound]` — only Lean's
  foundational axioms.
- No project-defined `axiom` declarations.
- `lake build Strata.Backends.CBMC.GOTO.CoreCFGToGOTOCorrect` succeeds
  with no `sorry` warnings on the proof-chain theorems. Two pre-existing
  `unused variable` warnings remain (`h_wf_bool_goto` at line 175,
  `h_expr` at line 679); both are out of scope.
- `lake build StrataTest.Backends.CBMC.GOTO.SemanticsTests` succeeds
  and exercises `block_simulation_empty_finish` on a hand-built
  `WellFormedTranslation` for a one-block trivial CFG.

## Files touched (this branch)

- `Strata/Backends/CBMC/GOTO/Semantics.lean` — `StepGoto`, `StepGotoStar`,
  `GotoConfig`, `Program.instrAt`, `WellFormedSemanticEvalGotoBool`.
- `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOInvariants.lean` —
  `CmdEmittedAt`, `WellFormedTranslation`, instruction-count arithmetic,
  `isAdmittedCmd`.
- `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrect.lean` — the proof
  chain itself (10 named theorems).
- `Strata/Languages/Core/StatementSemanticsProps.lean` —
  `CoreCFGStepStar_rec` infrastructure (added in commit `6e94a20cb`).
- `StrataTest/Backends/CBMC/GOTO/SemanticsTests.lean` — sanity test
  and `#print axioms` line.

## Related documents

- `docs/CoreToGOTO_Gaps.md` — translation gaps (DFCC, axioms,
  unsupported types/expressions). Mostly orthogonal to this proof —
  that doc is about *what the translator emits*, this one is about
  *what we've proved correct about it*.
- `docs/CoreToGOTO_SemanticsComparison.md` — comparison with the
  alternative GOTO-semantics formalization on
  `tautschnig/goto-semantics`, including porting insights.
