# Round-7 supervisor report — R7a/R7b/R7c parallel run + v4 composition

**Run date:** 2026-05-22
**Supervisor:** main session on `htd/unstructured-to-goto`
**Workers:** three parallel agents on disjoint files + supervisor v4
composition.

## TL;DR

| Item | Status | Outcome |
|---|---|---|
| **Worker R7a** | **Tier 2 (Good)** | `goto_target_in_range_of_wf` discharges `h_goto_target_in_range` modulo a small `EveryGotoTargetIsLabelMapEntry` aux. Axioms `[propext, Quot.sound]` (no `Classical.choice`!). |
| **Worker R7b** | **Tier 1 (Best)** | `no_dead_program_of_translator` fully discharges `h_no_dead` by translator induction. Axioms standard. |
| **Worker R7c** | **Tier 3 (Acceptable)** | Strengthened `CmdEmittedAt` to expose lhs symbols; `_v2` bridge replaces R6a's three lookup-field passthroughs with provenance + pinning + value triplets. Axioms standard. |
| **Supervisor v4** | **closed** | `coreCFGToGotoTransform_forward_simulation_concrete_v4` composes R7a + R7b + R7c on top of v3, internally discharging the three round-6 passthroughs. |

Net contribution to `htd/unstructured-to-goto` since round 6:
**~1690 LoC** (R7a: 105 + 14 LoC; R7b: 716 + 16 LoC; R7c: ~570 LoC
new file + ~250 LoC of `CmdEmittedAt` strengthening + ~140 LoC v2
bridge; supervisor v4: ~285 LoC). `lake build` green. No
`sorry`/`admit`. Standard axiom set on all theorems.

## Per-worker outcomes

### Worker R7a — Tier 2 (Good)

`docs/_workers/R7a_goto_target_in_range_report.md`. Three commits.

**Delivered** (new file `Strata/Backends/CBMC/GOTO/GotoTargetInRange.lean`,
105 LoC):

* `EveryGotoTargetIsLabelMapEntry cfg pgm labelMap` — auxiliary
  predicate: every emitted GOTO's target is a labelMap entry for a
  block in `cfg.blocks`.
* `goto_target_in_range_of_wf` — under `wf` plus the auxiliary,
  every emitted GOTO's target PC is in bounds. Discharges R6a's
  `h_goto_target_in_range`.

**Notable:** axioms `[propext, Quot.sound]` (no `Classical.choice`!).
The proof uses `wf.layout_location` to extract the target
instruction without invoking choice.

**Tier 2 obstacle:** `WellFormedTranslation` is forward-only (CFG →
program); it doesn't expose a backward direction (program-GOTO →
block). Closing without auxiliary requires adding a
`goto_originates_from_block` field to `WellFormedTranslation` plus
its inductive discharge (~150-200 LoC). Out of round-7 scope; the
auxiliary is mechanically discharable from
`coreCFGToGotoTransform`'s structure.

### Worker R7b — Tier 1 (Best)

`docs/_workers/R7b_no_dead_report.md`. Three commits.

**Delivered** (new file `Strata/Backends/CBMC/GOTO/NoDead.lean`,
716 LoC + axiom test):

* `HasNoDead trans` — predicate: no DEAD instructions in the
  translator state's array.
* Per-translator-step preservation lemmas: `Cmd.toGotoInstructions`,
  `coreCFGToGotoCmdStep`, `cmdsFoldlM`, emit-helpers,
  `coreCFGToGotoBlockStep`, `blocksFoldlM`, `coreCFGToGotoPatchStep`,
  `patchesFoldlM`, `patchGotoTargets`.
* `no_dead_of_translator_no_contracts_explicit` — composes the
  preservation lemmas for the explicit decomposition pieces.
* `no_dead_of_translator` — direct form (uses
  `coreCFGToGotoTransform_decompose` internally).
* `no_dead_program_of_translator` — wrapper at the
  `Program.instrAt` level (the precise shape R6a's
  `h_no_dead` consumes).

**Verified** axioms `[propext, Classical.choice, Quot.sound]`.

### Worker R7c — Tier 3 (Acceptable)

`docs/_workers/R7c_lookup_fields_report.md`. Five commits.

**Delivered**:

1. **Strengthened `CmdEmittedAt`** in
   `CoreCFGToGOTOInvariants.lean`: the `init_det`/`init_nondet`/
   `set_det`/`set_nondet` constructors now fix the DECL/ASSIGN code's
   symbol operand to `Expr.symbol (identToString v) gty` (the exact
   translator emit shape) instead of an existential `∃ lhs`. The
   `set_nondet` constructor additionally exposes the nondet rhs's
   `.id = .side_effect .Nondet` and `.type = gty`. Builders and
   drivers in `CoreCFGToGotoTransformWF.lean` updated.

2. **Added `@[expose]`** to `Code.assign`, `Code.decl`, `Expr.symbol`
   (`Code.lean`, `Expr.lean`).

3. **New file** `Strata/Backends/CBMC/GOTO/InstructionLookups.lean`
   with three bridge theorems
   (`decl_lookup_of_provenance_and_pinned`,
   `assign_lookup_of_provenance_and_pinned`,
   `assign_nondet_lookup_of_provenance_and_pinned`).

4. **`wellFormedTranslation_to_translatorBridgeHyps_v2`** in
   `TranslatorBridgeHypsDischarge.lean` — replaces R6a's three
   lookup-field passthroughs with three provenance hypotheses +
   three pinning hypotheses, delegating to `InstructionLookups`.

**Why Tier 3 (not Tier 1):** R7c discovered a genuine semantic
constraint. The lookup fields require "for any `x` with InitState
at this PC, code's symbol = nameMap x", which by `nameMap`
injectivity forces `x = v_src` (the source-cmd's variable). This
trace-level constraint pinning `x = v_src` lives at the
bisimulation consumer's level, not at the `WellFormedTranslation`
layer. The discharge therefore *must* take a caller-side
hypothesis ("pinned") capturing this constraint. R7c's solution
(provenance + pinning split) is honest about which obligations are
mechanical and which are caller-side.

**Verified** axioms standard.

**A merge note:** R7c's worktree was based on
`htd/structure-to-unstructure-correct` rather than
`htd/unstructured-to-goto`. The supervisor cherry-picked R7c's
three substantive commits + the report; conflicts were trivial
because R7c only modified files that the divergent branch hadn't
touched.

## Supervisor — v4 composition

`coreCFGToGotoTransform_forward_simulation_concrete_v4` in
`CoreCFGToGOTOConcrete.lean` (~285 LoC). Layers on top of v3 by
internally discharging:

* `h_goto_target_in_range` via R7a's `goto_target_in_range_of_wf`
  (modulo `EveryGotoTargetIsLabelMapEntry` aux, taken as a
  hypothesis).
* `h_no_dead` via R7b's `no_dead_program_of_translator` (using
  `HasNoDead trans₀` as a hypothesis — trivially satisfied for
  empty initial state).
* `h_brHyps : TranslatorBridgeHyps` via R7c's `_v2` bridge
  (using provenance + pinning + value hypotheses).

Marked `GotoTargetInRange.EveryGotoTargetIsLabelMapEntry` as
`@[expose]` so the v4 proof can step into its body.

**Verified axiom set:**

```
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v4'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

Same as the original `coreCFGToGoto_forward_simulation`. No new
project-internal axioms.

## What this delivers

After round 7, the top-level concrete theorem `_v4` requires:

### Translator-input invariants (mostly trivial)

* `h_init_size`, `h_init_loc`, `h_init_no_dead` (trivial for
  `trans₀` with empty `instructions = #[]`).
* `h_distinct`, `h_admitted_blocks`, `h_loopContracts_empty_post`,
  `h_entry_first` (CFG-level fragment restrictions).

### B3 expression-side bundle

* `h_red`, `h_op`, `h_uniform`, `h_commutes_not`. Caller-supplied
  for the bool+int fragment.

### Genuine caller obligations

* `h_eval_bool_corr` (target/target boolean evaluator agreement).
* `h_corr` (initial-store correspondence).
* `h_inj : Function.Injective nameMap`.
* `h_wf_bool` (boolean evaluator well-formedness).

### R7c's pinning hypotheses (trace-level caller obligations)

* `h_decl_x_pinned`, `h_assn_x_pinned`, `h_assn_rhs_pinned`. These
  are *genuinely* caller-side: they relate the trace's
  source-side `InitState`/`UpdateState` witness `x` to the
  translator's emitted `nameMap`-named symbol. R7c showed these
  cannot be discharged at the `WellFormedTranslation` layer.

### R7c's value-side hypotheses (genuine caller obligations)

* `h_decl_empty_value`, `h_assign_value_corr`,
  `h_assign_nondet_value_corr`. Source-target evaluator agreement
  on values; not discharable from translator structure.

### Mechanically-discharable auxiliaries (deferred to round 8+)

* R7a's `h_aux_goto_target` (every GOTO target is a labelMap
  entry — derivable from the translator's emit-helpers).
* R7c's `h_decl_provenance`, `h_assn_provenance`,
  `h_assn_nondet_provenance` (every emitted DECL/ASSIGN code uses
  `Expr.symbol (nameMap v_src) gty` — derivable from the
  strengthened `CmdEmittedAt` plus a CFG-PC inversion).

### Source-side run

* `σ`, `σ'`, `b`, `σ_goto`, `h_run_src`.

This is the **"concrete soundness story modulo evaluator
agreement"** milestone. Every remaining hypothesis is either
* trivial for the standard caller (translator-input invariants),
* B3's expression-side bundle (a known caller obligation),
* a genuine caller obligation about the evaluator/store
  (`h_eval_bool_corr`, `h_corr`, the value-side hypotheses), or
* a mechanically-discharable structural fact (R7a aux, R7c
  provenance) that round 8 can close.

## Process observations

**All three workers ran cleanly** — no watchdog stalls in any of
the rounds 3-7.

**R7a's `[propext, Quot.sound]` axiom set** is notable. It avoided
`Classical.choice` by structuring the proof with `wf.layout_location`
directly rather than using `Classical.choose` on an existential.
This is a tighter axiom signature than the rest of the chain.

**R7b's per-translator-step preservation pattern** scaled cleanly
to a 716-LoC proof. The same pattern that worked for round-3 A3's
size_eq/locationNum_eq_index (Cmd-step → cmds-fold → block-step →
blocks-fold → patcher-step → patches-fold → patchGotoTargets) is
reusable for any preservation property.

**R7c's discovery of the trace-level pinning obligation** is
genuinely interesting. The naive view "the lookup field follows
from `CmdEmittedAt` + injectivity" is wrong: `CmdEmittedAt`'s
existential `lhs` was the symptom, not the cause. The cause is
that `CmdEmittedAt` is indexed by source-side cmds (`Cmd P`), but
the lookup field is indexed by source-side trace witnesses
(`InitState`/`UpdateState` derivations). The latter pin `x` to a
specific value via the trace, while the former is universal. The
"pinned" hypothesis is the bridge — and is genuinely irreducible
at the WF layer.

**A merge friction note (round 7):** R7c's worktree was based on
`htd/structure-to-unstructure-correct` rather than
`htd/unstructured-to-goto`. This was the second occurrence of a
worker basing its work on a divergent branch (R6a was the first).
The pattern: when a worker is told to "use git worktree", the
system sometimes picks an arbitrary branch base. Cherry-picks
have been clean both times because the workers' modifications
respected file-disjointness. For round 8, supervisor will brief
workers more explicitly on which branch to base their worktree
on.

## Cumulative across all rounds

| Round | New Lean LoC | Theorem closed |
|---|---|---|
| Pre-rounds | ~3000 | `coreCFGToGoto_forward_simulation` |
| Round 1 | ~2500 | A's sub-lemmas + B's per-operator + C's discharge |
| Round 2 | ~2000 | A2 + B2 + items 5/6 |
| Round 3 | ~1900 | A3 structural + B3 bool+int |
| Round 4 | ~1900 | A4 WF top-level + concrete v1 |
| Round 5 | ~2400 | A5a/A5b layout closures + strengthened WF |
| Round 6 | ~750 | R6a TranslatorBridgeHyps + R6b expression-side + v2/v3 |
| Round 7 | ~1690 | R7a goto-target-in-range + R7b no-dead + R7c lookup fields + v4 |

**~16,140 LoC** of correctness infrastructure. `lake build` green
throughout, no `sorry` in live code, all top-level theorems closed
under the standard axiom set `[propext, Classical.choice, Quot.sound]`.

## Files changed in round 7

| File | Change | Worker |
|---|---|---|
| `Strata/Backends/CBMC/GOTO/GotoTargetInRange.lean` | new (105 LoC; +1 char `@[expose]` from supervisor) | R7a + supervisor |
| `StrataTest/Backends/CBMC/GOTO/GotoTargetInRangeAxioms.lean` | new (14 LoC) | R7a |
| `Strata/Backends/CBMC/GOTO/NoDead.lean` | new (716 LoC) | R7b |
| `StrataTest/Backends/CBMC/GOTO/NoDeadAxioms.lean` | new (16 LoC) | R7b |
| `Strata/Backends/CBMC/GOTO/InstructionLookups.lean` | new (333 LoC) | R7c |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOInvariants.lean` | strengthened CmdEmittedAt (~70 LoC delta) | R7c |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean` | builder/driver updates for strengthened CmdEmittedAt | R7c |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrect.lean` | pattern-match re-ordering for strengthened CmdEmittedAt | R7c |
| `Strata/Backends/CBMC/GOTO/TranslatorBridgeHypsDischarge.lean` | added `_v2` bridge (~140 LoC) | R7c |
| `Strata/Backends/CBMC/GOTO/Code.lean` / `Expr.lean` | `@[expose]` markers | R7c |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` | added `_v4` (~285 LoC) | supervisor |
| `docs/_workers/R7a_goto_target_in_range_report.md` | new (154 LoC) | R7a |
| `docs/_workers/R7b_no_dead_report.md` | new (164 LoC) | R7b |
| `docs/_workers/R7c_lookup_fields_report.md` | new (207 LoC) | R7c |
| `docs/_workers/round7_supervisor_report.md` | new (this file) | supervisor |

## Worktree archival

Three round-7 worktrees remain locked at their final commits:

- R7a: `/Users/htd/Documents/Strata/.claude/worktrees/agent-ae776bc88c9f1c71b`
- R7b: `/Users/htd/Documents/Strata/.claude/worktrees/agent-a3191be5f96e0c534`
- R7c: `/Users/htd/Documents/Strata/.claude/worktrees/agent-a39967421d37146db`

## Suggested next steps

The round-8 candidates are R7a's `EveryGotoTargetIsLabelMapEntry`
aux and R7c's three provenance hypotheses. Both are mechanically
discharable from translator structural induction (~150-300 LoC
each).

After round 8, `_v5` would have only:
* Translator-input invariants (trivial for standard callers).
* B3's expression-side bundle.
* `Function.Injective nameMap`.
* R7c's three pinning hypotheses (trace-level — genuinely
  caller-side).
* R7c's three value-side hypotheses (caller-side evaluator
  agreement).
* `h_eval_bool_corr`, `h_corr`, source-side run, `h_wf_bool`.

That would be the **"concrete soundness story modulo trace-level
and evaluator obligations"** milestone — the absolute minimum
hypothesis surface achievable without an entirely new layer of
proof infrastructure (e.g. modeling source-side traces explicitly).
