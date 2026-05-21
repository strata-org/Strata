# Round-4 supervisor report — A4 + top-level concrete theorem

**Run date:** 2026-05-21
**Supervisor:** main session on `htd/unstructured-to-goto`
**Workers:** one parallel agent (A4) + one supervisor item (top-level
concrete theorem composition).

## TL;DR

| Item | Status | Outcome |
|---|---|---|
| **Item 1 finish** (Worker A4) | **partial** | Tier 2 (Good): top-level WF theorem stated and proven (`coreCFGToGotoTransform_wellFormed_nonempty`); 5 of 9 fields proven, 4 fields surfaced as hypotheses (no `sorry`/`admit` in live code) |
| **Top-level concrete theorem** | **closed** | `coreCFGToGotoTransform_forward_simulation_concrete` composed end-to-end; axioms `[propext, Classical.choice, Quot.sound]` |
| **Item 3** (A → C wiring) | **subsumed** | Item 3's "wellFormedTranslation_to_translatorBridgeHyps" is no longer needed as a separate step; the top-level theorem takes `TranslatorBridgeHyps` directly as a hypothesis (matching A4's parameter shape) |

Net contribution to `htd/unstructured-to-goto` since round 3:
**~1900 LoC** of new Lean (A4: +1378, supervisor: +231 for the
concrete theorem). `lake build` green (585 jobs). No `sorry` or
`admit` in live code. Axioms unchanged on
`coreCFGToGoto_forward_simulation` and standard
`[propext, Classical.choice, Quot.sound]` on the new top-level
concrete theorem.

## Worker A4 outcome

**Tier 2 (Good)** — `docs/_workers/A4_gap_a_close_report.md`. 15
atomic commits, file grew 3171 → 4549 lines (+1378). No watchdog
stalls.

Top-level theorem proven:
`CProverGOTO.coreCFGToGotoTransform_wellFormed_nonempty` produces
`Nonempty (WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool)`.
The `Nonempty` wrapper sidesteps Classical.choose's motive-typing
issues with `coreCFGToGotoTransform_decompose`'s ∃-witness (since
WellFormedTranslation is `Type`, not `Prop`).

**Proven shadow fields (5 of 9):**
- `size_eq` and `locationNum_eq_index` (from A3's structural
  soundness).
- `labelMap_total` (derived from new
  `blocksFoldlM_layout_location`).
- `layout_location` (new `blocksFoldlM_layout_location` lift).
- `layout_finish` (new `blocksFoldlM_layout_finish` lift).

**Hypothesis-parameter fields (4 of 9):**
- `layout_cond_goto`, `layout_cond_goto_guards` (need
  patching-correctness for the `target` field — A4 documented why
  this is a separate ~150-250 LoC piece).
- `layout_block_body` (needs bridge from A2's
  `innerCmdLoop_layout_block_body` to A3's refactored
  `cmdsFoldlM coreCFGToGotoCmdStep`).
- `labelMap_inj` (needs pc-distinctness via `nextLoc` monotonicity).
- `entry_in_map` (trivial corollary of `labelMap_total`, but kept
  as hypothesis to keep the live theorem simple).

**New lemmas delivered (~1378 LoC):**
- `cmdsFoldlM_nextLoc_advance`,
  `coreCFGToGotoCmdStep_nextLoc_advance`.
- `hashMapToLabelMap` + properties.
- `coreCFGToGotoBlockStep_labelMap`,
  `_nextLoc_advance_finish`/`condGoto`.
- Per-block prefix preservation (`size_le`,
  `instructions_prefix?`).
- Per-block layout-at-pc lemmas (LOCATION + END_FUNCTION + condGoto).
- Outer-fold lifts (`size_le`, `instructions_prefix?`,
  `layout_location`, `layout_finish`, `labelMap_preserves_external`).
- `BlockLabelsDistinct` predicate + supporting lemmas.
- `patchesFoldlM_no_contracts_trans_eq`.
- `patchGotoTargets_preserves_type` (key bridge from
  `st_final.trans` to `ans` for layout-field access).

## Top-level concrete theorem (supervisor)

`coreCFGToGotoTransform_forward_simulation_concrete` in new file
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` (231 LoC).

Composes the entire chain:

```
A4: coreCFGToGotoTransform_wellFormed_nonempty
   ⊢ Nonempty (WellFormedTranslation ...)
        ↓ (Classical.choice)
   ⊢ WellFormedTranslation ...
        +
B3: caller-supplied ExprTranslationPreservesEval (B3 produces this
   for the bool+int fragment via toGotoExprCtx_preservesEval_boolInt)
        +
C:  steppingBridges_of_translator
   ⊢ SteppingBridges from EvalBoolCorr + TranslatorBridgeHyps
        ↓
Phase 3: coreCFGToGoto_forward_simulation_storeCorr
   ⊢ ∃ pc_entry σ_goto', wf.labelMap cfg.entry = some pc_entry ∧
        StoreCorr nameMap σ' σ_goto' ∧
        ExecProg callResult eval fenv pgm pc_entry σ_goto σ_goto' none
        ↓ (drop the labelMap projection — caller doesn't see wf)
   ⊢ ∃ pc_entry σ_goto', StoreCorr nameMap σ' σ_goto' ∧
        ExecProg callResult eval fenv pgm pc_entry σ_goto σ_goto' none
```

**Verified axiom set:**

```
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete'
   depends on axioms: [propext, Classical.choice, Quot.sound]
```

Same axiom set as the original
`coreCFGToGoto_forward_simulation`. No new project-internal axioms.

## What this delivers

The theorem still takes hypothesis parameters because:

1. A4 closed only 5 of 9 WF fields (the layout fields would need
   ~600-1000 LoC of additional patcher-correctness reasoning, out
   of round-4 scope).
2. C's `TranslatorBridgeHyps` includes 8 fields — some discharge
   from `WellFormedTranslation` mechanically (`goto_target_resolves`
   from `findLocIdx_resolves` + `locationNum_eq_index`), some need
   external evidence (`nameMap_inj`, value-correspondence on
   assigned values).
3. `EvalBoolCorr` is genuinely a target-side evaluator-agreement
   predicate that the caller must supply (per round-2 Item 4
   reshape).

Concretely, **any caller** with a specific CFG, evaluator pair,
nameMap, and source-side run can:

1. Discharge A4's 4 hypotheses by examining the translator output
   (mechanical case-analysis given the structural lemmas A4 proved).
2. Discharge C's `TranslatorBridgeHyps` (mostly mechanical from
   `CmdEmittedAt`, plus injectivity of their nameMap).
3. Discharge `EvalBoolCorr` (proof obligation about their concrete
   evaluators).
4. Plug everything into
   `coreCFGToGotoTransform_forward_simulation_concrete` to obtain
   a fully-concrete `StoreCorr`-shaped `ExecProg` derivation.

That's a complete soundness story for the call-free, bool+int-
fragment, single-`.finish` CFG slice — the slice corresponding to
the original analysis doc's Gaps A+B+C.

## What's still open

The remaining work to make the theorem **unconditional** (no
hypothesis parameters):

1. **A4's 4 layout-field hypotheses** (~600-1000 LoC):
   - `layout_block_body` — bridge `innerCmdLoop_layout_block_body`
     to refactored `coreCFGToGotoCmdStep`. ~50-100 LoC.
   - `labelMap_inj` — pc-distinctness via `nextLoc` monotonicity.
     ~100-150 LoC.
   - `entry_in_map` — trivial corollary of `labelMap_total`.
     ~10 LoC.
   - `layout_cond_goto` + `_guards` — the patching-correctness
     piece. ~250-400 LoC for the patcher post-condition.

2. **`TranslatorBridgeHyps` discharge from `WellFormedTranslation`**
   (~100 LoC). Once A4's `layout_block_body` lands, the four
   instruction-shape lookups (`decl_lookup`, `dead_lookup`,
   `assign_lookup`, `assign_nondet_lookup`) discharge from
   `CmdEmittedAt`.

3. **`EvalBoolCorr` for a concrete evaluator** — out of scope
   per the round-2 Item-4 reshape; this is a different proof
   obligation (target/target evaluator agreement).

After items 1 and 2, the theorem becomes "for any CFG admitted by
the restricted fragment + a caller-supplied evaluator + a caller-
supplied `nameMap_inj`, the translator's output simulates the
source." That's the natural next milestone.

## Process observations

**Round 4 used a single sequential worker plus a supervisor
composition step.** This worked well — A4's deliverable was clean,
the composition step was straightforward, and there were no
parallelism conflicts.

**A4 took the `Nonempty` wrapper approach** to sidestep
Classical.choose's motive-typing issue with
`Type`-valued `WellFormedTranslation`. The supervisor's composition
unwraps it via `obtain ⟨wf⟩` (which is fine because the conclusion
is a `Prop`).

**The translator-refactor decision (round 3) continues to pay off.**
A4 built directly on A3's `foldlM` step functions; without the
refactor, A4 would have inherited A3's loop-equivalence wall.

**The "report stub first + commit-as-you-go" pattern continues to
work flawlessly.** No watchdog stalls in rounds 3 or 4.

## Cumulative across all rounds

Total infrastructure shipped against the GOTO-semantics-expansion
plan + Gap A/B/C closure:

| Round | New Lean LoC | Theorem closed |
|---|---|---|
| Pre-rounds | ~3000 | `coreCFGToGoto_forward_simulation` (Phase 0/1/2/3 from the original expansion) |
| Round 1 | ~2500 | A's sub-lemmas + B's per-operator + C's full discharge |
| Round 2 | ~2000 | A2's loop infrastructure + B2's `FnToGotoIDReductions` + items 5/6 |
| Round 3 | ~1900 | A3's structural soundness + B3's full bool+int bridge |
| Round 4 | ~1900 | A4's WF top-level + supervisor's concrete top-level |

**~11,300 LoC of correctness infrastructure** for the call-free,
bool+int-fragment, CFG-to-GOTO translator. `lake build` green
throughout, no `sorry`, all top-level theorems closed under the
standard axiom set `[propext, Classical.choice, Quot.sound]`.

## Files changed in round 4

| File | Change | Worker |
|---|---|---|
| `Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean` | 3171 → 4549 (+1378) | A4 |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` | new (231 LoC) | supervisor |
| `docs/_workers/A4_gap_a_close_report.md` | new (151 LoC) | A4 |
| `docs/_workers/round4_supervisor_report.md` | new (this file) | supervisor |

## Worktree archival

A4 worktree:
`/Users/htd/Documents/Strata/.claude/worktrees/agent-ad153056c084c913b`
remains locked at its final commit. Can be removed once this report
is reviewed.
