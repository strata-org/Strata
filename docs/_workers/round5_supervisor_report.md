# Round-5 supervisor report — A5a/A5b parallel run + theorem tightening

**Run date:** 2026-05-21
**Supervisor:** main session on `htd/unstructured-to-goto`
**Workers:** two parallel agents (A5a, A5b) on disjoint sub-problems
within the same file.

## TL;DR

| Item | Status | Outcome |
|---|---|---|
| **Worker A5a** | **Best (Tier 1)** | All three hypotheses closed: `entry_in_map_of_translator`, `labelMap_inj_of_translator`, `layout_block_body_of_translator` |
| **Worker A5b** | **Best (Tier 1)** | Both hypotheses closed: `layout_cond_goto_of_translator`, `layout_cond_goto_guards_of_translator` |
| **Strengthened WF theorem** | **closed** | `coreCFGToGotoTransform_wellFormed_strengthened` composes A4's theorem with the five round-5 closures; A4's hypothesis-parameter fields are gone |
| **Tightened concrete theorem** | **closed** | `coreCFGToGotoTransform_forward_simulation_concrete` updated to use the strengthened WF theorem |

Net contribution to `htd/unstructured-to-goto` since round 4:
**~2400 LoC** (A5a: +830, A5b: +1444, supervisor strengthened
theorem: +95, supervisor concrete theorem update: net +0). `lake build`
green throughout. No `sorry`/`admit` in live code. Standard axiom
set on all top-level theorems.

## Per-worker outcomes

### Worker A5a — Tier 1 (Best)

`docs/_workers/A5a_gap_a_close_report.md`. Six commits, all Tier 1.

**Three closure theorems delivered (no `sorry`):**

- **`entry_in_map_of_translator`** (~50 LoC) — case-split on
  `cfg.blocks`; empty case contradicts `h_entry_first`, cons case
  applies `blocksFoldlM_layout_location` to extract the labelMap
  entry for `cfg.entry`.

- **`labelMap_inj_of_translator`** (~190 LoC) — strategy: combined
  invariant `labelMapBoundedAndInj` saying every pc in the labelMap
  is `< trans.nextLoc` AND the labelMap is injective. Each block
  step preserves it because the new pc equals the old `nextLoc` and
  the new `nextLoc` strictly advances. Notably does NOT need
  `BlockLabelsDistinct`.

- **`layout_block_body_of_translator`** (~590 LoC) — three-layer
  proof:
  1. `cmdsFoldlM_eq_innerCmdLoop_on_admitted` shows the refactored
     `cmdsFoldlM coreCFGToGotoCmdStep` equals A2's `innerCmdLoop`
     on admitted commands, allowing reuse of A2's
     `innerCmdLoop_layout_block_body`.
  2. Per-block + outer-fold lifts
     (`coreCFGToGotoBlockStep_layout_block_body`,
     `blocksFoldlM_layout_block_body`).
  3. `patchGotoTargets_preserves_full_except_target` (new) bridges
     `st_final.trans.instructions` to `ans.instructions` — the
     patcher only modifies `target`, all other fields preserved,
     and `CmdEmittedAt` only checks `type`/`code`/`guard`.

### Worker A5b — Tier 1 (Best)

`docs/_workers/A5b_gap_a_close_report.md`. Six commits, all Tier 1.

**Two closure theorems delivered (no `sorry`):**

- **`layout_cond_goto_of_translator`** (~700 LoC) — composes a new
  patcher post-condition (`patchGotoTargets_target_at_patched_idx`)
  with `pendingPatches` index-distinctness lemmas and the lifted
  per-block layout. After patching, every `.condGoto` block produces
  two GOTOs at the right pcs with `.target = some pc_lf` and
  `.target = some pc_lt`.

- **`layout_cond_goto_guards_of_translator`** (~745 LoC) — adds new
  `patchGotoTargets_preserves_guard` lemma (analogue of A4's
  `_preserves_type`) and lifts the per-block guard shape
  (`e_goto.not` and `Expr.true`) through the foldlM and patcher.

### Supervisor — strengthened WF theorem + tightened concrete theorem

After A5a/A5b returned, supervisor:

1. **Merged worker outputs.** Both workers wrote to disjoint
   end-of-file insertion points (A5a at line 4491, A5b at line 4547
   of A4's HEAD). The supervisor concatenated A5a's full file (1..5375)
   + A5b's content (4547..5990) + trailer.

2. **Verified axioms** on all five closure theorems individually —
   each `[propext, Classical.choice, Quot.sound]`.

3. **Wrote `coreCFGToGotoTransform_wellFormed_strengthened`** in
   `CoreCFGToGotoTransformWF.lean`. Composes A4's theorem with the
   five round-5 closures by discharging each of A4's hypothesis
   parameters via the corresponding `*_of_translator` theorem.
   Verified axiom set: standard.

4. **Updated `CoreCFGToGOTOConcrete.lean`** to use the strengthened
   theorem. The top-level
   `coreCFGToGotoTransform_forward_simulation_concrete` is now
   substantially simpler — A4's five hypothesis parameters are gone
   (discharged internally). Verified axiom set: standard.

## What landed: the assembly tower after round 5

```
A5a/A5b: layout_*_of_translator + {labelMap_inj,entry_in_map}_of_translator ✅
        ↓
A4: coreCFGToGotoTransform_wellFormed_nonempty ✅
        ↓
Round 5 supervisor:
  coreCFGToGotoTransform_wellFormed_strengthened ✅
        ↓ (composed in CoreCFGToGOTOConcrete.lean)

        +
B3: caller-supplied ExprTranslationPreservesEval (B3 produces this
   for the bool+int fragment)
        +
C:  steppingBridges_of_translator
   ⊢ SteppingBridges from EvalBoolCorr + TranslatorBridgeHyps
        ↓
Phase 3: coreCFGToGoto_forward_simulation_storeCorr
        ↓
coreCFGToGotoTransform_forward_simulation_concrete ✅
   axioms: [propext, Classical.choice, Quot.sound]
```

## What remains for unconditional concrete soundness

Even after round 5, the top-level concrete theorem still takes
hypotheses. These break into three categories:

### 1. Translator-input invariants (mostly trivial)

- `h_init_size`, `h_init_loc`: trivial when `trans₀ = empty`.
- `h_distinct`: source CFG has distinct block labels (a global
  property of any well-formed input).
- `h_admitted_blocks`: original Gap A scope (no `.call`, no
  `.cover`, no nondet `.init`).
- `h_loopContracts_empty_post`: A3's loop-contract sidestep
  (any CFG without `specLoopInvariant`/`specDecreases` metadata).
- `h_entry_first`: the translator already checks and rejects on
  violation; for any CFG the translator accepts, this holds.

These are *almost* discharged for free at any concrete call site
that uses `stmtsToCFG` to build the CFG.

### 2. Translator-output bridge hypotheses (the genuine remaining work)

- `h_tx_eq`: technical identity between two views of the
  expression translator. Ought to be provable by `rfl` once the
  proof witness is taken to be the actual translator.
- `h_expr_translated_witness`: finer-grained version of
  `h_expr_corr` — supplied by Worker B3's
  `toGotoExprCtx_preservesEval_boolInt` for the bool+int
  fragment.
- `h_brHyps : TranslatorBridgeHyps`: per-PC structural facts about
  the translator's actual output. **Most of these discharge
  mechanically from the round-5 `WellFormedTranslation`** —
  particularly `decl_lookup`, `dead_lookup`, `assign_lookup`,
  `assign_nondet_lookup`, `goto_target_resolves`. Estimated
  ~100-200 LoC to wire up.

### 3. Caller-supplied evaluator obligations (out of scope for the
"prove the translator correct" question)

- `h_expr_corr : ExprTranslationPreservesEval`: caller-supplied
  source-target evaluator agreement. B3 produces this for the
  bool+int fragment.
- `h_eval_bool_corr : EvalBoolCorr`: target/target evaluator
  agreement (this branch's `δ_goto_bool` vs. tautschnig's `eval`).
  Genuinely a caller obligation.
- `h_corr : StoreCorr`: initial-store correspondence. Caller
  obligation.

## Process observations

**The "report stub first + commit-as-you-go + disjoint-end-of-file
discipline" pattern continued to work flawlessly.** Both A5a and
A5b ran cleanly to completion. No watchdog stalls in rounds 3, 4,
or 5.

**Disjoint end-of-file is now a proven scalable pattern.** Two
workers modifying the same file with no merge conflicts —
something that hand-merges typically struggle with — was achieved
by simply telling them to write at distinct end-of-file regions.
The supervisor's concatenation merge took less than 5 minutes.

**A5a's three-layer proof for `layout_block_body`** is the
craftiest piece of the round. Bridging A2's old `innerCmdLoop`
(round-2 work) to A3's refactored `cmdsFoldlM` (round-3 work)
required an explicit equivalence lemma plus careful handling of
the patcher's effect on instruction fields. The "patcher only
modifies `target`" abstraction (A2 had it for `locationNum`, A4
extended it to `type`, A5a extended it further to all fields
except `target`) is now a clean tower.

**A5b's patcher-correctness lemma**
(`patchGotoTargets_target_at_patched_idx`) is the cleanest
formulation of the "the patcher actually patches" fact. It says:
for every `(idx, targetLoc) ∈ resolvedPatches` whose first
projections are pairwise distinct, after patching,
`instructions[idx].target = some targetLoc`. The
`pendingPatches_indices_distinct` lemma A5b also added discharges
the distinctness side-condition mechanically.

## Cumulative across all rounds

| Round | New Lean LoC | Theorem closed |
|---|---|---|
| Pre-rounds | ~3000 | `coreCFGToGoto_forward_simulation` (Phase 0/1/2/3 from the original expansion plan) |
| Round 1 | ~2500 | A's sub-lemmas + B's per-operator + C's full discharge |
| Round 2 | ~2000 | A2's loop infrastructure + B2's `FnToGotoIDReductions` + items 5/6 |
| Round 3 | ~1900 | A3's structural soundness + B3's full bool+int bridge |
| Round 4 | ~1900 | A4's WF top-level (Tier 2) + supervisor's concrete top-level (Tier 1) |
| Round 5 | ~2400 | A5a/A5b layout closures (both Tier 1) + supervisor's strengthened WF |

**~13,700 LoC of correctness infrastructure** for the call-free,
bool+int-fragment, CFG-to-GOTO translator. `lake build` green
throughout, no `sorry` in live code, all top-level theorems closed
under the standard axiom set `[propext, Classical.choice, Quot.sound]`.

## Files changed in round 5

| File | Change | Worker |
|---|---|---|
| `Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean` | 4549 → 6918 (+2369) | A5a (+830), A5b (+1444), supervisor (+95) |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` | net rewrite (-93 +147) | supervisor |
| `docs/_workers/A5a_gap_a_close_report.md` | new (162 LoC) | A5a |
| `docs/_workers/A5b_gap_a_close_report.md` | new (194 LoC) | A5b |
| `docs/_workers/round5_supervisor_report.md` | new (this file) | supervisor |

## Worktree archival

A5a worktree:
`/Users/htd/Documents/Strata/.claude/worktrees/agent-acc1841b30fcc7e19`
A5b worktree:
`/Users/htd/Documents/Strata/.claude/worktrees/agent-a227fca902cfa5de2`

Both remain locked at their final commits. Can be removed once
this report is reviewed.

## Suggested next steps

After round 5, the call-free, bool+int-fragment, single-`.finish`
slice has a near-fully-unconditional concrete forward simulation
theorem with the standard axiom set. The remaining work to close
the remaining hypotheses — bringing the theorem from "concrete with
caller-supplied bridges" to "discharged for the actual translator
output" — splits into three:

1. **`TranslatorBridgeHyps` discharge from `WellFormedTranslation`**
   (~100-200 LoC) — mechanical extraction from `CmdEmittedAt`
   constructors plus `findLocIdx_resolves` for
   `goto_target_resolves`. This is the natural Round 6 scope.

2. **`h_tx_eq` discharge** — should follow by `rfl` if the
   `ExprTranslationPreservesEval.tx` field is taken to be the
   actual translator. ~10-30 LoC.

3. **`h_expr_translated_witness`** — should follow from B3's
   `toGotoExprCtx_preservesEval_boolInt` plus a uniformity lemma.
   ~50-100 LoC.

After all three: the only remaining hypotheses are the genuine
caller obligations (`h_expr_corr`, `h_eval_bool_corr`, `h_corr`,
fragment restrictions). At that point we have what was originally
called the "concrete soundness story" for the call-free,
bool+int-fragment, CFG-to-GOTO translator slice.
