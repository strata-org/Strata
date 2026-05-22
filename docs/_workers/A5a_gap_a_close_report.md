# Worker A5a — Gap A Close Report (round 5)

## Mission

Close three of the four hypotheses A4 left open in
`coreCFGToGotoTransform_wellFormed_nonempty`:
1. `entry_in_map_of_translator`
2. `labelMap_inj_of_translator`
3. `layout_block_body_of_translator`

Worker A5b in parallel handles the remaining `layout_cond_goto`
+ `layout_cond_goto_guards` hypotheses.

## Status: **Tier 1 — Best (all three closed without `sorry`)**

- [x] Read A4 report and identify the four hypothesis shapes.
- [x] Locate insertion point in `CoreCFGToGotoTransformWF.lean`.
- [x] Close `entry_in_map_of_translator` (~50 LoC, 1 commit).
- [x] Close `labelMap_inj_of_translator` (~190 LoC, 1 commit).
- [x] Close `layout_block_body_of_translator` (~590 LoC, 2 commits).
- [x] `lake build` green at every commit (585 jobs).
- [x] `FinishPlacementProbe` + `SemanticsTests` pass.
- [x] Axioms unchanged on `coreCFGToGoto_forward_simulation`:
  `[propext, Classical.choice, Quot.sound]`.

## Theorems delivered

All three closure theorems live at the end of
`Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean` in namespace
`CProverGOTO`, just after A4's `coreCFGToGotoTransform_wellFormed_nonempty`:

| Theorem | Line | Purpose |
|---|---|---|
| `entry_in_map_of_translator` | 4517 | Discharges A4's `h_entry_in_map` hypothesis given `h_entry_first` |
| `labelMap_inj_of_translator` | 4701 | Discharges A4's `h_labelMap_inj` hypothesis (no extra hyps needed) |
| `layout_block_body_of_translator` | 5148 | Discharges A4's `h_layout_block_body` hypothesis |

### Supporting lemmas (also added, ~700 LoC total)

`labelMap_inj` infrastructure:
- `labelMapBoundedAndInj` (def, line 4584): combined invariant
- `labelMapBoundedAndInj_empty` (line 4591): trivial holds for empty map
- `coreCFGToGotoBlockStep_preserves_labelMapBoundedAndInj` (line 4601):
  per-block step preserves the invariant
- `blocksFoldlM_preserves_labelMapBoundedAndInj` (line 4666):
  blocks-fold preserves the invariant

`layout_block_body` infrastructure:
- `cmdsFoldlM_eq_innerCmdLoop_on_admitted` (line 4756): cmdsFoldlM on
  admitted commands equals innerCmdLoop, allowing reuse of A2's
  `innerCmdLoop_layout_block_body`
- `coreCFGToGotoBlockStep_layout_block_body` (line 4791): per-block
  layout extraction
- `blocksFoldlM_layout_block_body` (line 4960): outer-fold lift
- `patch_one_preserves_full_except_target` (line 5101, private): single
  patch preserves all fields except `target`
- `patchGotoTargets_preserves_full_except_target` (line 5101): full
  patcher preserves all fields except `target`

## Strategies

### `entry_in_map_of_translator`
Case-split on `cfg.blocks`:
- `[]`: contradicts `h_entry_first : cfg.blocks.head?.map Prod.fst = some cfg.entry`.
- `(l, blk) :: rest`: from `h_entry_first`, `l = cfg.entry`. So
  `(cfg.entry, blk) ∈ cfg.blocks`. Apply `blocksFoldlM_layout_location`
  to get `st_final.labelMap[cfg.entry]? = some pc`.

### `labelMap_inj_of_translator`
Stronger combined invariant `labelMapBoundedAndInj`:
1. Every pc in the labelMap is `< trans.nextLoc`.
2. The labelMap is injective.

Each block step preserves the invariant:
- The newly inserted pc equals the pre-step `nextLoc`, which is
  strictly less than the post-step `nextLoc` (by
  `coreCFGToGotoBlockStep_nextLoc_advance_*`).
- For injectivity: pre-existing pcs were `< pre-step nextLoc`; the new
  pc equals the pre-step `nextLoc`. So no old entry can collide with
  the new entry.

`labelMapBoundedAndInj` holds at the initial state (empty labelMap).
Applying via `blocksFoldlM` yields it at `st_final`, from which
`labelMap_inj` follows. **Notably, this proof does NOT need
`BlockLabelsDistinct`** — even with duplicate labels, the foldlM-final
labelMap is injective because `nextLoc` strictly advances at each step.

### `layout_block_body_of_translator`
Three layers:

1. **Equivalence**: `cmdsFoldlM_eq_innerCmdLoop_on_admitted`. On
   admitted commands, `cmdsFoldlM coreCFGToGotoCmdStep trans = ok ans`
   iff `innerCmdLoop trans.T fname cmds trans = ok ans`. The
   `coreCFGToGotoCmdStep` step on `.cmd c` reduces to
   `Imperative.Cmd.toGotoInstructions trans.T fname c trans`
   (proven by `coreCFGToGotoCmdStep_cmd`). Lets us reuse A2's
   `innerCmdLoop_layout_block_body`.
2. **Per-block + outer-fold lifts**: `coreCFGToGotoBlockStep_layout_block_body`
   and `blocksFoldlM_layout_block_body` extend the layout extraction
   from individual cmds-fold to the full forward pass.
3. **Patcher bridge**: `patchGotoTargets_preserves_full_except_target`.
   The patcher only writes `target`. Other fields (`type`, `guard`,
   `code`, `locationNum`) are preserved at every index. Since
   `CmdEmittedAt` checks only `type`, `code`, `guard`, the lift from
   `st_final.trans.instructions` to `ans.instructions` (the patched
   output) goes through verbatim by case-splitting on the
   `CmdEmittedAt` constructor and rebuilding with the patched
   instruction.

## Commit summary (this round)

1. `docs(workers): A5a report stub`
2. `feat(goto-correct): A5a - close entry_in_map_of_translator hypothesis`
3. `feat(goto-correct): A5a - close labelMap_inj_of_translator hypothesis`
4. `feat(goto-correct): A5a - cmdsFoldlM_eq_innerCmdLoop + per-block + outer-fold layout_block_body lifts`
5. `feat(goto-correct): A5a - close layout_block_body_of_translator hypothesis (all three closures landed)`

Net file growth: 4549 → ~5325 LoC (+~780 LoC).

## Integration notes for the supervisor

The three closure theorems take the **same argument shapes** as A4's
top-level theorem `coreCFGToGotoTransform_wellFormed_nonempty`. The
supervisor can compose them with A5b's `layout_cond_goto`
+ `layout_cond_goto_guards` closures into a tighter top-level theorem
that no longer takes A4's four hypothesis parameters.

Specifically, A4's signature includes:
```
(h_layout_cond_goto : ...)        — closed by A5b
(h_layout_cond_goto_guards : ...) — closed by A5b
(h_layout_block_body : ...)       — closed by A5a (this report)
(h_labelMap_inj : ...)            — closed by A5a (this report)
(h_entry_in_map : ...)            — closed by A5a (this report)
```

After integration, the new top-level theorem only requires:
- `(cfg : Core.DetCFG)`, `Env`, `functionName`, `trans₀`
- `h_init_size`, `h_init_loc`
- `h_distinct : BlockLabelsDistinct cfg.blocks`
- `h_admitted_blocks`
- `h_loopContracts_empty_post`
- `h_entry_first : cfg.blocks.head?.map Prod.fst = some cfg.entry` (new — needed by A5a's entry_in_map closure)
- `(ans, h_run)` and `(δ, δ_goto, δ_goto_bool)`
- For layout_block_body: `(h_expr_corr, h_tx_eq)` — same as the
  loop-induction in `innerCmdLoop_layout_block_body`.

The `h_entry_first` hypothesis is needed because the translator
ACCEPTS empty `cfg.blocks` as a no-op (returning `pure ()` for the
entry-check), in which case `entry_in_map` is vacuously false. The
hypothesis encodes that the caller has actually provided a non-empty
CFG with the entry block first — which the translator already checks
(throwing if violated), but the proof needs it as input.

## Working notes

- Started 2026-05-21.
- Worktree:
  `/Users/htd/Documents/Strata/.claude/worktrees/agent-acc1841b30fcc7e19`
- Branch: `worktree-agent-acc1841b30fcc7e19`, started from
  `htd/unstructured-to-goto`.
- 5 commits over the round (1 stub + 4 feat).
