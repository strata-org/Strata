# Worker R9 — PC inversion theorems

**Round:** 9
**Branch base:** `htd/unstructured-to-goto` (HEAD `938639db1`).
**Worktree:** *working in main repo* (already on the right branch — the
worktree path was already used by `/Users/htd/Documents/Strata-goto`).

## Goal

Discharge R8b's three PC-inversion auxiliary hypotheses
(`DeclPcInversion`, `AssignPcInversion`, `AssignNondetPcInversion`) by
translator induction, in a new file
`Strata/Backends/CBMC/GOTO/PcInversion.lean`. Then write a `_v6` in
`CoreCFGToGOTOConcrete.lean` that drops the three `h_*_pc_inv`
arguments of `_v5`.

## Status: **IN PROGRESS** (this stub will be updated)

Plan:
1. **PcInversion.lean** — close `DeclPcInversion` and `AssignPcInversion`
   from the translator-blocks-fold + `layout_block_body_of_translator`
   (R5's existing infrastructure).
2. **`assn_nondet_pc_inv` is provably false in general.** Per R8b's
   discovery, every translator output emitting `init_det` or `set_det`
   produces non-nondet ASSIGNs. We therefore restrict to either
   (a) a strict source-CFG-shape hypothesis, or (b) the "no `init_det`
   or `set_det`" fragment. The strict variant matches R8b's existing
   `AssignNondetPcInversion`; we close it under that strict
   hypothesis only.
3. **`_v6`** — internalise the closures.

## Strategy (DECL / ASSIGN inversions)

The key observation: R5's `layout_block_body_of_translator` already
gives, for any `(l, blk) ∈ cfg.blocks` and offset `k`, a
`CmdEmittedAt` witness for the cmd at PC `pc + 1 +
cmdsPrefixInstrCount blk.cmds k` over `ans.instructions`.

What we still need is the **reverse-direction** inversion: from a PC
`pc'` carrying a DECL/ASSIGN instruction in `ans.instructions`,
recover a block + offset whose layout puts a DECL/ASSIGN at exactly
`pc'`. This is the missing ingredient.

The natural way to do this is:

1. Define a per-translator-state predicate `BodyPcCovered`: for every
   PC in `trans.instructions` whose type is DECL or ASSIGN, there
   exists a `(block, offset)` pair witnessing an emit.
2. Prove `BodyPcCovered` is preserved through `Cmd.toGotoInstructions`
   (each `init_*` / `set_*` push extends with a known DECL/ASSIGN PC).
3. Lift through `coreCFGToGotoCmdStep`, `cmdsFoldlM`,
   `coreCFGToGotoBlockStep`, `blocksFoldlM`. For non-body emits
   (LOCATION, GOTO, END_FUNCTION), the predicate is preserved trivially
   because they don't have type DECL or ASSIGN.
4. Patcher only changes `target` — preserves DECL/ASSIGN type and
   thus preserves the predicate (the witness PCs remain with same
   type).

But step 1's predicate needs to mention "block and offset" — not yet
in scope of the translator's state alone.

**Simpler approach** (tried first): track the inversion via a more
stringent predicate that records *which CFG blocks have been emitted
so far* alongside the position offsets. This is closer to a full
"translator simulation" — large.

**Pragmatic approach** (chosen): use the **shadow record** internal
to the strengthened theorem (`CoreCFGToGotoTransformShadow`). The
shadow's `layout_block_body` field already gives us the forward
direction; we then prove a complementary "every-DECL/ASSIGN-PC has a
`CmdEmittedAt`" lemma by translator-fold induction. This is a
direct preservation argument: each emit step extends the predicate,
and patcher preserves it (only `target` is modified).

## Tier outcome (TBD)

This stub will be updated as work proceeds.
