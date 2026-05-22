# Worker R7b — `h_no_dead` from translator induction

**Goal.** Discharge R6a's `h_no_dead` hypothesis: `coreCFGToGotoTransform`
never emits DEAD instructions. Provided as `no_dead_of_translator` (or
similar) in a new file
`Strata/Backends/CBMC/GOTO/NoDead.lean`.

## Outcome

(filled in after work)

## Strategy

Define a "no-DEAD" predicate
`HasNoDead trans := ∀ pc instr, trans.instructions[pc]? = some instr → instr.type ≠ .DEAD`,
then prove preservation through:

1. `coreCFGToGotoCmdStep` (per-cmd: `Cmd.toGotoInstructions` only emits
   DECL / ASSIGN / ASSERT / ASSUME from the per-Cmd helper; `.call`
   emits FUNCTION_CALL).
2. `cmdsFoldlM coreCFGToGotoCmdStep` (lift via induction on cmds).
3. `coreCFGToGotoBlockStep` (LOCATION via emitLabel + cmds + transfer
   GOTOs/END_FUNCTION).
4. `cfg.blocks.foldlM coreCFGToGotoBlockStep` (lift via induction on
   blocks).
5. `coreCFGToGotoPatchStep` (preserves `.type` per A4's
   `patchGotoTargets_preserves_type`).
6. `patchesFoldlM coreCFGToGotoPatchStep` (lift via induction on
   patches; we have the `_no_contracts` version of the patcher already).
7. `patchGotoTargets` final wrap (per A4).

## Files added / changed

* **Added** `Strata/Backends/CBMC/GOTO/NoDead.lean` — preservation
  lemmas + final theorem.
* **Updated** `Strata.lean` — register the new module so `lake lint`
  passes.

## Status checklist

- [x] Report stub.
- [ ] Read all required context.
- [ ] Per-instruction-emit lemmas (push / append).
- [ ] Cmd-step preservation.
- [ ] Cmds-fold preservation.
- [ ] Block-step preservation (label + cmds + transfer).
- [ ] Blocks-fold preservation.
- [ ] Patch-step preservation.
- [ ] Patches-fold preservation.
- [ ] Final composition: `no_dead_of_translator`.
- [ ] `lake build` green.
