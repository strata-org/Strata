# L3 — Preservation Combinator Application

**Worker:** L3 (write).
**Branch base:** `htd/unstructured-to-goto` (commit `3c23ec624`).
**Scope:** apply L2's design plan
([`docs/_workers/L2_preservation_combinator_design.md`](L2_preservation_combinator_design.md)):
build a `BlocksFoldClosed` typeclass that abstracts the per-translator-step
preservation skeleton, then port `NoDead.lean`, `GotoTargetProvenance.lean`
steps 1-9, and the `CoreCFGToGotoTransformWF` size_eq + locationNum chains
to use it.

## Plan

1. Create `Strata/Backends/CBMC/GOTO/BlocksFoldClosed.lean` exporting:
   * `class BlocksFoldClosed (P : Array Instruction → Prop)` with the
     9 step closures (toGotoInstructions … blocksFoldlM).
   * `ofPushClosure` helper deriving the leaf closures (emitLabel,
     emitCondGoto, emitUncondGoto, endFunction) from a single
     "P preserved by push of an acceptable instruction" assumption.
   * Two top-level theorems exposing `P st_final.trans.instructions`
     given `P trans₀.instructions` and a successful blocks-fold.

2. **Port `NoDead.lean`** — replace the 9 per-step preservation
   lemmas with one `BlocksFoldClosed (HasNoDead' ·)` instance.
   Keep `no_dead_program_of_translator` signature unchanged.

3. **Port `GotoTargetProvenance.lean` steps 1-9** — the patcher
   reverse-direction lemma stays untouched.

4. **Extract the size_eq + locationNum chain** from
   `CoreCFGToGotoTransformWF.lean`. Note: these steps take an
   additional `h_admitted` hypothesis on the cmd-step / cmds-fold
   layer; will assess if the combinator can absorb it via a
   per-step admission predicate.

5. **Skip** PcInversion (Class E, intractable) and WfLabelMapAgree
   (Class B, would need different combinator).

## Risk gate

If the NoDead port nets less than ~250 LoC of saving (vs.
the projected 360), I'll declare Tier 2 partial and stop after NoDead.
Same for size_eq if `h_admitted` plumbing eats the saving.

## Tier verdict

To be filled in at completion.
