# R8a — `everyGotoTargetIsLabelMapEntry_of_translator`

## Goal

Close R7a's `EveryGotoTargetIsLabelMapEntry` auxiliary by translator
induction: every emitted GOTO instruction's `target` resolves to a
labelMap entry for some block of `cfg.blocks`.

## Outcome

**Tier 2 (Good).** Closed for the translator's own labelMap
(`hashMapToLabelMap st_final.labelMap`) by full structural induction;
the `wf.labelMap`-form takes a thin caller-supplied bridge.

The structural side — the bulk of the work — is fully discharged:
- preservation through cmd-step,
- preservation through block-step (incl. `.condGoto` pendingPatches
  push),
- preservation through `cmdsFoldlM` and `blocksFoldlM`,
- preservation through `coreCFGToGotoPatchStep` (no contracts) and
  `patchesFoldlM` (no contracts),
- patcher reverse-target lemma (`patchGotoTargets_target_some_in_patches`),
- patches-fold reverse direction (`patchesFoldlM_no_contracts_resolved_reverse`),
- labelMap-keys-are-block-labels lemma
  (`blocksFoldlM_labelMap_keys_in_blocks`),
- final composition: `everyGotoTargetIsLabelMapEntry_of_translator_translatorMap`.

The `wf.labelMap` form takes one extra hypothesis
(`h_labelMap_agree`) bridging `wf.labelMap` and the translator's
hashmap-keyed labelMap. This bridge is genuinely outside
`WellFormedTranslation`'s current vocabulary (forward-only CFG →
program direction; same R7a observation).

## Files added

* `Strata/Backends/CBMC/GOTO/GotoTargetProvenance.lean`
  (1116 LoC) — the proof.
* `StrataTest/Backends/CBMC/GOTO/GotoTargetProvenanceAxioms.lean`
  (18 LoC) — axiom smoke test.

## Status checklist

- [x] Branch base: `htd/unstructured-to-goto` (HEAD `e2c552ab6`).
- [x] Report stub.
- [x] State-level predicate `NoGotoHasTarget` defined.
- [x] Push/append preservation primitives.
- [x] `Cmd.toGotoInstructions` preservation
      (`toGotoInstructions_preserves_no_goto_target`).
- [x] `coreCFGToGotoCmdStep` preservation
      (`coreCFGToGotoCmdStep_preserves_no_goto_target`).
- [x] `cmdsFoldlM` preservation
      (`cmdsFoldlM_preserves_no_goto_target`).
- [x] Per-emit-helper preservation
      (`emitLabel_*`, `emitCondGoto_*`, `emitUncondGoto_*`,
      `endFunction_emit_*`).
- [x] `coreCFGToGotoBlockStep` preservation
      (`coreCFGToGotoBlockStep_preserves_no_goto_target`).
- [x] `blocksFoldlM` preservation
      (`blocksFoldlM_preserves_no_goto_target`).
- [x] `coreCFGToGotoPatchStep` (no contracts) preservation
      (`coreCFGToGotoPatchStep_preserves_no_goto_target_no_contracts`).
- [x] `patchesFoldlM` (no contracts) preservation
      (`patchesFoldlM_preserves_no_goto_target_no_contracts`).
- [x] Patcher reverse-target lemma
      (`patchGotoTargets_target_some_in_patches`).
- [x] Patches-fold reverse direction
      (`patchesFoldlM_no_contracts_resolved_reverse`,
      `patchesFoldlM_no_contracts_resolved_reverse_array`).
- [x] labelMap-keys-are-block-labels
      (`blocksFoldlM_labelMap_keys_in_blocks`).
- [x] Top-level (translator-map form):
      `everyGotoTargetIsLabelMapEntry_of_translator_translatorMap`.
- [x] Top-level (wf-form, with caller-supplied bridge):
      `everyGotoTargetIsLabelMapEntry_of_translator`.
- [x] `lake build` green (585/585 jobs).
- [x] Axiom check: `[propext, Classical.choice, Quot.sound]`
      (matches the project baseline).

## Predicates

```lean
def NoGotoHasTarget (trans : Imperative.GotoTransform Core.Expression.TyEnv) : Prop :=
  ∀ {pc : Nat} {instr : Instruction},
    trans.instructions[pc]? = some instr → instr.type = .GOTO →
    instr.target = none
```

The translator emits GOTOs with `target := none`; the `target` is
filled in by the patcher only after the blocks-fold.

## Top-level theorems

```lean
theorem everyGotoTargetIsLabelMapEntry_of_translator_translatorMap
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_no_goto_target : NoGotoHasTarget trans₀)
    (h_loopContracts_empty_post : ...)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    (st_final : Strata.CoreCFGTransLoopState)
    (h_blocks_run :
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀)
      = Except.ok st_final) :
    GotoTargetInRange.EveryGotoTargetIsLabelMapEntry cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      (hashMapToLabelMap st_final.labelMap)
```

```lean
theorem everyGotoTargetIsLabelMapEntry_of_translator
    ... -- all the above
    (δ ...) (δ_goto ...) (δ_goto_bool ...)
    (wf : WellFormedTranslation cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions } δ δ_goto δ_goto_bool)
    -- caller-supplied bridge
    (h_labelMap_agree :
      ∀ l blk target, (l, blk) ∈ cfg.blocks →
        st_final.labelMap[l]? = some target →
        wf.labelMap l = some target) :
    GotoTargetInRange.EveryGotoTargetIsLabelMapEntry cfg ... wf.labelMap
```

## Proof strategy

The translator decomposes (via `coreCFGToGotoTransform_decompose`) as:

1. **Blocks-fold** emits LOCATION/DECL/ASSIGN/etc., plus GOTO with
   `target = none` for `.condGoto` transfers, and END_FUNCTION for
   `.finish` transfers. Throughout, no GOTO has `target = some _`.
2. **Patches-fold** under empty `loopContracts` is a no-op on `trans`
   (per A4's `patchesFoldlM_no_contracts_trans_eq`); it only builds
   `resolvedPatches`. Each `(idx, label) ∈ pendingPatches` becomes
   `(idx, targetLoc) ∈ resolved` where `targetLoc =
   labelMap[label]?`.
3. **`patchGotoTargets resolved`** writes each `(idx, target) ∈
   resolved` into `instructions[idx].target := some target`. Other
   indices are unchanged.

For a GOTO at `pc` in `ans` with `target = some t`:
- Pre-patcher state has `instr_pre.target = none` (by NoGotoHasTarget).
- By the patcher reverse-target lemma, `(pc, t) ∈ resolved`.
- By the patches-fold reverse direction, ∃ `label`, `(pc, label) ∈
  pendingPatches` and `st_final.labelMap[label]? = some t`.
- By labelMap-keys-are-block-labels, `label ∈ cfg.blocks.map Prod.fst`.
- Pick the corresponding `(label, blk) ∈ cfg.blocks` and conclude.

## Why the `wf.labelMap` bridge is caller-supplied

`WellFormedTranslation` is *forward-only* (CFG → program): for each
`(l, blk) ∈ cfg.blocks`, what GOTOs/LOCATIONs are emitted (per
`layout_*` fields). It doesn't expose the *backward* direction
(program → CFG): for an arbitrary GOTO target value `t`, recover the
`(l, blk)` that emitted it.

For an arbitrary `wf`, the bridge `wf.labelMap l = some target` (given
`hashMapToLabelMap st_final.labelMap l = some target`) requires
**uniqueness of LOCATION instructions per block label** in `pgm`,
which `WellFormedTranslation` doesn't currently enforce. (R7a's
report flagged this as the Tier 1 obstacle.)

For the v4 use case, the `wf` is constructed via
`coreCFGToGotoTransform_wellFormed_strengthened`, whose internal
`wellFormedTranslation_of_shadow` builds `wf.labelMap` directly from
`hashMapToLabelMap st_final.labelMap`. So the bridge is trivially
provable in that context.

## Build verification

```
$ lake build Strata.Backends.CBMC.GOTO.GotoTargetProvenance
✔ Built Strata.Backends.CBMC.GOTO.GotoTargetProvenance (1.9s)
Build completed successfully (211 jobs).

$ lake build
Build completed successfully (585 jobs).

$ lake env lean StrataTest/Backends/CBMC/GOTO/GotoTargetProvenanceAxioms.lean
'CProverGOTO.GotoTargetProvenance.everyGotoTargetIsLabelMapEntry_of_translator_translatorMap'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'CProverGOTO.GotoTargetProvenance.everyGotoTargetIsLabelMapEntry_of_translator'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

## What's left for v5 supervisor composition

The supervisor's v5 (which would discharge R7a's aux internally)
needs:
1. The `h_init_no_goto_target` hypothesis (trivial for `trans₀`
   with empty `instructions = #[]`).
2. The `st_final` decomposition (already done as part of v4's
   structure).
3. The `h_labelMap_agree` bridge:
   - For the v4-style `obtain ⟨wf⟩ := h_wf_nonempty`, the bridge is
     not directly definitional (Nonempty.choice is opaque).
   - Cleanest path: replace the v4 use of `coreCFGToGotoTransform_wellFormed_strengthened`
     with a direct call to `wellFormedTranslation_of_shadow` so the
     constructed `wf` has `wf.labelMap = hashMapToLabelMap st_final.labelMap`
     definitionally.
   - Alternative: extend `WellFormedTranslation` with a labelMap-
     uniqueness field (parallel to A4's existing `layout_*` fields,
     ~50-100 LoC).

## Suggested follow-ups

1. **Wire into v5.** Use `everyGotoTargetIsLabelMapEntry_of_translator`
   in a v5 of `coreCFGToGotoTransform_forward_simulation_concrete`
   to discharge `h_aux_goto_target` internally — replacing v4's
   external hypothesis. Reduces the v5 caller's hypothesis surface
   by 1.
2. **Consider extending `WellFormedTranslation`** with a labelMap-
   uniqueness field. Then the `h_labelMap_agree` bridge becomes
   automatic for any `wf : WellFormedTranslation`. Removes the only
   gap.
3. **Generalize past no-loop-contracts.** The patcher mutates only
   `target` (not `type` or `guard` non-loop-contract metadata) under
   the `_no_contracts` hypothesis. With contracts, the patcher
   additionally writes `guard.setNamedField "#spec_loop_invariant"
   ...` for backward-edge GOTOs at indices in `pendingPatches`.
   `target` is still set the same way, so the predicate proof goes
   through; only the patches-fold preservation lemma needs to drop
   the `_no_contracts` qualifier.

## Commit log (in order)

1. `docs(R8a): report stub for everyGotoTargetIsLabelMapEntry_of_translator`
2. `feat(R8a): NoGotoHasTarget predicate + preservation through blocks-fold + patches-fold`
3. `feat(R8a): patcher reverse-target lemma — set targets came from patches list`
4. `feat(R8a): patches-fold reverse direction — resolved targets came from labelMap lookups`
5. `feat(R8a): top-level theorem — every emitted GOTO target maps to a block label`
6. `feat(R8a): add wf.labelMap-form (with caller-supplied labelMap-bridge hypothesis)`
7. `feat(R8a): axiom smoke test for the two top-level theorems`
8. `docs(R8a): final report` (this commit)
