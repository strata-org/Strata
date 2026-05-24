# S1 — Drop unused `_h_inj` parameters from `InstructionLookups.lean`

## Summary

Per the audit at `docs/CoreToGOTO_ShrinkAudit.md`, three theorems in
`Strata/Backends/CBMC/GOTO/InstructionLookups.lean` carried an
`(_h_inj : Function.Injective nameMap)` parameter that was never
referenced inside the body — the underscore prefix already silenced the
linter, but the parameter still threaded through call sites and was
strict baggage. This commit drops the parameter from the three theorem
signatures and removes the corresponding `h_inj` argument from the
three call sites in `TranslatorBridgeHypsDischarge.lean`.

## Verification

* The three `_h_inj` binders were the only `h_inj`-named occurrences in
  `InstructionLookups.lean` before the change (`grep -n h_inj` returned
  exactly the three binder lines), confirming they are unused inside
  the theorem bodies.
* `h_inj` is still bound and used elsewhere in
  `TranslatorBridgeHypsDischarge.lean` (`nameMap_inj := h_inj` and the
  passthrough into `wellFormedTranslation_to_translatorBridgeHyps`), so
  only the three argument positions were removed; the outer binders on
  `wellFormedTranslation_to_translatorBridgeHypsFromConcreteShapes` /
  `wellFormedTranslation_to_translatorBridgeHypsFromConcrete` remain.

## Files changed

* `Strata/Backends/CBMC/GOTO/InstructionLookups.lean`
  - line 180: dropped `(_h_inj : Function.Injective nameMap)` from
    `decl_lookup_of_provenance_and_pinned`.
  - line 232: dropped `(_h_inj : Function.Injective nameMap)` from
    `assign_lookup_of_provenance_and_pinned`.
  - line 296: dropped `(_h_inj : Function.Injective nameMap)` from
    `assign_nondet_lookup_of_provenance_and_pinned`.
* `Strata/Backends/CBMC/GOTO/TranslatorBridgeHypsDischarge.lean`
  - lines 362, 365, 370: removed the `h_inj` argument from the three
    `InstructionLookups.*_of_provenance_and_pinned` call sites.

`git diff --stat`: 3 insertions, 6 deletions across 2 files (net
−3 LoC). The audit's "~15 LoC removable" estimate was conservative;
the actual savings are three signature lines plus three inline arg
positions. The audit's underlying claim — that the parameters are
strict deadweight — held up.

## Build / axiom verification

* `lake build Strata.Backends.CBMC.GOTO.TranslatorBridgeHypsDischarge`:
  green.
* `lake build StrataTest.Backends.CBMC.GOTO.CoreCFGToGOTOConcreteAxioms`:
  green; `_v4`, `_v5`, `_v6`, `_v7` all print
  `[propext, Classical.choice, Quot.sound]` — unchanged.
* `lake build` (full): green, 585 jobs.
* No `sorry` introduced.
