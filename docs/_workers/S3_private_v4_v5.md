# S3 — Mark `_v4` / `_v5` private

## Summary

Marked `coreCFGToGotoTransform_forward_simulation_concrete_v4` and
`coreCFGToGotoTransform_forward_simulation_concrete_v5` as `private` in
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` so that only `_v6`
and `_v7` are part of the public API of the module. The internal call
chain `_v6 → _v5 → _v4` and `_v7 → _v6` is preserved: same-file `private`
references resolve normally under Lean 4's module system, including the
file's `module` / `public import` / `public section` setup.

## Keyword used

Plain `private theorem`. No alternate keyword was needed — the
`module` / `public section` machinery in this file does not interact
with `private` in a way that breaks same-file uses, and the existing
proof bodies of `_v6` (which calls `_v5` by name on line 1150) and `_v7`
(which calls `_v6` by name on line 1362) elaborate without any
qualification or other adjustment.

## LoC saved

- `StrataTest/Backends/CBMC/GOTO/CoreCFGToGOTOConcreteAxioms.lean`:
  removed 6 lines (the two `#print axioms` blocks for `_v4` and `_v5`,
  including blank-line spacing). Doc comment was also tweaked to note
  that `_v4`/`_v5` are private helpers.
- `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean`: net 0 LoC
  (two `private` keywords added in place).

## Axiom verification

After the change, `lake build StrataTest.Backends.CBMC.GOTO.CoreCFGToGOTOConcreteAxioms`
reports exactly:

```
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v6'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v7'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, no extra axioms — the public theorems still rest on the
standard Lean classical axioms only, unchanged from before this round.

## Downstream consumers

`grep` over the workspace for `coreCFGToGotoTransform_forward_simulation_concrete_v4`
and `_v5` outside `CoreCFGToGOTOConcrete.lean` and the axioms-test
returned no matches, so no consumer is broken by hiding them.
