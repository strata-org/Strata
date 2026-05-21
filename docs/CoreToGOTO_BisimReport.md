# Phase 0 Bisim Report — `StepGoto` ↔ `StepInstr`

This document is the Phase-0 outcome report for the
`docs/superpowers/specs/2026-05-20-goto-semantics-expansion-design.md`
plan. It records what fell out of the
`Strata/Backends/CBMC/GOTO/Bisim.lean` bridge work.

## What landed

| Constructor | Bridged? | Hypotheses needed |
|---|---|---|
| `step_location` | ✓ | none beyond `instrAt` lookup |
| `step_skip` | ✓ | same |
| `step_assert_pass` | ✓ | `EvalBoolCorr` |
| `step_assume_pass` | ✓ | `EvalBoolCorr` |
| `step_goto_fallthrough` | ✓ | `EvalBoolCorr` |
| `step_assert_fail` | ✓ | `EvalBoolCorr`; produces a separate `AssertFails` witness |
| `step_goto_taken` | ✓ | `EvalBoolCorr` + `findLocIdx`-resolution hypothesis |
| `step_dead` | ✓ | `Function.Injective nameMap` + `getSymbolName` lookup |
| `step_assign` | ✓ | `EvalValueCorr` + `Function.Injective nameMap` + lhs/rhs lookups + `toValue` correspondence on the assigned value |
| `step_decl` | ✓ | `Function.Injective nameMap` + `getSymbolName` lookup + `toValue v = some .vEmpty` hypothesis |
| `step_assign_nondet` | ✓ | `Function.Injective nameMap` + lhs/rhs lookups + `rhs.id = .side_effect .Nondet` syntactic check + `toValue` correspondence |
| `step_end_function` | ✓ (closure-level) | bridges to `ExecProg.end_function` rather than to `StepInstr` (their `END_FUNCTION` is observed by the multi-step relation, not the single-step) |

All twelve `StepGoto` constructors now have a bridge — eleven to
`StepInstr` and one (`step_end_function`) at the closure level.
Phase 0's per-instruction goal is functionally complete; the
remaining work is assembling the trace-level
`StepGotoStar → ExecProg` lift, which lives in
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrectStore.lean` and is
the load-bearing chunk of Phase 3.

## What it tells us

### `Function.Injective nameMap` is required

Both `step_dead` and `step_assign` need
`Function.Injective nameMap` for `StoreCorr` preservation. Without
it, two distinct source identifiers `x ≠ y` could map to the same
GOTO-side string `nameMap x = nameMap y`, in which case updating
`σ_imp` at `x` *and* `σ_goto` at `nameMap x` would leave `σ_goto`
disagreeing with `σ_imp` at `y`.

Whether this hypothesis is *provable* for the actual translator
output remains an open question. The spec's Risk #1 calls out that
the realistic
`<proc>::<scope>::<name>` renaming may not be globally injective in
the presence of shadowed locals; if so, Phase 3 needs a
non-injective fallback (e.g., `nameMap` parameterized by scope).

### `EvalCorr` cleaves into `EvalBoolCorr` + `EvalValueCorr`

The spec's `EvalCorr` is a single predicate. The bridges naturally
want two: `EvalBoolCorr` (boolean evaluators agree) for ASSERT /
ASSUME / GOTO, and `EvalValueCorr` (value evaluators agree, modulo
`vc.toValue`) for ASSIGN. Splitting them keeps each bridge's
hypothesis surface minimal — store-unchanged constructors only
need the boolean half, and the value half only matters for ASSIGN.

### Failure-flag bridge is one-sided

`step_assert_fail` flips this branch's failed flag inside the
configuration; tautschnig's `StepInstr.assert_fail` advances PC
normally and surfaces failure via the separate `AssertFails`
predicate. The bridge produces *both* a `StepInstr` step *and* an
`AssertFails` witness. This is consistent with the spec's
`failureFlag_corresponds` plan and confirms it as a single
single-step bridge (not a "trail of consequences").

### `findLocIdx`-resolution is purely external

This branch's `step_goto_taken` uses pre-resolved `instr.target =
some pc_lt`; tautschnig's `StepInstr.goto_taken` walks
`findLocIdx`. The bridge takes
`findLocIdx pgm.instructions loc = some pc_lt`
plus `instrTarget pgm pc = some (some loc)`
as external hypotheses. There is no need to push this into
`WellFormedTranslation` for the bridge itself; downstream callers
that *use* the bridge will likely want to discharge it via a
`WellFormedTranslation` field.

### `step_decl` and `step_assign_nondet` bridges land via external hypotheses

Both constructors bridge to their `StepInstr` analogues without
reshaping `StepGoto`, by exposing the divergence as a hypothesis on
the bridge theorem:

* `step_decl`: tautschnig sets the freshly-declared symbol to
  `vEmpty` regardless of `InitState`'s witness. The bridge takes
  `vc.toValue v = some .vEmpty` as an external hypothesis; under
  the current `valueCorrCore` instance this fires only at call sites
  that supply a sentinel-aware instance.

* `step_assign_nondet`: tautschnig's `assign_nondet` requires
  `rhs.id = .side_effect .Nondet` syntactically; ours does not. The
  bridge takes the syntactic check as an external hypothesis. Future
  work could tighten this branch's constructor to bake the check in,
  but the bridge does not require it.

### `step_end_function` is intrinsically closure-level

This branch's `step_end_function` produces `.terminal σ failed`;
tautschnig has no `terminal` configuration. Their `END_FUNCTION` is
*observed* by the `ExecProg.end_function` constructor, which closes
out the multi-step relation. The bridge therefore lives at the
*closure* level: `stepGoto_end_function_to_execProg` produces a
one-step `ExecProg` derivation rather than a `StepInstr` step.
A future trace-level lift `StepGotoStar … (.terminal σ' b)` ↔
`ExecProg … pc σ_g σ_g' none` will compose this with the
per-`StepInstr` bridges to give the full
`coreCFGToGoto_forward_simulation_storeCorr` theorem.

## Necessary reshape of Phases 1-5

Based on the bridge work above:

- **Phase 1:** no reshape. The cheap additive constructors
  (`step_skip`, `step_dead`) landed; `step_function_call` is
  deferred until a downstream proof needs it. `StepGotoRange`,
  shape-determinism, and the per-instruction progress lemmas all
  landed cleanly.
- **Phase 2:** delivered via the ported tautschnig files (Phase 0
  prereq) plus `ValueCorrCore.lean` for the `Core.Expression`
  instance. The `Value` inductive lives inside
  `SemanticsTautschnig.lean` rather than a standalone `Value.lean`;
  since Phase 5 is the gated convergence step that would fold
  everything anyway, hoisting is unnecessary.
- **Phase 3:** **closed.** `coreCFGToGoto_forward_simulation_storeCorr`
  in `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrectStore.lean`
  composes the existing closed forward simulation with the new
  `StepGotoStar_to_ExecProg` trace lift to produce a
  `StoreCorr`-shaped existential conclusion. Axiom set:
  `[propext, Classical.choice, Quot.sound]` (identical to the
  original `coreCFGToGoto_forward_simulation`; no new
  project-internal axioms).
- **Phase 4:** unchanged status — optional structured-pipeline
  expansion.
- **Phase 5:** unchanged status — gated terminal.

## Build state

All commits in this branch since Phase 0 work began build green.
`#print axioms CProverGOTO.coreCFGToGoto_forward_simulation` remains
exactly `[propext, Classical.choice, Quot.sound]`. No new
project-internal axioms; no `sorry` introduced.
