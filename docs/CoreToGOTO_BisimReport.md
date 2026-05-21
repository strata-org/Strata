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
| `step_decl` | not bridged | needs a relaxed `StoreCorr` permitting `vEmpty` for any `InitState` value, *or* a fold with the subsequent `step_assign_nondet` that the translator emits |
| `step_assign_nondet` | not bridged | needs the syntactic `rhs.id = .side_effect .Nondet` constraint that this branch's constructor lacks |
| `step_end_function` | not single-step bridgeable | their `END_FUNCTION` lives on `ExecProg.end_function`, not `StepInstr`; bridge is at the closure level |

Nine of the twelve `StepGoto` constructors bridge to a single
`StepInstr` step. The remaining three are documented in `Bisim.lean`'s
header as known structural divergences that need either constructor
refactors or closure-level reasoning.

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

### `step_decl` and `step_assign_nondet` need real reshape

* `step_decl`: tautschnig sets the freshly-declared symbol to
  `vEmpty` regardless of `InitState`'s witness value. Two clean
  paths forward: (1) reshape `StoreCorr` to be permissive at
  freshly-declared keys, or (2) fold `step_decl` with the
  immediately-following `step_assign_nondet` that the translator
  emits, treating the pair as a single bisim step.

* `step_assign_nondet`: tautschnig's `assign_nondet` requires the
  syntactic check `rhs.id = .side_effect .Nondet`; ours does not.
  Tightening `step_assign_nondet`'s constructor to require that
  check would allow the bridge to fire directly. Alternatively, the
  bridge could supply the syntactic constraint as a hypothesis.

### `step_end_function` is intrinsically not single-step

This branch's `step_end_function` produces `.terminal σ failed`;
tautschnig has no `terminal` configuration. Their `END_FUNCTION` is
*observed* by the `ExecProg.end_function` constructor, which closes
out the multi-step relation. The bridge therefore lives at the
*closure* level: a `StepGotoStar … (.terminal σ' b)` corresponds to
an `ExecProg … pc σ_g σ_g' retVal` with `retVal = none` (we don't
model returns) and the failed flag bridged separately.

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
- **Phase 3:** the load-bearing question (whether
  `coreCFGToGoto_forward_simulation_storeCorr` exists and has the
  expected axioms) is not yet answered. The bridges above are the
  *building blocks* needed to lift the existing
  `coreCFGToGoto_forward_simulation` into a `StoreCorr`-shaped
  conclusion; assembling them is the next chunk of work and is
  estimated at ~200-400 LOC. The `step_decl` reshape (above) is
  likely a prerequisite, since the existing simulation does
  introduce `step_decl`.
- **Phase 4:** unchanged status — optional structured-pipeline
  expansion.
- **Phase 5:** unchanged status — gated terminal.

## Build state

All commits in this branch since Phase 0 work began build green.
`#print axioms CProverGOTO.coreCFGToGoto_forward_simulation` remains
exactly `[propext, Classical.choice, Quot.sound]`. No new
project-internal axioms; no `sorry` introduced.
