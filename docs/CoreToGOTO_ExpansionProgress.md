# GOTO Semantics Expansion — Progress Report

This report summarises the work landed against
`docs/superpowers/specs/2026-05-20-goto-semantics-expansion-design.md`
on the `htd/unstructured-to-goto` branch, between commit `6014c12ca`
(baseline: `coreCFGToGoto_forward_simulation` already closed) and
commit `c0785b87a`.

Companion documents:

- `docs/CoreToGOTO_BisimReport.md` — Phase 0 outcome report (per-
  constructor bridge status, learnings, reshape recommendations).
- `docs/CoreToGOTO_SemanticsComparison.md` — diagnostic comparison of
  this branch and `tautschnig/goto-semantics` (predates the
  expansion work; left as a snapshot of the *baseline* differences).

## Headline result

**Phases 0, 1, 2, and 3 — the load-bearing path — are closed.**
Phase 4 has a partial implementation (cheap `sim_X` primitives);
its compositional/state-changing primitives are deferred per the
spec's own gating ("only fires if a structured-pipeline consumer
appears"). Phase 5 is unstarted, again per the spec's own gating
("default: no, unless a concrete soundness driver appears").

The new end-to-end theorem
`CProverGOTO.coreCFGToGoto_forward_simulation_storeCorr` closes
parallel to the existing `coreCFGToGoto_forward_simulation`, with
identical axiom set
`[propext, Classical.choice, Quot.sound]` — no new project-internal
axioms. The existing equational theorem is unchanged; downstream
consumers can now choose between the equational and the
`StoreCorr`-existential conclusion.

## Per-phase status

### Phase 0 — Bisimulation bridge

**Status:** closed.

Tautschnig's `Semantics.lean` / `SemanticsEval.lean` /
`SemanticsProps.lean` are ported into the
`CProverGOTO.SemanticsTautschnig` namespace. All twelve `StepGoto`
constructors have a per-step bridge:

- Eleven bridge to `StepInstr`: `step_location`, `step_skip`,
  `step_assert_pass`, `step_assert_fail` (produces an `AssertFails`
  side-witness), `step_assume_pass`, `step_goto_fallthrough`,
  `step_goto_taken` (takes a `findLocIdx`-resolution hypothesis),
  `step_dead` (via `Function.Injective nameMap`), `step_decl` (via
  `toValue v = some .vEmpty`), `step_assign` (via `EvalValueCorr` +
  injectivity + value correspondence), `step_assign_nondet` (via
  the syntactic `.side_effect .Nondet` check + injectivity).
- One bridges at the closure level: `step_end_function` →
  `ExecProg.end_function` (since tautschnig has no `.terminal`
  configuration).

A `valueCorrCore : ValueCorr Core.Expression` instance covers
booleans + integers, sufficient for the spec's Phase 0 ratchet.
Smoke tests are in `StrataTest/Backends/CBMC/GOTO/BisimTests.lean`.
The `docs/CoreToGOTO_BisimReport.md` outcome report records what
fell out about provability of `Function.Injective nameMap` and the
shape of `EvalCorr` (cleaved naturally into `EvalBoolCorr` and
`EvalValueCorr`).

### Phase 1 — Tier 1 additive expansion

**Status:** closed (load-bearing parts).

| Sub-phase | Status |
|---|---|
| 1.a `step_skip` / `step_dead` | done |
| 1.a `step_function_call` | deferred (no consumer; spec sub-phase 1.a explicitly allows this) |
| 1.b `StepGoto_deterministic_*` | done as `StepGoto_shape_deterministic` plus `DeterministicEvalGoto`/`DeterministicEvalGotoBool` predicates; full successor-store determinism for state-changing constructors stays out of reach because their abstract `InitState`/`UpdateState`/`RemoveState` witnesses are existentials, and the `Bisim.lean` bridges resolve this need at a different layer |
| 1.c `progress_*` | done; ten per-instruction progress lemmas |
| 1.d `StepGotoRange` | done; transitivity and forgetful coercion to `StepGotoStar` |
| 1.e `old()` support | deferred (no consumer; spec sub-phase 1.e explicitly defers) |

Existing `coreCFGToGoto_forward_simulation` still type-checks with
axioms `[propext, Classical.choice, Quot.sound]`.

### Phase 2 — Concrete `Value` and `concreteEval`

**Status:** closed (load-bearing parts).

Phase 2's `Value` inductive, `Store := String → Option Value`, and
`concreteEval : ExprEval` arrive bundled in the Phase-0
`SemanticsTautschnig.lean`/`SemanticsEvalTautschnig.lean` ports. The
spec's planned hoist into a standalone `Value.lean` is unnecessary
unless Phase 5 fires.

| Sub-phase | Status |
|---|---|
| 2.a `Value`/`Store` | done (in `SemanticsTautschnig.lean`) |
| 2.b `concreteEval` port | done (in `SemanticsEvalTautschnig.lean`) |
| 2.c `concreteEval` totality | open (still `partial def`; sub-phase 2.c mitigation explicitly allows this) |
| 2.d `ValueCorr Core.Expression` | done (in `ValueCorrCore.lean`) |

`StrataTest/Backends/CBMC/GOTO/SemanticsEvalTautschnigTests.lean`
exercises `concreteEval` and `parseConstant` on small examples.

### Phase 3 — `StoreCorr`-based simulation theorem

**Status:** closed.

`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrectStore.lean` defines:

- `SteppingBridges` — a hypothesis bundle abstracting the per-step
  bridges. Two fields: `step_running` (running → running successor
  produces a `StepInstr` step) and `step_terminal` (running →
  terminal produces an `ExecProg.end_function` derivation).
- `StepGotoStar_to_ExecProg` — trace-level lift. Inducts on the
  underlying `ReflTrans` chain and dispatches each step to the
  appropriate field of `SteppingBridges`.
- `coreCFGToGoto_forward_simulation_storeCorr` — the end-to-end
  theorem. Composes the existing closed forward simulation with
  the trace lift to produce a `StoreCorr`-shaped existential
  conclusion.

Verified axiom set:
```
'CProverGOTO.coreCFGToGoto_forward_simulation_storeCorr'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```
identical to the original.

### Phase 4 — `sim_X` primitives over `StepGoto`

**Status:** partial per spec gating.

`Strata/Backends/CBMC/GOTO/SimPrimitives.lean` ports the cheap
no-state-change primitives:

- `sim_location`, `sim_skip`
- `sim_assume_pass`, `sim_assert_pass`
- `sim_goto_fallthrough`
- `sim_end_function`

Each primitive takes a single instruction at a known PC and
produces a one-step `StepGotoStar` segment, mirroring tautschnig's
`sim_X` shape.

State-changing primitives (`sim_assign`, `sim_init`, `sim_havoc`)
and compositional primitives (`sim_cmd`, `sim_block`, `sim_loop`,
`sim_ite_*`, `sim_end_to_end`) remain unimplemented. Per the spec:
"Phase 4 only fires if we want to support direct structured-
pipeline simulation here. Our existing chain is the unstructured
version. Phase 4 only fires if we want to support direct
structured-pipeline simulation here." No such consumer exists
today; the partial set is enough to land the file as a documented
starting point.

### Phase 5 — Convergence

**Status:** not started; gated.

The spec is explicit: "Phase 5 only fires if there is a *concrete
soundness driver*" and "Default: no, unless a concrete soundness
driver appears." Neither condition holds. Phase 5 is genuinely
left untouched, *intentionally*.

## Files touched

**New:**

- `Strata/Backends/CBMC/GOTO/SemanticsTautschnig.lean` (327 lines)
- `Strata/Backends/CBMC/GOTO/SemanticsEvalTautschnig.lean` (158 lines)
- `Strata/Backends/CBMC/GOTO/SemanticsPropsTautschnig.lean` (324 lines)
- `Strata/Backends/CBMC/GOTO/Bisim.lean` (650 lines)
- `Strata/Backends/CBMC/GOTO/StepGotoProps.lean` (303 lines)
- `Strata/Backends/CBMC/GOTO/ValueCorrCore.lean` (157 lines)
- `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrectStore.lean` (233 lines)
- `Strata/Backends/CBMC/GOTO/SimPrimitives.lean` (123 lines)
- `StrataTest/Backends/CBMC/GOTO/BisimTests.lean` (84 lines)
- `StrataTest/Backends/CBMC/GOTO/SemanticsEvalTautschnigTests.lean` (70 lines)
- `docs/CoreToGOTO_BisimReport.md` (137 lines)

**Modified:**

- `Strata/Backends/CBMC/GOTO/Semantics.lean` (+46 lines — added
  `step_skip`, `step_dead`, and the supporting `RemoveState`
  inductive).

Total: 2,612 lines added, 2 lines removed across 12 files. Nineteen
commits between baseline and the latest expansion commit.

## Build invariants

After every commit in this work:

- `lake build` of the full project succeeds.
- `grep -rn 'sorry' Strata/Backends/CBMC/GOTO/` returns no live
  matches (only a docstring reference in `Bisim.lean`).
- `#print axioms CProverGOTO.coreCFGToGoto_forward_simulation`
  remains `[propext, Classical.choice, Quot.sound]`.
- `#print axioms CProverGOTO.coreCFGToGoto_forward_simulation_storeCorr`
  is `[propext, Classical.choice, Quot.sound]` — the new theorem
  introduces no new project-internal axioms.

## Key learnings (re: the spec's open questions)

These three are also discussed at length in
`docs/CoreToGOTO_BisimReport.md`; the brief version:

1. **`Function.Injective nameMap` is required** for
   `step_dead`/`step_decl`/`step_assign`/`step_assign_nondet`
   bridges. Whether it is provable for the actual
   `<proc>::<scope>::<name>` renaming on real translator output
   remains a separate open question — Risk #1 is *surfaced* but not
   *resolved* by this work.
2. **`EvalCorr` cleaves naturally into two predicates.** The
   spec's single `EvalCorr` is split in the implementation into
   `EvalBoolCorr` (boolean evaluators agree, used by
   ASSERT/ASSUME/GOTO bridges) and `EvalValueCorr` (value
   evaluators agree modulo `vc.toValue`, used only by ASSIGN).
   The split keeps each bridge's hypothesis surface minimal.
3. **Failure-flag bridge is one-sided and clean.** The spec's
   `failureFlag_corresponds` plan turns out to be a single one-step
   bridge: `step_assert_fail` produces *both* a
   `StepInstr.assert_fail` step *and* a separate `AssertFails`
   witness. No "trail of consequences" is needed.

## Follow-up work (not addressed here)

The following remain explicitly out of scope per the spec, or
intentionally deferred:

- `WellFormedTranslation` discharge against `coreCFGToGotoTransform`
  (separate spec).
- `ExprTranslationPreservesEval` discharge against
  `Lambda.LExpr.toGotoExprCtx` (separate spec).
- `step_function_call` constructor (Phase 1.a, deferred until a
  consumer needs it).
- `old()` support / two-state evaluator (Phase 1.e, deferred until a
  consumer needs it).
- `gotoConcreteEval` totality (Phase 2.c; stays `partial def`).
- State-changing and compositional `sim_X` primitives (Phase 4
  remainder; deferred until a structured-pipeline consumer
  appears).
- Phase 5 convergence (gated; no driver).
