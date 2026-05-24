# Core → CBMC GOTO: Current Proof Status

**Branch:** `htd/unstructured-to-goto`
**Last refreshed:** 2026-05-23

This is the canonical status doc for the Core-to-CBMC-GOTO
forward-simulation proof. For the high-level comparison with
`tautschnig/goto-semantics`, see
[`CoreToGOTO_SemanticsComparison.md`](CoreToGOTO_SemanticsComparison.md).

---

## TL;DR

* **Closed:** end-to-end forward simulation from `Core.DetCFG` (the
  source) to the actual `Strata.coreCFGToGotoTransform` output (the
  target GOTO program), on the call-free CFG fragment.
* **Axioms:** `[propext, Classical.choice, Quot.sound]` — the
  standard Lean axiom set. **No project-internal axioms.**
* **Proof state:** sorry-free, builds green (585 jobs), public theorem
  signatures stable.
* **Remaining hypotheses:** all caller-irreducible (B3 expression-side
  bundle, trace-level pinning, value-side correspondence, evaluator
  agreement, source-side run).

---

## The theorem chain

Two public theorems are exposed downstream. Internal helpers (`_v4`,
`_v5`) are marked `private`.

| Theorem | Location | What it states |
|---|---|---|
| `coreCFGToGoto_forward_simulation` | `CoreCFGToGOTOCorrect.lean:893` | Generic forward simulation: given a `WellFormedTranslation` witness, every terminating source CFG run is matched by a GOTO `StepGotoStar` from `wf.labelMap cfg.entry`. |
| `coreCFGToGoto_forward_simulation_storeCorr` | `CoreCFGToGOTOCorrectStore.lean:191` | Same, lifted to `ExecProg` over a concrete `SemanticsTautschnig.Store` via `StoreCorr` + `SteppingBridges`. |
| `coreCFGToGotoTransform_forward_simulation_concrete_v6` | `CoreCFGToGOTOConcrete.lean:190` | The above, instantiated against the actual translator output. Builds the WF from the strengthened theorem internally. |
| `coreCFGToGotoTransform_forward_simulation_concrete_v7` | `CoreCFGToGOTOConcrete.lean:521` | Like `_v6` but additionally internalizes `st_final` and `h_blocks_run` via `coreCFGToGotoTransform_decompose`. |

Live call chain: **`_v7 → _v6 → _v5 → _v4`** (the latter two are
private). All four versions verify the standard axiom set.

`#print axioms` smoke test:
`StrataTest/Backends/CBMC/GOTO/CoreCFGToGOTOConcreteAxioms.lean`.

---

## Hypothesis surface on `_v7`

Every remaining hypothesis is in one of two classes:

### Trivial for the standard caller

For `trans₀.instructions = #[]` (the standard initial state):
`h_init_size`, `h_init_loc`, `h_init_no_dead`,
`h_init_no_goto_target`, `h_init_empty_decl_assign`,
`h_init_no_location`. Plus CFG-fragment restrictions
(`h_distinct`, `h_admitted_blocks`, `h_loopContracts_empty_post`,
`h_entry_first`).

### Caller-irreducible (genuine consumer obligations)

**B3 expression-side bundle** — `h_red`, `h_op`, `h_uniform`,
`h_commutes_not`. The bool+int fragment standing requirements.

**Trace-level pinning** — `h_decl_x_pinned`, `h_assn_x_pinned`,
`h_assn_rhs_pinned`. These cannot live at the
`WellFormedTranslation` layer; they relate the trace's
`InitState`/`UpdateState` witness to the translator's emitted
symbol.

**Value-side correspondence** — `h_decl_empty_value`,
`h_assign_value_corr`, `h_assign_nondet_value_corr`. Source/target
evaluator agreement on values.

**Evaluator monotonicity** — `h_init_extension`. δ_goto monotone
across `InitState`'s store mutation. Standard property of any sane
evaluator.

**Top-level caller obligations** — `h_eval_bool_corr`, `h_inj`
(`Function.Injective identToString`), `h_wf_bool`, the source-side
run (`σ`, `σ'`, `b`, `σ_goto`, `h_corr`, `h_run_src`).

---

## What is *not* proven

In rough order from "closable with mechanical work" to "requires new
infrastructure":

1. **B3 expansion to non-bool+int operators** (quantifiers, function
   applications, `old`, side effects). The full Core-Expression
   fragment is open by design.
2. **`Function.Injective identToString`** for realistic source
   programs. Whether the `<proc>::<scope>::<name>`-style renaming is
   globally injective in the presence of shadowed locals is open;
   mitigation if not: parameterize `nameMap` by scope.
3. **Trace-level pinning + value-side hypotheses.** Not derivable
   from translator structure; closing them needs an explicit
   source-side trace model with PC-level annotations or a
   strengthened bisimulation invariant carried through the simulation
   theorem.
4. **Beyond the call-free fragment.** All theorems restrict to
   `isAdmittedCmd` (no `.call`). Admitting `.call` requires adding
   `step_function_call` to `StepGoto`, parameterizing by an abstract
   `CallResultRel`, and discharging that relation for the actual
   translator output.
5. **Structured-pipeline simulation primitives.** The cheap
   no-state-change `sim_X` primitives are landed in
   `SimPrimitives.lean`; compositional/state-changing primitives are
   deferred until a structured-pipeline consumer appears.

---

## Codebase layout

`Strata/Backends/CBMC/GOTO/` contains the proof. All files ≤1.5k LoC.

**Core theorems**

* `CoreCFGToGOTOCorrect.lean` (928 LoC) — original
  `coreCFGToGoto_forward_simulation`.
* `CoreCFGToGOTOCorrectStore.lean` (~235 LoC) — `_storeCorr` lift.
* `CoreCFGToGOTOConcrete.lean` (718 LoC) — `_v6` and `_v7`.

**Translator structural soundness** (`CoreCFGToGotoTransformWF/`)

* `Shape.lean` (941) — per-Cmd shape lemmas.
* `Preservation.lean` (1023) — per-step preservation.
* `StepPreservation.lean` (1290) — step-level preservation.
* `FoldAndDecompose.lean` (1192) — fold-level + decompose.
* `BlockBodyClosures.lean` (862) — block-body layout closures.
* `CondGotoClosures.lean` (1412) — condGoto layout closures.
* `CoreCFGToGotoTransformWF.lean` (142) — main re-export module.

**Bridge layer**

* `Bisim.lean` (587) — per-`StepGoto` bridges to tautschnig's `StepInstr`.
* `SteppingBridgesDischarge.lean` (357) — `SteppingBridges` from `EvalBoolCorr` + `TranslatorBridgeHyps`.
* `TranslatorBridgeHypsDischarge.lean` (334) — `_v2` bridge.
* `InstructionLookups.lean` (338) — DECL/ASSIGN lookup-field bridges.

**Per-property structural facts**

* `GotoTargetInRange.lean` (131) — every emitted GOTO's target is in range.
* `GotoTargetProvenance.lean` (567) — labelMap entry + patcher reverse direction.
* `NoDead.lean` (317) — translator emits no DEAD instructions.
* `CmdProvenance.lean` (304) — DECL/ASSIGN provenance.
* `PcInversion.lean` (999) — DECL/ASSIGN PC-inversion theorems.
* `WfLabelMapAgree.lean` (398) — universal labelMap-uniqueness.

**Expression-side correspondence**

* `ExprTranslationPreservesEvalBoolInt.lean` (1198) — bool+int
  fragment translation correctness.

**Reusable infrastructure**

* `BlocksFoldClosed.lean` (466) — `BlocksFoldClosed P` typeclass and
  helpers used by `NoDead`, `GotoTargetProvenance`, and
  `WfLabelMapAgree`.
* `Tactics.lean` (27) — `inj_subst` macro.
* `CoreCFGToGOTOInvariants.lean` (377) — `WellFormedTranslation`
  structure definition + supporting predicates.

**Total:** ~20,600 LoC of correctness infrastructure.

---

## Companion documents

* [`CoreToGOTO_SemanticsComparison.md`](CoreToGOTO_SemanticsComparison.md)
  — comparison with `tautschnig/goto-semantics`'s alternative
  semantics.
* [`CoreToGOTO_WhyDifficult.md`](CoreToGOTO_WhyDifficult.md) —
  explanatory doc: why the simulation proof is ~20k LoC even though
  the source and target look one-to-one, with concrete examples
  from the actual proof.
* [`historical/CoreToGOTO_ProofProgress.md`](historical/CoreToGOTO_ProofProgress.md)
  — the original sketch of the proof chain (line numbers may have
  drifted; structure remains).
* [`historical/CoreToGOTO_CorrectnessAnalysis.md`](historical/CoreToGOTO_CorrectnessAnalysis.md)
  — full-stack analysis of correctness levels.
* [`historical/CoreToGOTO_BisimReport.md`](historical/CoreToGOTO_BisimReport.md)
  — per-`StepGoto`-constructor bridge status.
* [`historical/CoreToGOTO_ExpansionProgress.md`](historical/CoreToGOTO_ExpansionProgress.md)
  — GOTO-semantics-expansion progress through Phases 0-4.
* [`historical/CoreToGOTO_Gaps.md`](historical/CoreToGOTO_Gaps.md)
  — translation gaps inventory (DFCC, axioms, not-modeled features).
* [`historical/CoreToGOTO_ProofStatusRound8.md`](historical/CoreToGOTO_ProofStatusRound8.md)
  — earlier status snapshot.
* [`historical/CoreToGOTO_ShrinkAudit.md`](historical/CoreToGOTO_ShrinkAudit.md)
  — input to the cleanup wave.
