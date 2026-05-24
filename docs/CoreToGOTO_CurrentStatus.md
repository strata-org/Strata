# Core → CBMC GOTO: Current Proof Status

**Branch:** `htd/unstructured-to-goto`
**Last refreshed:** 2026-05-23 (post round-12 cleanup)

This is the canonical status doc for the Core-to-CBMC-GOTO
forward-simulation proof. For the high-level comparison with
`tautschnig/goto-semantics`, see `CoreToGOTO_SemanticsComparison.md`.
For round-by-round historical detail, see `historical/`.

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
  agreement, source-side run). No further translator-induction work
  can shrink the surface.

---

## The theorem chain

Two public theorems are exposed downstream. Internal helpers (`_v4`,
`_v5`) are marked `private`.

| Theorem | Location | What it states |
|---|---|---|
| `coreCFGToGoto_forward_simulation` | `CoreCFGToGOTOCorrect.lean:893` | Generic forward simulation: given a `WellFormedTranslation` witness, every terminating source CFG run is matched by a GOTO `StepGotoStar` from `wf.labelMap cfg.entry`. |
| `coreCFGToGoto_forward_simulation_storeCorr` | `CoreCFGToGOTOCorrectStore.lean:191` | Same, lifted to `ExecProg` over a concrete `SemanticsTautschnig.Store` via `StoreCorr` + `SteppingBridges`. |
| `coreCFGToGotoTransform_forward_simulation_concrete_v6` | `CoreCFGToGOTOConcrete.lean:190` | The above, instantiated against the actual translator output. Builds the WF from the strengthened theorem internally. |
| `coreCFGToGotoTransform_forward_simulation_concrete_v7` | `CoreCFGToGOTOConcrete.lean:521` | Like `_v6` but additionally internalizes R10b's `st_final` and `h_blocks_run` via `coreCFGToGotoTransform_decompose`. |

Live call chain: **`_v7 → _v6 → _v5 → _v4`** (the latter two are
private). All four versions verify the standard axiom set.

`#print axioms` smoke test: `StrataTest/Backends/CBMC/GOTO/CoreCFGToGOTOConcreteAxioms.lean`.

---

## Hypothesis surface on `_v7`

After R10/R11, every remaining hypothesis is in one of four classes:

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

**R7c trace-level pinning** — `h_decl_x_pinned`,
`h_assn_x_pinned`, `h_assn_rhs_pinned`. R7c proved these cannot
live at the `WellFormedTranslation` layer; they relate the trace's
`InitState`/`UpdateState` witness to the translator's emitted symbol.

**R7c value-side correspondence** — `h_decl_empty_value`,
`h_assign_value_corr`, `h_assign_nondet_value_corr`. Source/target
evaluator agreement on values.

**R11 evaluator monotonicity** — `h_init_extension`. δ_goto monotone
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
   theorem. Out of scope for the round-by-round work.
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

## Round-by-round summary

The proof was closed across 12 rounds of work between rounds 1 and
12 (2026-05-22 through 2026-05-23). Detailed per-round reports live
under `docs/_workers/round*_supervisor_report.md` and
`docs/_workers/{R,L,W,A}*_report.md`. The headline contributions:

| Round | Outcome |
|---|---|
| 1-3 | Worker A's structural soundness sub-lemmas, Worker B/B3's per-operator correspondences, Worker C's `SteppingBridges` discharge. |
| 4-5 | A4 closed `WellFormedTranslation` top-level (modulo 5 layout-field hypotheses). A5a/A5b discharged those 5 fields. The strengthened theorem `coreCFGToGotoTransform_wellFormed_strengthened` exposes a `Nonempty WF` from translator structure alone. |
| 6 | R6a's `TranslatorBridgeHyps` + `SteppingBridgesDischarge`. R6b's expression-side `B3` bundle for the bool+int fragment. |
| 7 | R7a (`EveryGotoTargetIsLabelMapEntry`), R7b (`HasNoDead`), R7c (lookup-field provenance + pinning split). |
| 8 | R8a (labelMap-entry / patcher reverse direction), R8b (DECL/ASSIGN provenance under PC-inversion auxiliaries). |
| 9 | R9 (`PcInversion.lean` — DECL/ASSIGN PC-inversion theorems via translator induction). Cleanup deleted dead `_v1`/`_v2`/`_v3`. |
| 10 | R10a (`WfLabelMapAgree.lean` — universal labelMap-uniqueness via new `layout_location_labels` field on WF). R10b (internalize `st_final`/`h_blocks_run` via `coreCFGToGotoTransform_decompose`). R10c (Tier-3 finding: bridge refactor for `assn_nondet` is intractable at the bridge layer alone). |
| 11 | R11 closed R10c's blockage at the simulation-skeleton layer: switched `init_det` arm to `step_assign` using a new `h_init_extension` monotonicity hypothesis; tightened `step_assign_nondet` to require `rhs.id = .side_effect .Nondet` directly. The strict `AssignNondetPcInversion` is gone from `_v7`. |
| 12 | Aggressive cleanup wave: 3,952 LoC removed across 13 workers (S1-S3, L1-L4, W1-W6, A1-A6). Highlights: WF file split into 6 sub-modules (each ≤1.5k LoC); B3 collapsed via `BoolIntBinOpDesc` (-719 LoC); `Concrete.lean` flattened by inlining `_v4`/`_v5` (-658 LoC). |

---

## Codebase layout

`Strata/Backends/CBMC/GOTO/` contains the proof. Top-level files (each
≤1.5k LoC):

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
* `TranslatorBridgeHypsDischarge.lean` (334) — `_v2` bridge (R6a + R7c).
* `InstructionLookups.lean` (338) — DECL/ASSIGN lookup-field bridges.

**Per-property structural facts** (post-cleanup sizes)

* `GotoTargetInRange.lean` (131) — R7a.
* `GotoTargetProvenance.lean` (567) — R8a (labelMap entry + patcher reverse).
* `NoDead.lean` (317) — R7b.
* `CmdProvenance.lean` (304) — R8b (DECL/ASSIGN provenance).
* `PcInversion.lean` (999) — R9 (PC-inversion theorems).
* `WfLabelMapAgree.lean` (398) — R10a (universal labelMap-uniqueness).

**Expression-side correspondence**

* `ExprTranslationPreservesEvalBoolInt.lean` (1198) — B3 bool+int
  fragment.

**Reusable infrastructure**

* `BlocksFoldClosed.lean` (466) — `BlocksFoldClosed P` typeclass and
  helpers used by `NoDead`, `GotoTargetProvenance`, and
  `WfLabelMapAgree`.
* `Tactics.lean` (27) — `inj_subst` macro.
* `CoreCFGToGOTOInvariants.lean` (377) — `WellFormedTranslation`
  structure definition + supporting predicates.

**Total:** ~20,600 LoC of correctness infrastructure (down from a
peak of ~24,300 LoC after round-12 cleanup).

---

## Companion documents

* `CoreToGOTO_SemanticsComparison.md` — comparison with
  `tautschnig/goto-semantics`'s alternative semantics.
* `historical/CoreToGOTO_ProofProgress.md` — the original sketch of
  the proof chain (line numbers may have drifted; structure remains).
* `historical/CoreToGOTO_CorrectnessAnalysis.md` — full-stack analysis
  of correctness levels (predates rounds 5-12).
* `historical/CoreToGOTO_BisimReport.md` — Phase-0 per-constructor
  bridge status.
* `historical/CoreToGOTO_ExpansionProgress.md` — Phases 0-4 status
  (predates rounds 5-12).
* `historical/CoreToGOTO_Gaps.md` — translation gaps inventory (DFCC,
  axioms, not-modeled features).
* `historical/CoreToGOTO_ProofStatusRound8.md` — round-8 snapshot.
* `historical/CoreToGOTO_ShrinkAudit.md` — input to round-12 cleanup.
* `_workers/round{1..8}_supervisor_report.md` — per-round narratives.
* `_workers/{R9..R11,L1-L4,S1-S3,W1-W6,A1-A6}*_report.md` — per-worker
  reports.
