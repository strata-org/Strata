# Core DetCFG → CBMC GOTO: Proof status as of round 8 (2026-05-22)

> **Update post-R9 (2026-05-22, later):** Round 9 added `_v6` (closes
> R8b's two non-strict PC-inversion auxiliaries via translator
> induction) and the round-9 cleanup deleted the dead `_v1`/`_v2`/`_v3`
> waypoint versions (~498 LoC reduction). The live call chain is now
> `_v6 → _v5 → _v4`. See `docs/CoreToGOTO_CurrentStatus.md` for the
> updated picture; the round-by-round narrative below is unchanged.

This document records the state of the multi-round closure effort over
`coreCFGToGoto_forward_simulation` and its `_v1`–`_v5` "concrete"
descendants on branch `htd/unstructured-to-goto`. It complements
`docs/CoreToGOTO_ProofProgress.md` (which describes the original
single-theorem chain) by tracking the round-by-round narrowing of the
hypothesis surface from "structural-soundness assumed" toward "the
absolute minimum that any consumer must supply about evaluators and
traces."

## Top-level theorems (current snapshot)

All listed theorems live under `Strata/Backends/CBMC/GOTO/`. Every
named theorem builds, has no `sorry` in live code, and verifies axioms
`[propext, Classical.choice, Quot.sound]` (the standard set).

| Theorem | File | What it takes | What it gives |
|---|---|---|---|
| `coreCFGToGoto_forward_simulation` | `CoreCFGToGOTOCorrect.lean` | `WellFormedTranslation` + `ExprTranslationPreservesEval` | StepGotoStar simulation |
| `coreCFGToGoto_forward_simulation_storeCorr` | `CoreCFGToGOTOCorrectStore.lean` | adds `SteppingBridges` + `StoreCorr` + `Function.Injective nameMap` | `ExecProg` simulation in `Store` shape |
| `coreCFGToGotoTransform_forward_simulation_concrete_v1` | `CoreCFGToGOTOConcrete.lean` | concrete-translator hypotheses + `WellFormedTranslation` | discharges `coreCFGToGoto_forward_simulation_storeCorr` |
| `_v2` | same | replaces `WellFormedTranslation` with `ExprTranslationPreservesEval` + structural inputs (round-5 strengthened theorem) | same conclusion, smaller hypothesis surface |
| `_v3` | same | replaces `ExprTranslationPreservesEval` with B3's bool+int bundle | same conclusion, B3 fragment |
| `_v4` | same | adds R7a/R7b/R7c's lookup-field discharges and provenance hypotheses | further-discharged `_v3` |
| `_v5` | same | adds R8a/R8b's structural auxiliaries; fixes `nameMap = identToString` | further-discharged `_v4`; closest current form to "concrete soundness" |

Axiom verification (`StrataTest/Backends/CBMC/GOTO/CoreCFGToGOTOConcreteAxioms.lean`):

```
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v4'
  depends on axioms: [propext, Classical.choice, Quot.sound]

'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v5'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

## What's closed across rounds 1–8

| Round | Worker(s) | New LoC | Key outcome |
|---|---|---|---|
| Pre-rounds | — | ~3000 | `coreCFGToGoto_forward_simulation` sorry-free |
| Round 1 | A / B / C | ~2500 | A's sub-lemmas + B's per-operator + C's discharge |
| Round 2 | A2 / B2 + items 5/6 | ~2000 | A2 (stronger WF) + B2 (more operators) |
| Round 3 | A3 / B3 | ~1900 | A3 structural soundness + B3 bool+int operator bundle |
| Round 4 | A4 + concrete v1 | ~1900 | A4 WF top-level + first concrete forward simulation |
| Round 5 | A5a / A5b | ~2400 | layout closures + strengthened WF |
| Round 6 | R6a / R6b + v2/v3 | ~750 | TranslatorBridgeHyps + expression-side bundle |
| Round 7 | R7a / R7b / R7c + v4 | ~1690 | goto-target-in-range + no-dead + lookup fields |
| Round 8 | R8a / R8b + v5 | ~1850 | goto-provenance + cmd-provenance + v5 |

**~17,990 LoC** of correctness infrastructure. `lake build` green
throughout. No `sorry` in live code. All top-level theorems closed
under the standard axiom set.

The decisive narrowing at each round shrunk the structural-soundness
hypothesis surface; categorising the remaining `_v5` hypotheses below.

## `_v5` hypothesis classification

`coreCFGToGotoTransform_forward_simulation_concrete_v5` takes the
following hypothesis families. Each family is labelled with one of
**[trivial]** (mechanical for the standard caller),
**[mechanical-deferred]** (closable from translator structure but not
yet done), **[bridge-required]** (needs a bridge-level refactor not
worker-tractable), or **[caller-irreducible]** (genuinely needs to
come from outside the translator/structure layer).

### Translator-input invariants

* `h_init_size`, `h_init_loc`, `h_init_no_dead`, `h_init_no_goto_target`
  — **[trivial]** for any standard `trans₀` with empty
  `instructions = #[]`.
* `h_distinct`, `h_admitted_blocks`, `h_loopContracts_empty_post`,
  `h_entry_first` — **[trivial]** CFG-fragment restrictions.

### B3 expression-side bundle

* `h_red`, `h_op`, `h_uniform`, `h_commutes_not` — **[caller-irreducible]**;
  the bool+int fragment's standing requirements.

### Worker C parameters

* `callResult`, `eval`, `fenv` — **[caller-irreducible]** (concrete
  evaluator and call-result relation).
* `h_eval_bool_corr`, `h_inj` — **[caller-irreducible]**; latter is
  `Function.Injective identToString`.
* `h_wf_bool` — **[caller-irreducible]**.

### R8a's structural witnesses

* `st_final`, `h_blocks_run` — **[mechanical-deferred]**; recoverable
  from `coreCFGToGotoTransform_decompose`. Estimated ~50 LoC to
  internalise.
* `h_labelMap_agree` — **[mechanical-deferred]** but subtler. The
  WF returned by `coreCFGToGotoTransform_wellFormed_strengthened` has
  `labelMap` definitionally equal to `hashMapToLabelMap st_final.labelMap`,
  but R7a/v4's auxiliary path is universally quantified over WF
  values, so a uniqueness-of-WF-labelMap lemma (or surfacing the
  strengthened-WF's specific `labelMap` shape) is needed. Estimated
  ~100-200 LoC.

### R8b's PC-inversion auxiliaries

* `h_decl_pc_inv`, `h_assn_pc_inv`, `h_assn_nondet_pc_inv` —
  **[mechanical-deferred]**. Each characterises which translator
  constructor emitted each DECL/ASSIGN PC. Mechanically discharable
  from the translator's outer-loop induction (~100-300 LoC each).
* The third one, `AssignNondetPcInversion`, is a **strict** form
  whose discharge for general CFGs is *impossible* (any source CFG
  containing `set _ (.det _) _` or `init _ _ (.det _) _` cmds emits
  non-nondet ASSIGNs). Closing the v2 bridge's
  `assign_nondet_lookup` field cleanly is **[bridge-required]** — a
  refactor in `InstructionLookups.lean` and
  `TranslatorBridgeHypsDischarge.lean` to take a per-PC partial
  provenance gated on a `step_assign_nondet`-firing trace
  precondition.

### R7c's pinning hypotheses

* `h_decl_x_pinned`, `h_assn_x_pinned`, `h_assn_rhs_pinned` —
  **[caller-irreducible]**. R7c proved these cannot be discharged at
  the `WellFormedTranslation` layer. They relate the trace's
  source-side `InitState`/`UpdateState` witness `x` to the
  translator's emitted symbol — which only the bisimulation
  consumer's loop can supply.

### R7c's value-side hypotheses

* `h_decl_empty_value`, `h_assign_value_corr`,
  `h_assign_nondet_value_corr` — **[caller-irreducible]**. Source-target
  evaluator agreement on values; not derivable from translator
  structure.

### Source-side run

* `σ`, `σ'`, `b`, `σ_goto`, `h_corr`, `h_run_src` —
  **[caller-irreducible]** (standard source-run + initial-store
  correspondence inputs).

## Two findings worth carrying forward

### R7c's `h_assn_nondet_provenance` is provably false as written

R8b discovered that the third hypothesis in R7c's v2 bridge,
`h_assn_nondet_provenance`, asserts that *every* ASSIGN PC has a
nondet rhs. This is provably false in general: `init_det` and
`set_det` constructors emit ASSIGNs whose rhs is a translated source
expression, not `Side_effect.Nondet`.

R8b worked around this by providing an `assn_nondet_provenance_of_translator_strict`
form which assumes every ASSIGN PC is exactly a `set _ .nondet _`
cmd-start (`AssignNondetPcInversion`). That assumption is satisfied
only by source CFGs where every ASSIGN is a nondet one — a strong
restriction.

The proper fix lives at the v2-bridge layer. The bridge's
`assign_nondet_lookup_of_provenance_and_pinned` should take a per-PC
partial provenance gated on a "this firing is a `step_assign_nondet`"
precondition, rather than a universal existence claim. This is
**[bridge-required]**, separable from translator-structure work.

### R8b's `identToString` vs caller-`nameMap` mismatch

R7's strengthening of `CmdEmittedAt` exposed the literal symbol
`Expr.symbol (identToString v) gty` in the constructors. R8b's
provenance theorems consequently produce that literal form, while
v4's hypotheses (and R6a's bridge) accept a caller-supplied
`nameMap`.

`_v5` resolves the mismatch by fixing `nameMap = identToString`,
which matches the natural `Imperative.ToGoto Core.Expression` instance
in `CoreToCProverGOTO.lean`. A future round could generalise R8b's
theorems to a parametric `nameMap` plus a name-translation
hypothesis, but no current consumer requires it.

## Open / future tasks

### Immediate "round 9" candidates

1. **Internalise R8a's structural witnesses.** Make `_v6` recover
   `st_final`, `h_blocks_run`, and `h_labelMap_agree` internally
   from `coreCFGToGotoTransform_decompose` plus a uniqueness-of-WF-labelMap
   lemma. Estimated 200-300 LoC in `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean`
   and possibly a small new file. **Mechanical.**
2. **Internalise R8b's three PC-inversion auxiliaries.** Each is a
   straight induction over the translator's outer loop. Estimated
   100-300 LoC per auxiliary; can be parallelised across three workers
   on disjoint files in the same way rounds 6-8 did. **Mechanical.**

After (1) and (2), `_v6` would have only the **[caller-irreducible]**
families plus the **[trivial]** translator-input invariants — the
absolute minimum hypothesis surface achievable without modelling
source-side traces explicitly or augmenting `WellFormedTranslation`
with structural-inversion fields.

### Bridge-level refactors (separable)

3. **Refactor `assign_nondet_lookup_of_provenance_and_pinned` in
   `InstructionLookups.lean`.** Replace the universal-over-PCs
   `h_assn_nondet_provenance` with a per-PC partial provenance gated
   on a firing-trace precondition. Then re-thread through
   `TranslatorBridgeHypsDischarge.lean`'s `_v2` bridge. Estimated
   100-200 LoC. **Bridge-required**, not a worker-tractable
   translator-structure task.
4. **Revisit `nameMap` parameterisation of R8b.** Generalise the
   three provenance theorems in `CmdProvenance.lean` to take a
   parametric `nameMap` plus a "name translation matches identToString"
   hypothesis, mirroring R7c's bridge. Optional; only worth doing if
   a non-`identToString` caller appears.

### Beyond the current proof family

5. **Discharging the WF-discharge's own auxiliary obligations.**
   R7a's `EveryGotoTargetIsLabelMapEntry` was closed in round 8;
   R7c's three lookup fields were split into provenance + pinning in
   round 7. The pinning hypotheses (`h_decl_x_pinned`,
   `h_assn_x_pinned`, `h_assn_rhs_pinned`) are documented as
   **[caller-irreducible]** at the WF layer. Closing them would
   require an entirely new layer of proof infrastructure: explicit
   modelling of source-side traces with PC-level annotations, or a
   strengthened bisimulation invariant carried through
   `coreCFGToGoto_forward_simulation_storeCorr`. Out of scope for
   the round-by-round work; would need a separate spec.
6. **Closing the value-side hypotheses.** Same situation as #5:
   `h_decl_empty_value`, `h_assign_value_corr`, and
   `h_assign_nondet_value_corr` describe source/target evaluator
   agreement on values. Not derivable from translator structure.
   Would require a `ValueCorr` extension covering the relevant
   value cases plus an evaluator-correspondence theorem on
   `concreteEval`/B3. Separate spec.

### Documented follow-ups from `goto-semantics-expansion-design.md`

7. **Phase 2.c — `concreteEval` total.** Attempted in round-8
   follow-up work and abandoned in favour of staying on `partial def`
   (recorded in the spec doc). Lean 4's pattern-match equation
   binding plus `where`-clause termination obstacles make a clean
   conversion bigger than projected (~250 LoC vs the projected ~80
   LoC). No downstream consumer currently requires `concreteEval` to
   compute in proofs. Revisit if/when a consumer needs it.
8. **Phase 1.a continuation — `step_function_call`** and **Phase 1.e
   — `old`-support.** Both deferred per the spec until a downstream
   consumer needs them.
9. **Phase 4 — compositional and state-changing `sim_X` primitives.**
   Cheap no-state-change primitives are landed; the rest are deferred
   until a structured-pipeline consumer appears.
10. **Phase 5 — convergence onto a single canonical step relation.**
    Gated on a concrete soundness driver that does not currently
    exist. The default stands: don't fire.

## Process notes for future rounds

* **Worker dispatch via worktrees.** All multi-worker rounds (R6, R7,
  R8) used parallel `git worktree`-isolated agents on
  file-disjoint targets. Cherry-picking onto
  `htd/unstructured-to-goto` has been clean every time due to the
  disjoint-file discipline. The "report stub first, commit
  incrementally" pattern (since round 3) eliminated the
  watchdog-stall problem that plagued rounds 1-2.
* **Branch-base drift.** R6a, R7c, R8a, and R8b all based their
  worktrees on divergent branches. Cherry-picks have been clean each
  time but supervisors should brief workers explicitly on which
  branch to base. (Documented in round-7 and round-8 supervisor
  reports.)
* **Tier system.** Workers report Tier 1 (Best, full closure), Tier
  2 (Good, closure modulo a stable auxiliary), or Tier 3 (Acceptable,
  partial closure with a documented obstacle). Rounds 6-8 mostly
  delivered Tier 2 outcomes — closure modulo small mechanically
  discharable auxiliaries — which the next round then closed. R7c
  and R8b each surfaced one **genuine semantic finding** not
  visible in advance: R7c's trace-level pinning obligation, and
  R8b's discovery of R7c's false `h_assn_nondet_provenance` shape.

## Files added or substantially modified, rounds 6-8

| File | Status | Notes |
|---|---|---|
| `Strata/Backends/CBMC/GOTO/TranslatorBridgeHypsDischarge.lean` | new (R6a) | + `_v2` (R7c) |
| `Strata/Backends/CBMC/GOTO/SteppingBridgesDischarge.lean` | new (R6a) | |
| `Strata/Backends/CBMC/GOTO/ExprTranslationPreservesEvalBoolInt.lean` | new (R6b) | 2246 LoC; B3 closure |
| `Strata/Backends/CBMC/GOTO/GotoTargetInRange.lean` | new (R7a) | Tier 2 |
| `Strata/Backends/CBMC/GOTO/NoDead.lean` | new (R7b) | Tier 1 |
| `Strata/Backends/CBMC/GOTO/InstructionLookups.lean` | new (R7c) | Tier 3 |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOInvariants.lean` | strengthened (R7c) | exposes literal `identToString` symbol |
| `Strata/Backends/CBMC/GOTO/GotoTargetProvenance.lean` | new (R8a) | 1116 LoC |
| `Strata/Backends/CBMC/GOTO/CmdProvenance.lean` | new (R8b) | 372 LoC |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` | extended (each round) | hosts `_v1`-`_v5` |
| `StrataTest/Backends/CBMC/GOTO/{GotoTargetInRange,NoDead,GotoTargetProvenance,CoreCFGToGOTOConcrete}Axioms.lean` | new | per-round axiom smoke tests |
| `docs/_workers/round{6,7,8}_supervisor_report.md` | new | per-round narratives |

## Summary table: from `coreCFGToGoto_forward_simulation` to `_v5`

| Layer | Original takes | `_v5` takes |
|---|---|---|
| `WellFormedTranslation` | hypothesis | discharged via strengthened theorem (round 5) + R7+R8 auxiliaries |
| `ExprTranslationPreservesEval` | hypothesis | discharged via B3's bool+int bundle (round 6) |
| `SteppingBridges` | hypothesis | discharged via R6a's `TranslatorBridgeHyps` (rounds 6-7) |
| Translator-input invariants | n/a | trivial for `trans₀ = empty` |
| Trace-level pinning + value-side | n/a (implicit) | surfaced as caller-irreducible hypotheses |
| `Function.Injective nameMap` | hypothesis | hypothesis (now `identToString`-specific in v5) |
| Source-side run | hypothesis | hypothesis |

The forward path from "WellFormedTranslation assumed" to "every
non-evaluator/non-trace obligation discharged" is essentially
complete. Remaining gaps are the **[caller-irreducible]** ones (which
no amount of translator-structure work can close) and the
**[mechanical-deferred]** ones (which a future R9 round can close).

The "concrete soundness story modulo trace-level and evaluator
obligations" milestone (per round-7 and round-8 reports) has been
reached. A genuine end-to-end compiler-correctness theorem on
`coreCFGToGotoTransform`'s actual output would require either (a) a
downstream caller that supplies the trace-level pinning and
value-side hypotheses (likely a bisimulation simulator built on top
of this proof), or (b) a major new layer of proof infrastructure.
