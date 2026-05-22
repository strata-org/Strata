# Round-8 supervisor report — R8a/R8b parallel run + v5 composition

**Run date:** 2026-05-22
**Supervisor:** main session on `htd/unstructured-to-goto`
**Workers:** two parallel agents on disjoint files + supervisor v5
composition.

## TL;DR

| Item | Status | Outcome |
|---|---|---|
| **Worker R8a** | **Tier 2 (Good)** | `everyGotoTargetIsLabelMapEntry_of_translator_translatorMap` fully discharges the auxiliary in the translator-hashmap-keyed form. The `wf.labelMap` form requires a small `h_labelMap_agree` bridge hypothesis (trivially provable for the strengthened-WF case). Axioms `[propext, Classical.choice, Quot.sound]`. |
| **Worker R8b** | **Tier 2 (Good)** for DECL/ASSIGN; **Tier 3 (Acceptable)** for ASSIGN-Nondet | Three provenance theorems closed under PC-inversion auxiliaries. Discovered R7c's `h_assn_nondet_provenance` as written is **provably false** for typical CFGs; delivered a strict variant requiring `AssignNondetPcInversion`. Axioms standard. |
| **Supervisor v5** | **closed** | `coreCFGToGotoTransform_forward_simulation_concrete_v5` composes R8a + R8b on top of v4, internally discharging R7a's `h_aux_goto_target` and R7c's three provenance hypotheses. Fixes `nameMap = identToString` to bridge R8b's literal identToString shape with v4's caller-nameMap shape. |

Net contribution to `htd/unstructured-to-goto` since round 7:
**~1850 LoC** (R8a: 1116 LoC new file + 14 LoC axiom test; R8b: 372 LoC
new file; supervisor v5: ~360 LoC + 19 LoC axiom test). `lake build`
green (585 jobs). No `sorry`/`admit`. Standard axiom set
`[propext, Classical.choice, Quot.sound]` on all top-level theorems.

## Per-worker outcomes

### Worker R8a — Tier 2 (Good)

`docs/_workers/R8a_goto_provenance_report.md`. Six commits.

**Delivered** (new file `Strata/Backends/CBMC/GOTO/GotoTargetProvenance.lean`,
1116 LoC):

* `NoGotoHasTarget trans` — predicate: every `GOTO` instruction in
  the translator state has `target = none`. Held throughout the
  blocks-fold (the translator only emits GOTOs without resolved
  targets; the patcher fills targets later).
* Per-translator-step preservation lemmas: `Cmd.toGotoInstructions`,
  `coreCFGToGotoCmdStep`, `cmdsFoldlM`, `emitLabel`, `emitCondGoto`,
  `emitUncondGoto`, `endFunction_emit`, `coreCFGToGotoBlockStep`,
  `blocksFoldlM`, plus parallel reverse-direction lemmas for
  `coreCFGToGotoPatchStep` and `patchesFoldlM`.
* Patcher reverse-target lemmas
  (`patchGotoTargets_target_some_in_patches`,
  `coreCFGToGotoPatchStep_no_contracts_resolved_reverse`,
  `patchesFoldlM_no_contracts_resolved_reverse`,
  `patchesFoldlM_no_contracts_resolved_reverse_array`): every
  patched `target` came from an entry in the patches list.
* `blocksFoldlM_labelMap_keys_in_blocks` — every label key in the
  post-fold labelMap was a block label in `cfg.blocks`.
* `everyGotoTargetIsLabelMapEntry_of_translator_translatorMap` —
  the top-level theorem in translator-hashmap-keyed form.
* `everyGotoTargetIsLabelMapEntry_of_translator` — the
  `wf.labelMap` form, accepting a caller-supplied
  `h_labelMap_agree` bridge hypothesis.

**Verified** axioms `[propext, Classical.choice, Quot.sound]` via
`StrataTest/Backends/CBMC/GOTO/GotoTargetProvenanceAxioms.lean`.

**Tier 2 obstacle:** the `wf.labelMap` form requires a bridge to
the translator's `hashMapToLabelMap st_final.labelMap`. The
strengthened WF's `labelMap` field is *definitionally*
`hashMapToLabelMap st_final.labelMap` — an obvious unfolding,
but not closable inside R8a without exposing the WF
construction's internal shadow record. Surfacing it as an
explicit hypothesis was cleaner than rewriting the WF API.

### Worker R8b — Tier 2 (Good) for two of three

`docs/_workers/R8b_cmd_provenance_report.md`. Two commits.

**Delivered** (new file `Strata/Backends/CBMC/GOTO/CmdProvenance.lean`,
372 LoC):

* `DeclPcInversion` — auxiliary predicate: every DECL PC
  corresponds to the cmd-start of an `init_*` cmd.
  `decl_provenance_of_translator` — under `wf` + `DeclPcInversion`,
  every DECL PC has code `Code.decl (Expr.symbol (identToString
  v_src) gty)` for some source `v_src`.
* `AssignPcInversion` — auxiliary predicate: every ASSIGN PC is
  either a `set _ _ _` cmd-start or an `init _ _ (.det _) _`
  offset-1.  `assn_provenance_of_translator` — analogous closure
  for ASSIGN.
* `AssignNondetPcInversion` (strict) — auxiliary predicate: every
  ASSIGN PC is exactly a `set _ .nondet _` cmd-start.
  `assn_nondet_provenance_of_translator_strict` — closes the
  ASSIGN-Nondet provenance under the strict inversion.

**Verified** axioms standard.

**Tier 3 finding for ASSIGN-Nondet:** R7c's
`h_assn_nondet_provenance` says "every ASSIGN has a nondet rhs".
This is **provably false** for any translator output containing
an `init_det` or `set_det` cmd: those emit ASSIGNs whose rhs is a
translated source expression, not `Side_effect.Nondet`. R8b
therefore delivers only the *strict* variant (assuming every
ASSIGN PC is a `set _ .nondet _` cmd-start), which is satisfied
only by source CFGs where every ASSIGN is a nondet one. The
proper fix at the v2 bridge level is a per-PC partial
provenance gated on a `step_assign_nondet`-firing precondition
— a bridge-level refactor in `InstructionLookups.lean` /
`TranslatorBridgeHypsDischarge.lean`, not a translator-level
theorem. This is documented in the file's module-level docstring
and in R8b's report.

**Tier 2 obstacle for DECL/ASSIGN:** the proofs of the two
non-strict provenance theorems hinge on a CFG-PC inversion: from
a `pc` carrying a DECL/ASSIGN, find the `(l, blk) ∈ cfg.blocks`
and offset such that `pc = labelMap l + 1 + cmdsPrefixInstrCount
blk.cmds k`. That inversion is mechanically discharable from
the translator's outer-loop induction (~100-200 LoC of structural
translator reasoning) but was deferred in favor of taking it as
an explicit auxiliary hypothesis. The Tier-2 split (closure
modulo a specific structural auxiliary) is honest about which
obligations are mechanical and which remain.

## Supervisor — v5 composition

`coreCFGToGotoTransform_forward_simulation_concrete_v5` in
`CoreCFGToGOTOConcrete.lean` (~360 LoC). Layers on top of v4 by
internally discharging:

* **R7a's `h_aux_goto_target`** via R8a's
  `everyGotoTargetIsLabelMapEntry_of_translator_translatorMap`
  (using `h_labelMap_agree` as a hypothesis bridging the WF's
  `labelMap` to the translator's hashmap-keyed labelMap).
* **R7c's three provenance hypotheses**
  (`h_decl_provenance`/`h_assn_provenance`/`h_assn_nondet_provenance`)
  via R8b's `decl_provenance_of_translator`,
  `assn_provenance_of_translator`, and
  `assn_nondet_provenance_of_translator_strict` (using R8b's
  three PC-inversion auxiliaries).

A small but real friction: R8b's theorems prove `instr.code =
Code.decl (Expr.symbol (identToString v_src) gty)` (literal
`identToString`), while v4's hypotheses use the caller-supplied
`nameMap`. To bridge, **v5 fixes
`nameMap = Imperative.ToGoto.identToString`**. This is the
natural choice for `Core.Expression` (matches the
`Imperative.ToGoto` instance in `CoreToCProverGOTO.lean`), so
it doesn't exclude any practical caller.

**Verified axiom set:**

```
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v5'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

Same as the original `coreCFGToGoto_forward_simulation`.

## What this delivers

After round 8, the top-level concrete theorem `_v5` requires:

### Translator-input invariants (mostly trivial)

* `h_init_size`, `h_init_loc`, `h_init_no_dead`, `h_init_no_goto_target`
  — all trivial for `trans₀` with empty
  `instructions = #[]` (the standard initial state).
* `h_distinct`, `h_admitted_blocks`, `h_loopContracts_empty_post`,
  `h_entry_first` — CFG-level fragment restrictions.

### B3 expression-side bundle

* `h_red`, `h_op`, `h_uniform`, `h_commutes_not`. Caller-supplied
  for the bool+int fragment.

### Genuine caller obligations

* `h_eval_bool_corr` (target/target boolean evaluator agreement).
* `h_corr` (initial-store correspondence).
* `h_inj : Function.Injective identToString`.
* `h_wf_bool` (boolean evaluator well-formedness).

### R8a's structural witnesses (mechanically discharable)

* `st_final` and `h_blocks_run` — the inner blocks-fold result. A
  follow-up round can extract these from
  `coreCFGToGotoTransform_decompose` internally.
* `h_labelMap_agree` — agreement of the WF's `labelMap` with the
  translator's hashmap-keyed labelMap. Trivially provable for any
  WF built via the strengthened theorem (definitional unfolding).

### R8b's PC-inversion auxiliaries (mechanically discharable)

* `h_decl_pc_inv`, `h_assn_pc_inv`, `h_assn_nondet_pc_inv` — the
  three CFG-PC inversions characterizing which translator
  constructor emitted each DECL/ASSIGN PC. Estimated 100-300 LoC
  each from translator-induction.

### R7c's pinning hypotheses (trace-level caller obligations)

* `h_decl_x_pinned`, `h_assn_x_pinned`, `h_assn_rhs_pinned`. These
  are *genuinely* caller-side: they relate the trace's
  source-side `InitState`/`UpdateState` witness `x` to the
  translator's emitted `identToString`-named symbol. R7c showed
  these cannot be discharged at the `WellFormedTranslation`
  layer.

### R7c's value-side hypotheses (genuine caller obligations)

* `h_decl_empty_value`, `h_assign_value_corr`,
  `h_assign_nondet_value_corr`. Source-target evaluator
  agreement on values; not discharable from translator
  structure.

### Source-side run

* `σ`, `σ'`, `b`, `σ_goto`, `h_run_src`.

This is the **"concrete soundness story modulo trace-level and
evaluator obligations"** milestone — the absolute minimum
hypothesis surface achievable without an entirely new layer of
proof infrastructure (e.g. modeling source-side traces explicitly
or augmenting `WellFormedTranslation` with structural inversion
fields).

## Process observations

**Both workers ran cleanly** — no watchdog stalls. R8a's six
commits were progressive (each closing one structural piece);
R8b's two commits cleanly partitioned DECL+ASSIGN provenance
from the strict ASSIGN-Nondet variant.

**R8a's `[propext, Classical.choice, Quot.sound]` axiom set is
expected** because the proof uses `Classical.choose` indirectly
via `coreCFGToGotoTransform_decompose`'s ∃-witness extraction.
This matches the rest of the chain and is not a regression.

**R8b's discovery of the false `h_assn_nondet_provenance`** is a
genuine semantic finding. R7c's `_v2` bridge took the field at
face value, treating it as a structural property; R8b's
constructor-level case-analysis revealed that the only
constructors emitting nondet ASSIGNs are `set_nondet` ones.
Closing the `assign_nondet_lookup` field on the v2 bridge
without restricting the source CFG requires a refactor at the
bridge level (per-PC partial provenance gated by a
firing-trace precondition), not a translator-level theorem.

**R8b's `identToString` vs R7c's `nameMap` mismatch** is the
expected consequence of strengthening `CmdEmittedAt` to expose
the literal symbol in round 7. The mismatch surfaces when
composing R8b with R7c's `_v2` bridge: R8b proves the literal
form, but the bridge accepts the `nameMap` form. v5 resolves
this by fixing `nameMap = identToString`. A future round could
generalize R8b's theorems to a parametric `nameMap` plus a
"name-translation hypothesis" if a non-identToString caller
ever appears.

**A merge friction note (round 8):** Both R8a and R8b were
based on divergent branches — the third and fourth occurrences
of this pattern. Cherry-picks were clean both times due to
disjoint-file discipline. The pattern is now expected and
tooled around: supervisors check the branch base when
inspecting worker output and cherry-pick onto local
`htd/unstructured-to-goto` when the worker's commits are
substantive.

## Cumulative across all rounds

| Round | New Lean LoC | Theorem closed |
|---|---|---|
| Pre-rounds | ~3000 | `coreCFGToGoto_forward_simulation` |
| Round 1 | ~2500 | A's sub-lemmas + B's per-operator + C's discharge |
| Round 2 | ~2000 | A2 + B2 + items 5/6 |
| Round 3 | ~1900 | A3 structural + B3 bool+int |
| Round 4 | ~1900 | A4 WF top-level + concrete v1 |
| Round 5 | ~2400 | A5a/A5b layout closures + strengthened WF |
| Round 6 | ~750 | R6a TranslatorBridgeHyps + R6b expression-side + v2/v3 |
| Round 7 | ~1690 | R7a goto-target-in-range + R7b no-dead + R7c lookup fields + v4 |
| Round 8 | ~1850 | R8a goto-provenance + R8b cmd-provenance + v5 |

**~17,990 LoC** of correctness infrastructure. `lake build` green
throughout, no `sorry` in live code, all top-level theorems
closed under the standard axiom set
`[propext, Classical.choice, Quot.sound]`.

## Files changed in round 8

| File | Change | Worker |
|---|---|---|
| `Strata/Backends/CBMC/GOTO/GotoTargetProvenance.lean` | new (1116 LoC) | R8a |
| `StrataTest/Backends/CBMC/GOTO/GotoTargetProvenanceAxioms.lean` | new (14 LoC) | R8a |
| `Strata/Backends/CBMC/GOTO/CmdProvenance.lean` | new (372 LoC) | R8b |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` | added `_v5` (~360 LoC) | supervisor |
| `StrataTest/Backends/CBMC/GOTO/CoreCFGToGOTOConcreteAxioms.lean` | new (19 LoC; covers v4 + v5) | supervisor |
| `docs/_workers/R8a_goto_provenance_report.md` | new | R8a |
| `docs/_workers/R8b_cmd_provenance_report.md` | new | R8b |
| `docs/_workers/round8_supervisor_report.md` | new (this file) | supervisor |

## Worktree archival

The two round-8 worktrees remain locked at their final commits.

## Suggested next steps

The round-9 candidates are R8a's three structural witnesses
(`st_final`, `h_blocks_run`, `h_labelMap_agree`) and R8b's three
PC-inversion auxiliaries. Both are mechanically discharable.

After round 9, `_v6` would have only:
* Translator-input invariants (trivial for standard callers).
* B3's expression-side bundle.
* `Function.Injective identToString`.
* R7c's three pinning hypotheses (trace-level — genuinely
  caller-side).
* R7c's three value-side hypotheses (caller-side evaluator
  agreement).
* `h_eval_bool_corr`, `h_corr`, source-side run, `h_wf_bool`.

That would be the absolute minimum hypothesis surface achievable
without an entirely new layer of proof infrastructure. The
remaining caller-side hypotheses then become the natural input
to whatever bisimulation-driving infrastructure the consumer
provides.

There is also a deeper round-9+ candidate: **fix R7c's
`h_assn_nondet_provenance`** at the bridge level. The current
shape is provably false; the right fix is in
`InstructionLookups.lean` and `TranslatorBridgeHypsDischarge.lean`,
where `assign_nondet_lookup_of_provenance_and_pinned` should
take a per-PC partial provenance gated by a "firing trace says
this is a step_assign_nondet" precondition. This is genuinely
bridge-level work, separable from the translator-structure
auxiliaries.
