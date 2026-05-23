# Worker R9 — PC inversion theorems

**Round:** 9
**Branch base:** `htd/unstructured-to-goto` (HEAD `938639db1`)
**Worktree:** *worked directly in `/Users/htd/Documents/Strata-goto`* (the
intended worktree path was already in use).
**Commits added:**

* `877b15f24` — `feat(goto-correct): R9 - close DECL/ASSIGN PC
  inversions via translator induction` (new file `PcInversion.lean`,
  ~1380 LoC + report stub)
* `36cda3b78` — `feat(goto-correct): R9 - v6 internalises DECL/ASSIGN
  PC inversions` (`_v6` in `CoreCFGToGOTOConcrete.lean`, ~290 LoC)

## Tier outcome

**Tier 2 (Good)** — closure of the two non-strict R8b inversions
(`DeclPcInversion`, `AssignPcInversion`) modulo a single, trivial
auxiliary hypothesis (`h_init_empty_decl_assign`); strict
`AssignNondetPcInversion` *not* closed because it is provably false
in general per R8b's prior finding.

## What's in each theorem

### `Strata/Backends/CBMC/GOTO/PcInversion.lean` (new file)

* **`BodyPcCovered`** predicate over a translator state and target
  program: every PC in `trans.instructions` carrying DECL or ASSIGN
  has a corresponding `CmdEmittedAt` witness over the target program
  at the right offset (PC for DECL/set; PC-1 for init_det's ASSIGN).

* **Push/append preservation primitives**
  (`push_preserves_body_pc_covered`,
  `append_two_preserves_body_pc_covered`) that handle the
  in-bounds/at-fresh-slot/out-of-bounds cases.

* **Per-translator-step preservation** mirroring the round-7/8
  templates:
  * `toGotoInstructions_preserves_body_pc_covered` — covers all 7
    `Imperative.Cmd` shapes (init_det, init_nondet, set_det, set_nondet,
    assert, assume, cover); each emit's new DECL/ASSIGN positions are
    covered by `cmdEmittedAt_*_of_toGotoInstructions` lemmas already
    in `CoreCFGToGotoTransformWF.lean`.
  * `coreCFGToGotoCmdStep_preserves_body_pc_covered` — handles `.cmd`
    (delegates to above) and `.call` (FUNCTION_CALL, not body).
  * `cmdsFoldlM_preserves_body_pc_covered` — induction over cmd lists.
  * `emitLabel_preserves_body_pc_covered` — LOCATION (no body).
  * `emitCondGoto_preserves_body_pc_covered`,
    `emitUncondGoto_preserves_body_pc_covered` — GOTO (no body).
  * `endFunction_emit_preserves_body_pc_covered` — END_FUNCTION
    (no body).
  * `coreCFGToGotoBlockStep_preserves_body_pc_covered` — composes
    emitLabel + cmdsFoldlM + transfer-emit.
  * `blocksFoldlM_preserves_body_pc_covered` — induction over the
    outer blocks fold.

* **Patcher preservation**
  (`cmdEmittedAt_preserved_target_only`,
  `patchGotoTargets_preserves_body_pc_covered`) — `CmdEmittedAt` is
  preserved when the program changes only target fields, since each
  constructor only references type/guard/code.

* **Top-level theorems**:
  * `declPcInversion_of_translator` — given the standard input
    invariants, every DECL PC in `ans.instructions` has a `CmdEmittedAt`
    witness at the same PC.
  * `declPcInversion_of_translator_abbrev` — same packaged as the
    `CmdProvenance.DeclPcInversion` abbrev R8b expects.
  * `assignPcInversion_of_translator` — every ASSIGN PC is either
    offset-0 of a `set _ _ _` cmd or offset-1 of an `init _ _ (.det _) _`
    cmd.
  * `assignPcInversion_of_translator_abbrev` — same packaged as
    `CmdProvenance.AssignPcInversion`.

* **Strict ASSIGN-Nondet** documented as not closeable here; module
  docstring explains the bridge-level refactor needed.

### `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` (extension)

* **`coreCFGToGotoTransform_forward_simulation_concrete_v6`** — drops
  `_v5`'s `h_decl_pc_inv` and `h_assn_pc_inv` arguments and discharges
  them internally via R9's two top-level theorems. Adds a single
  small input `h_init_empty_decl_assign`. Keeps `h_assn_nondet_pc_inv`
  (the strict variant) since it cannot be closed at the
  translator-structure layer.

### `StrataTest/Backends/CBMC/GOTO/CoreCFGToGOTOConcreteAxioms.lean`

Adds an axiom-check `#print axioms` for `_v6`.

## Verified axioms

```
'CProverGOTO.PcInversion.declPcInversion_of_translator'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'CProverGOTO.PcInversion.assignPcInversion_of_translator'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'CProverGOTO.PcInversion.declPcInversion_of_translator_abbrev'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'CProverGOTO.PcInversion.assignPcInversion_of_translator_abbrev'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v4'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v5'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v6'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

All three of v4, v5, v6 use **exactly** the standard axiom set
`[propext, Classical.choice, Quot.sound]` — the same axioms as
`coreCFGToGoto_forward_simulation`. No additional axioms introduced.

## Build verification

```
$ lake build
Build completed successfully (585 jobs).
```

Same job count as round 8 — no jobs added (the new file is incremental
to the existing chain). `lake build` green at every commit.

## Obstacles and trade-offs

### `BodyPcCovered` as `def` vs `abbrev`

The predicate is a `def`. When passing a `BodyPcCovered ...` term to
the inductive hypothesis (which expects another `BodyPcCovered ...`),
Lean's elaborator unfolded the definition and treated the term as a
function expecting the implicit `pc, instr` arguments. The fix was to
intro `pc instr h_at` first and apply `ih ... h_cov' h_at`. This is a
standard idiom — the existing GotoTargetProvenance pattern used the
same trick.

### Strict `AssignNondetPcInversion` not closed

Per R8b's report, the strict form requires that *every* ASSIGN PC be
exactly a `set _ .nondet _` cmd-start. This is **provably false** for
any source CFG containing a `.set _ (.det _) _` or `.init _ _ (.det _) _`
cmd, since those constructors emit ASSIGNs whose rhs is a translated
source expression. Closing the v2 bridge cleanly requires the
bridge-level refactor noted in
`docs/CoreToGOTO_ProofStatusRound8.md` (per-firing-trace gating in
`InstructionLookups.lean`/`TranslatorBridgeHypsDischarge.lean`), not
a translator-level theorem. Therefore the strict
`AssignNondetPcInversion` remains on `_v6`.

### `h_init_empty_decl_assign` as a new hypothesis

R9 introduces this single new hypothesis stating that
`trans₀.instructions` carries no DECL or ASSIGN at any PC. This is
**trivially true** for the standard caller whose `trans₀` has
`instructions := #[]`. It's surfaced as an explicit hypothesis (rather
than baked into a "standard initial state" theorem) to keep the
deliverable auditable. A future round could combine it with the
existing `h_init_no_dead`/`h_init_no_goto_target` invariants into a
single "`trans₀` is the empty initial state" predicate.

## What `_v6` delivers

After R9, the only "structural" hypotheses on
`coreCFGToGotoTransform_forward_simulation_concrete_v6` are:

| Hypothesis | Status | Notes |
|---|---|---|
| `h_init_size`, `h_init_loc`, `h_init_no_dead`, `h_init_no_goto_target`, **`h_init_empty_decl_assign`**, `h_distinct`, `h_admitted_blocks`, `h_loopContracts_empty_post`, `h_entry_first` | **[trivial]** | All trivial for the standard `trans₀` |
| `h_red`, `h_op`, `h_uniform`, `h_commutes_not` | **[caller-irreducible]** | B3 expression-side bundle |
| `callResult`, `eval`, `fenv`, `h_eval_bool_corr`, `h_inj`, `h_wf_bool` | **[caller-irreducible]** | Worker C parameters |
| `st_final`, `h_blocks_run`, `h_labelMap_agree` | **[mechanical-deferred]** | R8a's structural witnesses; remain |
| `h_assn_nondet_pc_inv` | **[bridge-required]** | Strict variant; provably false in general |
| `h_decl_x_pinned`, `h_assn_x_pinned`, `h_assn_rhs_pinned` | **[caller-irreducible]** | Trace-level pinning |
| `h_decl_empty_value`, `h_assign_value_corr`, `h_assign_nondet_value_corr` | **[caller-irreducible]** | Source/target evaluator agreement |
| `σ`, `σ'`, `b`, `σ_goto`, `h_corr`, `h_run_src` | **[caller-irreducible]** | Source-side run + initial-store |

The two **[mechanical-deferred]** auxiliaries that R9 closed
(`h_decl_pc_inv`, `h_assn_pc_inv`) are gone from `_v6`. The remaining
**[mechanical-deferred]** items (R8a's three structural witnesses) are
the natural target for a follow-up R10.

## Suggested next steps

1. **R10: internalise R8a's three structural witnesses.** Make `_v7`
   recover `st_final`, `h_blocks_run`, `h_labelMap_agree` internally
   from `coreCFGToGotoTransform_decompose` plus a uniqueness-of-WF-labelMap
   lemma. Estimated 200-300 LoC.

2. **Bridge-level refactor for `AssignNondetPcInversion`**: rewrite
   `assign_nondet_lookup_of_provenance_and_pinned` in
   `InstructionLookups.lean` to take a per-PC partial provenance gated
   on a `step_assign_nondet`-firing precondition. Then re-thread
   through `TranslatorBridgeHypsDischarge.lean`'s `_v2` bridge. This
   is the cleanest fix for the v2 bridge's incorrect universal
   `assign_nondet_lookup` field.

After (1) and (2), the only **[mechanical-deferred]** entry in the
table above would be gone, and the remaining hypotheses would all be
**[caller-irreducible]** — the absolute minimum hypothesis surface.

## Status checklist

- [x] Verify branch base (`938639db1`).
- [x] Write report stub.
- [x] Read R8a/R8b reports + ProofStatusRound8 doc.
- [x] Read `NoDead.lean` and `GotoTargetProvenance.lean` patterns.
- [x] Read `CmdProvenance.lean` to understand the inversion abbrevs.
- [x] Read `CoreCFGToGotoTransformWF.lean` for translator-fold
      preservation idioms (especially `cmdEmittedAt_*_of_toGotoInstructions`).
- [x] Add `Strata/Backends/CBMC/GOTO/PcInversion.lean` with
      `BodyPcCovered` + preservation lemmas + two top-level theorems.
- [x] Add `_v6` in `CoreCFGToGOTOConcrete.lean`.
- [x] Update axiom-check test for `_v6`.
- [x] Verify `lake build` is green at every commit (585 jobs).
- [x] Verify axiom set unchanged on all three concrete theorems
      (`[propext, Classical.choice, Quot.sound]`).
- [x] Document the strict ASSIGN-Nondet finding (deferred per R8b).
- [x] Final report.
