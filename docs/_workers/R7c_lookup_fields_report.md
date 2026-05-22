# Worker R7c — Lookup-Field Discharges

**Branch:** worktree off `htd/unstructured-to-goto`
**Goal:** Close R6a's three lookup-field caller passthroughs:
- `decl_lookup_of_wf` — DECL.code symbol matches `nameMap x`
- `assign_lookup_of_wf` — ASSIGN.code lhs symbol matches `nameMap x` AND
  rhs matches the GOTO translation
- `assign_nondet_lookup_of_wf` — ASSIGN.code lhs symbol matches
  `nameMap x` AND rhs is `Code.side_effect Nondet`

## Outcome

**Tier 3 (Acceptable).** Each lookup field is now closed via a small
bridge lemma (`InstructionLookups.lean`) that takes structured
auxiliary hypotheses **strictly smaller** than the original field. The
auxiliary hypotheses split the original obligation into:

1. **Per-PC structural witnesses** (`*_provenance`) — at every DECL/
   ASSIGN PC, the GOTO code matches the translator's emit shape
   (carrying a specific source-cmd variable `v_src`). Mechanically
   discharable from `wf.layout_block_body` + the strengthened
   `CmdEmittedAt` (round-7 prereq) + a CFG-PC inversion lemma (deferred
   to a follow-up round, ~100-200 LoC).

2. **Per-firing trace-level witnesses** (`*_pinned`) — for any
   `InitState`/`UpdateState` firing at this PC, `x` equals the
   source-cmd's variable `v_src`. Caller-side bisimulation invariant;
   irreducible at the WF layer.

## Why the original fields cannot be discharged from `wf` alone

R6a flagged the obstacle precisely. Restating with concrete
detail:

The `decl_lookup` field is universally quantified over `pc, x, σ, σ',
v` with `InitState σ x v σ'`. The conclusion fixes the GOTO code's
symbol (a function of `pc` only) to `nameMap x`. By injectivity of
`nameMap`, this forces `x` to be the unique source-cmd variable at
that PC — but the field type itself does not pin `x` to that variable;
the firing's `x` is free.

Concretely: at any DECL PC, the translator emits `Code.decl
(Expr.symbol (identToString v_src) gty)` for a specific `v_src` (the
source-CFG init cmd's variable). For this code to match `nameMap x`
for *any* `x` satisfying `InitState`, we need `x = v_src` for every
valid InitState at this PC. But `InitState σ x v σ'` only requires
`σ x = none`, which can be satisfied by many `x` values for a partial
store `σ`.

Therefore the field is **provably false** for arbitrary callers; it's
*only* true at the simulation-level where `x` is constrained by the
source-side step.

## What this round delivers

### 1. Strengthened `CmdEmittedAt` (Option 1)

`CoreCFGToGOTOInvariants.lean`. The `init_det`, `init_nondet`,
`set_det`, `set_nondet` constructors now carry:

* `init_det`: `h_decl_code : i_decl.code = Code.decl (Expr.symbol
  (identToString v) gty)` and `h_assn_code : i_assn.code = Code.assign
  (Expr.symbol (identToString v) gty) e_goto`. The `gty` is now an
  explicit constructor argument.
* `init_nondet`: same `h_decl_code` (no assn).
* `set_det`: same `h_assn_code`.
* `set_nondet`: `h_assn_code : ∃ e_nondet, i_assn.code = Code.assign
  (Expr.symbol (identToString v) gty) e_nondet ∧ e_nondet.id =
  .side_effect .Nondet ∧ e_nondet.type = gty`.

The existential `∃ lhs, ...` has been replaced with a fixed
`Expr.symbol (identToString v) gty` shape. The `lhs` is now uniquely
determined by the source-cmd's variable `v` and the translator's
ident-to-string function.

Updated builders (`cmdEmittedAt_init_det` etc.) and drivers
(`cmdEmittedAt_init_det_of_toGotoInstructions` etc.) to provide and
harvest the strengthened evidence. The strengthening of
`Cmd_toGotoInstructions_set_nondet_ok`'s shape lemma is included in
the same file. `CoreCFGToGOTOCorrect.lean`'s pattern-matches on
`CmdEmittedAt` cases were updated to thread the new args.

### 2. `Code.assign`, `Code.decl`, `Expr.symbol` made `@[expose]`

So that the bridge lemmas in `InstructionLookups.lean` can reduce
`getSymbolName/getAssignLhs/getAssignRhs` to the underlying
string/expression. One-token additions to `Code.lean` and `Expr.lean`.
Safe — these are simple non-recursive constructors.

### 3. New file: `Strata/Backends/CBMC/GOTO/InstructionLookups.lean`

Three theorems:

* `decl_lookup_of_provenance_and_pinned (pgm nameMap _h_inj
  h_decl_provenance h_x_pinned) : decl_lookup field`
* `assign_lookup_of_provenance_and_pinned (pgm δ_goto nameMap _h_inj
  h_assn_provenance h_x_pinned h_rhs_pinned) : assign_lookup field`
* `assign_nondet_lookup_of_provenance_and_pinned (pgm nameMap _h_inj
  h_assn_nondet_provenance h_x_pinned) : assign_nondet_lookup field`

Each takes structured auxiliary hypotheses (provenance + pinned) and
produces the lookup field. Internal proof: small calculation rewriting
to `getSymbolName/getAssignLhs/getAssignRhs` of the explicit
record-literal forms; closed by `rfl`.

`lake build` green; axioms `[propext, Quot.sound]` (no `Classical.choice`
because the lemmas don't need it locally).

### 4. v2 bridge in `TranslatorBridgeHypsDischarge.lean`

`wellFormedTranslation_to_translatorBridgeHyps_v2` mirrors v1's
signature except that the three lookup fields are replaced with:

* 3 provenance hypotheses (`h_decl_provenance`, `h_assn_provenance`,
  `h_assn_nondet_provenance`),
* 3 pinning hypotheses (`h_decl_x_pinned`, `h_assn_x_pinned`,
  `h_assn_rhs_pinned`).

The body delegates to v1 with the lookup fields built via
`InstructionLookups.*_of_provenance_and_pinned`. Net hypothesis count
goes up by 3 (5 instead of 3), but each new hypothesis has narrower
quantifier scope and a more localised proof obligation.

`lake build` green; axioms on v2:
`[propext, Classical.choice, Quot.sound]` (same as
`coreCFGToGoto_forward_simulation`).

## Files added / changed

* **Added** `Strata/Backends/CBMC/GOTO/InstructionLookups.lean`
  (~310 LoC).
* **Changed** `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOInvariants.lean`
  — strengthened `CmdEmittedAt` constructors (~50 LoC of additional
  per-constructor structure).
* **Changed** `Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean`
  — updated builders, drivers, and shape lemma for set_nondet
  (~120 LoC of additions/edits).
* **Changed** `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrect.lean`
  — pattern-match argument count adjustments (4 small `_` insertions).
* **Changed** `Strata/Backends/CBMC/GOTO/TranslatorBridgeHypsDischarge.lean`
  — added v2 bridge (~140 LoC).
* **Changed** `Strata/Backends/CBMC/GOTO/Code.lean` (+`@[expose]` on
  `assign`, `decl`),
  `Strata/Backends/CBMC/GOTO/Expr.lean` (+`@[expose]` on `symbol`).

## Build verification

```
$ lake build
Build completed successfully (585 jobs).

$ lake env lean tmp/axiom_check.lean
'CProverGOTO.InstructionLookups.decl_lookup_of_provenance_and_pinned'
  depends on axioms: [propext, Quot.sound]
'CProverGOTO.InstructionLookups.assign_lookup_of_provenance_and_pinned'
  depends on axioms: [propext, Quot.sound]
'CProverGOTO.InstructionLookups.assign_nondet_lookup_of_provenance_and_pinned'
  depends on axioms: [propext, Quot.sound]
'CProverGOTO.TranslatorBridgeHypsDischarge.wellFormedTranslation_to_translatorBridgeHyps_v2'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'CProverGOTO.coreCFGToGoto_forward_simulation'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

`coreCFGToGoto_forward_simulation` axiom set unchanged.

## Suggested next steps

To close the provenance hypotheses from `wf` (raising R7c from Tier 3
to Tier 1):

1. **Add a `WellFormedTranslation.pc_to_block_cmd` field** (or
   companion lemma) that maps every PC carrying a body instruction
   (DECL/ASSIGN/ASSERT/ASSUME) back to a unique `(l, blk, k)` triple
   such that `(l, blk) ∈ cfg.blocks`, `labelMap l = some pc_l`, and
   `pc = pc_l + 1 + cmdsPrefixInstrCount blk.cmds k`.

2. **Compose** `pc_to_block_cmd` with `layout_block_body` to get the
   CmdEmittedAt witness for any DECL/ASSIGN PC.

3. **Pattern-match** on the strengthened `CmdEmittedAt` cases to
   extract the source-cmd's variable and the explicit code shape.

This is mechanical from the translator's loop induction (each emit
step preserves a PC-to-block-cmd map). Estimated 100-200 LoC.

The pinning hypotheses (`*_x_pinned`, `*_rhs_pinned`) are genuinely
trace-level and cannot be discharged from WF; they live at the
simulation consumer's level (e.g., in
`CoreCFGToGOTOConcrete.coreCFGToGotoTransform_forward_simulation_concrete_v3`,
where source-side `EvalCmd` and target-side `step_decl/step_assign`
are coupled by bisimulation invariants).

## Status checklist

- [x] Report stub.
- [x] Read all required context (R6a report, round-6 supervisor
      report, `CmdEmittedAt`, builders, `Cmd.toGotoInstructions`,
      `TranslatorBridgeHyps`).
- [x] Strengthen `CmdEmittedAt` (Option 1 from supervisor prompt).
- [x] Update builders + drivers + Correct.lean pattern-matches.
- [x] Write `InstructionLookups.lean` with three bridge lemmas.
- [x] Wire through `wellFormedTranslation_to_translatorBridgeHyps_v2`.
- [x] `lake build` green.
- [x] Axiom set verified ([propext, Classical.choice, Quot.sound] on
      v2; `coreCFGToGoto_forward_simulation` unchanged).
- [x] Final report.
