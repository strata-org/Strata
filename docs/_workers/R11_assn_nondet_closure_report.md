# R11 — Assign-Nondet PC-Inversion Closure

**Status**: **Tier 2** — closed via Path A (constructor tightening +
small δ_goto well-formedness hypothesis).
**Branch**: worktree-agent-ac500ecc701b4b4ae
**Base commit**: `936122c65` (R10 reconcile)
**Build**: green (585 jobs).
**Axioms on the load-bearing original**:
`#print axioms CProverGOTO.coreCFGToGoto_forward_simulation` →
`[propext, Classical.choice, Quot.sound]` (unchanged).
**Axioms on `_v4`/`_v5`/`_v6`/`_v7`**: same — `[propext,
Classical.choice, Quot.sound]`.

## Outcome

`h_assn_nondet_pc_inv` (R8b's strict `AssignNondetPcInversion`) has
been **removed entirely** from `_v5`/`_v6`/`_v7` of
`coreCFGToGotoTransform_forward_simulation_concrete`. The only new
hypothesis added to the chain is `h_init_extension`, a small
well-formedness assumption on `δ_goto` (fresh-variable monotonicity
across `InitState` — a standard property of any sane evaluator).

The previously [bridge-required] flag on R8b's strict PC-inversion is
discharged.

## What R10c diagnosed and how R11 closes it

R10c (Tier 3) identified the structural obstacle: `step_assign_nondet`
fires for two distinct cases — true nondet (`set_nondet`) and "no-op
padding" (`init_det` after `step_decl`). The latter sidesteps the
`step_assign` δ_goto-eval premise. Any per-PC "rhs is nondet"
witness is provably false in the second case.

R11's fix takes Path A:

1. Add `h_init_extension` (fresh-variable monotonicity of `δ_goto`)
   so that the `init_det` arm of `single_cmd_simulation` can use
   `step_assign` instead of `step_assign_nondet`. The required eval
   witness on σ' is built from the eval witness on σ (via
   `ExprTranslated.value_agree`) lifted through `h_init_extension`.
2. Tighten `StepGoto.step_assign_nondet`'s constructor to require
   `instr.code = Code.assign lhs rhs ∧ rhs.id = .side_effect .Nondet`.
   With `init_det` no longer using this constructor, the only remaining
   firing is `set_nondet`, where the rhs-shape witness is exactly
   what `CmdEmittedAt.set_nondet` already exposes.
3. Reshape `TranslatorBridgeHyps.assign_nondet_lookup` to take
   `h_code` and `h_id` as preconditions (the constructor's witnesses)
   and reduce to a structural `getAssignLhs/getAssignRhs` lookup.
4. Update `InstructionLookups.assign_nondet_lookup_of_provenance_-
   and_pinned` to discharge the new field shape using only
   `h_assn_provenance` (the *non-strict* variant, already used by
   `assign_lookup`) and `h_assn_x_pinned`. No
   `AssignNondetPcInversion` is needed.
5. Drop `h_assn_nondet_pc_inv` from `_v5`/`_v6`/`_v7`.
6. Drop `h_assn_nondet_provenance` from `_v4` and the v2 bridge.

## Files touched

| File | Nature of change |
|------|------------------|
| `Strata/Backends/CBMC/GOTO/Semantics.lean` | Tighten `step_assign_nondet` constructor with rhs-shape fields |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrect.lean` | Add `h_init_extension`; switch `init_det` arm to `step_assign`; thread hypothesis through `block_body_*`, `block_simulation`, `cfgStepStar_to_gotoStar`, `coreCFGToGoto_forward_simulation` |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrectStore.lean` | Thread `h_init_extension` through `_storeCorr` |
| `Strata/Backends/CBMC/GOTO/Bisim.lean` | (no change — `stepGoto_assign_nondet_to_stepInstr` still takes `h_rhs_nondet` as an argument; the constructor's `h_id` witness is passed to it directly from the discharge) |
| `Strata/Backends/CBMC/GOTO/SteppingBridgesDischarge.lean` | Reshape `TranslatorBridgeHyps.assign_nondet_lookup`; update consumer pattern |
| `Strata/Backends/CBMC/GOTO/InstructionLookups.lean` | Rewrite `assign_nondet_lookup_of_provenance_and_pinned` for new field shape; uses `h_assn_provenance` (not strict variant) |
| `Strata/Backends/CBMC/GOTO/TranslatorBridgeHypsDischarge.lean` | Update v1 + v2 bridges; drop `h_assn_nondet_provenance` parameter from v2 |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` | Add `h_init_extension`; drop `h_assn_nondet_pc_inv` from `_v5`/`_v6`/`_v7`; drop `h_assn_nondet_provenance` from `_v4`; update docstrings |

## Hypothesis surface change on `_v7`

**Removed**:
- `h_assn_nondet_pc_inv` (one universally-quantified bundle requiring
  R8b's strict PC inversion which was provably false in general).

**Added**:
- `h_init_extension` (~6 lines, expressing
  "if `InitState σ x v_init σ'` and `δ_goto σ e = some v` then
  `δ_goto σ' e = some v`"). Any concrete evaluator that's monotone
  on fresh-variable extensions discharges it directly.

Net: surface shrinks (the new hypothesis is dramatically smaller
than the old one and is universally well-known to hold for any sane
evaluator).

## Why "Tier 2" not "Tier 1"

The supervisor's spec said:

> Tier 1: `h_assn_nondet_pc_inv` removed from `_v7`. `lake build`
> green. Axioms unchanged on the original simulation theorem.
> *Possibly with a small new well-formedness hypothesis on the
> evaluator.*

Tier 2 is described as: "A small auxiliary remains (e.g., a
`WellFormedSemanticEvalGotoExtension`-style hypothesis)".

Reading the spec's Tier 1 description, "possibly with a small new
well-formedness hypothesis" appears to be permitted under Tier 1.
But strictly, since I added one new such hypothesis, I'll classify
this as Tier 2 to be conservative. Either way, the closure is
complete and the new hypothesis is reasonable.

## Verification

### Build status

```
$ lake build
Build completed successfully (585 jobs).
```

### Axiom check

```
$ lake env lean StrataTest/Backends/CBMC/GOTO/CoreCFGToGOTOConcreteAxioms.lean
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v4' depends on axioms: [propext, Classical.choice, Quot.sound]
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v5' depends on axioms: [propext, Classical.choice, Quot.sound]
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v6' depends on axioms: [propext, Classical.choice, Quot.sound]
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v7' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```
# coreCFGToGoto_forward_simulation (the load-bearing original)
'CProverGOTO.coreCFGToGoto_forward_simulation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All axioms exactly `[propext, Classical.choice, Quot.sound]`. No
project-internal axioms introduced.

## Commits

```
b79c14c1b docs(goto-correct): R11 - update _v6 docstring after dropping h_assn_nondet_pc_inv
e43cfda5f fix(goto-correct): R11 - update v1 bridge h_assign_nondet_lookup arity
628ed7cb3 feat(goto-correct): R11 step 3 - drop h_assn_nondet_pc_inv from v5/v6/v7
1a3ed9627 feat(goto-correct): R11 step 2 - tighten step_assign_nondet rhs-shape
5869e46b7 feat(goto-correct): R11 step 1 - switch init_det arm to step_assign
```

## Vestigial declarations kept

The following declarations from R8b are no longer used by the chain
but are *retained* in `CmdProvenance.lean`:

- `AssignNondetPcInversion` (the strict per-PC nondet-cmd inversion).
- `assn_nondet_provenance_of_translator_strict` (the structural
  theorem deriving the strict provenance from the inversion).

They're left in place because (a) they are still standalone valid
facts, and (b) cleanup is out of scope for R11. A follow-up could
delete them if no test ever exercises them.

## Summary

R11 closes the only remaining `[bridge-required]` hypothesis on
`_v7`. The fix is a clean structural change: tightening
`step_assign_nondet`'s constructor (matching the pattern of
`step_assign`) and adding one small well-formedness assumption on
`δ_goto`. Axioms on the load-bearing original simulation theorem are
unchanged, and the chain `_v4`/`_v5`/`_v6`/`_v7` now have a tighter
hypothesis surface.
