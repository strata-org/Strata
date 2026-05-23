# R10c — Assign-Nondet Bridge Refactor

**Branch**: `worker-r10c-assign-nondet-bridge` (worktree)
**Status**: **Tier 3** (refactor proves intractable in scope; obstacle documented)
**Base commit**: `5aab65adac45977e011f44f2308a209f631aab96`
**Build**: green at baseline; no functional changes committed (see "Outcome").

## Goal

Restructure the `assign_nondet_lookup` field of `TranslatorBridgeHyps`
so that the strict `AssignNondetPcInversion` hypothesis (currently
required by `_v6` of `coreCFGToGotoTransform_forward_simulation_concrete`
in `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` around line
982) becomes unnecessary.

## What I investigated

1. `Strata/Backends/CBMC/GOTO/InstructionLookups.lean` — existing
   `assign_nondet_lookup_of_provenance_and_pinned` (line 293).
2. `Strata/Backends/CBMC/GOTO/TranslatorBridgeHypsDischarge.lean` —
   existing `wellFormedTranslation_to_translatorBridgeHyps_v2` (line
   260) and the field types it constructs.
3. `Strata/Backends/CBMC/GOTO/SteppingBridgesDischarge.lean` — both
   the `TranslatorBridgeHyps.assign_nondet_lookup` field (line 187)
   and the consumer at `step_assign_nondet h_at h_ty h_upd =>` (line
   357–363).
4. `Strata/Backends/CBMC/GOTO/Bisim.lean` — the per-step bridge
   `stepGoto_assign_nondet_to_stepInstr` (line 520) and its required
   `h_rhs_nondet : rhs_g.id = .side_effect .Nondet` premise.
5. `Strata/Backends/CBMC/GOTO/Semantics.lean` — the
   `StepGoto.step_assign_nondet` constructor (line 193). Confirmed
   it does **not** carry any rhs-shape witness at the constructor
   level.
6. `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrect.lean` — the
   `single_cmd_simulation` theorem (line 172) and specifically the
   `init_det` arm (line 189–214) which uses
   `step_assign_nondet … h_assn_at h_assn_ty h_upd_self` as a
   **no-op padding** for the second instruction emitted by an
   `.init v ty (.det e_core) md` source command.
7. `Strata/Backends/CBMC/GOTO/CmdProvenance.lean` — R8b's strict
   `AssignNondetPcInversion` (line 327) and
   `assn_nondet_provenance_of_translator_strict` (line 345).

## The obstacle

The supervisor's hint suggests reshaping the bridge field so it
takes a per-PC precondition "this firing is from `step_assign_nondet`
and the GOTO rhs is `.side_effect .Nondet`", with the witness
"naturally available wherever `step_assign_nondet` is matched."

Investigation revealed this witness is **not naturally available**.
The reason is structural and load-bearing:

### `step_assign_nondet` fires for two semantically distinct cases

`single_cmd_simulation` (`CoreCFGToGOTOCorrect.lean`, lines 188–240)
introduces `StepGoto.step_assign_nondet` from **two** different
source-side cmd kinds, against **two** different `CmdEmittedAt`
layouts:

| Source cmd | Layout | GOTO rhs | Note |
|------------|--------|----------|------|
| `.set v .nondet md` | `set_nondet` | `e_nondet.id = .side_effect .Nondet` | True nondet firing. |
| `.init v ty (.det e_core) md` | `init_det` | `e_goto = exprTrans e_core` (translated rhs, **NOT** nondet) | "No-op padding" via `UpdateState_self`. |

For the second case (`init_det`), `single_cmd_simulation`'s comment
explicitly states (lines 195–200):

> `step_assign_nondet` (rather than `step_assign`) on σ' as a no-op
> via `UpdateState_self`. We sidestep the δ_goto evaluation premise
> of `step_assign` (which would otherwise require expression-evaluator
> monotonicity from σ to σ'). `step_assign_nondet` only requires
> `instr.type = .ASSIGN`, …

So `init_det` deliberately uses `step_assign_nondet` as a "weak" step
that doesn't constrain the GOTO rhs — precisely because the
correctness proof of `step_assign` (monotonicity of `δ_goto` across
the preceding DECL's store mutation) is open elsewhere.

### Consequence for the bridge field

In the consumer (`steppingBridges_of_translator.step_running` arm
`step_assign_nondet`), we cannot supply a per-firing precondition
"this PC has a nondet rhs" because:

* For the `set_nondet` source cmd, the precondition holds.
* For the `init_det` source cmd, the precondition is **false** — the
  GOTO rhs is a translated source expression `exprTrans e_core`, not
  `.side_effect .Nondet`.

Both kinds of firings fire `step_assign_nondet` against the **same
bridge field**. The field cannot demand a nondet rhs witness because
in the `init_det` case the witness doesn't exist.

This is exactly why R8b's strict `AssignNondetPcInversion` is
provably false in general — it requires every ASSIGN PC to be a
`set_nondet` cmd-start, which excludes the `init_det` case.

## Why a "trace precondition" doesn't help

The supervisor's hint suggests pushing the witness up to a
trace-level precondition. But the `init_det` case generates a
`step_assign_nondet` firing whose underlying GOTO instruction is
**not nondet**. So no trace-level invariant can produce the
precondition for that firing — it would have to claim the firing's
rhs is nondet, which contradicts the actual translator output.

## What WOULD work, and why it's out of scope

The clean architectural fix is to **change `single_cmd_simulation`'s
`init_det` arm to use `StepGoto.step_assign` instead of
`step_assign_nondet`**. This requires producing a `δ_goto σ' e_goto =
some v_init` witness — i.e., proving GOTO-side evaluator monotonicity
across a preceding DECL's store mutation. The current code
deliberately sidesteps this by using `step_assign_nondet` as a no-op.

Alternative fixes:

1. **Tighten `StepGoto.step_assign_nondet`**: Add
   `rhs.id = .side_effect .Nondet` as a premise on the GOTO
   instruction's rhs. This breaks `single_cmd_simulation.init_det` —
   forcing the cleanup above.
2. **Reshape `single_cmd_simulation` to produce different bridges
   for `init_det` vs `set_nondet`**: The `init_det` arm uses
   `step_assign` (with a monotonicity-derived eval witness), the
   `set_nondet` arm uses the existing `step_assign_nondet` path.
   Same monotonicity prerequisite.
3. **Carry the source-side `CmdEmittedAt` shape down to the
   consumer**: Plumb the layout context through `StepGotoStar_to_-
   ExecProg`'s induction, allowing the consumer to case-split on
   `init_det` vs `set_nondet` and produce different `StepInstr`
   steps. Major surgery; reshapes the trace-lift's invariants.

All three are upstream changes that go beyond the bridge-field
refactor R10c was scoped to. The supervisor's task description even
flags R10c as "the riskiest of the three workers" with explicit
permission to declare Tier 3 if the consumer's elimination
structure can't supply the precondition cleanly.

## What I committed

**Nothing functional.** Only this report.

The work I did:

* Read all relevant files (above).
* Built the project at baseline (`lake build` green).
* Drafted three potential refactor shapes (per-PC precondition,
  disjunctive case split, tightened constructor). None close
  cleanly without addressing the `init_det` no-op.

## Recommendation for the supervisor

Two ways forward:

1. **Tier-3 acceptance for now.** Keep `h_assn_nondet_pc_inv` on
   `_v6` as a documented "structural debt" and note in the
   end-to-end docs that this hypothesis is provably false for
   programs containing `set _ (.det _) _` or
   `init _ _ (.det _) _` cmds. The strict inversion is
   discharable only for restricted source CFGs (purely-nondet
   ASSIGNs).
2. **Open a follow-up worker R11 to address the `init_det`
   no-op.** Either prove `δ_goto` monotonicity across `step_decl`,
   or reshape `single_cmd_simulation` to split the `init_det` and
   `set_nondet` arms into different bridge paths. Once that lands,
   `step_assign_nondet` can be tightened to carry the nondet-rhs
   witness, and the bridge field can be reshaped per the
   supervisor's original spec.

The R11 prerequisite (monotonicity of `δ_goto` across `step_decl`)
is interesting in its own right — it's a corollary of the
`StoreCorr`-respect of `δ_goto` for the `valueCorrCore` instance —
and may already be partially proven in `ExprTranslationPreservesEval`
or similar. A follow-up worker could check.

## Files touched in this branch

* `docs/_workers/R10c_assign_nondet_bridge_refactor_report.md` (new)

No other files were modified.

## Axiom check (baseline)

Not run because no functional changes were made. The axioms on
`_v6` at the baseline commit are (per R9's report):
`[propext, Classical.choice, Quot.sound]`.
