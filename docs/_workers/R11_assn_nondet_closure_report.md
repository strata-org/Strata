# R11 — Assign-Nondet PC-Inversion Closure (stub)

**Status**: WIP — plan stub.
**Branch**: worktree-agent-ac500ecc701b4b4ae
**Base commit**: 936122c65 (R10 reconcile)

## Goal

Eliminate `h_assn_nondet_pc_inv` from `coreCFGToGotoTransform_forward_simulation_concrete_v7` (and `_v6`). This is the only `[bridge-required]` hypothesis remaining on `_v7`.

## Diagnosis (per R10c)

`StepGoto.step_assign_nondet` fires for two semantically distinct cases:

| Source cmd | Layout | GOTO rhs |
|---|---|---|
| `.set v .nondet md` | `set_nondet` | `.side_effect .Nondet` ✓ |
| `.init v ty (.det e_core) md` | `init_det` | `exprTrans e_core` (NOT nondet) |

The second case uses `step_assign_nondet` as a **no-op padding** via `UpdateState_self`, sidestepping the `δ_goto`-evaluation premise of `step_assign`.

This is why a per-PC "rhs is nondet" precondition is impossible: in the `init_det` case, the rhs *isn't* nondet.

## Plan (Path A — `δ_goto`-monotonicity across `step_decl`)

1. **Plan stub written** (this file).
2. **Add monotonicity lemma**: prove
   `δ_goto σ e_goto = some v → InitState σ x v_init σ' → σ x = none → δ_goto σ' e_goto = some v`
   under a well-formedness assumption that `δ_goto` only depends on the in-store values of free variables (i.e., a `WellFormedSemanticEvalGotoExprCongr` style hypothesis). This is the standard "evaluator is congruent on the store" property.

   The cleanest form: take a hypothesis `h_wf_congr : WellFormedSemanticEvalGotoExprCongr δ_goto`, reduce the goal to "σ and σ' agree on getVars e_goto". σ' agrees with σ on all `y ≠ x` (by `InitState`). For `y = x`, σ x = none and σ' x = some v_init differ, but if `x ∈ getVars e_goto`, then `δ_goto σ e_goto` would have to read `none` from `σ` for `x` — and a well-formed evaluator that returns `some v` must not depend on undefined variables.

   Concretely the requirement is: "if `x ∉ getVars e` or σ y agrees with σ' y on all y in getVars e_goto, then δ σ e = δ σ' e". This is `WellFormedSemanticEvalExprCongr` lifted to `δ_goto`.

3. **Switch single_cmd_simulation.init_det** to use `step_assign` (with the monotonicity-derived eval witness on `σ'`) instead of `step_assign_nondet`.

4. **Tighten `StepGoto.step_assign_nondet` constructor** to require `rhs.id = .side_effect .Nondet` on the GOTO instruction (extracted from `instr.code` as a `Code.assign _ rhs`). This makes the constructor structurally exclude the "no-op padding" usage.

5. **Update `Bisim.stepGoto_assign_nondet_to_stepInstr`** to use the constructor's rhs-shape field instead of taking `h_rhs_nondet` as a separate premise.

6. **Reshape `TranslatorBridgeHyps.assign_nondet_lookup`** — the precondition can now require the constructor's rhs witness.

7. **Drop `h_assn_nondet_pc_inv`** from `_v6` and `_v7`.

## Risks

- The monotonicity lemma might require a new well-formedness hypothesis on `δ_goto` (a `WellFormedSemanticEvalGotoExprCongr`-style assumption). This is acceptable per supervisor — a hypothesis on the evaluator is standard.
- The `e_goto` we use is the translated `e_core`. We need to know `getVars e_goto` doesn't include `x`. This is exactly what `WellFormedSemanticEvalExprCongr δ_goto` gives us, *combined with* the source-side fact that `δ σ e_core = some v` and `σ x = none`.
- Alternatively, since `ExprTranslated` carries `value_agree`, we can do everything on the source side: `δ σ e_core = some v` + `σ x = none` + `WellFormedSemanticEvalExprCongr δ` → `δ σ' e_core = some v` → (via value_agree) `δ_goto σ' e_goto = some v`. **This is the cleaner path** — only need a hypothesis on `δ` (which we already have access to).

## Files to touch

- `Strata/Backends/CBMC/GOTO/Semantics.lean` — tighten `step_assign_nondet`.
- `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrect.lean` — switch `init_det` arm; provide congruence lemma.
- `Strata/Backends/CBMC/GOTO/Bisim.lean` — simplify `stepGoto_assign_nondet_to_stepInstr`.
- `Strata/Backends/CBMC/GOTO/SteppingBridgesDischarge.lean` — adjust `step_assign_nondet` consumer.
- `Strata/Backends/CBMC/GOTO/InstructionLookups.lean` — possibly simplify `assign_nondet_lookup_of_provenance_and_pinned`.
- `Strata/Backends/CBMC/GOTO/TranslatorBridgeHypsDischarge.lean` — _v2 bridge update.
- `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` — drop `h_assn_nondet_pc_inv` from `_v6` and `_v7`.

## Tier targets

- **Tier 1**: `_v7` no longer takes `h_assn_nondet_pc_inv`, axioms unchanged.
- **Tier 2**: Same, but with a new well-formedness hypothesis on `δ` (for monotonicity) — acceptable per spec.
- **Tier 3**: Block — document and back out.
