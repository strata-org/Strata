# Integration notes — A/B/C wiring after parallel run

This file tracks integration work after the parallel A/B/C run
landed. Subsequent items proceed in supervisor-report order; this
file captures the reality of how the interfaces compose, including
items that needed re-shaping when the actual definitions were
checked.

## Item 6 (vEmpty sentinel) — done in `8be270559`

Added `coreVEmptySentinel` (an `LExpr.fvar` with magic name
`__strata_vEmpty__`) and threaded it through `coreToValue` /
`coreFromValue`. Closes Worker C's `decl_empty_value` obligation.

## Item 5 (findLocIdx_resolves) — done in `6894c78a9`

Added `WellFormedTranslation.locationNum_eq_index` field, then
proved `findLocIdx_resolves` in a new file
`Strata/Backends/CBMC/GOTO/WellFormedTranslationProps.lean`. Closes
Worker C's `goto_target_resolves` obligation.

## Item 4 (wire B → C via EvalBoolCorr) — RESHAPED

The supervisor report listed this as a 50-LoC mechanical wire-up.
On inspection it's **not mechanical** because the interfaces don't
align:

* Worker B's output is `IsBoolIntTranslated e_core e_goto →
  ExprTranslated δ δ_goto δ_goto_bool e_core e_goto`. This is a
  *per-LExpr-pair* statement linking source and target.

* Worker C consumes `EvalBoolCorr nameMap δ_goto_bool eval`, which
  is `∀ σ_imp σ_goto e b, StoreCorr nameMap σ_imp σ_goto →
  δ_goto_bool σ_imp e = some b → eval σ_goto e = some (.vBool b)`.
  This is about the *GOTO-side evaluators agreeing with each other*
  on the GOTO store, with no mention of source expressions or
  source evaluators.

The two predicates are about different things:

| | Source-side | Target-side |
|---|---|---|
| **B's `ExprTranslated`** | Refers to `δ` and `e_core` | Refers to `δ_goto`, `δ_goto_bool`, `e_goto` |
| **C's `EvalBoolCorr`** | Refers to `σ_imp` (via `StoreCorr`) | Refers to `δ_goto_bool` (this branch) and `eval` (tautschnig); both apply to GOTO `Expr`s and stores |

`EvalBoolCorr` is a "two GOTO-side evaluators agree" lemma. The
boolean evaluator `δ_goto_bool` (this branch's abstract bool eval)
and `eval` (tautschnig's value eval, restricted to bools via
`some (.vBool b)`) must produce the same bool on the same GOTO
expression and `StoreCorr`-translated store.

This *cannot* be discharged from Worker B's bundle alone — B's
hypotheses are about source/target *translation* correspondence,
not target/target *evaluator* correspondence.

**Three resolution options:**

1. **Take `EvalBoolCorr` as a separate hypothesis at the top-level
   theorem.** The cleanest. Concrete callers supply it directly.
2. **Choose `δ_goto_bool := λ σ e → match eval σ e with | some
   (.vBool b) => some b | _ => none`.** That definition makes
   `EvalBoolCorr` automatic. But it forces this branch's abstract
   boolean evaluator to be defined *in terms of* tautschnig's
   `eval`, which is a non-trivial commitment — and then
   `δ_goto_bool` is no longer parametric.
3. **Add a `BoolEvalAgreesWithValueEval` predicate as a hypothesis
   in B's bundle and re-prove B's per-operator lemmas with that
   added.** Increases B's hypothesis surface; doesn't add real
   content.

**Decision:** option 1. The top-level final theorem will take
`EvalBoolCorr` as a hypothesis alongside `BoolIntOpHypotheses`, and
concrete callers will pick a `δ_goto_bool` and an `eval` that
visibly satisfy it. This matches how Worker C's discharge already
works (the existing `Bisim` bridges already require an external
`EvalBoolCorr`).

**Status:** wiring item 4 is therefore "documented and deferred to
the concrete top-level theorem" rather than landed as code.

## Item 3 (wire A → C: WellFormedTranslation → TranslatorBridgeHyps) — pending

The supervisor report's outline:
> "wellFormedTranslation_to_translatorBridgeHyps covering the four
> mechanical fields (`decl_lookup`, `dead_lookup`, `assign_lookup`,
> `assign_nondet_lookup`) by case-analysis on `CmdEmittedAt`"

Tractable to discharge from Worker A's `CmdEmittedAt` builders:

* `decl_lookup` — via `CmdEmittedAt.init_nondet` / `init_det`'s DECL
  component.
* `dead_lookup` — translator doesn't emit DEAD; vacuous (or take as
  `¬ ∃` hypothesis).
* `assign_lookup` — via `CmdEmittedAt.set_det` / `init_det`'s ASSIGN
  component.
* `assign_nondet_lookup` — via `CmdEmittedAt.set_nondet`.

Hold on this until items 1 and 2 land — the wiring needs both A's
loop-induction theorem (to get `WellFormedTranslation` from the
translator) and the per-Cmd `CmdEmittedAt` builders (to extract
each lookup field).

## Items 1 and 2 — pending

Worker A's loop-invariant induction (~300-700 LoC) and Worker B's
remaining bridge cases (`app`, `op`, `ite`; ~150-300 LoC) are the
two large items still standing. Both fit the parallel-worker
pattern.

## What this clarifies

The original A+B+C dependency graph in `CoreToGOTO_CorrectnessAnalysis.md`
treated `EvalCorr` as a single thing. In practice it cleaves into:

1. **Translation correctness** (Worker B's territory): "the source
   and target expressions evaluate to corresponding values."
2. **Target/target evaluator agreement** (no worker covered this):
   "this branch's abstract `δ_goto_bool` agrees with tautschnig's
   `eval` on the same GOTO expression and translated store."

These two halves compose to give "concrete property preservation".
We have (1) on the bool+int fragment from B; (2) is an open
hypothesis that any concrete caller must supply. The supervisor
report's "Item 4" was conflating them.

Concretely, the eventual top-level theorem looks like:

```lean
theorem coreCFGToGoto_forward_simulation_storeCorr_concrete
    (h_eval_bool_agrees : Bisim.EvalBoolCorr ...)
    (h_eval_value_corr : Bisim.EvalValueCorr ...)
    (h_b_hyps : BoolIntOpHypotheses ...)
    (h_a_wf : ∀ ans, coreCFGToGotoTransform ... = .ok ans →
                     WellFormedTranslation ...)
    ... :
    forward_simulation_storeCorr_conclusion
```

where `h_eval_bool_agrees` and `h_eval_value_corr` are evaluator-
side; `h_b_hyps` is translation-side; `h_a_wf` is translator-side.
