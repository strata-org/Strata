# Worker C — Gap C: `SteppingBridges` discharge

## Deliverable

A new file
`Strata/Backends/CBMC/GOTO/SteppingBridgesDischarge.lean` that
produces a `SteppingBridges` value (the Phase-3 hypothesis bundle
consumed by `StepGotoStar_to_ExecProg` in
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrectStore.lean`) from a
single, explicitly-stated hypothesis package.

The file builds in `lake build Strata.Backends.CBMC.GOTO.SteppingBridgesDischarge`,
produces no `sorry`s, and the full `lake build Strata` continues to
succeed.

## Top-level theorem

```lean
theorem steppingBridges_of_translator
    {P : Imperative.PureExpr} [HasBool P] [HasNot P]
    [SemanticsTautschnig.ValueCorr P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program}
    {nameMap : P.Ident → String}
    {callResult : SemanticsTautschnig.CallResultRel}
    {eval : SemanticsTautschnig.ExprEval}
    {fenv : SemanticsTautschnig.FuncEnv}
    (h_eval_bool_corr : Bisim.EvalBoolCorr nameMap δ_goto_bool eval)
    (h_brHyps : TranslatorBridgeHyps pgm nameMap δ_goto eval) :
    SteppingBridges δ_goto δ_goto_bool pgm nameMap callResult eval fenv
```

The interface is intentionally narrow: one boolean-evaluator
correspondence (Worker B) and one bundle of per-PC translator-shape
hypotheses (Worker A + the post-patcher facts not currently in
`WellFormedTranslation`).

## Per-constructor discharge status

`StepGoto` has 12 constructors (11 running successors, 1 terminal).
All are discharged in `step_running` / `step_terminal` of the
returned `SteppingBridges`. The bridges in `Bisim.lean` are reused
where they fit; one case (`step_assign`) is closed by direct
application of `StepInstr.assign` because the existing `Bisim`
bridge over-specifies its rhs through `exprTrans`.

| StepGoto constructor       | Discharge mechanism                              | Extra hypothesis from `TranslatorBridgeHyps` |
|---                         |---                                               |---                                            |
| `step_location`            | `Bisim.stepGoto_location_to_stepInstr`           | none |
| `step_skip`                | `Bisim.stepGoto_skip_to_stepInstr`               | none |
| `step_assert_pass`         | `Bisim.stepGoto_assert_pass_to_stepInstr`        | none (uses `EvalBoolCorr`) |
| `step_assume_pass`         | `Bisim.stepGoto_assume_pass_to_stepInstr`        | none (uses `EvalBoolCorr`) |
| `step_goto_fallthrough`    | `Bisim.stepGoto_goto_fallthrough_to_stepInstr`   | none (uses `EvalBoolCorr`) |
| `step_assert_fail`         | `Bisim.stepGoto_assert_fail_to_stepInstr` (drop AssertFails witness) | none (uses `EvalBoolCorr`) |
| `step_dead`                | `Bisim.stepGoto_dead_to_stepInstr`               | `nameMap_inj`, `dead_lookup` |
| `step_decl`                | `Bisim.stepGoto_decl_to_stepInstr`               | `nameMap_inj`, `decl_lookup`, **`decl_empty_value`** |
| `step_assign`              | direct `StepInstr.assign` + local `storeCorr_preserve_update` | `nameMap_inj`, `assign_lookup`, **`assign_value_corr`** |
| `step_assign_nondet`       | `Bisim.stepGoto_assign_nondet_to_stepInstr`      | `nameMap_inj`, `assign_nondet_lookup`, `assign_nondet_value_corr` |
| `step_goto_taken`          | `Bisim.stepGoto_goto_taken_to_stepInstr`         | **`goto_target_resolves`** |
| `step_end_function` (term.)| `Bisim.stepGoto_end_function_to_execProg`        | none |

Bolded extra hypotheses are the genuinely-new ones identified in
§4 of the analysis: see "Open obligations" below.

## Why `step_assign` is not via `Bisim.stepGoto_assign_to_stepInstr`

`StepGoto.step_assign`'s rhs is an arbitrary GOTO `Expr` (the
constructor's `δ_goto σ rhs = some v` clause introduces `rhs : Expr`
as a binder). `Bisim.stepGoto_assign_to_stepInstr` is parameterised
by `exprTrans : P.Expr → Expr` and requires
`δ_goto σ_imp (exprTrans rhs_imp) = some v_imp` — i.e. it
*pre-supposes* the rhs is in the image of `exprTrans`.

Two ways to bridge:

1. **Strengthen the hypothesis:** "for every ASSIGN at PC, `rhs =
   exprTrans (some source-side rhs_imp)`." This tracks the
   translator's shape (`CmdEmittedAt.set_det / .set_nondet` carry
   `i.code = Code.assign lhs e_goto` with `e_goto = exprTrans
   e_core`), but threads `exprTrans` through the entire bundle and
   adds an existential per discharge call.
2. **Bypass `exprTrans`:** discharge `StepInstr.assign` directly,
   pulling the rhs from the instruction code via `getAssignRhs`.
   This requires the translator-shape bundle to provide
   `eval σ_goto rhs = some v_goto` per-PC (i.e. the GOTO-side
   semantic agreement on the *actual* rhs), which is exactly what
   Worker B's `EvalCorr` discharges per PC.

Path 2 is implemented. The trade-off: `assign_value_corr` carries
the `eval` agreement plus the `vc.toValue` correspondence
together. This keeps the bundle independent of `exprTrans`, which
matches reality — the trace lift never sees a source-side
expression — and avoids leaking translator details into the
discharge interface.

## `TranslatorBridgeHyps` interface shape

```lean
structure TranslatorBridgeHyps
    {P : Imperative.PureExpr} [HasBool P] [HasNot P]
    [SemanticsTautschnig.ValueCorr P]
    (pgm : Program)
    (nameMap : P.Ident → String)
    (δ_goto : SemanticEvalGoto P)
    (eval : SemanticsTautschnig.ExprEval) : Prop where
  nameMap_inj : Function.Injective nameMap
  decl_lookup       : <∀ DECL PC, instrCode → getSymbolName = nameMap x>
  dead_lookup       : <∀ DEAD PC, instrCode → getSymbolName = nameMap x>
  assign_lookup     : <∀ ASSIGN PC, instrCode → getAssignLhs/Rhs = (nameMap x, rhs_g)>
  assign_nondet_lookup : <∀ ASSIGN PC firing assign_nondet, ∃ rhs_g …>
  goto_target_resolves : <∀ GOTO PC, ∃ loc, instrTarget = some loc ∧ findLocIdx = target>
  decl_empty_value     : <∀ DECL PC, vc.toValue v = some .vEmpty>
  assign_value_corr    : <∀ ASSIGN PC firing step_assign, ∃ v_goto, vc.toValue v_imp = v_goto ∧ eval σ_goto rhs_g = v_goto>
  assign_nondet_value_corr : <∀ ASSIGN PC firing assign_nondet, ∃ v_goto, vc.toValue v_imp = v_goto>
```

Each field is universally-quantified over PCs *plus* conditional on
the shape of the StepGoto step that fires there (the predicate
returns `True` when the PC's instruction type doesn't match). This
matches how `step_running` consumes the bundle: each constructor
case pulls the relevant field with the instruction's PC and the
constructor's witnesses.

## Hypotheses that integrate cleanly with Worker A's
`WellFormedTranslation`

These four follow directly from `WellFormedTranslation.layout_block_body`'s
`CmdEmittedAt` cases:

* `decl_lookup` — `CmdEmittedAt.init_nondet` (and `init_det`'s
  DECL component) carry `i_decl.type = .DECL` and the
  translator emits a `Code.symbol (nameMap x)` operand. Mechanical.
* `dead_lookup` — currently the translator does *not* emit
  `DEAD` (per `Semantics.lean:166`), so this field is vacuously
  satisfiable for the current translator output. It's still
  required by the discharge because `StepGoto.step_dead` is
  available; in practice no source-CFG run produces it.
* `assign_lookup` — `CmdEmittedAt.set_det` and `init_det` (the
  ASSIGN-after-DECL second instruction) carry
  `i.code = Code.assign lhs e_goto`. Mechanical.
* `assign_nondet_lookup` — `CmdEmittedAt.set_nondet` carries
  `i.code = Code.assign lhs e_nondet` with `e_nondet.id =
  .side_effect .Nondet`. Mechanical.

## Hypotheses requiring extra translator facts beyond
`WellFormedTranslation`

### `goto_target_resolves`

The translator's second-pass patcher (`patchGotoTargets`) sets
`instr.target = some pc_target`, but the bridge needs both:

* `instrTarget pgm pc = some (some loc)` for some `locationNum
  loc`, and
* `findLocIdx pgm.instructions loc = some pc_target`.

`WellFormedTranslation.layout_cond_goto` gives the index target
but says nothing about `loc` or `findLocIdx` resolution. This is
genuinely a separate post-condition the patcher must establish:
"every emitted GOTO's `instr.target` carries a `locationNum` that
`findLocIdx` resolves back to the same index." This is *not* free
from current `WellFormedTranslation`.

Concrete next step: extend Worker A's bundle (or add a sibling
predicate) with a `layout_findLocIdx_resolves` field.

### `decl_empty_value`

`Bisim.stepGoto_decl_to_stepInstr` requires
`vc.toValue v = some .vEmpty`. Under `valueCorrCore`, no
`Lambda.LExpr` constructor has `toValue = some .vEmpty` — so this
hypothesis is **unsatisfiable** for the current setup.

Three resolutions, in increasing order of work:

1. Enrich `valueCorrCore` to recognise some sentinel constructor
   (e.g. `Lambda.LExpr.fvar "__nondet"`) as `.vEmpty`. Cost: a few
   lines; semantics only changes for the sentinel.
2. Reshape the bridge: collapse `step_decl + step_assign` into a
   single `StepInstr.decl ; StepInstr.assign` pair. Requires
   `Bisim.lean` to gain a "two-step bridge" theorem, and the
   discharge layer here would need to look ahead one step.
3. Tighten `Imperative.InitState` so it only fires from the source
   side when the value is the empty sentinel; force the source
   semantics to re-emit a follow-up `step_assign`. Most invasive.

Option 1 is the smallest delta. The current shape leaves the field
in place but acknowledges no concrete `WellFormedTranslation` can
discharge it; the documented note in `Bisim.lean:443-458` and §4.6
of the analysis are aligned with this.

### `assign_value_corr`

Combines two facts:

* `vc.toValue v_imp = some v_goto` for the source-side value
  `v_imp` produced by `δ_goto σ rhs_g` (from
  `StepGoto.step_assign`).
* `eval σ_goto rhs_g = some v_goto` (the GOTO-side concrete
  evaluator agrees).

The first is a constraint on which `v_imp` the source-side
evaluator can produce; under `valueCorrCore` it's satisfied for
`Lambda.LExpr.const`-shaped values but not for arbitrary
`LExpr`s. The second is exactly Worker B's `EvalCorr` discharge.

Practical reading: the field is satisfied for the *fragment* where
the source-side evaluator returns expressions the `ValueCorr`
instance recognises. Concretely: integer literals, boolean
literals, structurally-correlated bitvectors. Outside this
fragment, `assign_value_corr` is the same kind of obligation as
"this expression has a concrete value" — a fragment restriction,
not a soundness gap.

## What blocked me

Nothing structural blocked closing all 12 cases — but two cases
(`step_decl` empty-value, `step_assign` value-corr) discharge
*conditionally*, where the condition is not satisfiable under
current `valueCorrCore` for arbitrary source expressions.

The decision to surface these as fields on `TranslatorBridgeHyps`
(rather than try to discharge them in this file) is a deliberate
interface choice: it keeps the discharge layer's hypothesis
surface honest about what's needed downstream, rather than baking
in a strictly-stronger `ValueCorr P` instance that an integrator
would have to peel back open.

## Concrete next steps

1. **Worker A integration** — once Worker A's
   `WellFormedTranslation`-discharge theorem stabilises, write
   `wellFormedTranslation_to_translatorBridgeHyps` covering the
   four mechanical fields (`decl_lookup`, `dead_lookup`,
   `assign_lookup`, `assign_nondet_lookup`). This is straight
   case-analysis on `CmdEmittedAt`.
2. **Patcher post-condition** — add a
   `findLocIdx_resolves` lemma proven against
   `patchGotoTargets`, then extend `WellFormedTranslation` with a
   `layout_findLocIdx_resolves` field that
   `goto_target_resolves` consumes.
3. **`vEmpty` strategy choice** — pick between (a) enriching
   `valueCorrCore`, (b) collapsing DECL+ASSIGN, (c) reshaping
   `InitState`. Recommend (a) for minimum disruption.
4. **`assign_value_corr` integration** — Worker B's
   `EvalCorr`/`EvalValueCorr` output, paired with a
   `valueCorrCore`-recognises-this-shape predicate on the source-
   side evaluator's output, discharges
   `assign_value_corr`. Mechanical once both are in hand.

## Files added / changed

* **Added** `Strata/Backends/CBMC/GOTO/SteppingBridgesDischarge.lean`
  (393 lines, no `sorry`, no axioms beyond what
  `CoreCFGToGOTOCorrectStore.lean` already uses:
  `[propext, Classical.choice, Quot.sound]`).
* No other files modified.

## Build verification

```
$ lake build Strata.Backends.CBMC.GOTO.SteppingBridgesDischarge
✔ [143/143] Built Strata.Backends.CBMC.GOTO.SteppingBridgesDischarge
Build completed successfully (143 jobs).

$ lake build Strata
✔ [306/306] Built Strata
Build completed successfully (306 jobs).
```
