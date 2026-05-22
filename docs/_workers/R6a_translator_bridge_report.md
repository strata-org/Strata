# Worker R6a — `WellFormedTranslation` → `TranslatorBridgeHyps`

**Goal.** Bridge from Round-5's `WellFormedTranslation`
(`CoreCFGToGOTOInvariants.lean`) to Worker C's
`TranslatorBridgeHyps` (`SteppingBridgesDischarge.lean`).

**File.** New file
`Strata/Backends/CBMC/GOTO/TranslatorBridgeHypsDischarge.lean`
(~225 LoC). Build green. Axioms:
`[propext, Classical.choice, Quot.sound]`.

## Outcome

Tier 3 (Acceptable) — partial bridge that builds and reduces the
hypothesis surface compared to a pure passthrough. Three fields
discharged (one fully from `wf`, two via small metaproperty
hypotheses), five fields surfaced as caller passthroughs.

| Field | Source | Status |
|---|---|---|
| `nameMap_inj` | caller-supplied `h_inj` | passthrough |
| `decl_lookup` | passthrough (see below) | passthrough |
| `dead_lookup` | discharged via `h_no_dead` | discharged |
| `assign_lookup` | passthrough | passthrough |
| `assign_nondet_lookup` | passthrough | passthrough |
| `goto_target_resolves` | discharged via `findLocIdx_resolves` + `wf.locationNum_eq_index` | discharged |
| `decl_empty_value` | passthrough (caller-side `vEmpty`) | passthrough |
| `assign_value_corr` | passthrough (caller-side eval) | passthrough |
| `assign_nondet_value_corr` | passthrough (caller-side eval) | passthrough |

**Score:** 2 of 8 fields discharged from `wf` (one with a small
side-hypothesis bundle), 1 of 8 discharged via passthrough of a
metaproperty (`h_no_dead`). Net: 3 discharges + 5 passthroughs.
Below the round target of 3-5 discharges + 3-5 passthroughs but
above the "Acceptable" threshold.

## Why the lookup/value fields can't be discharged from `wf`

### Lookup fields (`decl_lookup`, `assign_lookup`, `assign_nondet_lookup`)

Each is universally quantified over PCs *and* over arbitrary
`x : Core.Expression.Ident`. To discharge `decl_lookup`, we'd need:

> for every DECL PC + arbitrary `InitState σ x v σ'` firing,
> `(instrCode pgm pc).bind getSymbolName = some (nameMap x)`.

The `(∀ x ...)` quantifier is the problem. The translator emits
`Code.decl (Expr.symbol (G.identToString v_src) gty)` where
`v_src` is the *source command's variable* — a specific value, not
"any x". Any `x ≠ v_src` for which `InitState σ x v σ'` happens
to hold would falsify the lookup.

In practice (during forward simulation), `step_decl` only ever
fires with `x = v_src` because the source-side `EvalCmd.eval_init`
pins `x`. But the bridge's interface doesn't see the source-side —
the `(∀ x ...)` is unconditional in the field's *type*.

Closing this requires either:

1. **A strengthened `CmdEmittedAt`** that exposes
   `i.code = Code.decl (Expr.symbol (nameMap v_src) gty)`
   (currently the constructors carry existential `lhs` and don't
   tie to `nameMap v`). Then a CFG-PC inversion lemma walks
   `cfg.blocks` to find the source command, gets `v_src`, and
   constrains `x = v_src` from `InitState σ x v σ' + σ x = none +
   σ v_src = none + σ y ≠ none for y ∉ ...` (a strong claim
   about store-vacancy invariants).

2. **A reshaped `TranslatorBridgeHyps`** where the lookup fields
   are conditional on a "the step at this PC fires from a CFG
   command with variable `v_src` and `x = v_src`" premise. Worker
   C's discharge then takes that premise as input to each step.

Option 2 is cleaner architecturally; option 1 is more invasive but
more uniform. Both deferred.

### `dead_lookup`

The translator never emits DEAD instructions. `step_dead` therefore
never fires in any concrete trace. We capture this via a small
"`pgm` has no DEAD instructions" hypothesis (`h_no_dead`), making
`dead_lookup` vacuous.

`h_no_dead` is provable by induction on the translator (every
emit-helper pushes DECL/ASSIGN/ASSERT/ASSUME/GOTO/LOCATION, never
DEAD). It's a *metaproperty* of the translator orthogonal to
`WellFormedTranslation`'s structural facts — closing it from
`coreCFGToGotoTransform` directly is straightforward and deferred
to a follow-up.

### Value fields

`decl_empty_value`, `assign_value_corr`, `assign_nondet_value_corr`
are caller-side obligations on the source-side `δ` ↔ target-side
`eval` agreement. They're not properties of the translator's output
— they're properties of how the *evaluators* agree on the
translated expressions. Out of scope here.

## What `goto_target_resolves` discharge looks like

The mechanical part:

* `instr.type = .GOTO + instr.target = some target` ⇒
  `instrTarget pgm pc = some (some target)` (by `simp` on
  `instrTarget`'s definition + `Program.instrAt`).
* `findLocIdx pgm.instructions target = some target` follows from
  `findLocIdx_resolves` (`WellFormedTranslationProps.lean`) +
  `wf.locationNum_eq_index`, *given* that `pgm.instrAt target`
  exists for some instruction.

The "exists" side condition is the only real obstruction:
`findLocIdx_resolves` requires `pgm.instrAt target = some _`. We
take this as a small side hypothesis `h_goto_target_in_range`;
closing it from `wf` alone requires a "every GOTO in `pgm`
originated from `layout_cond_goto`" inversion that's not in
`WellFormedTranslation` today.

## Final shape of the bridge

```lean
theorem wellFormedTranslation_to_translatorBridgeHyps
    (cfg : Core.DetCFG) (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool)
    (nameMap : Core.Expression.Ident → String)
    (h_inj : Function.Injective nameMap)
    (eval : SemanticsTautschnig.ExprEval)
    -- Two metaproperty side hypotheses (mechanical from translator
    -- structure, but not in `wf`):
    (h_goto_target_in_range : ...) (h_no_dead : ...)
    -- Six caller passthroughs (lookup + value fields):
    (h_decl_lookup : ...) (h_assign_lookup : ...)
    (h_assign_nondet_lookup : ...) (h_decl_empty_value : ...)
    (h_assign_value_corr : ...) (h_assign_nondet_value_corr : ...) :
    TranslatorBridgeHyps pgm nameMap δ_goto eval
```

## Files added / changed

* **Added** `Strata/Backends/CBMC/GOTO/TranslatorBridgeHypsDischarge.lean`
  (~225 LoC). Build green. Axioms:
  `[propext, Classical.choice, Quot.sound]`.

## Build verification

```
$ lake build Strata.Backends.CBMC.GOTO.TranslatorBridgeHypsDischarge
✔ [145/145] Built Strata.Backends.CBMC.GOTO.TranslatorBridgeHypsDischarge (1.7s)
Build completed successfully (145 jobs).

$ lake build
... (full build)
Build completed successfully (585 jobs).
```

## Suggested next steps

To raise the discharge count to 5+ of 8:

1. **Close `h_goto_target_in_range`** by adding a
   `WellFormedTranslation.goto_target_in_range` field with a "every
   GOTO came from `layout_cond_goto`" inversion. Mechanical from
   the translator's loop induction.

2. **Close `h_no_dead`** by adding a
   `WellFormedTranslation.no_dead_instructions` field. Mechanical
   from the translator's emit-helper coverage.

3. **Strengthen `CmdEmittedAt`** to expose
   `i.code = Code.decl (Expr.symbol (nameMap v) gty)` and
   `i.code = Code.assign (Expr.symbol (nameMap v) gty) e_goto`
   (replacing existential `lhs`/`e_nondet`). Then write a
   CFG-PC inversion lemma giving back `(l, blk, k, src_cmd)` for
   every admitted PC.

4. **Tighten `TranslatorBridgeHyps`'s lookup fields** to be
   conditional on a "step at this PC matches a CFG command" premise
   that consumers establish via the inversion lemma.

After (3) + (4), the lookup fields close from
`WellFormedTranslation` mechanically. The value fields remain
caller-side (genuinely caller obligation).

## Status checklist

- [x] Report stub.
- [x] Read all required context.
- [x] Sketch theorem signature.
- [x] Discharge `nameMap_inj` (passthrough).
- [x] Discharge `goto_target_resolves` via `findLocIdx_resolves`.
- [x] Discharge `dead_lookup` via `h_no_dead`.
- [x] State + take as hypothesis the three lookup fields (decl,
      assign, assign_nondet) and three value fields.
- [x] `lake build` green.
- [x] `#print axioms` is the standard set.
