# GOTO Semantics: This Branch vs. `tautschnig/goto-semantics`

This document compares two formalizations of CBMC GOTO program semantics
that exist in this repository: the one on this branch
(`htd/unstructured-to-goto`), used by `coreCFGToGoto_forward_simulation`,
and the one on `tautschnig/goto-semantics`, which builds an end-to-end
simulation theorem for the structured (non-CFG) Core → GOTO pipeline.

It also collects insights into how the proofs on this branch could be
ported across, or how the two efforts could be reconciled.

The summary up front: the two semantics agree on the broad shape (a
small-step relation over an instruction-array program counter), but
differ in scope, value modeling, expression evaluation, and how function
calls and termination are handled. This branch's semantics is narrower
and lighter; the tautschnig branch's is broader and more concrete.

**Important caveat on what each branch delivers.** This branch carries
a *closed* end-to-end simulation theorem
(`coreCFGToGoto_forward_simulation`, `#print axioms` =
`[propext, Classical.choice, Quot.sound]`) on the call-free CFG slice.
After rounds 5-11 of work the structural well-formedness hypothesis
has been discharged against the actual translator (live theorem
`coreCFGToGotoTransform_forward_simulation_concrete_v7`); the only
remaining hypotheses are caller-irreducible (B3 expression-side
bundle, R7c trace-level pinning, value-side correspondence,
evaluator agreement). See
`docs/CoreToGOTO_CurrentStatus.md` for the current hypothesis
classification.

The tautschnig branch builds *more infrastructure* (concrete
`Value`, `concreteEval`, determinism, progress, `sim_X` building
blocks) but does *not* assemble these into an end-to-end
translator-correctness theorem: `sim_end_to_end` is compositional
plumbing whose preconditions (`hstmt_sim` and `hrange`) are
themselves undischarged for the actual `transformToGoto` output.
Both branches share the open obligation of committing a concrete
`Value` correspondence and discharging a concrete evaluator.
Neither alone is a complete concrete-soundness proof; they cover
*different* halves of the picture.

## Snapshot

| Aspect | This branch | `tautschnig/goto-semantics` |
|---|---|---|
| File layout | `Semantics.lean` (231 lines) | `Semantics.lean` (462) + `SemanticsEval.lean` (189) + `SemanticsProps.lean` (381) + `SemanticsSim.lean` (608) = 1640 |
| Module pattern | Lean 4 `module` / `public import` / `public section` | Plain `import` (legacy module style) |
| Pipeline target | Unstructured (`Core.DetCFG` → GOTO) | Structured (`Imperative.EvalBlock` → GOTO) |
| Top-level theorem | `coreCFGToGoto_forward_simulation` (forward simulation, terminating runs) | `sim_end_to_end` (existential store correspondence + `ExecProg` composition) |
| Open hypotheses | Caller-irreducible only after R10/R11: B3 expression-side bundle, trace-level pinning (R7c), value-side correspondence, evaluator agreement. Structural `WellFormedTranslation` is internally discharged in `_v7`. | `StoreCorr`/`EvalCorr` correspondences supplied by callers; `concreteEval` provided but its correspondence to Lambda eval is left open |
| Termination model | Reflexive-transitive closure of `StepGoto`; `.terminal` config | Inductive `ExecProg` rooted at `END_FUNCTION` / out-of-bounds; explicit `.set_return_value` |
| Failure model | `failed : Bool` flag accumulates assert failures inside the config | `assert_fail` advances PC normally; failure observed via separate `AssertFails` and `ProgramSafe` predicates |
| Instructions modeled | 7 (`LOCATION`, `DECL`, `ASSIGN`, `ASSERT`, `ASSUME`, `GOTO`, `END_FUNCTION`) plus `step_assign_nondet` | 11 (the 7 above plus `SKIP`, `DEAD`, `FUNCTION_CALL`, `SET_RETURN_VALUE`) |
| Function calls | Unmodeled — the proof restricts to `isAdmittedCmd` (no `.call`) | Modeled abstractly via `CallResultRel` parameter |
| Loop semantics | Not modeled (CFG transfers handle it via `condGoto`) | Modeled directly as `ExecLoop` and `ExecRange` |

## Detailed comparison

### 1. Configurations

**This branch.** A `GotoConfig P` is either `running pc σ failed` or
`terminal σ failed`. The `failed` flag lives *inside* the config, and
each configuration knows whether it is in-flight or done. This mirrors
`Imperative.CFGConfig` exactly, which makes the simulation relation
`Sim` straightforward to state.

```lean
inductive GotoConfig (P : PureExpr) : Type where
  | running : Nat → SemanticStore P → Bool → GotoConfig P
  | terminal : SemanticStore P → Bool → GotoConfig P
```

**`tautschnig` branch.** No explicit configuration type. Instead, the
relations expose `pc`, `σ`, and a separate optional `retVal : Option Value`
for `ExecProg`. Failure is a *property* of a state, not a flag in it:
`AssertFails` and `ProgramSafe` look at the program independently.
`assert_fail` continues execution, matching CBMC's "record-and-continue"
behavior literally; this branch's `assert_fail` flips the failed flag
and then continues, which is observationally equivalent for forward
simulation but more convenient for stating the theorem.

### 2. Stores and values

**This branch.** Stores are `Imperative.SemanticStore P =
P.Ident → Option P.Expr` — they carry *expressions* as values, inherited
unchanged from the imperative dialect's existing semantics. There is
no separate `Value` type. All value reasoning piggybacks on the
expression evaluator `δ`.

**`tautschnig` branch.** Stores are `String → Option Value`, where
`Value` is a concrete inductive:

```lean
inductive Value where
  | vBool   : Bool → Value
  | vInt    : Int → Value
  | vBV     : (width : Nat) → Int → Value
  | vReal   : Int → Int → Value
  | vString : String → Value
  | vArray  : List Value → Value
  | vStruct : List (String × Value) → Value
  | vEmpty  : Value
```

This is faithful to CBMC's runtime values. It also forces a
`StoreCorr nameMap σ_imp σ_goto` correspondence to bridge from the
imperative dialect's expression-valued stores: a class-based
`ValueCorr P` provides `toValue / fromValue`, and `nameMap` translates
`P.Ident` into GOTO `String` symbol names (covering renaming like
`<proc>::<scope>::<name>`).

The trade-off is clear: this branch's expression-valued store is light
on infrastructure but assumes the source and target use the same
expression language. The tautschnig branch's concrete `Value` matches
CBMC ground truth but requires a 90-line `StoreCorr` /
`EvalCorr` / `ValueCorr` correspondence layer up front.

### 3. Expression evaluation

**This branch.** `δ_goto : SemanticEvalGoto P` is an abstract
parameter. The simulation relies on a hypothesis
(`ExprTranslationPreservesEval`) that the GOTO and Core evaluators
agree on translated pairs. The hypothesis is currently *not* discharged
— that's a known open obligation.

**`tautschnig` branch.** Provides both: an abstract `ExprEval` parameter
**and** a concrete `concreteEval` evaluator (in `SemanticsEval.lean`,
~190 lines, `partial def`). `concreteEval` covers:

- nullary symbols and constants (with type-aware constant parsing),
- unary `Not`, `UnaryMinus`, `Typecast`,
- binary `Div / Mod / Minus`, comparisons, `Implies`, `Index`,
- ternary `ite` and `with`,
- multiary `And / Or / Plus / Mult`.

Quantifiers, side-effects, function-application, and bitvector bit-ops
return `none`. This evaluator is intended to be the canonical
interpretation; correspondence with Lambda-level expression evaluation
is listed as a TODO.

The `withOld` lifting in `Semantics.lean` extends a single-state
evaluator to a two-state `ExprEval₂` for `old(e)` in postconditions:

```lean
def ExprEval.withOld (eval : ExprEval) : ExprEval₂ := fun σ_old σ_cur e =>
  match e.id, e.operands with
  | .unary .Old, [inner] => eval σ_old inner
  | _, _ => eval σ_cur e
```

This is something this branch does not address — the proof's source
fragment doesn't use `old()`, so two-state evaluation never arises.

### 4. Instruction coverage

**This branch.** Eight `StepGoto` constructors:

```
step_location, step_decl, step_assign, step_assign_nondet,
step_assert_pass, step_assert_fail, step_assume_pass,
step_goto_taken, step_goto_fallthrough, step_end_function.
```

Notably missing: `SKIP` (treated identically to `LOCATION` in the
translator), `DEAD` (the source pipeline does not emit lifetime ends),
`FUNCTION_CALL` (call-free fragment), and `SET_RETURN_VALUE` (the
proof doesn't reach return-bearing pure functions).

**`tautschnig` branch.** Twelve `StepInstr` constructors covering all
of the above plus `SKIP`, `DEAD`, `FUNCTION_CALL`. `SET_RETURN_VALUE`
sits separately on the `ExecProg` relation (since it interacts with
the `retVal` channel).

The lack of `SKIP` and `DEAD` rules on this branch is a real omission
if the proof is ever extended to handle programs that emit them. Both
are trivially semantics-preserving; adding them is one constructor each.

The `step_assign_nondet` rule on this branch is novel relative to the
tautschnig branch's `assign_nondet`: this branch's version requires a
`UpdateState` witness from the caller (any value `v` is acceptable),
which is what the simulation needs for both `set_nondet` (source has
nondet) and the second half of `init_det` (after `step_decl` lands at
`σ'`, the subsequent `step_assign_nondet` is invoked with
`UpdateState_self` to no-op). The tautschnig branch's `assign_nondet`
universally quantifies `v` in the conclusion, which is closer to the
CBMC reading but requires an extra `cases` to instantiate.

### 5. GOTO target resolution

**This branch.** `Instruction.target` is `Option Nat` (a direct
instruction index). The translator computes targets ahead of time, so
the `WellFormedTranslation.layout_cond_goto` field's
`instr.target = some pc_lf` is already an index.

**`tautschnig` branch.** `Instruction.target` is a `locationNum`, and
the step relation walks the instruction array via `findLocIdx` to
resolve it on each step:

```lean
| goto_taken :
  instrType prog pc = some .GOTO →
  instrTarget prog pc = some (some tgt) →
  ... →
  findLocIdx prog.instructions tgt = some tgtIdx →
  StepInstr ... pc σ tgtIdx σ
```

`findLocIdx` is `O(n)` per resolution. The trade-off: tautschnig's
form is closer to CBMC's wire format (location numbers), while this
branch trades faithfulness for a faster, simpler step relation by
pre-resolving in the translator and exposing the result through
`WellFormedTranslation.layout_cond_goto`.

### 6. Reflexive-transitive closure

**This branch.** `StepGotoStar P δ_goto δ_goto_bool pgm =
ReflTrans (StepGoto P δ_goto δ_goto_bool pgm)` — a clean reuse of
the project's `Strata.DL.Util.Relations.ReflTrans`. This is the same
machinery used by `StepCFGStar`, which makes
`ReflTrans_Transitive` available for free in the simulation proof.

**`tautschnig` branch.** Defines its own `ExecProg` inductive that
combines stepping with termination markers and the `retVal` channel:

```lean
inductive ExecProg ... where
  | out_of_bounds : pc ≥ prog.instructions.size → ExecProg ...
  | end_function  : instrType prog pc = some .END_FUNCTION → ExecProg ...
  | set_return_value : ... → ExecProg ... pc σ σ' (retVal <|> some v)
  | step : StepInstr ... → ExecProg ... pc' σ' σ'' retVal → ExecProg ... pc σ σ'' retVal
```

It also defines `ExecRange` for executing within `[pc_start, pc_end)`
and proves `ExecRange_then_ExecProg` and `ExecRange_trans` for
composition. This is more powerful (it can talk about "execute this
sub-range"), but it is more bespoke and doesn't reuse the project's
generic `ReflTrans`.

### 7. The simulation proof shape

**This branch.** Forward simulation:

```
∀ run : CoreCFGStepStar π φ δ cfg (.cont cfg.entry σ false) (.terminal σ' b),
  ∃ pc_entry, wf.labelMap cfg.entry = some pc_entry ∧
    StepGotoStar … (.running pc_entry σ false) (.terminal σ' b)
```

State equivalence comes for free because the source and target stores
are the same `Imperative.SemanticStore P`. The `Sim` relation just
matches `(.cont l σ failed)` ↔ `(.running pc σ failed)` and
`(.terminal σ failed)` ↔ `(.terminal σ failed)`.

**`tautschnig` branch.** Existential store correspondence:

```
∃ σ_g', StoreCorr nameMap σ_imp' σ_g' ∧ ExecProg ... pc_start σ_goto σ_goto' retVal
```

The conclusion is **weaker** in one sense and **stronger** in another:

- Weaker: it's existential over the post-state, not equational. The
  tautschnig formulation says "there is *some* GOTO post-state matching
  the source post-state up to correspondence" — useful for property
  preservation but not directly usable for reasoning about specific
  GOTO traces.
- Stronger: it composes `ExecProg` with `ExecRange`, so it gives a
  full program execution path, not just a sub-trace. This branch's
  result, by contrast, is one step closer to the CBMC `pc_entry`
  start — but only for the call-free, no-return-value fragment.

Either formulation is sound for the soundness story (no false negatives
in CBMC). The choice between them is largely about what downstream
clients want to consume.

## Where the two branches converge

These pieces are essentially the same in both:

- Stores as total functions to `Option`.
- `instrAt` / `instrType` as the primary access pattern over the
  instruction array.
- `step_assert_pass / step_assert_fail / step_assume_pass`
  constructors are structurally identical (modulo the failed-flag
  threading vs. external `AssertFails`).
- Reuse of the source `Imperative.UpdateState` / `InitState` for
  store transitions in `step_decl` / `step_assign`.
- `ASSUME` with a false guard has *no* derivation (infeasible path) on
  both sides, matching CBMC's "block" semantics.
- `END_FUNCTION` terminates execution (this branch via the `.terminal`
  configuration; tautschnig via the `ExecProg.end_function` constructor).

## Porting insights

What can move from this branch to the tautschnig formulation, and vice
versa, with reasonable effort?

### From this branch → tautschnig

**1. The `cfgStepStar_to_gotoStar` / `block_simulation` chain (pretty direct).**
The induction structure is the same: walk over `EvalDetBlock`-style
block evaluations, glue with a transitive closure. Adapting requires:

- Replace `Sim … (.cont l σ failed) (.running pc σ failed)` with
  `StoreCorr nameMap σ_imp σ_goto`. The bound-variable names diverge but
  the proof obligation is shape-equivalent.
- Replace `StepGotoStar … (.running pc σ failed) (.terminal σ' b)` with
  `ExecProg ... pc σ σ' retVal` (or `ExecRange` for the per-block
  bound). The transitivity step is `ExecRange_then_ExecProg` /
  `ExecRange_trans` instead of `ReflTrans_Transitive`.
- The `failed` flag has to come out of the configuration and become an
  external `AssertFails`-or-not predicate. This is the largest
  structural change because the simulation's invariant ("Sim threads
  failed") becomes "ProgramSafe is preserved across the simulation."

**Estimated effort:** medium. The mechanical induction translates
directly; the failure-flag refactor is the main cost.

**2. `WellFormedTranslation`'s structural fields.** Tautschnig's branch
mostly assumes well-formedness via the `instrType` / `instrCode` /
`instrTarget` accessors and per-rule existentials, but does not have an
explicit predicate. The `WellFormedTranslation` structure here would
make the tautschnig proofs less existential and more declarative. It
would also be the natural place to record `findLocIdx` resolution
results (collapsing the `O(n)` lookup per step).

**3. `Core.CoreCFGStepStar_rec`** (the manual induction principle).
Tautschnig's branch uses the structured (non-CFG) pipeline, so it
doesn't need this directly. But if/when the unstructured pipeline is
modeled there, this lemma — and the conversion lemmas to/from
`ReflTrans (StepCFG …)` — port over verbatim. Already lives in
`Strata/Languages/Core/StatementSemanticsProps.lean`.

### From tautschnig → this branch

**1. Concrete `concreteEval` for GOTO `Expr`.** This branch's proof
takes `δ_goto` as an abstract parameter; tautschnig's
`SemanticsEval.lean` defines a real `partial def concreteEval`
covering ~30 expression forms. To use it here:

- Drop in `concreteEval` as the `δ_goto` instance.
- Re-prove `WellFormedSemanticEvalGotoBool` for it (closure under
  negation; `Expr.true` evaluates to `true`). For `concreteEval`, both
  follow by case analysis on the `Not` branch.
- The bigger question — *whether `concreteEval` matches Lambda-level
  evaluation* — is left open in tautschnig (TODO at
  `SemanticsEval.lean:42`). Importing `concreteEval` doesn't discharge
  the `ExprTranslationPreservesEval` hypothesis, just provides a candidate
  evaluator for callers to instantiate.

**2. Function-call modeling via `CallResultRel`.** Tautschnig's
branch parameterizes the step relation by an abstract
`callResult : ExprEval → FuncEnv → String → Store → Store → Option Value → Prop`.
Adding `step_function_call` here would mirror that structure:

```lean
| step_function_call :
  pgm.instrAt pc = some instr →
  instr.type = .FUNCTION_CALL →
  callResult ... callee σ σ' retVal →
  StepGoto ... (.running pc σ failed) (.running (pc + 1) σ_after failed)
```

This unblocks admitting `.call` into the proof, but only abstractly —
discharging `callResult` for the actual translator output is itself a
substantial sub-proof. (Aside: this branch's
`Core.CmdExt.isPlainCmd` / `isAdmittedCmd` already factor the call-free
restriction cleanly, so swapping in `callResult` is an additive change
that does not invalidate the existing proof.)

**3. `ExecRange` and `ExecRange_trans`.** A range-bounded execution
relation would let this branch state and prove
`block_body_simulation`'s conclusion as `ExecRange pc_start pc_end σ σ'`
rather than as a direct `StepGotoStar` to a specific final config.
The benefit: composition becomes routine via `ExecRange_trans`
instead of needing to align fall-through PCs by hand. The cost: an
extra inductive plus its transitivity lemma. Probably worth it if the
proof is extended to deeply nested control flow.

**4. `Value` type and `StoreCorr`.** This branch will eventually need
something like this if it integrates with a concrete CBMC backend that
uses real runtime values rather than carrying `Core.Expression.Expr`
as the value domain. Not urgent for the soundness story — the current
expression-valued store is fine for the forward-simulation theorem —
but it will be needed for any property-preservation result that talks
about *specific* values (e.g., "no integer overflow").

**5. Loop semantics via `ExecLoop`.** Tautschnig's `ExecLoop` is
defined directly over the compiled GOTO pattern (the
`LOCATION; GOTO[!g]; body; GOTO start; LOCATION` shape). This branch
sidesteps loop reasoning because the source CFG already represents
loops as `condGoto`-cycle blocks, and `CoreCFGStepStar` handles
unrolling implicitly. But if/when the source side gains structured
loops (and the translation produces the standard pattern),
`ExecLoop` is the right shape to import.

### Reconciliation directions

If the two branches were merged, the obvious split is:

1. **`Semantics.lean`** — share. Pick one configuration model
   (`GotoConfig` with embedded failed flag *or* externalized
   `AssertFails`). The embedded form is cleaner for forward simulation;
   the external form is closer to CBMC's literal behavior. A compromise:
   keep both, with a one-line equivalence lemma.
2. **`SemanticsEval.lean`** — port directly. This branch has nothing
   in this slot.
3. **`SemanticsProps.lean`** — port the determinism and progress
   lemmas. They do not depend on the proof's shape.
4. **`SemanticsSim.lean`** (tautschnig) and `CoreCFGToGOTOCorrect.lean`
   (this branch) — keep separate, since they target different source
   pipelines (structured `EvalBlock` vs. unstructured `DetCFG`). Once
   `coreCFGToGotoTransform` is the canonical lowering, the structured
   path can be expressed by composition (`structured → CFG → GOTO`),
   making the tautschnig direct path redundant.

A merged form would also let us share the open obligations
(`WellFormedTranslation` discharge, `ExprTranslationPreservesEval`
discharge, `concreteEval` correctness vs. Lambda) so each only needs
to be proved once.

## What the tautschnig branch is *not* doing

It is worth being explicit about gaps, since the file count
(`Semantics.lean` + `SemanticsEval.lean` + `SemanticsProps.lean` +
`SemanticsSim.lean` ≈ 1640 lines) overstates the closed-proof content.

1. **No end-to-end translator-correctness theorem.** A search for
   uses of `sim_end_to_end` outside its own definition site
   (`SemanticsSim.lean:574`) finds none.  The theorem is stated and
   proved, but never instantiated against `transformToGoto` output.
   `sim_end_to_end`'s preconditions include `hrange : ExecRange ...`
   (the translated GOTO instructions execute as a range) and
   `hstmt_sim` (each statement preserves store correspondence) — both
   are caller-supplied; no theorem on the branch discharges them for
   the actual translator.
2. **`eval` is still abstract.** Their `StepInstr` is parameterized by
   `eval : ExprEval = Store → Expr → Option Value`, exactly as our
   `StepGoto` is parameterized by `δ_goto`. The concrete `concreteEval`
   exists in `SemanticsEval.lean`, but it is *not* threaded into the
   simulation theorems — those still take `eval` as an opaque
   argument. The "concreteness gap" is the value type and the
   *available-but-disconnected* concrete evaluator, not the step
   relation itself.
3. **`concreteEval` is `partial def`.** It is not directly usable in
   Lean proofs without a non-`partial` reformulation.  Its
   correspondence with Lambda-level expression evaluation is listed
   as a TODO (`SemanticsEval.lean` header).
4. **No `ValueCorr` instance for `Core.Expression`.** The `ValueCorr P`
   typeclass is defined and `StoreCorr nameMap` consumes it, but no
   instance is provided for any concrete `P`. Any caller of `sim_set`
   / `sim_init` / etc. has to define `toValue : Core.Expression.Expr →
   Option Value` themselves, including the numeric-width and
   structured-value conventions.
5. **`Function.Injective nameMap` is a hypothesis, not a theorem.**
   Their `sim_set`/`sim_init` lemmas require it; nothing on the branch
   discharges it for `Lambda.LExpr.toGotoExprCtx`'s actual renaming
   (`<proc>::<scope>::<name>`).

In short: theirs is **infrastructure that hasn't been assembled into
a concrete soundness statement**. Ours is **a closed simulation
skeleton parametric over abstract evaluators and abstract values**.
Both branches stop short of concrete soundness; the gaps are
complementary.

## What concrete soundness requires

A "real" translator-correctness theorem instantiated against
`transformToGoto`'s actual output, capable of expressing properties
like "no integer overflow," would need all of the following pieces.
Neither branch alone has them:

| Piece | This branch | Tautschnig | Open on both? |
|---|---|---|---|
| Source-side semantics | parametric (`δ`) | parametric (`δ`) | yes |
| Target-side step relation | `StepGoto` (abstract `δ_goto`) | `StepInstr` (abstract `eval`) | partial — both abstract |
| Target-side concrete value type | `P.Expr` (abstract) | `Value` ✓ | one branch only |
| Target-side concrete evaluator | none | `concreteEval` (`partial def`) | one branch only |
| End-to-end forward simulation against translator | `coreCFGToGoto_forward_simulation` ✓ | none | one branch only |
| `WellFormedTranslation` discharge against `transformToGoto` | open | open (no analogue) | yes |
| `ExprTranslationPreservesEval` (a.k.a. `EvalCorr`) discharge against `Lambda.LExpr.toGotoExprCtx` | open | open | yes |
| `ValueCorr P` instance for `Core.Expression` | n/a | open | one branch only |
| `Function.Injective nameMap` discharge | n/a | open | one branch only |
| Determinism, progress, store-operation lemmas | none | proven for `StepInstr` | one branch only |

The cheapest path through this table is **additive**: keep this
branch's closed forward-simulation skeleton, layer the tautschnig
infrastructure (concrete `Value`, `concreteEval`, `StoreCorr`,
determinism, progress) on top of `StepGoto`, and discharge the open
hypotheses against the concrete pieces as they land.  The
foundational store-type swap (replacing `SemanticStore P` with
`Store`) is *not* required for soundness; bridging via
`StoreCorr nameMap` is sufficient, leaves our existing proof intact,
and is exactly the path the tautschnig branch already chose for *its*
side.

See `docs/superpowers/specs/2026-05-20-goto-semantics-expansion-design.md`
for the staged plan that operationalizes this, including the
`StepGoto ↔ StepInstr` bisimulation bridge that lets downstream
consumers move between the two step relations without committing to
a single canonical one up front.

## Summary

This branch aims for a **narrow, sharp** result: a closed forward
simulation on the call-free `DetCFG` fragment, with all proof
infrastructure under `Strata/Backends/CBMC/GOTO/` (split across
several files since the rounds-5-through-12 cleanup work; the
`WellFormedTranslation` construction in particular is now under
`CoreCFGToGotoTransformWF/` as 6 sub-modules of ≤1.5k LoC each), and
the proof chain closed modulo a small set of caller-irreducible
hypotheses (per-PC trace-level pinning, evaluator agreement). See
`docs/CoreToGOTO_CurrentStatus.md` for the up-to-date hypothesis
inventory.

The tautschnig branch aims for a **broader infrastructure**: a more
faithful semantics surface (concrete `Value`, function calls, loops,
returns, `old()`), a concrete expression evaluator, determinism,
progress, and statement-level simulation building blocks — with no
end-to-end translator-correctness theorem assembled from them.

Neither is strictly better; they cover different halves of the
concrete-soundness story. The most leveraged next step is **not** to
replace one with the other, but to grow the two halves toward each
other additively: keep the closed simulation here, port the concrete
infrastructure from there, and discharge the shared open hypotheses
against the concrete instantiations as they land.
