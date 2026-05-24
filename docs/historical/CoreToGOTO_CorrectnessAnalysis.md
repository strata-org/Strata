# What it would take to prove `coreCFGToGotoTransform` correct

This document is a full-stack analysis of what is required to claim
that the unstructured-to-GOTO transformation in
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOPipeline.lean` is *correct*,
in any honest sense of the word. It situates the existing closed
results (`coreCFGToGoto_forward_simulation`,
`coreCFGToGoto_forward_simulation_storeCorr`) against the gaps that
remain.

Companion documents:

- `docs/CoreToGOTO_ExpansionProgress.md` — what landed in the
  GOTO-semantics-expansion plan (Phases 0–4).
- `docs/CoreToGOTO_BisimReport.md` — Phase 0 outcome report
  (per-`StepGoto`-constructor bridge status).
- `docs/CoreToGOTO_SemanticsComparison.md` — diagnostic
  comparison of this branch's semantics with
  `tautschnig/goto-semantics`.

> ## Latent bug (now fixed): `END_FUNCTION` emitted per `.finish`, not once at end
>
> **Symptom.** Before commit `1de80e8e0`, a CFG with multiple
> `.finish` blocks (e.g. multiple early returns) was silently
> miscompiled: `coreCFGToGotoTransform`'s `.finish` case emitted
> *no* instruction, and `procedureToGotoCtxViaCFG` appended a single
> trailing `END_FUNCTION`. With `n` `.finish` blocks, only the last
> one's fall-through reached the trailing `END_FUNCTION`;
> intermediate blocks fell through into the next block's `LOCATION`,
> executing arbitrary code the source-level semantics said was
> unreachable. CBMC could report false positives on assertions in
> later blocks; the simulation proof's
> `WellFormedTranslation.layout_finish` field (universal over
> `.finish` blocks) was unprovable on the previous translator output.
>
> **Reproducer / regression test.** See
> `StrataTest/Backends/CBMC/GOTO/FinishPlacementProbe.lean`. Before
> the fix it printed
> `[(0, LOCATION), (1, LOCATION)]` (no `END_FUNCTION` emitted by the
> per-block code; only the wrapper's trailing one would land at index 2).
> After the fix it prints
> `[(0, LOCATION), (1, END_FUNCTION), (2, LOCATION), (3, END_FUNCTION)]` —
> exactly the shape `WellFormedTranslation.layout_finish` requires.
>
> **Fix (Option 1).** `coreCFGToGotoTransform`'s `.finish` case now
> emits one `END_FUNCTION` instruction inline; the wrapper no longer
> appends a trailing `END_FUNCTION`. The trade-off vs. CBMC
> convention (which prefers a shared exit reached via `GOTO`) is
> presentational, not semantic; multiple `END_FUNCTION`s in one
> program are legal and CBMC accepts them. Option 1 was chosen
> because it lets `WellFormedTranslation.layout_finish` stand as
> currently written — discharging Gap A no longer has to reshape
> the field. See §6 below for the full discussion.

## 0. What does "correct" mean here?

"`coreCFGToGotoTransform` is correct" is not a single sentence — it
is a stack of distinct claims, each strictly stronger than the last:

| # | Name | Statement (informal) | Use case |
|---|---|---|---|
| 1 | **Type-correctness** | The translator emits well-formed GOTO programs (decidable layout invariants). | Static sanity. |
| 2 | **Forward simulation, terminating** | If the source CFG runs to `(σ', failed)`, the target GOTO runs to a corresponding state. | Soundness for properties that fire on terminating traces. |
| 3 | **Forward simulation + property-preservation** | "GOTO satisfies P" ⇒ "Source satisfies P" for some P (e.g. assertion safety). | The headline soundness theorem CBMC users want. |
| 4 | **Bisimulation** | Forward + backward simulation. | Completeness: CBMC reports a bug ⇔ source has a bug. |
| 5 | **Bisimulation + observational equivalence** | Plus: same I/O, same termination behaviour, same divergence. | Refinement / compiler-style correctness. |

The current proof (`coreCFGToGoto_forward_simulation`) is statement #2
on a *restricted fragment* and *modulo two open hypotheses*. The
question "what do we need" is really: *what closes the gap between
"#2 on a restricted fragment, modulo hypotheses" and "#3 / #4 / #5 on
the full pipeline".*

Below the gaps are split into seven independent buckets (A–G). All
need to be filled to reach #3 honestly; #4 and #5 are strictly
stronger.

## 1. The closed skeleton, in one paragraph

`CProverGOTO.coreCFGToGoto_forward_simulation` (in
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrect.lean:849-875`,
~880 LoC of supporting proof, axioms
`[propext, Classical.choice, Quot.sound]`) takes:

- a source evaluator `δ` and target evaluators `δ_goto`/`δ_goto_bool`;
- an `ExprTranslationPreservesEval` witness saying the two
  evaluators agree on translated expressions;
- a `WellFormedSemanticEvalGotoBool` witness saying the boolean
  evaluator commutes with `not`;
- a `WellFormedTranslation cfg pgm` witness asserting the program is
  structurally what we expect;
- a call-free hypothesis (`Core.CmdExt.isAdmittedCmd`);
- a terminating source run
  `Core.CoreCFGStepStar π φ δ cfg (.cont entry σ false) (.terminal σ' b)`,

and produces a matching `StepGotoStar … (.terminal σ' b)` on the
target GOTO program.

Phase 3 of the expansion plan added a parallel
`coreCFGToGoto_forward_simulation_storeCorr` whose conclusion uses
`SemanticsTautschnig.ExecProg` and `StoreCorr`, parameterised by a
`SteppingBridges` bundle (in
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrectStore.lean`).

Everything below is "what is *not* in this skeleton, and what is
needed to get to a real correctness theorem against the actual
translator code."

## 2. Gap A — Discharge `WellFormedTranslation` against the actual translator

This is the largest concrete missing proof.

### What is needed

A theorem of the shape:

```lean
theorem coreCFGToGotoTransform_wellFormed
    (Env : Core.Expression.TyEnv) (pname : String) (cfg : Core.DetCFG)
    (initTrans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init : ...)  -- the initial GotoTransform state we expect
    (δ δ_goto δ_goto_bool : ...)
    (h_eval_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : coreCFGToGotoTransform Env pname cfg initTrans = .ok ans) :
  ∃ pgm,
    pgm.instructions = ans.instructions ∧
    -- ... wrapping by procedureToGotoCtxViaCFG
    WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool
```

### Why it is hard

`coreCFGToGotoTransform` is a 100-line imperative `for`-loop in the
`Except Format` monad over the CFG's block list, with nested
`for`-loops over commands, plus a second pass that patches GOTO
targets. To verify it you need:

1. **A loop invariant** capturing the partial-translation state
   after `k` blocks: the prefix of `pgm.instructions` is structurally
   well-formed for the first `k` blocks; `labelMap` resolves all
   visited labels; `pendingPatches` is a list of `(idx, label)` pairs
   whose labels are forward references.

2. **Per-block lemmas:**
   - `emitLabel` advances `nextLoc` by 1 and adds a `LOCATION`
     instruction (proves `WellFormedTranslation.layout_location`).
   - For each `Imperative.Cmd` shape, `Cmd.toGotoInstructions` (in
     `Strata/DL/Imperative/ToCProverGOTO.lean:95-205`) emits exactly
     the shape `CmdEmittedAt` requires — this requires unfolding the
     translator and proving each constructor case.
   - For `condGoto`: `emitCondGoto (e_goto.not)` produces a GOTO
     whose guard is `e_goto.not` (gives `layout_cond_goto` plus the
     negation half of `layout_cond_goto_guards`); `emitUncondGoto`
     produces a GOTO whose guard is `Expr.true` (the second half).
   - For `finish`: nothing emitted by the per-block code; the
     `END_FUNCTION` is appended outside the loop, which connects to
     `layout_finish`.

3. **Patching is order-preserving.** The second pass
   (`patchGotoTargets`) only mutates `target` fields, never `type` or
   `guard` or `code`, so any structural property of the unpatched
   program transfers; *and* after patching, every emitted GOTO's
   `target` is `some (labelMap[label])`. This requires inversion
   lemmas on `patchGotoTargets`.

4. **`labelMap_inj`.** Each block label is inserted into `labelMap`
   exactly once, with the value being the current `nextLoc`, and
   `nextLoc` is strictly monotonic. Therefore the map is injective —
   but proving this needs an invariant tying the state of `labelMap`,
   `nextLoc`, and the `instructions` array across loop iterations.

### Cost estimate

Plausibly **800–1500 LoC** of Lean. The closest analogue in this
codebase is `Strata.Transform.DetToKleeneCorrect`, which proves a
different translator correct by exactly this style of inductive
invariant.

### Risk

Two structural fields are slightly suspect:

- `labelMap_inj` may *fail* in the wrapping pipeline
  `procedureToGotoCtxViaCFG` if block labels collide across nested
  scopes. The block labels come from `stmtsToCFG`'s string generator
  and are probably fine, but this needs verifying.
- `layout_block_body` requires every block's command list to
  translate consistently. If `Cmd.toGotoInstructions` ever emits a
  different number of instructions than `gotoInstrCount` predicts
  (e.g. for a `.cover` we miscount), the field does not hold.

## 3. Gap B — Discharge `ExprTranslationPreservesEval` against `Lambda.LExpr.toGotoExprCtx`

### What is needed

A theorem:

```lean
theorem toGotoExprCtx_preservesEval
    (δ : SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_compatible : ...)  -- the two evaluators are defined consistently
    : ExprTranslationPreservesEval δ δ_goto δ_goto_bool
```

with the witness `tx := Lambda.LExpr.toGotoExprCtx [] · |>.toOption`
(success path).

### Why it is hard

`LExpr.toGotoExprCtx` is a 100-line structural recursion over
`Lambda.LExpr` (in `LambdaToCProverGOTO.lean:264-357`) that
pattern-matches on every constructor and operator. To prove
`ExprTranslated` for every Core expression you need:

1. **Structural induction on `Lambda.LExpr`.** Easy.

2. **Per-operator lemmas — and there are *many*:**
   - **Integer ops:** `+`, `-`, `*`, `/`, `mod`, comparisons,
     equality. Need to know that
     `Lambda.LExpr.app (.app (.op "+") e1) e2` evaluates by Core's
     interpreter to the integer sum, *and* the GOTO `multiary .Plus`
     evaluator does the same on the translated args. This pins down
     *which* concrete `δ_goto` we mean.
   - **Bitvector ops:** 30+ operators, including `bvExtract` (which
     is unary in Core but binary in GOTO via `Extractbits`),
     `Concat`, signed/unsigned comparison, overflow predicates.
     Many have CBMC-specific ABI conventions (e.g. signed-bv operands
     cast via `toSigned`); each needs a per-operator soundness
     argument.
   - **Bool ops:** `Not`, `And`, `Or`, `Implies`. These bridge
     `HasBool.tt` ↔ `Value.vBool true` and similarly for `false`.
     Phase 2.d's `valueCorrCore` instance covers exactly these for
     the boolean case.
   - **String / Real / Map / Regex / Quantifiers:** most fall through
     to `functionApplication` and CBMC may or may not handle them.
     For these we either declare them out of scope ("partial
     correctness on the supported fragment") or supply concrete
     evaluator semantics.
   - **Special cases that are genuinely tricky:**
     - `Int.EuclideanDiv` / `Int.EuclideanMod` are *expanded* into
       compound expressions (`mkEuclideanDiv`, `mkEuclideanMod`) —
       the proof must show the expansion is semantically equivalent,
       *and* that CBMC interprets the expanded shape correctly.
     - `SDivOverflow` is similarly expanded.
     - `bvExtract` is parsed from the operator name — the proof
       needs the parser to be correct.
     - `old(e)` is translated to `Expr.unary .Old`, which is *not*
       evaluable by `concreteEval` — it lives on the two-state
       `concreteEval₂`. So `ExprTranslationPreservesEval` must
       restrict to single-state expressions or we need a two-state
       evaluator on the Core side too.

3. **`tx_commutes_not`.** Already required by the simulation proof.
   Easy when `not` translates to `Expr.unary .Not`, which it does.

### Cost estimate

**1000–2000 LoC**, dominated by per-operator lemmas. This is a
separate spec because *what* we need to prove depends on *which*
concrete evaluators we instantiate `δ` and `δ_goto` to, which in turn
depends on which downstream property we want to preserve.

### Risk

- **The two evaluators do not exist concretely yet.** Core's `δ` is
  parametric over `CoreEval`; GOTO's `δ_goto` is parametric over
  `SemanticEvalGoto`. Phase 2 added `concreteEval` on the GOTO side
  but it is `partial def`, so it cannot be directly used as `δ_goto`
  in proofs. To discharge `ExprTranslationPreservesEval` we either
  (a) make `concreteEval` total (Phase 2.c), (b) keep both
  evaluators abstract and supply axiomatic `ExprTranslated`
  per-operator, or (c) define a new total `gotoConcreteEval'` over a
  restricted `Expr` fragment.
- **Restricted fragment.** Several operators don't even have a
  Core-side semantics yet (e.g. some BV operators are uninterpreted
  in Lambda). These need to be declared out of scope, and the
  discharge becomes "ExprTranslationPreservesEval holds on the
  supported expression fragment".
- **Side effects.** GOTO `Expr` includes `.side_effect .Nondet` and
  `.side_effect .Assign` — Core has nothing like this. The proof
  must rule these out from the source side (the translator never
  produces them in the success path) or admit them only in the
  wrapped `step_assign_nondet` / `step_function_call` cases.

## 4. Gap C — Discharge the `SteppingBridges` bundle for the actual translator

The Phase-3 theorem `coreCFGToGoto_forward_simulation_storeCorr`
produces an `ExecProg` derivation parameterised by a
`SteppingBridges` bundle. The bundle abstracts the per-step bridges
in `Bisim.lean`, each of which has its own hypotheses (`EvalBoolCorr`,
`EvalValueCorr`, `Function.Injective nameMap`,
`findLocIdx`-resolution, value-correspondence on assigned values,
syntactic Nondet checks).

To turn this into a usable corollary, you need to **discharge the
bundle for the actual translator output**. That means:

1. **A concrete `nameMap`.** For `procedureToGotoCtxViaCFG`, it is
   `<proc>::<scope>::<name>` — and a proof that this is
   `Function.Injective` on the *actual* identifiers the translator
   sees. If the source program has a top-level local `x` shadowed by
   an inner-block `x`, the renamings collide. Mitigation: either
   parameterise `nameMap` by source-level scope (a richer
   `Core.Expression.Ident` than just a string), or restrict the
   input source to non-shadowing programs.

2. **A concrete `eval`.** Tautschnig's `concreteEval` is the natural
   choice, but as noted it is `partial def`. Phase 2.c is the
   relevant follow-up.

3. **`EvalBoolCorr` / `EvalValueCorr` instantiations.** These are the
   boolean / value forms of `ExprTranslationPreservesEval` on the
   *translated* GOTO side, which folds back into Gap B above.

4. **`findLocIdx`-resolution.** For each `condGoto`, the emitted
   GOTO's target must satisfy
   `findLocIdx pgm.instructions <locationNum> = some <pre-resolved-pc>`.
   This is a property of the `patchGotoTargets` second pass and folds
   into Gap A.

5. **Instruction-code lookups for ASSIGN/DECL/DEAD.**
   `(instrCode pgm pc).bind getAssignLhs = some (nameMap x)` etc.
   Each follows from `Cmd.toGotoInstructions`'s shape, but the proof
   has to enumerate cases.

6. **`toValue v = some .vEmpty` for fresh DECLs.** The bridge for
   `step_decl` requires the source-side initialization value `v`
   corresponds to GOTO's `vEmpty` sentinel. Under `valueCorrCore` no
   `LExpr` constructor satisfies this, so either the bridge has to
   fold `step_decl` with the immediately-following
   `step_assign_nondet` / `step_assign` the translator emits, or the
   `ValueCorr` instance has to be enriched to recognise some
   sentinel.

### Cost estimate

**500–1000 LoC**, mostly mechanical once Gaps A and B are closed.

### Why this matters for property preservation

Forward simulation alone does not quite say "GOTO is safe ⇒ source
is safe". It says "source executes to `(σ', b)` ⇒ GOTO executes to
a corresponding `(σ', b)`". To get "GOTO safe ⇒ source safe" you
need:

- **The failed-flag bridge.** Source `b = true` ⇔ some intermediate
  GOTO PC has `AssertFails`. The Phase-0
  `stepGoto_assert_fail_to_stepInstr` bridge gives one direction; the
  other direction needs a backward-style argument (or use of
  determinism + the forward bridge's converse).
- **The observation lift.** Define `ProgramSafe` on the source CFG
  (no reachable failed-state) and show it is implied by
  `ProgramSafe` on the GOTO `ExecProg`. Phase 0's
  `Reachable`/`ProgramSafe` are tautschnig-side; the lift needs a
  Core-side analogue.
- **Divergent-trace exclusion.** Forward simulation only handles
  *terminating* runs. If the source diverges, neither side
  terminates, so neither emits a failed assertion — but property
  preservation still holds *vacuously* on divergent traces. We need
  either a divergent-coinductive analogue or a careful argument that
  "for all terminating prefixes, safety holds" suffices.

## 5. Gap D — Fragment restriction (calls, cover, nondet init)

The current proof restricts to `Core.CmdExt.isAdmittedCmd`, which
excludes:

| Excluded | Why excluded | What it would take to admit |
|---|---|---|
| `.call _ _ _` | `StepGoto` has no `step_function_call` constructor | Phase 1.a's deferred sub-phase: add `step_function_call` parameterised by a `CallResultRel`, then prove the simulation chain still type-checks. ~80 LoC + signature ripple of ~50 lines across the proof. The harder part is the *real* call semantics: a procedure-environment lookup, parameter passing, `SET_RETURN_VALUE` / return-value retrieval. The Phase 4 `sim_call` primitive in tautschnig's source assumes a `CallResultRel` discharge, which is itself an open obligation per-callee. |
| `.cover label e md` | Source-side semantics is a no-op (it does not fail or change state); GOTO emits an `ASSERT` whose evaluator may flip `failed`. **This is a per-trace divergence**, not a soundness issue — covers exist *to* induce assert-fail traces for coverage analysis. | Either (a) declare divergence: prove a *weaker* simulation that allows the `failed` flag to be set independently on the GOTO side for cover instructions; (b) prove a *trace-set* equivalence: the two languages produce the same set of safe traces, where covers contribute differently to each set; or (c) lift `cover` to source-side semantics that flips `failed` analogously, and accept the source-side meaning change. Discussed in `docs/superpowers/2026-05-19-cover-semantics-discussion.md` (referenced in `CoreCFGToGOTOInvariants.lean:84-86`). |
| `.init _ _ .nondet _` | Source binds *some* value `v` (havoc); GOTO emits a single `DECL` (no value pin). The two are not equational. | Tracked at github.com/strata-org/Strata/issues/1186. Requires either `step_decl` to carry the `InitState` semantics (which it does on this branch — but tautschnig's `decl` always produces `vEmpty`, which is the Phase 0 `step_decl` bridge issue), or fold the bridge with the immediately-following havoc step. |

### Cost estimate

`step_function_call` constructor + ripple: **~150 LoC**. Real call
semantics: a separate spec, possibly **1500+ LoC**. `cover`: a design
call before any LoC. nondet `init`: **~100 LoC** after the
`step_decl` bridge reshape.

## 6. Gap E — The wrapping pipeline (`procedureToGotoCtxViaCFG`)

`coreCFGToGotoTransform` is not the entry point users see. The actual
translator is `procedureToGotoCtxViaCFG` (in
`CoreCFGToGOTOPipeline.lean:188+`), which:

1. Renames identifiers via `renameCoreDetCFG` (or `renameCoreStmt`
   for the structured path).
2. Seeds the type environment with renamed input/output parameters.
3. Emits axioms as `ASSUME` instructions at the procedure entry.
4. Emits distinct declarations as pairwise `!=` ASSUMEs.
5. Calls `coreCFGToGotoTransform`.
6. Appends an `END_FUNCTION` instruction.
7. Translates procedure contracts (preconditions / postconditions /
   loop invariants / measure decreases) into JSON-encoded named
   fields on instructions.

Each of these steps changes the meaning of the program in subtle
ways:

- **Renaming.** The `<proc>::<scope>::<name>` rewrite must be
  semantics-preserving on the source side, which requires either
  (a) showing `renameCoreDetCFG` commutes with `EvalDetBlock` (a
  bisimulation modulo renaming), or (b) viewing the renamed CFG as
  the *real* source program and not connecting it back. Path (b) is
  honest but reduces what we are claiming.
- **Axiom emission.** The translator turns `Core.Axiom { e := φ, ... }`
  into a leading `ASSUME φ`. The corresponding source-side claim is
  "every reachable state satisfies φ" — *not* "execute the assume" —
  which is a different kind of fact. We need either (a) a
  meta-theorem that source axioms are sound (i.e. φ is true in every
  state, not just assumed), in which case the ASSUME is trivially
  redundant; or (b) a target-side reading that the GOTO program is
  "verifying assuming φ", which is what CBMC actually does.
- **Distinct declarations.** Same as axioms but for `distinct`:
  pairwise inequalities are emitted as ASSUMEs. The source-side
  semantics says distinct names refer to distinct values; the
  target-side says "we assume they are distinct". Needs the same
  translation argument as axioms.
- **Contracts.** `#spec_requires`, `#spec_ensures`,
  `#spec_loop_invariant`, `#spec_decreases` are JSON-encoded named
  fields that CBMC's contract-checking mode reads. Their meaning
  lives in CBMC, not in our `StepGoto` semantics. To prove them
  sound we need a *meta*-correspondence between Core's contract
  semantics (`Procedure.Spec`) and CBMC's contract checker — which
  is not Lean-formalisable without modelling CBMC.
- **`END_FUNCTION` placement.** *(Resolved as of commit
  `1de80e8e0`.)* Previously the wrapper appended one `END_FUNCTION`
  after the per-block translation, and the per-block `.finish` case
  emitted *no* instruction. With multiple `.finish` blocks, only the
  *last one's* fall-through reached the trailing `END_FUNCTION`;
  intermediate `.finish` blocks fell through into the next block's
  `LOCATION`, executing arbitrary code that source-level semantics
  said was unreachable. The fix (Option 1 in the table below) emits
  one `END_FUNCTION` per `.finish` block inline, dropping the
  wrapper's trailing append. `WellFormedTranslation.layout_finish`
  is now satisfiable as currently written.

  The choice between Option 1 (multiple `END_FUNCTION`s) and Option 2
  (each `.finish` emits a `GOTO` to a shared exit) was a decision
  about presentation vs. proof-shape: Option 2 is closer to CBMC's
  idiomatic GOTO output but requires a non-trivial reshape of
  `WellFormedTranslation.layout_finish` and one extra step in the
  per-block simulation argument. Option 1 keeps the layout invariant
  unchanged and the simulation proof one-step-per-block; the only
  cost is multiple `END_FUNCTION` instructions in one program, which
  CBMC accepts.

  | Option | Description | Status |
  |---|---|---|
  | **Option 1 (chosen)** | Emit `END_FUNCTION` per `.finish` block inline | Landed in `1de80e8e0` |
  | Option 2 | Emit `GOTO`-to-shared-exit per `.finish`; one `END_FUNCTION` at end | Future option if CBMC convention matters |
  | Option 3 | Add a precondition: at most one `.finish`, last in block list | Rejected (footgun for `Procedure.Body.cfg` users) |

### Cost estimate

A separate spec, plausibly **500–1000 LoC** for the remaining wrapper
issues (renaming, axioms, distincts, contracts). The `.finish`
sub-issue is no longer in this scope (resolved). The remaining
wrapper-correctness work is now genuinely about "does this pile of
ASSUMEs and JSON annotations correspond to source semantics" rather
than "does the program even terminate where the source said".

## 7. Gap F — Source-side semantics fidelity

The proof assumes Core's semantics (`Imperative.EvalCmd`,
`Core.EvalCommand`, `EvalDetBlock`, `CoreCFGStepStar`) is the right
meaning of the source language. This is its own claim:

1. **`EvalCmd` covers the language.** It currently has constructors
   for `init`/`set` (det / nondet), `assert` (pass/fail), `assume`,
   `cover`. Anything else? The `Imperative.Cmd` inductive should be
   totalised: every constructor either has a step rule or is rejected
   at typecheck.
2. **`EvalDetBlock` is faithful to the CFG semantics CBMC users have
   in mind.** The block runs commands sequentially, then transfers;
   on `.condGoto` it picks the branch by evaluating the condition.
   The faithful question is: does CBMC also evaluate the guard once
   and pick a branch, or does it do something subtler (e.g. symbolic
   execution forking)?
3. **`CoreCFGStepStar` admits exactly the runs CBMC can simulate.**
   Currently it is a clean reflexive-transitive closure, but CBMC has
   loop-unwinding bounds, depth limits, and assumption-discharge
   orderings. None of those are modelled.
4. **The structured-to-unstructured pass `stmtsToCFG`** has *no*
   correctness theorem. There is `Strata/Transform/StructuredToUnstructured.lean`
   (188 lines) but no `StructuredToUnstructuredCorrect.lean`. So if
   the entry point is a structured Core procedure, we are claiming
   forward simulation only against the *unstructured* CFG semantics —
   losing the bridge back to the structured semantics.

### Cost estimate

`stmtsToCFGCorrect`: **~500 LoC**. Source-semantics faithfulness
arguments: more like meta-arguments and design notes than Lean
proofs.

## 8. Gap G — Direction (forward vs. backward) and termination model

Even with all of A–F discharged, the resulting theorem is *forward
simulation* on *terminating* runs. For a real CBMC verifier this is
*enough for soundness*, but not for *completeness*:

- **Soundness as currently stated.** "If the source program reaches
  an asserting failure on some terminating trace, the GOTO program
  also reaches an asserting failure." This means: **if CBMC says
  safe, the source might still have a non-terminating bug or a
  divergent counterexample CBMC missed.** Whether this is acceptable
  depends on what CBMC users believe it does.
- **Completeness (backward simulation).** "If the GOTO program
  reaches an asserting failure, the source does too." Without this,
  **CBMC could falsely report bugs that do not exist in the
  source.** Phase 0's bridges are formally bidirectional (each
  `stepGoto_X_to_stepInstr` would have a converse
  `stepInstr_to_stepGoto`); we have only the forward direction.
- **Divergent-trace handling.** If the source is non-terminating
  (e.g. an infinite loop with a true assertion), the current theorem
  says nothing. For a CBMC-style "bounded model checking" reading
  this is fine (CBMC unwinds loops finitely). For a "we proved it
  correct" claim it is a loose end.
- **Concurrency, threads, atomicity.** Explicit non-goals in
  `Semantics.lean:21`, but CBMC supports these. So our correctness
  theorem is for the single-threaded fragment only.
- **Memory model.** Not modelled at all. CBMC supports a concrete
  byte-level memory model with pointers and aliasing. Our Stores are
  pure `Ident → Option Expr` (or `String → Option Value`). Gigantic
  gap if we ever want to verify code that uses pointers.

### Cost estimate

Backward simulation: 2× to 3× the forward proof's LoC. Coinductive
divergence handling: another spec entirely. Concurrency / memory:
not really expressible without restructuring everything.

## 9. The dependency graph

```
                   correctness theorem (#3 in §0)
                                  ▲
              ┌───────────────────┼─────────────────────┐
              │                   │                     │
         Gap A (WF)         Gap B (Eval)          Gap C (Value)
         (translator         (LExpr             (concrete σ
          well-formed)       eval correct)        correspondence)
              │                   │                     │
              │                   ▼                     │
              │            Phase 2.c                    │
              │            (concreteEval                │
              │             totalised)                  │
              │                                         │
              └────────────────►◄────────────────►◄─────┘
                                  │
                            already closed:
              forward simulation (CoreCFGToGOTOCorrect.lean)
              StoreCorr lift   (CoreCFGToGOTOCorrectStore.lean)

       Gap D (fragment) ──┐
       Gap E (pipeline)  ─┤
       Gap F (source)    ─┼─► strengthen the *statement*
       Gap G (direction) ─┘   beyond restricted-fragment forward simulation
```

Closing **A + B + C** gives you a *concrete*, *unconditional*,
*call-free*, *forward*, *terminating* correctness theorem for
`coreCFGToGotoTransform`. That is the natural next milestone.

**D–G** are independent strength-improvements. They can be ordered
however the application's needs dictate; D has the most leverage
because admitting `.call` opens the door to actually-useful
programs.

## 10. Concrete prioritisation (with effort estimates)

| Priority | Task | LoC | Calendar | Unlocks |
|---|---|---|---|---|
| **P0** | Gap A: `WellFormedTranslation` discharge | 1000–1500 | 2–3 weeks | Removes one of the two open hypotheses |
| **P0** | Gap B: `ExprTranslationPreservesEval` discharge (boolean + integer fragment) | 400–800 | 1–2 weeks | Removes the other open hypothesis on a restricted expression fragment |
| **P1** | Gap C: discharge `SteppingBridges` for the actual translator output | 500–1000 | 2–3 weeks | Closes Phase 3 end-to-end concretely |
| ~~P1~~ | ~~Gap E (latent `.finish`/`END_FUNCTION` issue): investigate and fix~~ | ~~discovery-bound~~ | ~~days~~ | **Done in `1de80e8e0`** (Option 1) |
| **P2** | Gap D: admit `.call` (Phase 1.a `step_function_call` + ripple + concrete `CallResultRel`) | 200 + a downstream spec | 1 month+ | The largest practical fragment expansion |
| **P2** | Gap F: `stmtsToCFGCorrect` | 500 | 1–2 weeks | Lifts the theorem to structured Core procedures (the actual user entry point) |
| **P3** | Gap B (full): bitvector / string / quantifier operators | 500–1000 | 2–3 weeks | Removes the "boolean + integer fragment" caveat |
| **P3** | Gap E (axioms / distincts / contracts): wrapping correctness | 500 | 1–2 weeks | Lifts theorem from `coreCFGToGotoTransform` to `procedureToGotoCtxViaCFG` |
| **P4** | Gap G (backward simulation) | 1500–2500 | 4–6 weeks | Bisimulation; "no false bugs" guarantee |
| **P4** | Gap D (`.cover` semantics) | design + 200–400 | weeks | Resolves a documented per-trace asymmetry |
| **out of scope?** | Concurrency / threads / memory model | unbounded | months+ | CBMC parity for non-trivial C |

## 11. The honest one-paragraph summary

The current state of "is `coreCFGToGotoTransform` correct?" is: *we
have a closed forward simulation skeleton on the call-free
`DetCFG → GOTO` slice, modulo two open hypotheses
(`WellFormedTranslation` against the actual translator,
`ExprTranslationPreservesEval` against `Lambda.LExpr.toGotoExprCtx`).*
The latent `.finish`/`END_FUNCTION` placement bug that previously
made `WellFormedTranslation.layout_finish` unprovable on programs
with multiple `.finish` blocks has been fixed (commit `1de80e8e0`).
To turn the skeleton into a real, unconditional correctness statement
of CBMC-grade strength, in priority order: (1) discharge the two
open hypotheses against the actual translator code; (2) connect
them through Phase 3's `SteppingBridges` to get concrete-`Value`
property preservation; (3) admit `.call`s and the remaining wrapper
correctness questions (axioms, distincts, contracts); (4) lift to
the structured-Core entry point via `stmtsToCFGCorrect`; (5) prove
backward simulation if completeness matters. Steps 1–2 close the
"this proof is about the real translator" loop; steps 3–4 expand the
supported fragment to something usable; step 5 promotes the theorem
from soundness to bisimulation. Everything else (concurrency, memory
model, real CBMC-feature parity) is a different research project.
