# Program transformations

This directory holds Strata's program transformations (passes) and their correctness
proofs. Most passes rewrite Strata Core programs, and Core's verifier runs them as phases of a
pipeline (`Core.PipelinePhase`, in `Strata/Languages/Core/PipelinePhase.lean`). Each file's
header lists its key definitions and theorems.

## Shared files

- `CoreTransform.lean` — `CoreTransformState`, the state every Core pass runs in, and the
  monad `CoreTransformM := ExceptT Err (StateM CoreTransformState)`. The state records the
  fresh-name generator (`genState`), the cached analyses such as the call graph
  (`cachedAnalyses`), the factory of functions a pass may use besides the program's own
  (`factory`), and per-pass counters for fresh prefixes. It also has the drivers that lift a
  statement-level rewrite to a whole program (`runStmtsRec`, `runProgram`, `runProgramUntil`).
  `CoreTransformProps.lean` holds their properties.
- `Specification.lean` — the trace-based correctness statements shared by passes: the
  `OverapproximatesTraces` family and `AssertValidityPreservedWhen`. `SpecificationProps.lean`
  holds their properties, such as the preservation of assertion validity.
- `SpecHoareConnection.lean` — transports a Hoare triple (`Strata.Logic.Hoare.TripleWith`)
  from the output of a pass back to its input along an `OverapproximatesTraces` statement.
  `CoreSpecHoareConnection.lean` specializes the transport to Core triples
  (`Core.Logic.Hoare.Triple`) for passes whose trace relation matches events one by one.
- `CoreSpecification.lean` / `CoreSpecificationProps.lean` — the Core instances of the
  shared statements.

The program-level statements used for whole pipelines (`PhaseOverapproximatesFrom`,
`PhaseReflectsLemmas`, `PhasePreservesDeductiveVerificationFrom`) are not here. They are in
`Strata/Languages/Core/Analysis/DeductiveVerification.lean`, with their properties in
`DeductiveVerificationProps.lean`.

## The files of a pass

A pass named `<Pass>` is laid out as follows.

1. **`<Pass>.lean`** holds the implementation, and it defines the pass's `PipelinePhase`, the
   form Core's pipeline runs, unless the phase's contract is proved (item 4). Ideally the phase's `transform` is a
   program-level function of type `Core.Program → CoreTransformM (Bool × Core.Program)`,
   defined in the same file. The `Bool` says whether the program changed. Running in
   `CoreTransformM` is what keeps the fresh names a pass generates apart from those of other
   passes, and what keeps the cached analyses up to date. A pass should therefore draw fresh
   names from the state's generator rather than from a generator of its own, and it should
   update or drop the cached analyses it invalidates.
2. **`<Pass>Props.lean`** (optional) holds lemmas about the implementation that the proofs
   use: shape facts, well-formedness preservation, simulations of single statements, and so
   on.
3. **`<Pass>Correct.lean`** holds the top-level correctness statement, and
   **`<Pass>CoreCorrect.lean`** holds the statement over Core when `<Pass>Correct.lean` is
   stated for the generic Imperative dialect. For example, `LoopElimCorrect.lean` proves big-step
   simulations for any `PureExpr`, and `LoopElimCoreCorrect.lean` states the trace
   overapproximation and the Hoare-triple transport over `Core.Logic.EventLang.coreBlock`. A
   Core-level file may come with its own `<Pass>CoreProps.lean` for supporting lemmas. These
   files state only top-level results, so helper lemmas belong in a `*Props.lean` file.
4. **`<Pass>FactCorrect.lean`** proves the pass's phase contract, and holds only those
   statements: for every fact the phase claims and does not list in `unproved`, a `*_keeps`
   theorem for its `preserves` (`termCheck_keeps`: a fact that holds of the input holds of the
   output), and a `*_establishes` theorem for its `establishes`, of the shape
   `requires.holds p → (transform p).run s = .ok (b, p') → f.holds p'`. The lemmas about the
   implementation they rest on go in `<Pass>Props.lean`. A phase whose contract is proved
   cannot be defined in `<Pass>.lean`, which this file imports: a small **`<Pass>Phase.lean`**
   then assembles the `PipelinePhase` from the transform and those theorems, its
   `establishes_ok` and `preserves_ok` each applying one of them. A phase with
   `unproved := ProgramFactSet.all` needs neither file. `TerminationCheckPhase.lean` is an
   example. The proofs are fields of the phase, so a phase that drops a fact from `unproved`
   does not compile until the proof exists. Each fact left in `unproved` comes with a comment
   saying why it is not proved.
5. **A pass made of several files** goes in a subdirectory named after it, as `SSA/`,
   `Simplify/`, `WP/` and `Passive/` do. Each file there should cover one part of the pass, and
   its name should say which part.

## Correctness statements

A pass's top-level statement takes one of the following forms.

### `OverapproximatesTraces` and its variants (`Specification.lean`)

A statement about one statement list, usually a procedure body, and the list the pass turns
it into. `OverapproximatesTraces2UptoWhen Rtrace Rtrace_full Rin Rout` says that, from related
entries (`Rin`) admitted by the source's gate, every finite execution of the source has a
finite execution of the target with a trace related by `Rtrace`, and every finished run of the
source has a target run that finishes the same way, in an environment related by `Rout`, with
a trace related by `Rtrace_full`. `OverapproximatesTracesUptoWhen` uses one trace relation for
both, and `OverapproximatesTracesWhen` and `OverapproximatesTraces` fix the environment
relations to equality.

### `AssertValidityPreservedWhen` and the `assertValid` theorems (`Specification.lean`)

`AssertValidityPreservedWhen I L₁ L₂ T pre params₁ params₂` says that for each source `s`
admitted by the precondition `pre` that `T` turns into `s'`, an assertion valid on every trace
of `s'` (from entries admitted by `L₂.initEnvWF params₂ s'`) is valid on every trace of `s`
(from entries admitted by `L₁.initEnvWF params₁ s`). An `OverapproximatesTraces` statement whose
prefix relation reflects the validity of each assertion gives it
(`overapproximatesTraces2UptoWhen_assertValidityPreservedWhen`), and the results compose
(`assertValidityPreservedWhen_comp`). A Core pass states it as `assertValid`, with the pass's
gate as `pre` and the condition on the interpretation `I` as a hypothesis (for example
`Core.LoopElim.assertValid` and `deadDefElim_assertValid`).

### Hoare-triple transport (`triple`)

An `OverapproximatesTraces` statement with trace equality, or with a relation that matches
events one by one, carries a Hoare triple proved on the output back to the input
(`SpecHoareConnection.lean`, `CoreSpecHoareConnection.lean`), and so carries Core's
`Procedure.contractTriple`. A Core pass states its transport as `triple` in
`<Pass>CoreCorrect.lean`, for example `Core.LoopElim.triple`, and the
`StrataTest/Languages/Core/Tests/Logic/HoareAfter<Pass>.lean` tests use it to carry a contract
proved on the output back to the input.

### Per-procedure results over a program (`*_coreProgram`)

The statements above are about one statement list. A `*_coreProgram` theorem lifts them to the
program-level transform: when the pass turns `p` into `p'`, each structured procedure body `ss`
of `p` has a body `ss'` at the same declaration index of `p'`, and the overapproximation,
`assertValid` or `triple` statement holds between `ss` and `ss'` (for example
`Core.LoopElim.overapproximatesTraces_coreProgram`). The first two are stated for the
transformation sending only `ss` to `ss'` (`fun s => if s = ss then some ss' else none`;
`assertValidityPreservedWhen_single` builds the second). `validOnTracesVerifier_coreProgram` adds
that a verifier that is valid on traces and accepts `ss'` makes every assertion of `ss` valid.

### Procedure correctness from a verification statement (`ProcedureAssertsValidOnTraces`)

A pass that builds a statement to verify a procedure against its contract states that the
validity of that statement gives `ProcedureAssertsValidOnTraces`
(`Languages/Core/Analysis/ProcedureCorrectness.lean`): the procedure exists, every assertion its
body reaches is valid, and the non-free postconditions hold at the end of every run of the
body that finishes. `procBodyVerify_procedureCorrectOnTraces` (`ProcBodyVerifyCorrect.lean`)
is the example.

### The phase contract (`Languages/Core/PipelinePhase.lean`)

A statement about which program facts a phase delivers, not about its semantics: the
`establishes_ok` and `preserves_ok` fields of `PipelinePhase` prove that each fact the phase
claims and does not list in `unproved` holds of its output, given its `requires` on the input.
Pipeline validation relies on these claims to order phases. `<Pass>FactCorrect.lean` holds
the proofs.

### `PhaseOverapproximatesFrom` (`DeductiveVerification.lean`)

A statement about a whole `PipelinePhase`: whenever the phase turns `p` into `p'`, every entry
of `p` (a procedure entry, or the declarations entry that reads axioms, `distinct` declarations
and lemmas) has a corresponding entry of `p'` whose runs overapproximate its own up to
`ValidityReflected`. With `PhaseKeepsLemmaLabels` it preserves deductive verification
(`PhaseOverapproximatesFrom.preservesDeductiveVerification`), and a sequence of such phases
does too (`PhasesRun.preservesDeductiveVerification`).

### `PhaseReflectsLemmas` (`DeductiveVerification.lean`)

The statement for phases that rewrite the declarations entry: each lemma of `p` that is
asserted under the facts before it has a lemma of `p'` with the same name and metadata,
asserted under the facts before it, whose truth implies the original's (`DeclsReflect`). On
programs without procedures it gives `PhaseOverapproximatesFrom`
(`PhaseReflectsLemmas.overapproximates`). `MonomorphizeFunctionsCorrect.lean` is an example.
