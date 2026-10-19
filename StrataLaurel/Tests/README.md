# EndToEndTests

The folder EndToEndTests contains tests that operate from the user perspective. They take as input a user program and a method of executing Strata on this program, and expect a certain output from Strata.

Usually the expected output is specified through inline comments that follow a specific format so they're recognized as expected output.

Every feature in Laurel should be tested through the EndToEndTests folder.

The EndToEndTest are divided into three folders:
- Execution. This folder should contains tests for all features that don't relate to verification. These tests should be able to give the expected output by:
    - Executing all procedures without arguments. (Currently these tests are not actually executed, but we will do it once we have a Laurel interpreter)
    - Verifying all procedures
- Resolution. This folder should contain tests for all features. These tests give the expected output by running the Laurel resolver on them.
- Verification. This folder should contain tests for features that relate to verification, such as assertions and contracts. These tests only give their expected output by running unbounded symbolic verification on them.

The folder fixes the harness, and `testLaurelVerification` is used ONLY under `Verification`:

| folder | harness |
|---|---|
| `Execution` | `testLaurelExecution {}`, or with the paths an interpreter cannot run skipped — `skipCoreInterpreter`, `skipLaurelInterpreter`, or both |
| `Resolution` | `testLaurelResolution` |
| `Verification` | `testLaurelVerification` |

`testLaurelExecution` runs three independent paths, each with its own opt-out: the verifier unless
`skipVerification`, the Core interpreter unless `skipCoreInterpreter`, and the standalone Laurel
interpreter unless `skipLaurelInterpreter`. Skip the two interpreters and what is left is exactly
`testLaurelVerification`'s body — so `testLaurelExecution { skipCoreInterpreter := true,
skipLaurelInterpreter := true }` and `testLaurelVerification` do carry no behavioural difference,
and the choice between them is purely the statement of which kind of test this is. Use the one its
folder mandates. Note that `skipCoreInterpreter` ALONE is not that equivalence: it still runs the
Laurel interpreter.

Two things this rule catches. A case whose subject is whether an `assert` or a contract holds is a verification test wherever it happens to sit, and belongs under `Verification` — note that this covers the case that is expected to PASS just as much as the one expected to fail, and the passing one is the dangerous direction: move it to `testLaurelResolution` and it still reports nothing, so it still looks green while no longer checking anything. Satisfy this rule by MOVING the case, never by swapping its harness in place. And a case under `Resolution` that reports nothing under `testLaurelResolution` is not a resolution test: its diagnostic comes from a later pass. Many such cases exist today, and the better ones say so in their header, naming the check that ought to have produced the diagnostic — they are latent bugs in where a check lives, not license to reach for a different harness. Most do not yet say it, so a case here that reports nothing under `testLaurelResolution` is worth checking against this list rather than assumed deliberate.

## Naming test files

Two conventions, picked by what the test program does rather than by which folder it sits in:

- **A program that verifies gets a combination name**: name the file after the combination of features it exercises, so the set of covered combinations is readable from the file list. `TryFinallyThrow` exercises `try`/`finally` together with `throw`; `ThrowsOnClause` exercises one clause thoroughly. Treat a contract clause as a feature in its own right — `ensures` and `modifies` already are, so `throws` and `throwsOn` are too. If a name describes a *mechanism* (a pass, a lowering step) rather than a combination of surface features, it is the wrong name: the mechanism is why the case is interesting, which belongs in the file header, not in its title.
- **A program that is rejected gets a rule name**: name the file after the rule being enforced, as the files under `Resolution` do — `ThrowsEscape`, `CatchGuardTyping`, `UnsupportedExceptionShapes`. A rejection test pins one diagnostic, so a combination name would over-promise by implying the combination is supported.

Two consequences worth stating, because both have been got wrong before:

- Prefer folding a case into the file that owns its feature over adding a file. More files than there are combinations is a smell, and so is a grab-bag name like `Scenarios` that admits the file has no single subject.
- A test whose subject is a *pipeline* property rather than a language one does not belong here at all. Pass ordering is declared on each pass via `creates`/`removes`/`unsupported` over `NodeKind` shapes, and checked at `initialize` by `orderingRespected`, which folds the live shape set through the pipeline and rejects any pass whose `unsupported` shapes are still live. That is cheaper and harder to bypass than an end-to-end test standing in for it.

## Debugging

If an E2E test fails, the likely cause is one of Laurel's lowering passes. We can figure out which of the passes is to blame by using the Laurel semantics. If the output of running the Laurel's type checker or interpreter changes between passes, then this pass is to blame. Another method of investigation is to manually inspect the Laurel program between each pass to see where it changes its meaning.

# Idiomaticity

Idiomaticity tests enable manually reviewing the quality of the encoding of a particular pass. Such a test is always made for a particular pass, named `<pass>Test`, and compares code right before and right after the pass runs. Note that many passes only take a subset of Laurel code, so idiomaticity must take this into account when specifying the input program.

Having an idiomaticity test per pass is recommend but not required.

The only thing an idiomaticity test is allowed to do is parse the program, resolve it, run the pass, and compare the result against an expected program. `runPassForIdiomaticity` in `Tests/Util/TestLaurel.lean` is that flow, and a test should call it rather than re-deriving the steps: give it the pass and a `#strata` program, and it prints the pass's output — with the unchanged prelude dropped — for a `#guard_msgs` golden. `EliminateDoWhileTest` is the reference caller. A test that reaches past parse+resolve+run+compare (verifies, interprets, inspects internal state) is not an idiomaticity test and belongs elsewhere — see the UnitTests note below.

There is one file per pass, and the driver comes in a small family for the shapes a pass can take, all sharing `runPassForIdiomaticityCore`:

- `runPassForIdiomaticity` — a `Program → Program` lowering pass (the common case).
- `runPassAfterForIdiomaticity` — a lowering pass whose input a predecessor must prepare (e.g. `EliminateDeterministicHoles` after `InferHoleTypes`); the predecessor is input-shaping, run in the `prepare` argument, so the test still pins ONE pass.
- `runProgramToCorePassForIdiomaticity` / `runCorePassForIdiomaticity` — a pass that outputs, or both takes and outputs, `UnorderedCoreWithLaurelTypes` (e.g. `transparencyPass`, `functionalRewritePass`).

Pass `prelude := false` for a pass that TRANSFORMS the prelude procedures themselves (e.g. `Contracts`, `FunctionalRewrite`, `TransparencyPass` derive helper procedures from every prelude procedure, under names `dropPrelude` cannot recognise); such a pass's snippet must avoid every operator, since `+`, `>`, `==`, `&&` and friends are calls to prelude wrapper procedures and will not resolve without it.

A few tests legitimately cannot use the driver and say so in their headers: `LiftExpressionAssignments` (its lifter takes a `roots` argument the pass object does not expose, plus unresolved-input error paths), `GlobalParameterization` (a multi-pass sequence), and `ModifiesClausesLayer` (a hand-built `SemanticModel` that `resolve` would not reconstruct).

# UnitTests

The folder UnitTests contains tests that require calling internal Laurel APIs. Adding unit tests is recommend for utility functions such as the generic Laurel traversal code that's in MapStmtExprTest.

**Do not unit test how a feature or a pass behaves.** How a feature behaves belongs in EndToEndTests, from the user's perspective; how a pass encodes it belongs in Idiomaticity, comparing the program before and after that pass. A unit test that builds an AST by hand and calls a pass's `run` on it is the wrong tool for either question, for two reasons:

- It can pass while the feature is broken end to end, because it exercises one pass in isolation rather than the pipeline the user gets.
- It pins an AST that nothing may be able to produce. The parser, the resolver and the type checker all restrict what reaches a pass, so a hand-built input can encode a shape no source program and no earlier pass ever creates.

That second point is worth turning around, because it is easy to get backwards: if a behaviour cannot be expressed as a source program, that is evidence the behaviour is unreachable, not a licence to reach for a unit test. Check whether the shape is reachable — from the grammar, and from what earlier passes construct — before writing anything. If it is not reachable, the change under test needs a different justification than a test can give it, and saying so in the code review is more useful than a test that guards a shape nobody builds.

What is left, and genuinely belongs here, is of two kinds: a utility function with no single caller to observe it through (`MapStmtExprTest`, `HighTypeWalkersTest`, `MatchTypeArgTest`); and a shape that cannot be written in Laurel source, so a front end building an AST is the only way to reach it (`ExceptionAssignTargetTest`, `ValidateFullyAnnotatedTest` — both say so in their headers, which is a good habit). Writing that justification into the file header is worth the two lines: it is what lets the next reader tell a deliberate unit test from a misfiled feature test.

Do NOT add a unit test that pins an internal detail with no behavioural signature — an id-allocation invariant, or the rendering of a generated Core op. Such a test locks in whatever the implementation currently does, including its workarounds, so it fails when someone fixes the underlying wart rather than when someone breaks something. If the property matters it will break a feature test; if it breaks nothing, it is not a property worth a test.

## A known gap

The inline-annotation matcher compares a diagnostic's exact `line:col` range, so a diagnostic carrying NO source range cannot be pinned with `// ^^^` — the caret run always starts at column 2 or later and is at least one column wide, and an unlocated diagnostic reports `0-0`. Such a case still belongs under `EndToEndTests` when its subject is a language rule; pin the message with a `#guard_msgs` golden and say why in the header. `Resolution/Types/DivergentGenericComposite.lean` is the current example. Teaching the matcher an unlocated form would remove the exception.


# UseCases

The folder UseCases contains tests that demonstrate how a front end is expected to model a source-language pattern, rather than pinning the semantics of a single Laurel construct. They answer "is this idiom expressible, and does it read reasonably?" instead of "is this construct correct?", so they usually combine several features and mirror a shape from Java, Python, or JavaScript.

A use-case test is still an executable test — it fails if the pattern stops working — but when it fails, the question to ask is whether the idiom is still supported, not whether one construct regressed. `UncheckedExceptions` is an example: it shows a front end turning implicit runtime failures (null dereference, division by zero) into explicit guarded `throw`s, which is a usability claim about the exceptional surface rather than a rule about `throw`.

# CBMC

WIP.