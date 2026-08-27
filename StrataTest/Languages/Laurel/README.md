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

## Naming test files

Two conventions, picked by what the test program does rather than by which folder it sits in:

- **A program that verifies gets a combination name**: name the file after the combination of features it exercises, so the set of covered combinations is readable from the file list. `TryFinallyThrow` exercises `try`/`finally` together with `throw`; `ThrowsOnClause` exercises one clause thoroughly. Treat a contract clause as a feature in its own right — `ensures` and `modifies` already are, so `throws` and `throwsOn` are too. If a name describes a *mechanism* (a pass, a lowering step) rather than a combination of surface features, it is the wrong name: the mechanism is why the case is interesting, which belongs in the file header, not in its title.
- **A program that is rejected gets a rule name**: name the file after the rule being enforced, as the files under `Resolution` do — `ThrowsEscape`, `CatchGuardTyping`, `UnsupportedExceptionShapes`. A rejection test pins one diagnostic, so a combination name would over-promise by implying the combination is supported.

Two consequences worth stating, because both have been got wrong before:

- Prefer folding a case into the file that owns its feature over adding a file. More files than there are combinations is a smell, and so is a grab-bag name like `Scenarios` that admits the file has no single subject.
- A test whose subject is a *pipeline* property rather than a language one does not belong here at all. Pass ordering is declared on the pass itself with `comesBefore`/`comesAfter` and checked by `orderingRespected`, which is cheaper and harder to bypass than an end-to-end test standing in for it.

## Debugging

If an E2E test fails, the likely cause is one of Laurel's lowering passes. We can figure out which of the passes is to blame by using the Laurel semantics. If the output of running the Laurel's type checker or interpreter changes between passes, then this pass is to blame. Another method of investigation is to manually inspect the Laurel program between each pass to see where it changes its meaning.

# Idiomaticity

Idiomaticity tests enable manually reviewing the quality of the encoding of a particular pass. Such a test is always made for a particular pass, named `<pass>Test`, and compares code right before and right after the pass runs. Note that many passes only take a subset of Laurel code, so idiomaticity must take this into account when specifying the input program.

Having an idiomaticity test per pass is recommend but not required.

# UnitTests

The folder UnitTests contains tests that require calling internal Laurel APIs. Adding unit tests is recommend for utility functions such as the generic Laurel traversal code that's in MapStmtExprTest.

# UseCases

The folder UseCases contains tests that demonstrate how a front end is expected to model a source-language pattern, rather than pinning the semantics of a single Laurel construct. They answer "is this idiom expressible, and does it read reasonably?" instead of "is this construct correct?", so they usually combine several features and mirror a shape from Java, Python, or JavaScript.

A use-case test is still an executable test — it fails if the pattern stops working — but when it fails, the question to ask is whether the idiom is still supported, not whether one construct regressed. `UncheckedExceptions` is an example: it shows a front end turning implicit runtime failures (null dereference, division by zero) into explicit guarded `throw`s, which is a usability claim about the exceptional surface rather than a rule about `throw`.

# CBMC

WIP.