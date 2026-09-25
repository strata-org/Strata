/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in
-- the same process and environment as Verso
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Strata Core Transforms and Analysis" =>
%%%
shortTitle := "Core Transforms and Analysis"
%%%

# Introduction

This document describes the transforms and analyses available for Strata Core
programs. Transforms are program-to-program rewrites that are independent of any
specific analysis. Analyses consume a (possibly transformed) Core program and
produce verification results. For the language definition itself, see the
[Strata Core Language Definition](../../langdef/html-single/).

# Program Transforms

Program transforms are applied to a Strata Core program before analysis. They
are independent of the choice of analysis and can be composed in sequence. The
`strata transform` CLI command applies one or more passes to a Core program:

```
strata transform file.core.st --pass <name> [--procedures <procs>] [--pass <name> ...]
```

Passes are applied left to right. The `--procedures` and `--functions` flags
bind to the most recent `--pass`.

## Procedure Inlining (`inlineProcedures`)

Replaces procedure call sites with the body of the callee, substituting actuals
for formals. The `--procedures` flag restricts which procedures are inlined; if
omitted, all eligible procedures are inlined.

## Call Elimination (`callElim`)

Replaces each procedure call with the contract-based encoding described in the
language reference: assert preconditions, havoc outputs, assume postconditions.
This is the standard modular verification encoding.

## Loop Elimination (`loopElim`)

Replaces loops with their invariant-based abstraction: assert the invariant,
havoc the modified variables, assume the invariant and the negation of the
guard.

## Procedure Filtering (`filterProcedures`)

Removes all procedures except those named in the `--procedures` flag (and any
procedures they transitively depend on).

## Irrelevant Axiom Removal (`removeIrrelevantAxioms`)

Removes axioms that do not mention any of the functions named in the
`--functions` flag, reducing the size of the analysis problem.

Additional internal transforms (e.g., `PrecondElim`, `DetToKleene`,
`StructuredToUnstructured`) are used by the analysis pipelines but are not
currently exposed via the CLI.

# Configuring the Pipeline

The transforms above run as a *pipeline*: an ordered list of phases, each declaring
what it requires of the program it receives, what it establishes, and what it leaves
standing. A list composes when every phase's requirements are met by the phases before
it, and the back end accepts it when the list also delivers what obligation extraction
needs. Both are checked before anything runs, so an unworkable order is reported rather
than attempted.

`strata verify --display-phases` prints the default order as a pasteable argument, along
with the phases available outside it, and `--display-phase-contracts` prints what each
phase requires, delivers and preserves. Those two commands are the vocabulary: this
document deliberately does not list the phases, because the tool's output cannot fall out
of date and prose can.

`--phases <list>` runs a list of your own. With no file to verify it reports whether the
list composes, which is the cheapest way to try an order out. Order matters and the
checks will tell you so: naming a phase before the one that establishes what it requires
is refused, with the phase that would have established it named in the message.

`--phases` is also refused for inputs whose verifier cannot honour it, `.csimp.st` and the
B3 files, because those are verified through their own translation rather than the Core
pipeline.

A phase list may assert a fact instead of establishing it. For every fact with an
executable check there is an `assert<Fact>` phase — `assertNoLoops` and the like — which
checks the fact on the program and passes it through. That is how a list can stand where
another order runs a transform: if the input already has the property, checking it is
cheaper than rewriting the program to produce it.

A tool that keeps a registry of pipelines gates this further. `stratainternal` accepts
`--pipeline <name>` to run a registered pipeline, and refuses a `--phases` list that no
entry holds, answering with the three ways forward: enable unregistered pipelines in a
development build, run an existing pipeline by name if your package already uses that
exact list, or register the list by adding the entry the refusal prints. Where
unregistered pipelines are enabled the list runs and the run says so. Registration is what
lets a change to the phase vocabulary be carried to the packages that depend on one,
rather than silently changing what they verify.

A registered entry may also state facts it assumes of its input, and those are where the
assert forms earn their place: a command line cannot prove anything, so `--pipeline` puts
an `assert<Fact>` phase in front for each assumed fact and reports which ones it added.
The entry's own phases are unchanged; the checks are the price of arriving without a proof.

From Lean there is a second route. A front end that proves facts of the program it emits
can assume them instead, through the validating entry points that take those facts and the
proof that they hold, and then omit the phases that would have established them. A command
line has no way to supply such a proof, which is why the flags offer nothing equivalent.

`--no-cse`, `--function-inlining` and `--unroll-bounded-quantifiers` are unknown options: a
pipeline names the phases it runs, so no option reshapes it. To run those phases, name them
with `--phases` (`--display-phases` prints the default order to start from).

Migrating is mechanical but not a drop-in: a script or CI job still passing one of these
exits with an unknown-option error, and `--phases` names the whole order rather than toggling
one phase. Start from `--display-phases` and edit that list. On `stratainternal` an
unregistered `--phases` list is refused, so a caller of a registered pipeline uses
`--pipeline <name>` instead.

# Analysis Modes

Strata supports three analysis modes, selected via `--check-mode`. These modes
are independent of the specific analysis being used — they control how results
are classified.

1. *`deductive`* (default): Prove correctness — every assertion must hold on
   all inputs.
2. *`bugFinding`*: Find bugs assuming incomplete preconditions — only definite
   bugs are errors.
3. *`bugFindingAssumingCompleteSpec`*: Find bugs assuming complete
   preconditions — any counterexample is an error.

Each verification condition produces two queries: a satisfiability check
(`P ∧ Q`) asking whether the property can be true given the path condition,
and a validity check (`P ∧ ¬Q`) asking whether it can be false. The
combination determines the outcome and severity in each mode.

# SMT Analysis

The SMT analysis translates a Strata Core program into SMT-LIB queries and
delegates reasoning to an external SMT solver.

## Type Encoding

Abstract types are encoded as uninterpreted sorts. Algebraic datatypes are
encoded using the `declare-datatypes` command; the generated functions
(constructors, testers, accessors) are mapped to the corresponding SMT
functions (e.g., `Option..isNone` maps to `is-None`).

## Function Encoding

Functions with bodies are inlined by the partial evaluator where possible.
Functions without bodies are declared as uninterpreted functions.

Recursive functions are simplified by the partial evaluator but are encoded as
uninterpreted functions in the SMT encoding. For recursive functions with
`@[cases]`, per-constructor axioms are generated: for each constructor `C` of
the ADT at the `@[cases]` parameter, an axiom representing the corresponding
rewrite rule (e.g., `List.length Nil = 0` and
`forall h t, List.length (Cons h t) = 1 + List.length t`). Recursive functions
without `@[cases]` are encoded as pure uninterpreted functions with no axioms.

Termination checking is always on for `rec` functions. Strata supports two
termination modes:

- *Structural (ADT):* The TermCheck pipeline phase generates a
  `D..adtRank : D → Int` uninterpreted function with per-constructor axioms
  establishing that recursive fields have strictly smaller rank, and a `f$$term`
  verification procedure that asserts `adtRank(callArg) < adtRank(callerParam)`
  at each recursive call site.

- *Int-valued:* For functions with an int-valued `decreases` expression, the
  `f$$term` procedure asserts two obligations at each recursive call site:
  `0 <= call_measure` (non-negativity) and `call_measure < caller_measure`
  (strict decrease), where `call_measure` is the `decreases` expression with
  formals substituted by the actual arguments at the call site.

## Axiom Encoding

Axioms are emitted as universally quantified SMT assertions.
