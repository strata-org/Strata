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
[Strata Core Language Definition](../langdef/html-single/).

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
uninterpreted functions with per-constructor axioms in the SMT encoding. For
each constructor `C` of the ADT at the `@[cases]` parameter, the encoding
generates an axiom representing the corresponding rewrite rule (e.g.,
`List.length Nil = 0` and `forall h t, List.length (Cons h t) = 1 + List.length t`).

## Axiom Encoding

Axioms are emitted as universally quantified SMT assertions.
