# Experiment Report: AI-Assisted IR Design for Python Static Analysis

## Summary

This document describes the methodology used to design PythonSSA, a Static Single
Assignment intermediate representation for Python programs. The design was developed
collaboratively between a human language designer and an AI assistant (Claude),
following a data-driven, iterative process that moved from corpus analysis through
design exploration to a formal specification.

## Methodology

### Phase 1: Corpus-Driven Scope Analysis

Rather than designing an IR for "all of Python," we started by analyzing the actual
target corpus — 52 annotated Python files representing real-world AWS service scripts.

**Step 1: Feature extraction tool.** We built `pyFeatures`, a Lean subcommand that
traverses the Python DDM AST and tallies every constructor encountered (statements,
expressions, operators, constants, patterns). This was implemented as a monadic
traversal following existing patterns in the codebase (`Specs.lean`'s `PySpecMClass`).

**Step 2: Corpus-wide analysis.** Running `pyFeatures` on all 52 files produced
frequency counts across 8 syntactic categories. Key findings:
- The corpus uses only 17 of 27 statement types and 19 of 29 expression types.
- Some features dominate: `Name` (3717), `Constant` (2943), `Call` (1376).
- Many features have zero occurrences: all async constructs, `Lambda`, `Yield`,
  `Match`, `Global`, `Nonlocal`.

**Step 3: Coverage tiers.** We computed how many files each feature subset covers:
- 40/52 with just "dominant" features
- 46/52 adding 8 straightforward constructs (While, AugAssign, Slice, IfExp, etc.)
- 50/52 adding ListComp
- 52/52 adding DictComp + GeneratorExp

This let us make an informed scoping decision: target 46/52 files initially
(everything except comprehensions), with a clear path to 50+ later.

**Step 4: Type annotation analysis.** We extracted all type annotations from the
corpus using Python's `ast` module, and cross-referenced with the PySpec type system
(`SpecAtomType` in `Specs/Decls.lean`). This produced a precise `PyType` enum covering
every annotation in the dataset plus the PySpec builtins.

### Phase 2: Interactive Design Exploration

The IR design was developed through a structured Q&A process, with the AI proposing
design options and the human making decisions.

**Approach:** The AI presented design questions with concrete alternatives, often
including code previews showing what each choice would look like in practice. The
human provided decisions along with rationale, which informed subsequent questions.

**Key design decisions and how they emerged:**

1. **Block arguments vs phi nodes.** Human preference stated upfront (Crucible/SWIFT
   style). No exploration needed.

2. **Exception handling model.** This required multiple rounds:
   - AI initially proposed block-level handlers (one handler per block).
   - Human clarified they wanted instruction-level precision — knowing exactly which
     variables were assigned at the point of exception.
   - This led to the "split blocks at raising instructions" design.
   - Human then noted that uninitialized variables and exception optionality are the
     same problem, leading to the `undef`/`isDefined` design.
   - This in turn eliminated the need for trampolines — `undef` padding handles
     the handler fan-in problem naturally.

3. **undef semantics.** Emerged from the exception handling discussion. The human
   explicitly constrained `undef` to be purely about identifiers (not stored in
   data structures), avoiding LLVM-style poison/undef complexity. This was a key
   design insight that kept the IR simple.

4. **finally blocks.** The human proposed `Option Exception` as a parameter, which
   mapped directly to the `undef`/`isDefined` pattern once that was established.

5. **Short-circuit BoolOp, IfExp desugaring.** Human consistently chose precision
   over simplicity: faithful short-circuit semantics via `condBranch`, with the
   expectation that optimization passes can reconstruct higher-level constructs.

6. **Import resolution.** Human directed that imports should not be SSA instructions
   but instead update a binding table during translation, producing fully qualified
   call references in the output.

7. **Class representation.** Evolved from "flat function list" to the more specific
   `@ClassName_init` pattern through discussion of class body execution semantics.

**Observation:** The most productive design insights came from the human identifying
structural similarities between seemingly different problems (uninitialized variables
and exception optionality) and from explicitly constraining the design to avoid
known complexity traps (LLVM undef semantics).

### Phase 3: Design Review Checklist

After the initial design pass, the AI generated a checklist of 8 design points
requiring human attention. This served as a structured review mechanism:

- Some items were straightforward confirmations (chained comparisons, f-strings)
- Some required deeper discussion (exception precision, finally semantics)
- Some surfaced new design decisions (BoolOp short-circuit, IfExp desugaring)

The human annotated each item with decisions and rationale, which were then
incorporated into the revised design.

### Phase 4: Formal Specification

The design was consolidated into a reference manual (`docs/PythonSSA.md`) covering:
- All data types with precise definitions
- Well-formedness invariants
- Desugaring rules with concrete block-diagram examples for every in-scope construct
- Scope limitations explicitly documented
- Pretty-print notation for output format

### Phase 5: Test-Driven Implementation (planned)

The implementation plan follows spec-first, test-driven development:
1. Write example Python files exercising each feature in isolation
2. Hand-write expected SSA output for each example
3. Implement incrementally, validating against tests
4. Evaluate on the original corpus last (held-out benchmark)

The corpus files are deliberately held out from the test suite to serve as an
independent validation that the scoping analysis was correct.

## Tools Built

| Tool | Purpose |
|------|---------|
| `strata pyFeatures` | Lean subcommand: AST feature frequency analysis |
| `tally_features.py` | Python script: aggregate counts across files |
| `coverage_check.py` | Python script: compute file coverage for feature subsets |

## Observations on the Process

**Data-driven scoping works.** Building the feature analysis tool first (< 1 hour)
saved significant design time by focusing the IR on constructs that actually appear
in the target corpus. Without this, we might have designed for `Lambda`, `Yield`,
`Match`, etc. — none of which appear.

**Iterative design with concrete examples.** Each design question was grounded in
concrete Python code and corresponding block diagrams. This prevented abstract
debates and kept decisions testable.

**Human-AI complementarity.** The AI was effective at: exhaustive enumeration
(all constructors, all type annotations), identifying edge cases (chained comparisons,
f-string raising semantics, with-statement exception paths), and generating
structured alternatives. The human was effective at: identifying structural
similarities across problems, constraining designs to avoid known pitfalls, and
making aesthetic/philosophical choices (precision over simplicity, single-sorted SSA).

**Incremental commitment.** The design evolved over multiple rounds rather than being
specified upfront. Each decision was made with full context from prior decisions,
allowing later insights (like `undef`) to simplify earlier designs (like trampolines).
