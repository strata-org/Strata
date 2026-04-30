# Exit Semantics: Design Decisions

**Date:** 2026-04-22
**Status:** Proposed

## Decision 1: Where is exit state represented?

**Context.**
The formal semantics needs to record
whether a configuration is currently "propagating an exit."
That information has to live somewhere.

**Options.**
- (A) A dedicated `Config` constructor, `.exiting (label) (env)`,
  alongside `.stmt`, `.stmts`, `.terminal`, `.block`, `.seq`.
- (B) A flag on `Env` (parallel to the existing `.error` flag).
- (C) A separate `BlockResult` inductive that accompanies each relation,
  as used in some big-step formalisms.

**Tradeoffs.**
(A) keeps exit as a first-class control-flow state,
distinct from the data carried by the store and the evaluator.
The semantics pattern-matches on the `Config` shape
to decide which step rule applies,
and `.exiting` is one of those shapes.

(B) would make step rules shorter
(no extra `Config` case)
but couples control flow to data.
Properties like "exit does not modify the store"
become statements about the flag,
not about the shape of the configuration.

(C) was the form in an earlier big-step draft.
It disappeared when upstream removed big-step (#806).
Returning to it would require re-introducing a relation layer
that the project has deliberately left behind.

**Decision.**
(A) —
exit state is a `Config` constructor.

The small-step semantics already uses this shape,
and #869's review converged on reusing `CoreConfig`
(the Core-level instantiation of this `Config`)
rather than introducing a parallel `StepResult`.
Our proofs build directly on it.

Moving exit state onto `Env` is a possible future refactor
but is out of scope here.

## Decision 2: Exit inside loops propagates out

**Context.**
The type checker permits `exit` inside a loop body.
A loop body is not itself a labeled block,
so an exit reaching the loop body's end has nowhere to be consumed
by the loop itself.

**Options.**
- (A) The loop terminates immediately
  and propagates the exit outward.
- (B) Reject programs with `exit` inside loops.

**Tradeoffs.**
(A) matches the operational evaluator
and matches source-language semantics
(Java `break` / `continue` desugar to `exit`;
early `return` inside a loop desugars to `exit $body`).

(B) would break Python `try`/`except` and every language
that depends on control flow escaping loops.

**Decision.**
(A) —
an exit reaching a loop body's boundary propagates out of the loop.

The small-step relation already realizes this
via `step_loop_exit` and `step_loop_nondet_exit`.
No new step rules are needed for this decision.

## Decision 3: Well-formedness is `exitsCoveredByBlocks`

**Context.**
The theorems about exit need a predicate characterizing
"programs where every exit has a matching enclosing block."

Upstream `Stmt.lean` and `StmtSemantics.lean` already define
`Stmt.exitsCoveredByBlocks : List String → Stmt P CmdT → Prop`
and its `Config.exitsCoveredByBlocks` lift,
along with helper theorems
`step_preserves_exitsCoveredByBlocks`
and `exitsCoveredByBlocks_noEscape`.

An earlier draft of this proposal introduced a new inductive
`WFLabels` with the same coverage semantics
plus an additional no-shadowing constraint.

**Options.**
- (A) Use upstream's `exitsCoveredByBlocks` as the well-formedness predicate.
- (B) Introduce a new inductive `WFLabels` with the same coverage semantics.
- (C) Introduce `WFLabels` as a strictly stronger predicate
  (adding no-shadowing on top of coverage).

**Tradeoffs.**
(A) reuses proven machinery, avoids duplication,
and keeps this contribution aligned with the rest of the codebase.
A downside is that `exitsCoveredByBlocks` is a recursive function,
which is sometimes less ergonomic for structural induction
than an inductive predicate.

(B) would duplicate upstream code
and invite drift between the two predicates.
No new guarantees are produced.

(C) separates concerns cleanly
(coverage vs shadowing)
but adds a predicate whose only consumer at the moment
would be the no-shadowing lemma itself.
No current downstream consumer requires no-shadowing
to reason about its programs.

**Decision.**
(A) —
use upstream's `exitsCoveredByBlocks`.

No-shadowing is not required by any consumer today.
If a downstream proof needs it,
a focused `NoLabelShadowing` predicate can be added later
without affecting the properties documented here.

## Decision 4: Theorem naming uses descriptive names only

**Context.**
An earlier draft used identifiers like "E1" through "E9"
both as theorem names and as cross-references in design docs.

**Options.**
- (A) Descriptive snake_case names
  (`matching_block_consumes`, `nonmatching_exit_propagates`, …).
- (B) E-numbered names
  (`E1_preserves_env`, `E3_matching_block_consumes`, …).
- (C) Descriptive names in code,
  E-numbers preserved in docstrings and design docs
  as stable handles.

**Tradeoffs.**
(A) reads naturally in Lean code
and matches CONTRIBUTING.md's snake_case convention.

(B) makes cross-referencing trivial
but turns Lean code into number soup.

(C) duplicates information
and creates a drift risk
between doc numbers and code names.

**Decision.**
(A) —
descriptive names only.

Reviewer feedback on #993 explicitly preferred this.
Cross-references in docs cite theorem names directly.

## Decision 5: No new proof files are required for this contribution

**Context.**
The initial proposal planned three new files under
`Strata/DL/Imperative/`:
`ExitProperties.lean`,
`ExitWellFormedness.lean`,
and a new `ExitCompleteness.lean`
for the no-escape theorem.

On examination,
upstream `StmtSemantics.lean` already contains
`step_preserves_exitsCoveredByBlocks`
and `exitsCoveredByBlocks_noEscape`
(plus `block_exitsCoveredByBlocks_noEscape` for statement lists),
along with the per-transition step rules
that the proposed `ExitProperties.lean` theorems
would simply restate as named lemmas.

**Options.**
- (A) Ship this contribution as documentation only,
  citing the upstream theorems by their existing names.
- (B) Add a thin file of renamed aliases
  (`matching_block_consumes := step_block_exit_match` etc.)
  for ergonomic downstream use.
- (C) Write and land the three proof files as originally proposed,
  duplicating upstream.

**Tradeoffs.**
(A) is the smallest possible change
and acknowledges that the proofs we intended to write already exist.

(B) adds a layer of indirection.
Some downstream consumers may prefer descriptive names,
but introducing aliases without a consumer asking for them
is premature.

(C) duplicates existing code
and contradicts Decision 3.

**Decision.**
(B) —
add thin named-wrapper files.

The wrappers (`exit_preserves_env`, `matching_block_consumes`,
`nonmatching_exit_propagates`, and so on)
live in `Strata/DL/Imperative/ExitProperties.lean` and
`Strata/DL/Imperative/ExitWellFormedness.lean`.
Each is a one-line proof over the corresponding `StepStmt` constructor
or `Stmt.exitsCoveredByBlocks` definitional equation.

The contribution additionally promotes
`step_preserves_exitsCoveredByBlocks` from private to public,
so §4.3's requirement cites a public symbol.

## Decision 6: Global completeness is preservation, not liveness

**Context.**
An informal claim appears in multiple places:
*"an exit never escapes the procedure body in a well-formed program."*
The claim can be made formal in more than one way.

**Options.**
- (A) Preservation (safety).
  No reachable configuration from a well-formed procedure body
  is outer-`.exiting`.
- (B) Progress (liveness).
  Every `.exiting` reached inside the body is eventually consumed,
  leading to `.terminal`.
- (C) Both, as paired lemmas.

**Tradeoffs.**
(A) is what reviewers literally asked
and what #869's concrete interpreter needs
to justify treating escaped exits as unreachable.

(B) is stronger
but requires a termination argument orthogonal to exit semantics.
It is a substantially larger undertaking
and is not needed by any known downstream consumer.

(C) combines the burden of (B) with the value of (A).
Useful eventually,
not worth blocking this work on.

**Decision.**
(A) —
use preservation.

Upstream's `exitsCoveredByBlocks_noEscape`
already proves preservation
for a starting `Stmt`,
and `block_exitsCoveredByBlocks_noEscape` does the same
for a starting `.stmts`.
This contribution points at those theorems
rather than introducing a new one.

Liveness can be added later as a separate theorem
if a downstream consumer requires it.
The spec's "future work" section
notes that liveness is deliberately out of scope.

## Future work

The following are deliberately out of scope for this work
and are recorded here for future reference.

- **Liveness** (Decision 6, option B).
  A consumer that needs to know every exit *eventually* reaches
  a matching block
  will need a companion theorem
  and a termination argument.

- **Exit state on `Env`** (Decision 1, option B).
  If the Core interpreter (#869)
  or a later refactor
  wants exit state to live on `Env`,
  that is a larger change
  that would revisit every step rule
  and every proof in the affected files.

- **No-label-shadowing predicate** (Decision 3, option C).
  If a downstream consumer needs to reason about programs
  in which inner block labels cannot shadow outer ones,
  a `NoLabelShadowing` predicate can be added
  alongside `exitsCoveredByBlocks`.
