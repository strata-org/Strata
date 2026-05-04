# Exit Semantics: Formal Specification

**Date:** 2026-04-22
**Status:** Proposed

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT",
"SHOULD", "SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL"
in this document are to be interpreted as described in RFC 2119.

## 1. Context

The small-step operational semantics
in `Strata/DL/Imperative/StmtSemantics.lean`
implements `exit` and labeled blocks
through a dedicated `Config.exiting` constructor
and a family of step rules
(`step_exit`, `step_block_exit_*`, `step_seq_exit`, `step_block_body`, …).

This specification documents that behavior
and lists the properties the semantics satisfies.
It makes the existing semantics
explicit and citable
so contributors and downstream features
can build on a proven foundation
rather than re-deriving control-flow facts.

## 2. Definitions

### 2.1 Configurations

A configuration is one of:

| Shape | Meaning |
|---|---|
| `.stmt s env` | about to execute statement `s` |
| `.stmts ss env` | about to execute the first statement of list `ss` |
| `.seq inner ss` | executing `inner`; when it terminates, continue with `ss` |
| `.block L inner` | executing `inner` inside a block labeled `L` |
| `.terminal env` | done, normally |
| `.exiting label env` | propagating `exit label` outward |

A configuration's execution is modelled by the small-step transitions listed in §3.

### 2.2 Labels

An exit label is `Option String`.
`none` denotes an unlabeled exit
that is consumed by any enclosing labeled block.
`some L` denotes a labeled exit
that is consumed only by an enclosing block whose label equals `L`.

### 2.3 Well-formedness (`exitsCoveredByBlocks`)

A statement is well-formed with respect to exit
if every `exit` inside it
resolves to an enclosing labeled block.

Formally,
`Stmt.exitsCoveredByBlocks : List (Option String) → Stmt P CmdT → Prop`
(defined in `Stmt.lean`)
holds when:

- Every `exit (some L)` sub-statement satisfies `.some L ∈ labels`.
- Every `exit none` sub-statement has a non-empty `labels` list.
- Every `block L body` sub-statement
  has `body` well-formed under `L :: labels`
  (where `L : Option String`,
  since labels on blocks may be anonymous).

A program is well-formed
if its top-level statement is well-formed under the empty label list.

The predicate is lifted to configurations by
`Config.exitsCoveredByBlocks`
(in `StmtSemantics.lean`),
which extends well-formedness to the small-step configuration shapes.

## 3. Small-Step Transitions

The step rules that define the behavior of exit and labeled blocks
are given in `StmtSemantics.lean`
as constructors of the inductive relation `StepStmt`.
`StepStmtStar` is its reflexive-transitive closure.

See §4.1 for the transitions and their realizing constructors.

## 4. Correctness Properties

This section states the properties
that the small-step exit semantics satisfies.
Each property is given in English
followed by its formal statement.
Each requirement cites the existing Lean construct that discharges it.

### 4.1 Per-transition behavior

The following transitions describe how exit and labeled-block
configurations evolve under a single step of `StepStmt`.
Each is realized directly by a constructor of the inductive relation
and does not require a separate theorem.
The named wrappers in `ExitProperties.lean`
give each transition a descriptive identifier for citation.

| Transition | Realized by | Named wrapper |
|---|---|---|
| `.stmt (.exit label md) ρ ⟶ .exiting label ρ` | `StepStmt.step_exit` | `exit_preserves_env` |
| `.seq (.exiting label ρ) ss ⟶ .exiting label ρ` | `StepStmt.step_seq_exit` | `exit_skips_remaining` |
| `.block (some L) (.exiting (some L) ρ) ⟶ .terminal ρ` | `StepStmt.step_block_exit_match` | `matching_block_consumes` |
| `bl ≠ some M → .block bl (.exiting (some M) ρ) ⟶ .exiting (some M) ρ` | `StepStmt.step_block_exit_mismatch` | `nonmatching_exit_propagates` |
| `.block label (.terminal ρ) ⟶ .terminal ρ` | `StepStmt.step_block_done` | `normal_block_completion` |
| `.block label (.exiting none ρ) ⟶ .terminal ρ` | `StepStmt.step_block_exit_none` | `unlabeled_exit_consumed` |
| `inner ⟶ inner' → .block label inner ⟶ .block label inner'` | `StepStmt.step_block_body` | `block_body_steps` |

Two observations follow from the shape of the relation
and require no separate proof:

- An `exit` statement leaves the environment unchanged
  (the result-side `ρ` of `step_exit` is syntactically identical to its input `ρ`).
  The store, evaluator, and cumulative failure flag are likewise unchanged.
- Exit propagation through `if` / `else` is not handled by a dedicated rule.
  The generic seq and block-context rules
  (`step_seq_exit`, `step_block_body`)
  carry inner-configuration exits outward,
  so no conditional-specific step rule is needed.

### 4.2 Structural property of well-formedness

Under well-formedness,
every `exit (some L)` sub-statement has its label
present in the enclosing label list:

```
Stmt.exitsCoveredByBlocks labels (.exit (some L) md)  →  .some L ∈ labels
```

This follows directly from the definition of
`Stmt.exitsCoveredByBlocks`
(the `.exit (some l) _` case reduces to `.some l ∈ labels`).
Named wrapper: `exit_target_in_labels` in `ExitWellFormedness.lean`.

### 4.3 Preservation of well-formedness

If a configuration is well-formed under some label context,
any single step MUST lead to a configuration
that is still well-formed under the same label context.

```
StepStmt EvalCmd extendEval c₁ c₂  →
Config.exitsCoveredByBlocks labels c₁  →
Config.exitsCoveredByBlocks labels c₂
```

Realized by `step_preserves_exitsCoveredByBlocks`
in `StmtSemantics.lean`.

### 4.4 No-escape (preservation)

Exit MUST NOT escape a well-formed procedure body.
For any reachable configuration
starting from the initial configuration of a well-formed procedure body,
the reachable configuration MUST NOT be `.exiting`.

```
Stmt.exitsCoveredByBlocks [] s  →
∀ ρ lbl ρ',
  ¬ StepStmtStar EvalCmd extendEval (.stmt s ρ) (.exiting lbl ρ')
```

Realized by `exitsCoveredByBlocks_noEscape`
in `StmtSemantics.lean`.
A companion theorem
`block_exitsCoveredByBlocks_noEscape`
states the same property
for an execution starting from `.stmts ss ρ`.

Liveness —
the claim that every `.exiting` eventually reaches a consuming block —
is deliberately out of scope.
See `decisions.md` Decision 6.

## 5. File Layout

The underlying definitions and theorems exist in upstream main.
This contribution adds two thin files of named wrappers
plus one `private → public` promotion
so the spec's requirements cite descriptive, public symbols.

| File | Relevant contents |
|---|---|
| `Strata/DL/Imperative/Stmt.lean` | `Stmt.exitsCoveredByBlocks`, `block_exitsCoveredByBlocks_append`, `exitsCoveredByBlocks_weaken` |
| `Strata/DL/Imperative/StmtSemantics.lean` | `Config`, `StepStmt`, `StepStmtStar`, `Config.exitsCoveredByBlocks`, `step_preserves_exitsCoveredByBlocks` (public), `exitsCoveredByBlocks_noEscape`, `block_exitsCoveredByBlocks_noEscape` |
| `Strata/DL/Imperative/ExitProperties.lean` | Seven per-transition named wrappers and two multi-step companions (§4.1) |
| `Strata/DL/Imperative/ExitWellFormedness.lean` | `exit_target_in_labels`, `exit_none_has_enclosing` (§4.2) |

## 6. Dependents

The following in-tree feature currently depends on exit semantics:

- **Python `return`, `break`, and `continue`**
  in `Strata/Languages/Python/PythonToCore.lean`.
  The translator emits `.exit (some jmp_target)` to desugar each of these
  control-flow constructs into labeled blocks plus exit.

- **Core concrete interpreter** (landed in #869).
  The interpreter handles exit state at the procedure boundary.
  `exitsCoveredByBlocks_noEscape`
  and the newly-public `step_preserves_exitsCoveredByBlocks`
  justify treating escaped exits as unreachable there.

Other dependents
(Laurel `throw` / `try` / `catch` / `finally`,
JVerify's Java→Laurel frontend,
downstream formal-verification projects)
live on forks not yet merged to upstream
and are out of scope for this document.

## 7. Future Work

These items are deliberately out of scope for this work.

- **Liveness** (§4.4).
  See Decision 6.
- **No-label-shadowing**.
  `exitsCoveredByBlocks` allows a block to re-use a label
  that is already in scope.
  A future `NoLabelShadowing` predicate could rule that out
  if a downstream consumer needs it.
- **`break` / `continue`** for loops.
  Once added at source level,
  they desugar to `exit` against an inserted labeled block.
  No new semantics are required.
- **Exit state on `Env`**.
  See Decision 1, option B.
  A larger refactor that would revisit every step rule
  and every existing proof in the files listed in §5.
