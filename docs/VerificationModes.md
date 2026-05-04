> **Note:** The canonical reference for verification modes is now
> [Transforms and Analysis](verso/TransformsDoc.lean).
> This file is retained for the detailed error classification table not yet migrated.
> It may be removed in the future.

# Verification Modes

Strata supports three verification modes, selected via `--check-mode`:

- **`deductive`** (default) — Prove correctness: every assertion must hold on all inputs.
- **`bugFinding`** — Find bugs assuming incomplete preconditions: only definite bugs are errors.
- **`bugFindingAssumingCompleteSpec`** — Find bugs assuming complete preconditions: any counterexample is an error.

## Error Classification by Mode

Each verification condition produces two SMT queries:
- **P ∧ Q** (satisfiability): Can the property be true given the path condition?
- **P ∧ ¬Q** (validity): Can the property be false given the path condition?

The combination determines the outcome and its severity in each mode:

| Outcome                        | P ∧ Q   | P ∧ ¬Q  | Deductive | BugFinding | BugFinding+CompleteSpec |
|--------------------------------|---------|---------|-----------|------------|-------------------------|
| Always true and reachable      | sat     | unsat   | pass      | pass       | pass                    |
| Always false and reachable     | unsat   | sat     | error     | error      | error                   |
| Can be true or false           | sat     | sat     | error     | note       | error                   |
| Unreachable (dead code)        | unsat   | unsat   | warning   | error      | error                   |
| Can be true, validity unknown  | sat     | unknown | error     | note       | note                    |
| Always false if reached        | unsat   | unknown | error     | error      | error                   |
| Can be false, sat unknown      | unknown | sat     | error     | note       | error                   |
| Always true if reached         | unknown | unsat   | pass      | pass       | pass                    |
| Unknown                        | unknown | unknown | error     | note       | note                    |

## What Counts as an Error in Bug-Finding Modes

In `bugFinding` and `bugFindingAssumingCompleteSpec`, an assertion is an error when:

1. **Always false and reachable** (unsat, sat) — The assertion is provably false on every reachable path.
2. **Always false if reached** (unsat, unknown) — The assertion is provably false whenever the path is taken, even if reachability is unknown.
3. **Unreachable** (unsat, unsat) — The path condition is contradictory, indicating dead code. This is flagged as an error because unreachable code often signals a specification or implementation problem that should be investigated.

This differs from deductive mode, where unreachable assertions are only a warning (the assertion holds vacuously).

Additionally, in `bugFindingAssumingCompleteSpec`, any counterexample (sat on P ∧ ¬Q) is also an error, since the specification is assumed complete.
