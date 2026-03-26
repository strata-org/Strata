# Design: Upgraded Assert Outcomes via Two-Sided SMT Checks

## 1. Motivation

### 1.1 The Problem with Pass/Fail/Unknown

Strata currently reports three outcomes for verification conditions: pass, fail, and unknown. For an `assert P` under path condition `Φ`, the verifier checks whether `Φ ∧ ¬P` is satisfiable (a single `check-sat`). If unsat, the assertion passes; if sat, it fails. This conflates several distinct situations:

- A "pass" could mean `P` is always true when reached, or that the path condition `Φ` is itself contradictory (the assertion is unreachable, making it vacuously true).
- A "fail" could mean `P` is always false when reached, or that `P` is sometimes true and sometimes false depending on inputs.

Consider the following procedure with four assertions:

```
procedure example(x: int, y: int)
  requires y > 0
{
  if x > 0 {
    assert x + y > 0;    // A1: always true when reached (x > 0 and y > 0)
    assert x > y;         // A2: depends on inputs (x=1,y=2 → false; x=3,y=1 → true)
    assert x < 0;         // A3: always false when reached (x > 0 contradicts x < 0)
  }
  if x > 0 && x < 0 {
    assert false;         // A4: unreachable (contradictory path condition)
  }
}
```

Today (with PR #466's reachability check), Strata reports: A1 = pass (reachable), A2 = fail (reachable), A3 = fail (reachable), A4 = pass (unreachable). This distinguishes A1 from A4, but A2 and A3 both show as "fail (reachable)" even though they are fundamentally different: A3 is *always* false (a definitive bug), while A2 is *sometimes* true and *sometimes* false (depends on inputs, not necessarily a bug).

For Ergo, this distinction is critical: A3 is a surely incorrect program that should be rejected, while A2 might be correct for the intended inputs.

### 1.2 Cover Semantics and Its Limitations for Intraprocedural Analysis

The `cover` construct in Strata Core checks whether `Φ ∧ Q` is satisfiable — an existential check. Cover is useful for its intended purpose (checking that a condition *can* be reached and satisfied), but its existential semantics means it aggregates across paths: if *any* path from the start of a procedure satisfies the cover, it passes globally.

A single cover statement generates multiple proof obligations (one per path through the procedure). The global cover result is the disjunction of per-path results. Consider:

```
val x: int
if x > 0 { x := 1 } else { x := 0 }
cover x > 0
```

Path 1 (`x > 0`): `(x > 0) ∧ (1 > 0)` = sat → covered on this path.
Path 2 (`x ≤ 0`): `(x ≤ 0) ∧ (0 > 0)` = unsat → not covered on this path.

The cover passes globally because path 1 satisfies it, even though path 2 can never satisfy it. For Ergo, the question is different: "on *every* reachable path to this API call, is the specification violated?" That requires per-path information about both satisfiability and refutability — which is what the two-sided assert check provides.

### 1.3 Relationship to PR #466

PR #466 added a reachability check by emitting an extra `check-sat` for the path condition `Φ` alone before the obligation check:

```
check-sat(Φ)          -- reachability
check-sat(Φ ∧ ¬P)     -- obligation
```

This design proposes instead:

```
check-sat-assuming(Φ ∧ P)     -- can the assertion be true?
check-sat-assuming(Φ ∧ ¬P)    -- can the assertion be false?
```

The second formulation subsumes the first: if both `Φ ∧ P` and `Φ ∧ ¬P` are unsat, then `Φ` itself is unsatisfiable (unreachable). But it also distinguishes "always true" from "sometimes true, sometimes false" — information that PR #466's approach cannot provide.

## 2. Design

### 2.1 Two-Sided Check

For an `assert P` under path condition `Φ`, the verifier asks two questions:

1. **Can `P` be true?** — Is `Φ ∧ P` satisfiable?
2. **Can `P` be false?** — Is `Φ ∧ ¬P` satisfiable?

Each question yields an SMT decision (sat, unsat, or unknown). The pair of decisions determines the outcome. This subsumes the current single-query approach (which only asks question 2) and the reachability check from PR #466 (reachability falls out: if both are unsat, `Φ` is contradictory).

### 2.2 Outcome Representation

Each verification condition produces two SMT results: one for `Φ ∧ P` (`forProperty`) and one for `Φ ∧ ¬P` (`againstProperty`). The outcome stores these two raw results. Interpretation (the human-readable label) is derived from the pair, not stored separately.

Implementation errors (SMT encoding failures, solver crashes) are represented by wrapping the outcome in an exception rather than as a variant of the outcome itself. This keeps the outcome type focused on SMT semantics.

### 2.3 Per-Path Interpretation

The two SMT decisions form a pair (for, against) interpreted identically regardless of whether the statement is `assert` or `cover`:

- sat, unsat → **pass** — always true and reachable
- unsat, sat → **refuted** — always false and reachable
- sat, sat → **indecisive** — true or false, but reachable
- unsat, unsat → **unreachable** — path condition is contradictory
- sat, unknown → **reachable satisfiable** — reachable and can be true, unknown if always true
- unsat, unknown → **refuted if reachable** — always false if reached, reachability unknown
- unknown, sat → **reachable violable** — reachable and can be false, unknown if always false
- unknown, unsat → **unviolable if reachable** — always true if reached, reachability unknown
- unknown, unknown → **unknown**

For `assert`, each per-path outcome is reported individually.

Returning to the running example from section 1.1, the two-sided check produces:

- **A1** (`assert x + y > 0` under `Φ = x > 0 ∧ y > 0`): for=sat (e.g. x=1,y=1), against=unsat → **pass** — always true and reachable
- **A2** (`assert x > y` under `Φ = x > 0 ∧ y > 0`): for=sat (e.g. x=3,y=1), against=sat (e.g. x=1,y=2) → **indecisive** — true or false, but reachable
- **A3** (`assert x < 0` under `Φ = x > 0 ∧ y > 0`): for=unsat, against=sat (e.g. x=1,y=1) → **refuted** — always false and reachable
- **A4** (`assert false` under `Φ = x > 0 ∧ x < 0`): for=unsat, against=unsat → **unreachable** — path condition is contradictory

Compare with today's output (A1=pass reachable, A2=fail reachable, A3=fail reachable, A4=pass unreachable): the two-sided check distinguishes A2 (indecisive) from A3 (refuted) — the key distinction that the current verifier cannot make.

The models from both queries are available for reporting. In the "indecisive" case, the `forProperty` model witnesses a state where `Q` holds, and the `againstProperty` model witnesses a state where `Q` is violated — both from the start of the procedure.

### 2.4 Cover Aggregation

A cover statement with proposition `Q` and paths `Φ₁, ..., Φₙ` checks the existential question: is there some path on which `Q` can be true? Each path yields its own (for, against) pair. These are aggregated into a single outcome using disjunction:

- **for**: `∃ i. (Φᵢ ∧ Q) is sat` — sat if any path has for=sat; unsat if all paths have for=unsat; unknown otherwise.
- **against**: `∃ i. (Φᵢ ∧ ¬Q) is sat` — sat if any path has against=sat; unsat if all paths have against=unsat; unknown otherwise.

The aggregated pair is then interpreted using the same nine-way table. The cover is always reported as a single outcome.

This aggregation is lossy: for example, (sat, sat) does not distinguish whether `Q` is true and false on the *same* path or on *different* paths. This is acceptable — it matches the existential nature of cover semantics.

Additionally, cover can be interprocedural: different paths may originate from different call sites, not just different branches within a single procedure. The aggregation applies uniformly regardless of whether paths come from intraprocedural branching or interprocedural entry points.

### 2.5 Soundness Statement

The soundness of the upgraded assert outcomes can be stated as follows:

- **pass**: It is guaranteed that `P` is reachable from the beginning of the procedure, and that `P` is true whenever it is reached from any valid entry point.
- **refuted**: It is guaranteed that `P` is reachable from the beginning of the procedure, and that `P` is false whenever it is reached from any valid entry point.
- **indecisive**: It is guaranteed that `P` is reachable from the beginning of the procedure, and can be either true or false depending on the values of the parameters of the procedure in which it is declared.
- **unreachable**: It is guaranteed that the assert itself is unreachable from the beginning of the procedure (the path condition is contradictory).

The five "unknown" variants provide partial information when the solver cannot decide one of the two queries, with precise wording that avoids overclaiming.

### 2.6 CLI Flags and Options

The two-sided check involves two SMT queries per obligation instead of one. Not all use cases require both. The design principle is: **both checks are enabled by default** (the most informative mode), and users can **disable** individual checks when performance matters. When a check is disabled, its result is conservatively interpreted as `unknown`.

I prefer "enable by default, disable if needed" over the alternative ("disable by default, enable if needed") because:
- Strata must always perform at least one check — so the baseline is not zero queries.
- Defaulting to full information avoids silent loss of precision.
- Disabling is an explicit performance trade-off the user opts into.

The two checks are:
- **forProperty** (`Φ ∧ Q`): can the property be true?
- **againstProperty** (`Φ ∧ ¬Q`): can the property be false?

The current single-check behavior corresponds to having only `againstProperty` enabled for assert (and only `forProperty` for cover).

**Global option**: `--check-mode=full|deductive|satisfiability` (default: `full`)
- `full`: Both checks enabled. Reports all nine outcomes.
- `deductive`: Only `againstProperty` enabled for assert. This is the traditional verification mode: prove the assertion is always true. The skipped query is reported as `unknown`.
- `satisfiability`: Only `forProperty` enabled for assert. Checks whether the property can be satisfied. Useful for Ergo: if `forProperty=unsat`, the outcome is "refuted if reachable" — a strong signal of a bug without the cost of the second query.

For cover statements, the interpretation of these modes requires separate consideration. Cover's existential semantics and cross-path aggregation mean the "for" and "against" queries play different roles than for assert. The exact mapping of `deductive` and `satisfiability` modes to cover queries is left as a design decision to be resolved during implementation. In `full` mode, both queries are always performed for cover as well.

**Per-statement override**: A per-statement annotation can override the global mode. For example, `@[deductiveCheck]` on a specific assert would disable the `forProperty` query for that obligation only, even when the global mode is `full`. Conversely, `@[fullCheck]` would enable both queries even when the global mode is `deductive`.

When a check is skipped, the outcome degrades gracefully. For example, in `deductive` mode for an assert (only `againstProperty` enabled):
- againstProperty=unsat → **unviolable if reachable** (was "pass" with both checks, now we don't know if it's reachable or unreachable)
- againstProperty=sat → **reachable violable** (was "refuted" or "indecisive", now we don't know which)

This is conservative: no false positives or false negatives are introduced, only loss of precision.

PR #466's `--reach-check` flag and `@[reachCheck]` per-statement annotation are subsumed by this design. The `@[reachCheck]` annotation is reinterpreted as `@[fullCheck]` — it was requesting additional reachability information, which the full two-sided check provides.

The `--incremental` flag is automatically added to cvc5 when both checks are enabled. For z3, incremental mode is the default.

The `PropertyType` enum (`.assert | .cover`) remains unchanged. The two-sided check applies to both property types; the interpretation differs as described in sections 2.3 and 2.4.

## 3. Implementation Plan

### 3.1 SMT Layer Changes

**`Strata/DL/SMT/Solver.lean`**: Add a `checkSatAssuming` method to `Solver` that emits `(check-sat-assuming (lit₁ lit₂ ...))`. The existing `checkSat` method remains for backward compatibility.

**`Strata/DL/Imperative/SMTUtils.lean`**:
- `solverResult` must parse two verdict lines from stdout (one per `check-sat-assuming`), each potentially followed by a model. Returns a pair of `SMT.Result` values.
- `dischargeObligation` is updated to accept assumptions and obligation separately (rather than a flat list of terms), emit two `check-sat-assuming` calls, and return both results.

### 3.2 Core Encoding Changes

**`Strata/Languages/Core/Verifier.lean`** — New types replacing the old `Outcome` inductive:

```lean
structure VCOutcome where
  forProperty : SMT.Result
  againstProperty : SMT.Result

structure VCResult where
  obligation : Imperative.ProofObligation Expression
  outcome : Except String VCOutcome := .error "not yet computed"
  estate : EncoderState := EncoderState.init
  verbose : VerboseMode := .normal
```

**`Strata/Languages/Core/SMTEncoder.lean`**: `ProofObligation.toSMTTerms` already separates assumptions from the obligation term (as modified in PR #466). The key change: the obligation term is no longer appended to the assertion list. Instead, it is returned separately so the encoder can pass it to `check-sat-assuming`.

**`Strata/Languages/Core/Verifier.lean`**:
- `encodeCore` emits path condition assertions, then two `check-sat-assuming` calls (one with the obligation, one with its negation).
- The `Outcome` inductive is replaced by `VCOutcome`.
- `VCResult` stores `Except String VCOutcome` instead of separate `Outcome` and `SMT.Result` fields.
- `smtResultToOutcome` is removed. The interpretation logic moves to `VCOutcome.toFormat` and helper methods.
- `preprocessObligation` short-circuits are updated: when PE reduces the obligation to `true`, we can immediately return `VCOutcome` with `forProperty = .sat []` and `againstProperty = .unsat` (pass). Similar for `false`.
- `getObligationResult` invokes the two-query discharge and constructs a `VCOutcome`.
- Helper predicates (`isSuccess`, `isFailure`, etc.) are updated to work with `VCOutcome`.

### 3.3 Output and Reporting

**`Strata/Languages/Core/Verifier.lean`**: `ToFormat VCOutcome` renders the label and emoji based on the two decisions. `ToFormat VCResult` renders the obligation info, the outcome label, and models (when verbose).

**`Strata/Languages/Core/SarifOutput.lean`**: Currently, `outcomeToLevel` maps each `Outcome` to a SARIF level (`none`, `error`, `warning`), and `outcomeToMessage` produces a human-readable string. With the new `VCOutcome`, these functions are replaced by a mapping from the nine outcome combinations to SARIF fields:

- **pass** → level `none`, message "Verification succeeded: always true and reachable"
- **refuted** → level `error`, message "Verification failed: always false and reachable" + counterexample model from `againstProperty`
- **indecisive** → level `warning`, message "Verification inconclusive: true or false depending on inputs" + both models
- **unreachable** → level `note`, message "Path unreachable: path condition is contradictory"
- **reachable satisfiable** → level `note`, message "Reachable and can be true, unknown if always true"
- **refuted if reachable** → level `warning`, message "Always false if reached, reachability unknown"
- **reachable violable** → level `warning`, message "Reachable and can be false, unknown if always false" + counterexample model from `againstProperty`
- **unviolable if reachable** → level `note`, message "Always true if reached, reachability unknown"
- **unknown** → level `warning`, message "Verification result unknown (solver timeout or incomplete)"

Implementation errors (the `Except` wrapping `VCOutcome`) map to level `error` with the error message.

### 3.4 Downstream Consumers

**Ergo**: The Ergo project provides sound feedback to LLMs generating code with AWS APIs — ruling out surely incorrect programs without ruling out correct ones. Ergo cares about three outcomes:
- **refuted** — the API specification is provably violated and reachable. The generated code is surely wrong. Sound to reject.
- **unreachable** — the API call path is infeasible. Indicates dead code.
- **refuted if reachable** — the specification is always violated if the path is reached, but reachability is unknown. Still useful as a strong signal of a likely bug.

All other outcomes (pass, indecisive, unknown variants) are not grounds for rejection, consistent with the soundness goal of not ruling out correct programs.

### 3.5 Migration Path

The change is not backward-compatible at the API level: `Outcome` is removed, `VCResult` fields change. All consumers of `VCResult` must be updated. The main consumers are:

- `verifySingleEnv` in `Verifier.lean` (constructs and inspects `VCResult`)
- `SarifOutput.lean` (formats results)
- `Laurel/LaurelToCoreTranslator.lean` (calls `verify`, consumes `VCResults`)
- `C_Simp/Verify.lean` (calls `verify`, consumes `VCResults`)
- `SimpleAPI.lean` (exposes `Core.verify`)
- Test files in `StrataTest/`

Since the two-sided check is strictly more informative than the current single check, no information is lost. The `--check-mode=deductive` option preserves existing behavior for users who need it. The old "pass" maps to either "pass" or "unreachable"; the old "fail" maps to either "refuted" or "indecisive". Consumers that only care about pass/fail can check `VCOutcome.isSuccess` / `VCOutcome.isFailure` which preserve the old semantics (pass = success, everything else = not success).

## 4. Alternatives and State of the Art

### 4.1 Existing Approaches

Most verification tools recognize the vacuity problem — an assertion that passes only because its path condition is unsatisfiable — but address it as a separate, optional analysis layered on top of the standard pass/fail result:

**No vacuity detection** (Boogie, Dafny, CBMC): These tools generate a single verification condition per assertion and report pass or fail. Unreachable assertions silently pass. Users must manually add `assert false` or cover checks to detect vacuity. This is the most common approach in deductive verifiers and bounded model checkers.

**Separate reachability analysis** (Kani, Certora, ESC/Java2): These tools add an independent reachability check. Kani reports four outcomes (SUCCESS, FAILURE, UNREACHABLE, UNDETERMINED) by performing a separate reachability analysis per assertion. Certora appends `assert false` to each rule as a "sanity check." ESC/Java2 implemented reachability as a separate enhancement. In all cases, reachability is a bolt-on analysis with its own solver invocation, not part of the assertion outcome.

**Witness covers** (JasperGold): The closest analog to the two-sided check. JasperGold generates a cover property for each assertion, checking that the assertion's antecedent can be triggered. The assertion check proves the property holds; the witness cover proves it can be reached. However, these remain separate analyses with separate results, not a unified outcome.

None of these tools distinguish "always false" (refuted) from "sometimes true, sometimes false" (indecisive). A failure means the property can be violated, without indicating whether it can also hold.

### 4.2 Related Work on Proving Bug Existence

The idea of proving that a bug *definitely* exists (not just that it *might* exist) has been explored in several lines of work:

**"It's Doomed; We Can Prove It"** (Leino, Rümmer, Schaef, 2009): Defines a program fragment as "doomed" if its execution will inevitably fail regardless of starting state. This is precisely the "refuted" outcome in our design. The paper uses Boogie's verification infrastructure to detect doomed code by checking infeasibility of the negated error condition. However, the doomed analysis is a separate pass, not integrated into the standard assertion outcome.

**Corral** (Lal, Qadeer, Lahiri, 2012): A whole-program analysis tool for Boogie that solves the "reachability modulo theories" problem — determining whether a program can reach a particular control location. Corral finds concrete assertion violations (true bugs), but does not classify assertions into the full spectrum of outcomes.

**Incorrectness Logic** (O'Hearn, 2019): A theoretical framework that inverts Hoare logic to prove the *presence* of bugs via under-approximate reasoning. Where Hoare logic proves "no execution violates the property" (over-approximation), incorrectness logic proves "there exists an execution that violates the property" (under-approximation). This is the theoretical foundation for proving true bugs, and tools like Facebook Infer's Pulse use it in practice.

Our two-sided check combines both directions in a single analysis: the `againstProperty` query is the Hoare-style over-approximate check (can the property be violated?), and the `forProperty` query is the incorrectness-style under-approximate check (can the property be satisfied?). The combination yields the full spectrum of outcomes.

### 4.3 How This Design Differs

- **Unified outcome**: The outcome is a pair of SMT decisions that naturally encodes all four definitive cases (pass, refuted, indecisive, unreachable) and five partial cases, rather than a pass/fail result plus a separate reachability flag or a separate doomed analysis.
- **Indecisive as a first-class result**: While prior work has identified "doomed" (always fails) as a distinct category, the indecisive case (sometimes true, sometimes false) has not been surfaced as a named outcome. This distinction matters: refuted is a definitive bug, while indecisive means the property depends on inputs.
- **Single SMT session**: Both queries share learned clauses in one incremental solver session via `check-sat-assuming`, rather than paying the cost of independent solver invocations or separate analysis passes.
- **Configurable precision**: The `--check-mode` flag allows trading precision for performance, degrading gracefully to the traditional single-query approach.

### 4.4 Limitations

- **Counterexample soundness**: The models returned by the SMT solver (used for reporting in the indecisive, refuted, and reachable cases) are not guaranteed to correspond to concrete program executions. SMT solvers operate on an abstraction of the program, and the models may not be realizable. Only bounded model checkers (like CBMC or Kani) provide counterexamples that correspond to actual execution traces. The models in Strata should be understood as diagnostic aids, not as proofs of concrete reachability.
- **Solver incompleteness**: The "unknown" results reflect solver limitations (timeouts, incomplete theories). The two-sided check does not improve the solver's ability to decide queries — it only provides more information when the solver can decide them.
- **Performance**: The two-sided check doubles the number of solver queries in the worst case. The `--check-mode` flag mitigates this for users who do not need full information.
