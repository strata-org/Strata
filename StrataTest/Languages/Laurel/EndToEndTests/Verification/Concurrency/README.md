# Concurrency — coroutines and rely/guarantee

Verification tests for Laurel's `coroutine` feature: `yield`, the
`yields`/`resumes` value channels, per-yield `relies`/`guarantees`,
`oldGuarantee`/`oldRelies`, and the caller-side view of `resume`. Every test here
goes through `CoroutineTest.lean`'s `testCoroutine` helper (`testLaurelExecution {}` plus
`verifyCoroutine := true`), i.e. the YieldElim verification path.

Coverage of the same feature outside verification:

- **Execution** — deferred: coroutines cannot yet run in the concrete
  interpreter (it does not support `$heap` references), so there are no
  execution tests. The verifier cannot substitute: SMT will not unroll the
  generated `while (true)` dispatch loop, so concrete yielded values are only
  reachable once execution is supported.
- **Resolution** — `../../Resolution/Coroutines.lean`.

## Feature tests

One construct or rule per file. These are what should tell you *which part* of
the feature regressed.

| File | What it pins |
| --- | --- |
| `ValueChannels.lean` | `yields` / `resumes` bindings: the yielded value is checked at every yield and at the exit tail; the resumed value is fresh and arbitrary at every step |
| `ExitGuarantee.lean` | The guarantee is checked on the final `resume → halt` segment too, not only at yields |
| `LoopYieldStep.lean` | The per-yield guarantee assert is meaningful — not vacuous — when the loop body has code between yields |
| `LoopUserInvariants.lean` | Per-yield guarantees are deliberately *not* auto-injected at loop heads; the user writes them with `oldGuarantee(...)` |
| `OldSemantics.lean` | Which heap `old(...)` binds to in a guarantee versus in a rely, across multiple yields |
| `AllocAcrossYield.lean` | Allocation against the per-yield environment havoc (the monotone allocation counter) |
| `CallerPath.lean` | Caller-side reasoning: `relies` → `requires` and `guarantees` → two-state `ensures` on the generated opaque `resume` |
| `GlobalInContract.lean` | Regression: a rely/guarantee that references a file-scope global still verifies after `GlobalParameterization` |

`CoroutineTest.lean` is the shared helper, not a test.

## `Examples/` — algorithm case studies

`Examples/` holds published concurrent algorithms modeled as coroutines. They
demonstrate that the construct is expressive enough for real protocols; they are
**not** the tests for any individual part of the feature. When one fails, read it
as "this protocol no longer verifies" and use the feature tests above to find out
which part changed. Each model is paired with a `…Violations` file that mutates
it and pins the resulting diagnostics.

| File(s) | Algorithm |
| --- | --- |
| `Peterson.lean`, `PetersonMutex.lean`, `PetersonViolations.lean` | Peterson's mutual exclusion — two threads, interest flags plus a `turn` arbiter; `PetersonMutex` carries the mutex theorem as an inline assert |
| `Dekker.lean`, `DekkerViolations.lean` | Dekker's mutual exclusion (1965) — same contract shape as Peterson, harder control flow (a flag drop/raise around a nested spin) |
| `TicketLock.lean`, `TicketLockViolations.lean` | Ticket lock, single client, framed after fetch and with release |
| `MonotonicCounter.lean` | The textbook rely/guarantee example (`relies old(x) <= x`, `guarantees old(x) < x`), plus a study of two coroutines whose contracts are mutually incompatible |
