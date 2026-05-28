# Multi-path command evaluation — design

> **Status:** spec for review (not committed). Follow-up to
> `docs/superpowers/specs/2026-05-26-body-eval-at-call-site-design.md`.

## Problem

Strata's evaluator is built around a **multi-path** discipline at the
statement level. When a symbolic `if` is encountered, both branches
fork into separate `EnvWithNext` records, each carrying its own path
conditions. The fork-and-continue pattern lets every assertion on a
forked path produce a deferred SMT obligation under that path's own
assumptions — without cross-contamination.

The infrastructure exists today: `Statement.eval`, `evalAux`,
`evalAuxGo`, `processIteBranches`, and `evalOneStmt` all return
`List EnvWithNext` (statement-level) or `List Env` (top-level).
`evalAuxGo` distributes the list through a `foldl` over `evalOneStmt`,
flattening fan-outs into a longer active-path list. Path explosion is
bounded by `--path-cap` plus `Env.merge` and `splitConds`-tagged
re-merging in `enforcePathCap`. This system is sound, well-trodden,
and handles arbitrary symbolic branching.

But the multi-path contract **stops at the command level**. Look at
the type boundary:

| Function | Return type | Multi-path? |
|---|---|---|
| `Statement.eval (ss : Statements) : ...` | `List Env × Statistics` | yes |
| `evalAuxGo` | `List EnvWithNext × Statistics × Nat` | yes |
| `processIteBranches` | `List EnvWithNext × Statistics × Nat` | yes |
| `evalOneStmt` | `List EnvWithNext × Statistics × Nat` | yes |
| **`Command.eval (c : Command) : ...`** | **`Command × Env`** | **no** |
| **`Command.handleCall : ...`** | **`Command × Env`** | **no** |
| **`Command.inlineCallContract : ...`** | **`Command × Env`** | **no** |
| **`Command.inlineCallBody : ...`** | **`Command × Env`** | **no** |
| `Imperative.Cmd.eval` | `Cmd × State` | no |

The boundary is `evalOneStmt`'s `.cmd c` arm:

```lean
| .cmd c =>
  let (_, E) := Command.eval Ewn.env old_var_subst c
  ([{ Ewn with env := E, exitLabel := .none }], noStats, nextSplitId)
```

A statement that *is* a command is evaluated to **one** env via
`Command.eval`, then re-wrapped into a single-element list to satisfy
the surrounding multi-path contract. **A `.cmd` statement can never
fork in today's code.**

This was historically correct: `Imperative.Cmd` operations
(assignment, assert, assume, havoc) are deterministic. Even
`Command.inlineCallContract` is single-path (havoc the lhs, assume the
contract — one env out). Calls used to never fork either.

`Command.inlineCallBody` (the body-eval call handler) is the
**first command-level operation that can legitimately produce
multiple post-states.** A callee body with a symbolic branch produces
two result envs; an unmerged CFG diamond produces two finished envs;
etc. The `Command × Env` contract forces these to collapse into one
before returning.

There is no sound way to perform that collapse from inside
`Command.inlineCallBody` alone. Each result env carries its own
`pathConditions` — branch assumptions accumulated as the body
evaluated symbolic conditionals — and its own `exprEnv.state` with
possibly divergent variable bindings. Combining them into a single
env requires either path-conditional merging (which needs splitting
conditions that aren't available at this level — the body may have
multiple internal branches whose conditions accumulate as
`pathConditions` entries, not as a single guard) or surfacing the
list to the caller (which the return type forbids).

The current behaviour is to refuse: `inlineCallBody` produces an
explicit error when its body eval yields multiple result envs.
Under `--call-policy bodyOrContract` the error triggers contract
fallback; under `--call-policy body` it surfaces as a verifier error.
Either way, body-eval's reach on SMACK-style programs (where
symbolic CFG branches are pervasive) is sharply limited.

## Goal

Extend the multi-path contract one layer down: `Command.eval` and its
dependents (`handleCall`, `inlineCallContract`, `inlineCallBody`) gain
a `List Env` return type. After the change, body-eval calls fork like
`.ite` statements: the resulting list of paths flows naturally into
`evalAuxGo`'s active-path list, where each path is evaluated
independently against subsequent statements.

The fix is a mechanical return-type change. **No new merge machinery,
no new soundness argument**: the multi-path discipline that already
works for `.ite` simply extends to `.call`.

## Non-goals

- Redesigning `evalAuxGo`, `processIteBranches`, or
  `enforcePathCap`. They already speak the wider type and need no
  changes.
- Changing `Imperative.Cmd.eval`'s single-path semantics. Every
  `Imperative.Cmd` operation is genuinely deterministic and should
  stay so. The new `List Env` return type only affects `Core.Command`
  — the type that carries the new `.call` constructor.
- Introducing new merge semantics. `Env.merge` already exists and is
  used by `processIteBranches` and `enforcePathCap`. We don't add
  call-site-specific merging; we let the existing merge points handle
  multi-path commands transparently.
- Soundness improvements beyond what fork-and-continue already
  provides. Each path's deferred obligations carry that path's own
  `pathConditions`; the SMT solver checks each obligation under the
  right assumptions; we inherit `processIteBranches`'s soundness
  argument unchanged.
- Removing `--call-policy bodyOrContract`'s contract fallback. The
  fallback remains useful for `OutOfFuel` and other genuine
  body-eval failures.

## Architecture

### Return `List Env` instead of `Env` from the command-evaluation functions

Four functions change their return type from `Command × Env` to
`Command × List Env`:

```lean
def Command.inlineCallContract (E : Env) ... : Command × List Env
def Command.inlineCallBody     (E : Env) ... : Command × List Env
def Command.handleCall         (...) : Command × List Env
def Command.eval               (...) : Command × List Env
```

The list represents zero, one, or many post-call paths. Single-path
commands (every `Imperative.Cmd` operation, plus `inlineCallContract`)
return a one-element list; multi-path commands (`inlineCallBody` on
a callee whose body branches symbolically) return a list with each
path's distinct env.

Most existing callers and bodies require only mechanical updates:

- `Command.inlineCallContract` already produces one env. Wrap it:
  `(c, E)` → `(c, [E])`.
- `Command.inlineCallBody` already builds a `processedEnvs : List Env`
  internally; it currently squeezes that list down to one env. Drop
  the squeeze. Return `(retCmd, processedEnvs)`. The single-element
  case (`[e]`) returns `[e]`; the multi-element case returns the full
  list.
- `Command.handleCall` simply forwards whichever list its dispatched
  handler produces. The `.BodyOrContract` fall-back logic stays the
  same: on `OutOfFuel`, discard the list and call `inlineCallContract`
  on the original `E`, returning that singleton.
- `Command.eval`'s `.cmd c` (Imperative.Cmd) arm wraps as before:
  `(.cmd c, [E])`. The `.call` arm now naturally returns whatever
  list `handleCall` produces.

The boundary is `evalOneStmt`'s `.cmd c` arm. Today:

```lean
| .cmd c =>
  let (_, E) := Command.eval Ewn.env old_var_subst c
  ([{ Ewn with env := E, exitLabel := .none }], noStats, nextSplitId)
```

After the change:

```lean
| .cmd c =>
  let (_, envs) := Command.eval Ewn.env old_var_subst c
  (envs.map (fun E => { Ewn with env := E, exitLabel := .none }),
   noStats, nextSplitId)
```

The outer `evalAuxGo` already accumulates `List EnvWithNext`'s via
`foldl`; the wider input flows through unchanged.

### What this enables

After the change:

1. A symbolic CFG branch in a callee body produces two finished envs
   from `evalCalleeCFG`. `inlineCallBody` returns them as a list.
   `Command.eval` returns the list. `evalOneStmt` wraps each into an
   `EnvWithNext`. `evalAuxGo` adds them to the active-path list. The
   *next* statement after the call is evaluated for each path
   independently. Each path's assertions emit deferred obligations
   under that path's own `pathConditions`. The SMT solver checks
   each obligation under the right assumptions. **Sound.**

2. A symbolic structured-body `.ite` that doesn't converge in
   `processIteBranches` produces multiple `EnvWithNext`s. The
   internal `eval` call from `inlineCallBody` returns multiple result
   envs. `inlineCallBody` returns them as a list. Same downstream
   handling as case 1. **Sound.**

3. `--path-cap N` already merges paths back down via `Env.merge` and
   `splitConds` tags when the active list exceeds N. Body-eval forks
   participate in this merging without any additional code: they're
   just `EnvWithNext`s in the active list. **Sound.**

### Soundness argument

Returning `List Env` instead of `Env` preserves every existing
invariant. The argument has three parts:

**Part 1: Per-path obligation accounting.** Each forked path's
`pathConditions` reflects exactly the assumptions that path took
(branch conditions, assumed preconditions, etc.). Deferred obligations
generated on a path use that path's `pathConditions` as their
assumption set. Forking creates two paths with two distinct
`pathConditions`; obligations generated on each path are checked under
the right assumptions. This is the same accounting that
`processIteBranches`'s diverged case already relies on.

**Part 2: No cross-path state contamination.** Each `EnvWithNext` is
independent — its `exprEnv.state`, `pathConditions`, `deferred`,
`fuel`, etc. are the path's own. `evalAuxGo`'s `foldl` processes paths
one at a time without sharing mutable state between them. Forking
emits two paths whose `exprEnv.state` may differ (different lhs
bindings); each path's subsequent evaluation uses its own state. No
cross-contamination is possible.

**Part 3: Path-condition consistency at obligation generation.**
When an assertion is evaluated on a forked path, the deferred
obligation captures the path's `pathConditions` as its assumption
set. The SMT query is "given these path conditions, prove this
obligation," not a global query. Two paths through a callee whose
conditions are mutually exclusive (`b` and `¬b`) produce two
obligations with mutually exclusive assumption sets. The solver
checks each independently. **Sound.**

The current single-env `Command.eval` violated none of these
invariants either — but its squeeze step, when applied to a
multi-result `inlineCallBody`, *did* violate Part 1 (path-2
obligations carried path-2's `pathConditions` in `deferred`, but were
later substituted against path-1's `exprEnv.state`, which doesn't
satisfy path-2's assumptions). Removing the squeeze restores Part 1
naturally.

## Components

| Component | Location | Change |
|---|---|---|
| `Command.eval` | `Strata/Languages/Core/StatementEval.lean` | return type `Command × List Env`; `.cmd c` wraps as `[E]` |
| `Command.handleCall` | same | return type `Command × List Env`; `.Contract` returns `[inlineCallContract result]`; `.BodyOrContract` falls back to `[contract]` on OutOfFuel |
| `Command.inlineCallContract` | same | return type `Command × List Env`; existing single-env body wrapped as `[E]` at the return point |
| `Command.inlineCallBody` | same | return type `Command × List Env`; drop the multi-result squeeze (commit `fa82fe42b`'s error); return `processedEnvs` directly |
| `evalOneStmt` (`.cmd c` arm) | same | `envs.map (fun E => { Ewn with env := E, ... })` instead of singleton wrap |
| `InlineCallBodyTests` (test file) | `StrataTest/Languages/Core/Tests/InlineCallBodyTests.lean` | add tests demonstrating multi-path body-eval verdicts |

No other callers of `Command.eval`, `Command.inlineCallContract`,
`Command.handleCall`, or `Command.inlineCallBody` exist outside
`evalOneStmt` (verified by grep at the time of writing). The
return-type change is **local** to the eval module.

## Data flow

```
Statement.eval (returns List Env)
   └─ evalAuxGo (List EnvWithNext input, List EnvWithNext output)
        └─ continuing.foldl (per-path)
             └─ evalOneStmt s ewn ... → List EnvWithNext
                  └─ .cmd c case:
                      let (_, envs) := Command.eval E sm c        -- NEW: List Env
                      envs.map (fun E => { Ewn with env := E })   -- NEW: per-env wrap
                      └─ Command.eval (.call ...) → List Env      -- NEW
                           └─ Command.handleCall E.callPolicy → List Env
                                ├─ .Contract → [inlineCallContract E]
                                ├─ .Body → inlineCallBody E (already a list)
                                └─ .BodyOrContract →
                                     case .OutOfFuel: [inlineCallContract E]
                                     case _: inlineCallBody result
```

Every layer downstream of the wider command-eval interface either
already handles a list (`evalAuxGo`, `evalOneStmt`) or trivially wraps
its existing single-env result (`inlineCallContract`, the `.cmd c`
arm).

## Error handling

- **`Env.error = some .OutOfFuel`** (any path): unchanged.
  `evalAuxGo`'s short-circuit (`if env.error.isSome then env`) at the
  per-path level handles error propagation; an erroring path simply
  doesn't progress while siblings continue.
- **`.BodyOrContract` fall-back**: same as today. On
  `OutOfFuel` from `inlineCallBody`, discard the (possibly
  multi-element) list and re-run `inlineCallContract` on the original
  `E`. Return `[contract result]`.
- **No more "multi-result not yet sound" error**: the explicit
  guard added in `fa82fe42b` is removed. Multi-result is now
  the expected case, not an error.

## Testing

### Existing test corpus

The 6 tests added by Tasks 7 and 8 all use single-path callees and
remain valid. Their `#guard_msgs` outputs should be unchanged after
the return-type change:

- Tests 1, 3 (Body, single-path structured / CFG body): single env
  result, identical to today.
- Tests 2, 4 (Contract): unaffected — `inlineCallContract` still
  produces one env, just wrapped in `[…]`.
- Tests 5, 6 (fuel exhaustion): `OutOfFuel` is per-env; the existing
  `BodyOrContract` fallback continues to fire.

### New tests demonstrating multi-path semantics

1. **Symbolic CFG branch passes**: A callee with `if (b) r := 1 else
   r := 2` (CFG body, symbolic `b`). Caller asserts `r > 0`. Under
   `--call-policy body`, both paths produce deferred obligations
   (`r > 0` under `b` simplifies to `1 > 0` = true; under `¬b`,
   `2 > 0` = true). Verdict: PASS.

2. **Symbolic CFG branch fails on one branch**: Same callee, but
   caller asserts `r == 1`. Under `body`, path 1 simplifies to true;
   path 2 produces a deferred obligation `2 == 1` under `¬b`. SMT
   solver rejects. Verdict: FAIL with counterexample.

3. **Path-cap merging**: Same scenario as test 1 but with
   `--path-cap 1`. After the call's fork, the cap forces a re-merge.
   The post-merge env's `r` binding is `ite(b, 1, 2)`. The assertion
   `r > 0` simplifies to `ite(b, 1, 2) > 0`, which the solver
   discharges. Verdict: PASS.

4. **Nested calls fork independently**: A caller invokes `f` (forks
   into 2 paths) and then `g` (forks each into 2 more), producing
   4 active paths through the caller. Each path's assertion is
   checked under its own combined `pathConditions`.

5. **Recursion termination**: A directly-recursive callee with
   `--inline-fuel 5`. `OutOfFuel` is reached on the deepest call
   (one path); siblings without recursion continue normally.

### Regression coverage

The default-path behaviour (`--call-policy contract`) must produce
**byte-for-byte identical** output to today. This is the
non-negotiable regression gate — verified by running the full
existing test suite and the existing portfolio under default
`callPolicy = .Contract`.

## Alternatives considered

### Alternative — Build path-conditional merge in `inlineCallBody`

Instead of returning a list, keep `Command.eval`'s `Command × Env`
signature and implement `Env.merge`-equivalent combining inside
`inlineCallBody`: when multiple result envs are produced, find the
splitting condition and combine them into a single env using `ite`
expressions for divergent values.

- **Why rejected:** `inlineCallBody` doesn't have a single splitting
  condition. The callee body may contain *multiple* internal `.ite`s
  or CFG branches; the path conditions accumulate as assumption
  entries in `env.pathConditions`, not as one boolean cond.
  Reconstructing a single split-cond would require walking
  `pathConditions` and synthesizing an `ite` for each variable
  binding — which is essentially reimplementing
  `processIteBranches`'s converged-merge case but with multiple
  splitting conditions, a strictly harder problem.

  The fork-and-continue alternative bypasses this entirely: paths
  flow upward, each carrying its own assumption set, and `Env.merge`
  is invoked only by `enforcePathCap` *outside* the callee, where
  `splitConds` tags identify the splitting conditions for it.

### Alternative — Limit body-eval to procedures with no symbolic branching

Add a static check: refuse `body` policy on callees whose bodies
contain any potentially-symbolic branch.

- **Why rejected:** prohibitively conservative. Most realistic
  callees (parsers, validators, anything with input-dependent
  control flow) would be excluded. The feature loses most of its
  value on the SMACK matrix that motivated it.

### Alternative — Extend the `.BodyOrContract` fall-back to all multi-result cases

Treat any multi-result body as if it were `OutOfFuel` and always fall
back to contract under `BodyOrContract`. (This is closest to today's
behaviour after commit `fa82fe42b`.)

- **Why rejected:** functionally correct but defeats the feature on
  most realistic programs. `BodyOrContract` becomes equivalent to
  `Contract` whenever the callee branches symbolically. Body-eval's
  reach is limited to bodies whose every branch resolves to a
  concrete value at the call site — a narrow slice in practice.

### Alternative — Implement `Env.merge` based on accumulated path conditions

When `inlineCallBody` produces N result envs, walk through pairs of
envs and merge them via `Env.merge` using their accumulated
`pathConditions` as splitting conditions.

- **Why rejected:** `Env.merge` is built for two-way splits with a
  single boolean condition. Generalising to N-way merges with
  multiple conditions reduces to either repeated pairwise merges
  (which loses precision) or a one-shot N-way merge (which would be
  a new, complex operation). Either is harder than the proposed
  `List Env` return type, which doesn't merge at all and lets the
  existing per-path discipline carry the soundness.

### Alternative — Defer path explosion to a separate pass

Run body-eval in a dedicated pre-pass that produces one env per
caller path, threading paths in/out via some out-of-band channel.

- **Why rejected:** an architecture change that breaks the
  abstraction "evaluator processes statements." Returning `List Env`
  from the existing command-eval functions keeps the eval-loop
  architecture intact and just changes one return type.

## Build sequence (preview)

The implementation will deliver the change in this order:

1. **Widen `Command.eval`'s return type.** Change the signature from
   `Command × Env` to `Command × List Env`. Wrap the existing `.cmd c`
   case as `(.cmd c, [E])` and the `.call` case to forward
   `handleCall`'s list. Update `evalOneStmt`'s `.cmd c` arm to
   `envs.map (fun E => …)`. Build green; run existing tests.

2. **Widen `Command.handleCall`.** Same shape: return `Command ×
   List Env`. `.Contract` arm: `let (c, E') := inlineCallContract …;
   (c, [E'])`. `.Body` arm: forward `inlineCallBody`'s list. The
   `.BodyOrContract` arm remains structurally similar but acts on
   the list (check whether any returned env has `.OutOfFuel`; if so,
   fall back to `[inlineCallContract result]`).

3. **Widen `Command.inlineCallContract`.** Wrap the single existing
   return `(c, E)` as `(c, [E])` at all return sites.

4. **Widen `Command.inlineCallBody`.** Remove the squeeze (the
   `processedEnvs` match in commit `fa82fe42b`). Return `(retCmd,
   processedEnvs)` directly. The `.OutOfFuel` and "procedure not
   found" early-return paths still produce a single-element list:
   `(retCmd, [errorEnv])`.

5. **Add multi-path tests.** New tests in `InlineCallBodyTests.lean`
   demonstrating the cases listed in *Testing* above.

6. **Validate regression.** Run the full test suite. All existing
   tests must pass. Default-path behaviour must remain identical
   (`callPolicy = .Contract` exercises the singleton-list path; the
   solver sees the same obligations as before).

7. **Cross-validation.** When this feature lands on `htd/smack`, run
   the portfolio under `--call-policy bodyOrContract` and compare
   PASS counts to baseline `Contract`. Expected: equal or higher.

Each step leaves the tree buildable.

## Future work

- **Performance under `--path-cap none`**: SMACK harnesses with deep
  symbolic branching may produce thousands of paths. A safe default
  for `--path-cap` (e.g., 32) would prevent runaway path explosion
  without sacrificing precision in typical cases. Out of scope for
  this spec; tracked separately.
- **Better SMT-solver telemetry per fork**: today's solver
  invocations are per-obligation. A forked call site can produce
  many obligations across paths; better grouping would help debugging
  failed verifications.
- **Statistics counter for body-eval forks**: add an
  `Evaluator.Stats.callBodyForked` counter so users can see how often
  multi-path body-eval fires in a run.
- **CFG callee body unification with `evalCFGBlocks`**: today
  `evalCalleeCFG` (in `StatementEval.lean`) duplicates ~50 lines from
  `evalCFGBlocks` (in `ProcedureEval.lean`) due to the import
  direction. A future refactor that promotes the shared CFG-walking
  logic into a third module would eliminate the duplication.
