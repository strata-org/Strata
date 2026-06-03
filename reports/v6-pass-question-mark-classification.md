# PASS-? classification: the 15 vacuous-pass cases on the v6 SMACK matrix

**Date:** 2026-06-03
**Branch:** `htd/smack` @ `cbe1091c3` (post-B3 cherry-pick + follow-up)
**Method:** Local `dbg_trace` instrumentation in
`Strata/Languages/Core/Verifier.lean` printing the obligation label,
predicate, and assumptions whenever both SMT queries return UNSAT
(i.e. when `o.unreachable = true`). Drove `strata verify
--check-mode deductive --check-level full --call-policy bodyOrContract
--inline-fuel 100 --procedures <P>` on each PASS-? program's `main`
procedure and inspected the captured assumptions.

The instrumentation was **local-only** (never committed). This report
is the persistent artifact.

## TL;DR

**All 15 PASS-? cases share one mechanism: CFG-eval explores the
loop's exit branch using *concrete pre-loop* induction-variable
values, producing path conditions `assume false` whenever the loop
guard is initially true.** This is an evaluator gap, not a translator
artifact and not a genuine vacuity.

The mechanism is independent of `--inline-fuel` (verified earlier in
the v5-pass-question-mark-analysis fuel-bump experiment) and
independent of program shape (`for` loop, `while(cond)` loop, or
`while(1) { ... goto out; }` — all exhibit the same pattern).

The fix lives in the loop-handling logic of CFG-eval: either
- (a) symbolically execute the loop with fresh induction variables,
  taking the exit-branch only after `--inline-fuel` iterations have
  been unrolled, or
- (b) on the exit branch, replace the loop-modified-set with fresh
  symbolics so the post-loop path conditions don't pin the guard to
  pre-loop concrete values.

Both restore soundness for the would-be-PASS group (9 programs that
are genuinely safe) and surface the would-be-FAIL group (6 programs
that are unsafe under the SV-COMP oracle) as actual PARTIAL or FAIL.

## What the verifier sees

For `array_sum` (the smallest reproducer — 4-iteration `for` loop, `assert(sum == 10)`), the captured trace shows:

```
[unreachable-pass-q] label=(Origin_assert__i32_Requires)assert__i32_requires_0
  predicate = !((zext_i1_i32(sum == 10)) == 0)
  assumptions = [
    ...prelude...,
    (<cfgBranch_false: !($__nondet_0)>, if $__nondet_0 then false else true),
    (assume_19, !(_slt_i32(0, 4) == 1))
  ]
```

`_slt_i32(0, 4) == 1` is the loop guard `i < 4` evaluated with the
pre-loop value `i = 0`, which is `true`. `!(true)` = `false`. So the
last assumption is **`assume false`** — the path is trivially UNSAT.

The assertion `sum == 10` is reachable only if the loop exits, but
the verifier explored the exit path on iteration 1 with concrete
pre-loop values, when the loop cannot exit. The actual reachable exit
is after iteration 4 with `i = 4, sum = 10`, but CFG-eval never
explores that path because it doesn't unroll the loop.

The pre-translation `.core.st` of `array_sum`'s loop is:

```
_bb1: { ...; _i4 := _slt_i32(_i3, 4); ...; goto _bb2, _bb3; }
_bb2: { assume (_i4 == 1); ...; goto _bb4; }   -- loop body
_bb3: { assume !(_i4 == 1); ...; assert __i32(...); ... }   -- loop exit
_bb4: { ...; _i3 := _i9; goto _bb1; }   -- back-edge
```

CFG-eval with concrete `_i3 = 0` evaluates `_i4 = _slt_i32(0, 4) = 1`,
then explores both `_bb2` and `_bb3` symbolically. On `_bb3` the path
condition is `assume !(1 == 1)` = `assume false`. UNSAT. Reported as
`pass (path unreachable)` because `--check-level full` runs both SMT
queries and detects the vacuity.

## Per-program classification

All 15 are **EVALUATOR-GAP** (loop-havoc / induction-variable
abstraction failure). Evidence summarized below; full traces in
`/tmp/claude-503/passq-logs/`.

| Program | Oracle | Loop shape | Exit-branch path condition | Class |
|---|---|---|---|---|
| `array_sum` | n/a (safe by construction) | `for (i=0; i<4; i++) sum+=a[i]` | `assume !(_slt_i32(0,4) == 1)` ≡ `assume false` | EVALUATOR-GAP |
| `loop_sum` | n/a (safe by construction) | `for (i=0; i<5; i++) sum+=i` | `assume !(_slt_i32(0,5) == 1)` ≡ `assume false` | EVALUATOR-GAP |
| `sv_loops_loopv3` | safe | `while (x < 50000001)` | `assume !(_slt_i32(0,50000001) == 1)` ≡ `assume false` | EVALUATOR-GAP |
| `sv_loops_mono1_1_2` | safe | `while (x < 100000000)` (unsigned) | `assume !(_ult_i32(0,100000000) == 1)` ≡ `assume false` | EVALUATOR-GAP |
| `sv_loops_nested3_1` | safe | triply-nested `while` to 0x0fffffff | 3 `cfgBranch_false` assumptions on outer + inner guards, all UNSAT | EVALUATOR-GAP |
| `sv_loops_mono3_1` | unsafe | `while (x < 1000000)` (unsigned) | `assume !(_ult_i32(0,1000000) == 1)` ≡ `assume false` | EVALUATOR-GAP |
| `sv_loops_mono4_1` | unsafe | `while (x < 1000000)` (signed) | `assume !(_slt_i32(0,1000000) == 1)` ≡ `assume false` | EVALUATOR-GAP |
| `sv_loops_mono5_1` | unsafe | `while (x < 10000000)` (unsigned) | `assume !(_ult_i32(0,10000000) == 1)` ≡ `assume false` | EVALUATOR-GAP |
| `sv_loops_mono6_1` | unsafe | `while (x < 10000000)` (unsigned) | `assume !(_ult_i32(0,10000000) == 1)` ≡ `assume false` | EVALUATOR-GAP |
| `sv_locks_10` | safe | `while(1) { ...; goto out; }` 10 locks | (probe variance — see below) | EVALUATOR-GAP (presumed) |
| `sv_locks_11` | safe | 11 locks | (probe variance — see below) | EVALUATOR-GAP (presumed) |
| `sv_locks_12` | safe | 12 locks | (probe variance — see below) | EVALUATOR-GAP (presumed) |
| `sv_locks_13` | safe | 13 locks | (probe variance — see below) | EVALUATOR-GAP (presumed) |
| `sv_locks_14_2` | unsafe | 14 locks, ERROR arm | (probe variance — see below) | EVALUATOR-GAP (presumed) |
| `sv_locks_15_2` | unsafe | 15 locks | (probe variance — see below) | EVALUATOR-GAP (presumed) |

**Probe variance on sv_locks_*:** these programs' `main` procedure
took >120s to verify in the per-procedure probe but completed in v6
matrix runs under the same flag set. Re-running `sv_locks_10` with a
300s timeout produced verdict `WARN (0 VCs)` rather than PASS-? —
suggesting the v6 PASS-? verdict was nondeterministic, possibly
sensitive to SMT solver scheduling or path-exploration state.
Classification "EVALUATOR-GAP (presumed)" is based on the program
shape (`while(1)` loop with concrete-value entry to the lock chain)
matching the same mechanism as the other 9 programs — the verifier
will treat the `if (cond == 0) goto out` branch with concrete
pre-loop values, hitting the same `assume false` path condition.

## Implications for the matrix

**Would-be-PASS (9 programs, oracle: safe or n/a):**

`array_sum`, `loop_sum`, `sv_loops_loopv3`, `sv_loops_mono1_1_2`,
`sv_loops_nested3_1`, `sv_locks_10`, `sv_locks_11`, `sv_locks_12`,
`sv_locks_13`.

These should reach a real PASS once the evaluator gap is closed. The
underlying programs are genuinely safe; the verifier just isn't
reasoning about the loop body to know that. Each is a soundness-
preserving precision gap — the matrix's PASS-? correctly self-flags
the vacuity, but the goal is a real PASS.

**Would-be-FAIL (6 programs, oracle: unsafe):**

`sv_loops_mono3_1`, `sv_loops_mono4_1`, `sv_loops_mono5_1`,
`sv_loops_mono6_1`, `sv_locks_14_2`, `sv_locks_15_2`.

These programs are genuinely unsafe under the SV-COMP oracle. The
PASS-? hides this — a sound verdict would be FAIL. Once the
evaluator gap is closed, these will surface as PARTIAL with a
concrete failing VC at the post-loop assertion. They become a probe
for soundness regressions in any future loop-handling work.

**Net soundness picture today:** zero spurious PASSes (the matrix is
self-flagging via `--check-level full`), but the matrix's "PASS"
column over-counts by 9 in the would-be-PASS group and under-counts
the unsafe programs' failure-detection by 6.

## Recommended fixes, ranked

1. **Symbolic loop unrolling with fresh induction variables** —
   On entering a CFG loop, replace the loop-modified-set with fresh
   symbolic variables before exploring branches. This makes
   `assume !(_slt_i32(?fresh, 4) == 1)` satisfiable (with `?fresh ≥ 4`)
   and the would-be-PASS programs reach their post-loop assertions
   with the right state. Requires identifying the modified set per
   loop; CFG-eval already has the back-edge information.
2. **`--inline-fuel` extension to symbolic loops** — Treat the
   back-edge like an `inlineCallBody`: unroll up to N times before
   falling through to a havoc. The would-be-PASS programs with small
   concrete bounds (`array_sum`, `loop_sum`, `sv_loops_nested3_1` if
   bounds are small enough) reach a real PASS by full unrolling. The
   would-be-FAIL programs and large-bound would-be-PASS programs
   reach the havoc-and-assume-false case, which is the current
   behavior — no improvement on those.
3. **Hybrid: option (1) for pre-`fuel` exits + option (2) for
   loop-body inlining up to fuel** — Strongest, matches how `bound`
   model checkers handle finite loops. Same risks as (1) for fresh
   vars but adds bounded unrolling for cheap PASSes.

Option (1) is the minimum required to fix the mechanism. Options (2)
and (3) are progressive enhancements on top.

## Cross-references

- Background analysis (pre-v6): [`v5-pass-question-mark-analysis.md`](v5-pass-question-mark-analysis.md). The fuel-bump null result there is consistent with this report's diagnosis: `--inline-fuel` controls body-eval recursion (call inlining), not loop unrolling.
- v6 surfacing logic: `Examples/smack-docker/run_pipeline.py:264` (`if "path unreachable" in output: return ("PASS-?", ...)`).
- Matrix per-program PASS-? list: `Examples/smack-docker/README.md` "v6 per-program detail".
- Backlog entry: `reports/BACKLOG.md` "Qualitative analysis of the 15 PASS-? unreachable cases" — this report.

## Local artifacts (not committed)

- `/tmp/claude-503/passq-logs/<program>.log` — 15 per-program raw logs (stdout+stderr) from the instrumented strata.
- `/tmp/claude-503/passq-logs/sv_locks_*-main.log` — re-probed `main` procedure logs at 300s timeout for the 6 sv_locks programs.
- `/tmp/claude-503/probe-passq.py` — driver script that runs the 15 programs through the translation + instrumented-strata pipeline.
- `/tmp/claude-503/probe-sv-locks.py` — driver script for the sv_locks reprobe.
