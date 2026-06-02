# `evalCFGStep` doubles `Env.deferred` across symbolic `condGoto` branches

- **Status:** present on `htd/unstructured-procedure` (HEAD `b44918af4`) and every descendant up to `htd/smack`'s pre-fix state. **Not** on origin/main HEAD `75f005566` because CFG-eval landed on `htd/unstructured-procedure` only and hasn't merged to main yet (PR [#1196](https://github.com/strata-org/Strata/pulls)). The bug ships with #1196.
- **Severity:** soundness-adjacent — produces no spurious PASS verdicts (each duplicate obligation is structurally equal, so the verifier proves the same thing 2^N times), but causes time/memory-exhaustion hangs proportional to `2^(#sequential symbolic condGotos)`. On real workloads (SMACK-translated cJSON / JSON_Iterate / JSON_Validate / 4 `skip*Scalars` harnesses) this materializes ~4 billion `Imperative.ProofObligation` entries and hangs the verifier indefinitely.
- **Component:** `Strata/Languages/Core/ProcedureEval.lean` (`evalCFGStep`, the symbolic-condGoto arm)
- **Cross-references:** [`reports/stack-and-hang-conjectures-report.md`](stack-and-hang-conjectures-report.md) (issue 3 — full diagnosis path including disproof of two earlier conjectures); [`reports/issue-1-unblocking-2026-06-02.md`](issue-1-unblocking-2026-06-02.md) (related but different walker family).

## What's wrong

In `Strata/Languages/Core/ProcedureEval.lean:88-104`, `evalCFGStep`'s symbolic-`condGoto` arm builds `env_t` and `env_f` by record-update on the parent `env'`. Both inherit `env'.deferred` (the proof-obligation accumulator) wholesale:

```lean
| .condGoto cond lt lf _ =>
  let cond' := env'.exprEval cond
  match cond' with
  | .true _ => ((lt, env') :: newActive, finished, stats)
  | .false _ => ((lf, env') :: newActive, finished, stats)
  | _ =>
    let condErased := cond.eraseTypes
    let label_t := toString (f!"<cfgBranch_true: {condErased}>")
    let label_f := toString (f!"<cfgBranch_false: !({condErased})>")
    let env_t := { env' with pathConditions :=
      (env'.pathConditions.addInNewest
        [.assumption label_t cond']) }
    let env_f := { env' with pathConditions :=
      (env'.pathConditions.addInNewest
        [.assumption label_f
          (Lambda.LExpr.ite () cond' (LExpr.false ()) (LExpr.true ()))]) }
    ((lt, env_t) :: (lf, env_f) :: newActive, finished, stats))
```

`mergeResults` (called from `evalCFGBlocks`) then concatenates the terminal envs' `deferred` arrays without dedup, propagating duplicates into the next procedure's eval via `Program.eval`'s thread of `Env`.

Each symbolic branch therefore doubles the pre-split obligation set. After K sequential symbolic `condGoto` branches across N procedures, deferred grows ~`2^K` per procedure, accumulating across procedures via the env thread.

## Reproduction

15-procedure MWE that triggers the bug on `htd/smack`'s pre-fix state. The MWE works against any branch with the CFG-eval code path (`htd/unstructured-procedure`, `htd/smack-timeout-fix`, `htd/smack` pre-`277c468cb`).

```python
# gen.py — write to mwe-15procs.core.st
N = 15
print('program Core;')
for i in range(1, N + 1):
    print(f'\nprocedure P{i}(x : int, out y : int)')
    print('spec { ensures (y >= 0); }')
    print('{}')
    print('cfg entry {')
    print('  entry: { branch (x >= 0) goto pos else neg; }')
    print('  pos: { y := x; goto done; }')
    print('  neg: { y := 0; goto done; }')
    print('  done: { return; }')
    print('};')
```

(The empty `{}` locals block is required by `htd/smack`'s grammar; on `htd/unstructured-procedure` itself, omit the `{}` and use `branch (x >= 0) goto pos else goto neg;`.)

Run on a Strata binary built without the dedup fix:

```
$ python3 gen.py > mwe-15procs.core.st
$ strata verify --check-mode deductive --check-level full mwe-15procs.core.st
…
Stack overflow detected. Aborting.
```

Wall-clock: ~60 ms before SIGABRT (rc=134). Stack overflow happens in the post-eval ITE-chain walker when it tries to traverse a 65534-deep statement tree built from the doubled deferred array.

### Diagnostic data — the doubling progression

Add a one-line `dbg_trace` to `Strata/Languages/Core/ProgramEval.lean:62`:

```lean
| .proc proc _md =>
  let (E, procStats) := Procedure.eval declsE proc
  dbg_trace s!"[proc-eval-end] {proc.header.name} (deferred={E.deferred.size})"
  go rest E (stats.merge procStats)
```

Rebuild strata, re-run the MWE. Output (pre-fix):

```
[proc-eval-end] P1 (deferred=2)
[proc-eval-end] P2 (deferred=6)
[proc-eval-end] P3 (deferred=14)
[proc-eval-end] P4 (deferred=30)
[proc-eval-end] P5 (deferred=62)
[proc-eval-end] P6 (deferred=126)
[proc-eval-end] P7 (deferred=254)
[proc-eval-end] P8 (deferred=510)
[proc-eval-end] P9 (deferred=1022)
[proc-eval-end] P10 (deferred=2046)
[proc-eval-end] P11 (deferred=4094)
[proc-eval-end] P12 (deferred=8190)
[proc-eval-end] P13 (deferred=16382)
[proc-eval-end] P14 (deferred=32766)
[proc-eval-end] P15 (deferred=65534)
Stack overflow detected. Aborting.
```

Recurrence: `D_{n+1} = 2*D_n + 2`. Each procedure adds 2 obligations of its own (the postcondition assertion, fired on each branch arm) and doubles the inherited deferred.

### Real-world reproduction (smack-docker pipeline)

The same bug shape on SMACK-translated `.bpl` programs reaches multi-billion-element deferred arrays. Per-procedure trace on `cjson_cJSON_Parse_harness.bpl` (17 procedures):

```
cJSON_Delete:28
cJSON_ParseWithOpts:56
cJSON_ParseWithLengthOpts:4928
cJSON_New_Item:9856
skip_utf8_bom:68992
buffer_skip_whitespace:896896
parse_value:3960692736
hang in parse_string
```

Materializing a 3.96-billion-element `Array (Imperative.ProofObligation Expression)` was the actual hang on the SMACK pipeline. Eight programs in the smack-docker portfolio were affected: `cjson_cJSON_Parse_harness`, `JSON_Iterate_harness`, `JSON_SearchConst_harness`, `JSON_Validate_harness`, `skipAnyScalar_harness`, `skipCollection_harness`, `skipObjectScalars_harness`, `skipScalars_harness`.

## Fix

One line: clear `deferred` on the false branch of the symbolic `condGoto` arm, mirroring the existing structured `.ite` dedup at `Strata/Languages/Core/StatementEval.lean:673`:

```diff
              let env_t := { env' with pathConditions :=
                (env'.pathConditions.addInNewest
                  [.assumption label_t cond']) }
-              let env_f := { env' with pathConditions :=
-                (env'.pathConditions.addInNewest
-                  [.assumption label_f
-                    (Lambda.LExpr.ite () cond' (LExpr.false ()) (LExpr.true ()))]) }
+              -- Mirror processIteBranches at StatementEval.lean:673: clear
+              -- `deferred` on the false branch so pre-split obligations
+              -- aren't duplicated across both branches. Without this, every
+              -- symbolic condGoto multiplies the deferred-obligation count
+              -- by 2, leading to multi-billion-element arrays on programs
+              -- with many sequential branches.
+              let env_f := { env' with
+                deferred := #[]
+                pathConditions :=
+                  (env'.pathConditions.addInNewest
+                    [.assumption label_f
+                      (Lambda.LExpr.ite () cond' (LExpr.false ()) (LExpr.true ()))]) }
              ((lt, env_t) :: (lf, env_f) :: newActive, finished, stats))
```

The fix is commit [`277c468cb`](https://github.com/strata-org/Strata/commit/277c468cb) on `htd/smack-timeout-fix`, cherry-picked as `8f019818f` on `htd/smack`. Empirically validated: full 94-program SMACK matrix produces 68 PASS / 15 PASS-? / 11 PARTIAL / 0 FAIL / 0 TIMEOUT with PARTIAL identities matching the pre-fix v4 baseline exactly (no soundness regressions). Post-fix MWE progression: `2 → 4 → 6 → 8 → … → 30` (strict +2 per procedure), all 15 goals pass in ~2s.

## Soundness rationale

Each `ProofObligation` snapshots its `assumptions` (path conditions) at creation time (`Strata/DL/Imperative/CmdEval.lean:64-83`). The verifier proves `assumptions ⊨ predicate` without consulting the env's current state. So each obligation is self-contained; dropping a duplicate from one branch removes a redundant proof obligation that the sibling branch still carries. The set of distinct obligations is unchanged.

`Env.deferred` is otherwise write-only during eval (verified by grep — the only readers are post-eval consumers at `Core.lean:168` and `ProcedureEval.lean:60`).

## Regression test

A `#guard_msgs` test in `StrataTest/Languages/Core/Tests/ProcedureEvalCFGTests.lean` seeds a pre-split assert before a symbolic `condGoto` and verifies the merged `deferred` contains the obligation exactly once, not twice. Test passes post-fix; would fail pre-fix. (Test code is in the cherry-picked commit `8f019818f`.)

## Why earlier conjectures missed it

See [`reports/stack-and-hang-conjectures-report.md`](stack-and-hang-conjectures-report.md) issue (3) section. Three conjectures preceded the diagnosis:

- **Conjecture A** (per-obligation ITE chain in `oblProgram`'s post-eval walkers like `extractGo`/`stmtToCST`) was directionally close — the SIGABRT *does* fire in a post-eval walker on the 65534-deep ITE chain — but located the *cause* downstream. The actual cause is `Program.eval` accumulating a deferred array that's exponentially too large, *which then* causes downstream walkers to overflow. Fix is at the source, not in the walkers.
- **Conjecture B** (active-paths worklist blowup in `evalCalleeCFG`) was wrong on location — the active-paths worklist is correctly bounded by fuel.
- **Conjecture C** (body-eval introduces a new walker) was correctly ruled out — the bug is independent of `--call-policy` / `--inline-fuel` (verified empirically).

The diagnostic that worked: per-procedure `dbg_trace` of `E.deferred.size` after each `Procedure.eval`. The exponential growth is immediately visible.
