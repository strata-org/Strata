# Issue 1 unblocking: experiment branch + post-merge state

**Date:** 2026-06-02
**Branches involved:**
- `htd/smack` @ `bb604e553` (truth-of-record; carries the deferred-dedup fix and reorg)
- `htd/smack-tco-experiment` @ `b4f22e02e` (merged `htd/smack` in; carries the iterative walker fixes)

## TL;DR

**sce1 at N=100K now completes cleanly with `rc=0`** on the merged experiment branch in 38.9s, returning `All 0 goals passed.`

This is a step beyond the pre-merge experiment state documented in `Examples/tco-experiment/SUMMARY.md`, which reported "SIGABRT in 13.4s — partial fix" at N=100K. **The unblocking did not come from the merge of `htd/smack`** (which only added the deferred-dedup fix, irrelevant to sce1's pure-axiom flat-list shape). It came from three iterative-walker commits that landed on the experiment branch *after* the SUMMARY was written but *before* the merge. The SUMMARY was simply stale.

sce1 also passes at N=200K (144s wall-clock). sce2 unchanged (`rc=-6` SIGABRT in 0.1s) — no walker rewrite touches `elabExpr`.

## Timeline reconstruction

The SUMMARY at `Examples/tco-experiment/SUMMARY.md` (committed in `b20151b6c` on 2026-06-01) was written when the Round B fix tip was `a3fb64376` ("fix(verify): iterativize translateCoreDecls and Program.typeCheck"). Three more code-changing commits then landed on the experiment branch on the same day:

| Commit | Time | Touch | Net effect |
|---|---|---|---|
| `f3f409c66` | 2026-06-01 14:08 | `Strata/Transform/TerminationCheck.lean` (+117 / -1) | `TermCheck.transformDecls` rewritten from list-recursion to a `for`-loop that builds the result in reverse and reverses once at the end |
| `869d59f30` | 2026-06-01 15:14 | `Strata/Transform/PrecondElim.lean` (+118 / -1) | `PrecondElim.transformDecls` rewritten to the same pattern; this is the *exact* walker the conjectures-report named as the dominant culprit at N≈30K-50K |
| `438052e86` | 2026-06-01 16:14 | `Strata/Transform/CoreTransform.lean` (+41 / -28) | `runProgram` walker changed from O(N²) on `List.set` to O(N) — this is the upstream of `transformDecls` callers; the per-decl cost was previously quadratic in `decls.length` |

`SUMMARY.md` was not updated to reflect these three commits — its "post-fix" data was captured against the `a3fb64376` tip only. The SUMMARY's recommendation "Cherry-pick `a3fb64376` to `htd/smack`" was therefore conservative and incomplete; the four-commit set is the actually-validated unblocking package.

## Empirical re-validation (2026-06-02)

After merging `htd/smack` (`bb604e553`) into `htd/smack-tco-experiment` (`b4f22e02e`), `lake build strata` succeeds (542/542 jobs).

Running the harness:

```bash
cd /Users/htd/Documents/Strata-tco-experiment/Examples/tco-experiment
./run-all.sh post-merge
```

Results:

| Scenario | Pre-merge SUMMARY | Post-merge actual (2026-06-02) | Verdict |
|---|---|---|---|
| sce1 (N=100K axioms) | "SIGABRT in 13.4s" | `rc=0 elapsed=38.9s last='All 0 goals passed.'` | **Reaches verdict** |
| sce1 (N=200K axioms) | not tested | `rc=0 elapsed=144s last='All 0 goals passed.'` | **Reaches verdict** |
| sce2 (5000-deep ITE) | "SIGABRT in 0.1s" | `rc=-6 elapsed=0.1s last='Stack overflow detected. Aborting.'` | Unchanged (expected — no fix targets `elabExpr`) |

Logs in `Examples/tco-experiment/logs/post-merge/`.

## Why the merge itself was not the unblocking change

`htd/smack`'s recent Lean-code changes since the experiment's parent commit (`07f2ebb7e` cherry-pick #1185) are:

- `8f019818f` — `Strata/Languages/Core/ProcedureEval.lean` `evalCFGStep` deferred-dedup fix on the *false branch of CFG `condGoto`*. Affects symbolic CFG evaluation only.
- `bb604e553` — pure docs commit (no Lean code change).

sce1's input is 100K trivial axioms (`axiom [ax_0]: true; ...`); there are no procedures, no CFG, no symbolic conditions, and `Program.eval` doesn't materialize any deferred obligations. The deferred-dedup fix's code path is not exercised by sce1 at all. Verified by inspection: `evalCFGStep` is called only inside `Procedure.eval`, which is only called when the program has procedures. sce1 has none.

So the merge brought in the deferred-dedup fix as a no-op for sce1. The actual unblocking happened entirely on the experiment branch via the three commits listed above.

## What this means for cherry-pick scope

The plan was to cherry-pick `a3fb64376 f3f409c66 869d59f30 438052e86` (four commits) to `htd/smack` after re-validating against the v6 matrix. The re-validation now shows:

- Four commits is the right scope (matches the actually-validated set).
- sce1 at N=100K reaches a verdict, not the SUMMARY's "13.4s SIGABRT" — which means the cherry-pick is a stronger improvement than the spec advertised.
- The "residual at N≥100K" follow-up flagged in the SUMMARY's §"Follow-up work" is now obsolete for the documented N=100K reproducer. (Whether sce1 SIGABRTs at some larger N — say, 500K — is open; preliminary N=200K passed but a 500K test isn't necessary for the cherry-pick decision.)

The 94-program matrix re-run is in flight on the merged experiment branch. A clean baseline match (68 PASS / 15 PASS-? / 11 PARTIAL) confirms that the iterative-walker rewrites don't perturb the SMACK pipeline; that's the gate for the cherry-pick.

## Why was the SUMMARY stale

The experiment harness records logs per round (`logs/{pre,post-B,…}/`); the SUMMARY summarizes the most recently captured round. After Round B's first-ply commit (`a3fb64376`), the SUMMARY was written. Subsequent walker work on 2026-06-01 14:00-16:14 did not re-trigger a re-run of `run-all.sh`, so no new logs were captured and the SUMMARY's numbers stayed at the `a3fb64376` snapshot. This is a process gap (not an issue with the experiment itself); a follow-up note in `SUMMARY.md` would close it.

## Action items

1. **Cherry-pick** `a3fb64376 f3f409c66 869d59f30 438052e86` to `htd/smack` once the 94-program matrix on the merged experiment branch confirms the v6 baseline (68/15/11). Do this as four separate commits to preserve attribution; do not squash.
2. **Update `Examples/tco-experiment/SUMMARY.md`** on the experiment branch with a "2026-06-02 update" section recording the four-commit set and the 38.9s / 144s timings.
3. **Update `reports/stack-and-hang-conjectures-report.md`** issue (1) section: replace "Residual at N≥100K" with "Resolved at N=100K (38.9s) and N=200K (144s) on the merged experiment branch; threshold for the next downstream walker is now N≥??? — TBD if relevant."
4. **Update `BRANCH_FEATURES.md` bug #22** to reflect the now-fully-fixed-at-N=100K state (was "partial fix"; becomes "issue 1 fix complete at the documented reproducer; tracked further only if a larger-N reproducer becomes load-bearing").
