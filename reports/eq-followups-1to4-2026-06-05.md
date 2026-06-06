# EQ Follow-ups 1-4 Bundle (2026-06-05)

Roll-up of four follow-up items queued at the close of the autonomous-closeout pass:
1. Local merge of the e-15 decimal fix into htd/smack.
2. Solver-pin investigation (Option A: strip the two `Solver.setOption` calls in Verifier.lean).
3. TIMEOUT-shape sub-classification on the smallest 8 of the 28 Java-SMACK files.
4. Post-fix rerun plan (Tracks A and B), recipe-only.

## 1. Headline

- **Closed.** e-15 decimal fix merged locally into `htd/smack` (`c1b1ce5ee`); solver-pin Option A confirmed safe by full-matrix benchmark (zero regression, zero gain) and is merge-ready; the TIMEOUT-shape probe (8/8 smallest Java-SMACK files) returned a clean diagnosis. The post-fix rerun plan is committed in-tree.
- **Stayed open.** Neither the e-15 merge nor the solver-pin Option A has been pushed to origin. Track A's Java-SMACK 28-file re-test is still gated on lean4 PR #1331; Track B's 10-file Probe-2 re-test is now ready (e-15 trigger met locally) but unstarted.
- **Reframed.** Java-SMACK TIMEOUTs are now classified as **100% eval-side** on this 8-file sample, with a sharp internal split (3/8 VC-flooding, 5/8 stuck-pre-VC). The previous reflex of "blame the solver" is empirically refuted for this corpus — `--no-solve` does not change the verdict on any file. The right Tier-1 follow-up is an eval-phase profile, not an SMT cost-reduction effort. The "Body-eval cost regression" backlog item is the correct routing target for both sub-buckets.

## 2. Item 1 — e-15 local merge (cached)

- **Side branch (source):** `htd/decimal-e15-fix` at fix commit `6f5e74fa6` ("fix(decimal): emit decimal literals never scientific notation"), worktree `/Users/htd/Documents/Strata-decimal-e15-fix`.
- **Merge into htd/smack:** merge commit `c1b1ce5ee20b5a5fb757b297736e63715e1785ed`. Single-file change in `/Users/htd/Documents/Strata-smack/Strata/DDM/Util/Decimal.lean` (+9 / −4). No merge conflicts.
- **Build status:** `lake build strata` clean, 540/540 jobs.
- **Push status:** **NOT PUSHED.** `htd/smack` is currently 2 commits ahead of `origin/htd/smack`. Local-only by design — pushing is a separate explicit step.

## 3. Item 2 — Solver-pin Option A (cached)

- **Pinning sites:** `/Users/htd/Documents/Strata-smack/Strata/Languages/Core/Verifier.lean:180-181`, the z3-prelude branch:
  - `Solver.setOption "smt.mbqi" "false"`
  - `Solver.setOption "auto_config" "false"`
  Source comment acknowledges these are vestigial Boogie defaults without Strata-specific justification.
- **Option A** (the test): strip both `setOption` calls. Implemented in worktree `/Users/htd/Documents/Strata-smt-options-test` on branch `htd/smt-options-test` at `Verifier.lean:180-184`.
- **Build status:** clean.
- **Bench result (94-program SMACK matrix under `--call-policy bodyOrContract --split-procs`):** **68 PASS / 15 PASS-? / 11 PARTIAL** — bit-identical to the v6 `htd/smack` baseline. Zero regression, zero improvement.
  - Matrix log: `/tmp/claude-503/smtoptions-matrix.txt`.
- **Why no improvement.** The 15 PASS-? are evaluator-gap (CFG loop-exit using pre-loop concrete values; see [`v6-pass-question-mark-classification.md`](v6-pass-question-mark-classification.md)) and the 11 PARTIAL are not bound by SMT quantifier-instantiation precision. Stripping the pin doesn't unlock them.
- **Recommendation:** **merge Option A.** The change is empirically safe on the current corpus and removes a hidden-knob foot-gun for users whose programs need MBQI / Z3's auto-tuning to discharge.
- **Push status:** **NOT PUSHED.** Side-branch only; needs an explicit merge into `htd/smack` (and a separate push) when greenlit.

## 4. Item 3 — TIMEOUT shape (live)

**Files-attempted:** 8 of 8. Smallest TIMEOUT files from the 28-file Java-SMACK Tier-1 sweep, sizes 272 KB - 1.083 MB. Same-host wall-clock budget 90 s, baseline (full pipeline) vs `--no-solve`. VC counts measured by `find <vcs-dir> -type f | wc -l` after each run.

**Per-file table:**

| # | file                      | size (KB) | baseline rc | baseline elapsed | --no-solve rc | --no-solve elapsed | VCs emitted | class                          |
|---|---------------------------|----------:|------------:|-----------------:|--------------:|-------------------:|------------:|--------------------------------|
| 1 | EQ_hy1zdfiib10_out        |       272 |         124 |              90s |           124 |                90s |        7880 | eval-side (VC-flooding)        |
| 2 | EQ_rw303ny41mm_out        |       300 |         124 |              90s |           124 |                90s |           0 | eval-side (stuck-pre-VC)       |
| 3 | EQ_5h4vnvtthnw_out        |       340 |         124 |              90s |           124 |                91s |           0 | eval-side (stuck-pre-VC)       |
| 4 | EQ_djjs5dmnm0t_out        |       470 |         124 |              90s |           124 |                90s |        4966 | eval-side (VC-flooding)        |
| 5 | EQ_v1tojvpjjxs_out        |       609 |         124 |              90s |           124 |                91s |         391 | eval-side (VC-flooding)        |
| 6 | EQ_swtcbwgphx3_out        |       656 |         124 |              93s |           124 |                92s |           0 | eval-side (stuck-pre-VC)       |
| 7 | EQ_a0je0ul5r1z_out        |       811 |         124 |              90s |           124 |                90s |           0 | eval-side (stuck-pre-VC)       |
| 8 | EQ_4tzmitiatux_out        |      1083 |         124 |              90s |           124 |                90s |           0 | eval-side (stuck-pre-VC)       |

**Bucket counts.** eval-side **8/8**, SMT-side **0/8**, borderline **0/8**. Within eval-side: VC-flooding **3/8** (hy1z, djjs, v1to), stuck-pre-VC **5/8** (rw303, 5h4vn, swtcb, a0je0, 4tzmi).

**Headline diagnosis.** Java-SMACK TIMEOUTs on this size band are **100% eval-side**. The SMT solver is never the bottleneck — `--no-solve` does not move any file from TIMEOUT to PASS, and elapsed time is essentially identical (Δ ≤ 2 s) between baseline and `--no-solve` on every file. The eval bottleneck splits two ways:

- **(a) Stuck-pre-VC, 5/8** (rw303, 5h4vn, swtcb, a0je0, 4tzmi): zero VCs emitted in 90 s with `--no-solve`, zero stdout. Symbolic eval is pinned in a pre-VC phase — plausibly `bodyOrContract` inlining, fix_core_st-style super-linear processing, or a non-terminating eval branch. These never get to the obligation-emission phase.
- **(b) VC-flooding, 3/8** (hy1z 7880 VCs, djjs 4966 VCs, v1to 391 VCs): eval *does* emit VCs, but exhausts the 90 s wall before finishing the procedure list. Indicates a `bodyOrContract` + `--inline-fuel 100` cardinality blow-up that produces VCs faster than it can complete the program.

**Implication for Tier-1 follow-up.** The right next probe is an **eval-phase profile** — `--profile`, per-procedure timing, or a stack sample on a stuck-pre-VC file like `rw303` — *not* an SMT cost-reduction attempt. The existing "Body-eval cost regression on bodyOrContract" backlog entry is the correct routing target for both sub-buckets; no new backlog item is needed.

**Sub-items skipped/failed:** none. All 8 files completed both runs and produced VC counts. No measurement gaps.

**Artifacts:** `/tmp/claude/probe1b/results.csv`, per-file VC dirs at `/tmp/claude/probe1b/vcs-*/`.

## 5. Item 4 — Post-fix rerun plan

Recipes-only document, no live runs. Two re-tests queued behind separate triggers:

- **Track A (Post-#1331 Java-SMACK re-test, 28 files).** Trigger: lean4 PR #1331 reaches `htd/smack` via toolchain bump. Pass criteria: zero `Cannot find this fvar in the context! old` occurrences across all 28 logs. Expected outcome: the 6/28 elab-fail bucket clears.
- **Track B (Post-e15 Probe-2 re-test, 10 files).** Trigger **already met** as of the e-15 local merge `c1b1ce5ee`. Ready to run.

**Pointer:** [`/Users/htd/Documents/Strata-smack/reports/eq-post-fix-rerun-plan-2026-06-05.md`](eq-post-fix-rerun-plan-2026-06-05.md).

## 6. BACKLOG impact

**Flip / annotate (existing entries):**

- `### Strata-side: SMT2 emission bug — scientific-notation literal e-15 …` (BACKLOG.md:177): "Next action" currently reads "Push side branch and file upstream issue … Then merge `6f5e74fa6` into htd/smack". The local merge half is now done at `c1b1ce5ee`. Remaining next action: push and file upstream. (Annotation, not a status flip — upstream filing is still pending.)
- `### Body-eval cost regression on bodyOrContract` (BACKLOG.md:293): the 8-file TIMEOUT-shape probe in Item 3 confirms this bucket is the right home for both VC-flooding and stuck-pre-VC TIMEOUTs on Java-SMACK at this size band. Annotate with the new sub-classification and the `/tmp/claude/probe1b/` artifact pointer.
- `### Test the pipeline on the equalizer benchmark` (BACKLOG.md:36): the headline "RESOLVED-PROVISIONAL" is unchanged, but Item 3's diagnosis adds a 100%-eval-side empirical anchor that should be cited if a follow-up sweep is opened.

**Add (new entries):**

- **Solver-pin Option A merge follow-up.** Single-line: "Merge `htd/smt-options-test` (strip vestigial `smt.mbqi=false` / `auto_config=false` setOptions in `Verifier.lean:180-181`) into `htd/smack`. Bit-identical 68/15/11 on the 94-program matrix; zero regression, zero gain, but removes a hidden knob." Status: READY-TO-MERGE.
- **Eval-phase profile probe (Java-SMACK TIMEOUT root cause).** Single-line: "On a stuck-pre-VC file (recommend `rw303ny41mm`, the smallest at 300 KB) and a VC-flooding file (recommend `v1tojvpjjxs`, 609 KB / 391 VCs), run with `--profile` and/or take a process stack sample at the 60-90 s mark. Goal: discriminate inlining vs CFG-step vs trans-eval as the eval-phase bottleneck." Status: OPEN, queued behind solver-pin merge.

## 7. Recommended next step

Push the e-15 merge **and** Option A together as a small `htd/smack` upgrade batch: both are local-clean, both have benchmark coverage, both unblock downstream work (Probe-2 Track B for e-15; future MBQI-needing programs for Option A). After push, kick off Track B's 10-file re-test against the freshly-pushed `htd/smack` and use the eval-phase profile probe (Item 6 new entry) as the next investigative wedge if the Java-SMACK TIMEOUT bucket remains the dominant unresolved cohort.
