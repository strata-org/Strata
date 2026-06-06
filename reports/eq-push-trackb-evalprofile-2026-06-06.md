# EQ push batch + Track B re-test + eval-phase profile findings

**Date:** 2026-06-06
**Branch:** htd/smack
**origin/htd/smack SHA after push:** 528fec0f2e09387862cff151b325a8d6834f3a50

## 1. Headline

- **Pushed 5 commits to origin/htd/smack** (c52c7d178..528fec0f2 fast-forward), landing both the e-15 SMT2 decimal-literal fix (c1b1ce5ee merge of 6f5e74fa6) and the Option A vestigial-Z3-`setOption`-strip (528fec0f2 merge of bc4717354), plus the items-1-4 follow-up doc bundle.
- **Track B re-test cleared 5/5 e-evidence files at the SMT-symbol layer**, with 3/5 flipping clean to PASS (1,383 newly-passing goals across EQ_0exak45poxy, EQ_0q0oga15aij, EQ_0z42qdmejd0) and 2/5 losing the e-symptom but still TIMEOUT — meaning the e-15 fix unblocks them at the lexer/SMT layer but a separate solver-perf ceiling remains. Silent TIMEOUTs (4/10) did not shift; zero regressions; one unrelated FAIL-elab (issue #1331).
- **Eval-phase profile of the two long-tail TIMEOUT shapes (rw303 stuck-pre-VC, v1to VC-flooding) localised the cost to two pre-SMT Core transforms, neither of which is in `Procedure.eval`**: rw303 is pinned in the ANFEncoder's bottom-up `replaceExprs` HashMap-probed tree walk (RSS 6.4 GB at 25 s); v1to is pinned in obligation extraction's quadratic `PathConditions.addInNewest` (`newest ++ m`) churn over 391 VCs. This re-frames the body-eval BACKLOG entry: the cost regression is not body-eval-specific.

## 2. Push batch

Pushed cleanly as a fast-forward; 5 commits landed in this batch (oldest to newest):

- 6f5e74fa6 fix(decimal): emit decimal literals (never scientific notation) for SMT
- c1b1ce5ee Merge htd/decimal-e15-fix: SMT2 scientific-notation literal fix
- 940a9a406 docs: items 1-4 follow-up bundle (e-15 merge + solver-pin + TIMEOUT-shape + rerun plan)
- bc4717354 test(verifier): strip vestigial Z3 setOption pins (option A)
- 528fec0f2 Merge htd/smt-options-test: strip vestigial Z3 setOption pins

Local htd/smack and origin/htd/smack now both point at 528fec0f2. Build verified clean post-merge (540/540 jobs, "Build completed successfully"). Pre-push state was 3 commits ahead at 940a9a406; the Phase 1 merge of htd/smt-options-test (which had had to be committed locally as bc4717354 — the worktree carried only uncommitted edits at task start) brought the count to 4, and the push delivered all 4 plus the c1b1ce5ee merge that was already local.

## 3. Track B verdict (10 files, post-fix re-run)

| Bucket | Pre-fix count | Post-fix count | Behaviour |
|---|---|---|---|
| Cleared to PASS | — | 3 | #4 (261 goals), #7 (524 goals), #10 (598 goals) — total 1,383 goals |
| e-symptom cleared but still TIMEOUT | — | 2 | #3, #5 (e- evidence gone, hits separate solver-perf ceiling) |
| Silent TIMEOUTs (no e- pre or post) | 4 | 4 | #1, #2, #8, #9 — distinct non-e-15 root cause |
| Unrelated FAIL-elab (issue #1331) | 1 | 1 | #6 |
| Regressions | 0 | 0 | — |

**E-evidence at the SMT-symbol layer:** 5/10 pre-fix → 0/10 post-fix. 100% of the e-evidence symptom eliminated; 60% of e-evidence files flipped to fully PASS. The 2 partial-clear files (#3, #5) are now clean diagnostic candidates for whatever solver-side cost they hit — the lexer is no longer in the picture. Silent TIMEOUTs (4) are confirmed orthogonal: they had no e- evidence pre-fix and behave identically post-fix, ruling out the Option A `setOption` strip as a cause of regressions.

Artifacts: `/tmp/claude/probe2_retest/results.tsv` plus per-file stdout/stderr/.core.st.

## 4. Eval-phase profile diagnosis

5-second `sample` snapshots taken at t≈25 s (Strata `--profile` log buffered until completion and never flushed before SIGTERM, so the sample-based stack is the only ground truth here).

### rw303 (stuck-pre-VC, no `[obligation]` lines emitted)

- **Dominant phase:** `Strata.Core.verify` → `List.forIn'.loop` → `Core.anfEncoderPipelinePhase.lambda 0` → `Core.ANFEncoder.anfEncodeProgram` → recursive `Imperative.Block.mapExpr` / `Stmt.mapExpr`.
- **Bottom-of-stack mechanism:** 16% `Std.DHashMap.Internal.Raw.Const.get?` inside `ANFEncoder.replaceExprs.check`; 9% `replaceExprs.go`; 9% `Lambda.instHashableLMonoTy.hash`; ~25% combined malloc/free churn.
- **Mechanism:** `replaceExprs` does a bottom-up traversal that recomputes `LMonoTy` hashes and probes a duplicate-replacement HashMap at every subexpression node. With deep nested `Block`/`Stmt` trees from a multi-thousand-statement procedure, the HashMap probe + hash recompute per node dominates wall time; RSS at 6.4 GB by 25 s is consistent with allocation-heavy tree rewriting.
- **Why no VCs are emitted:** ANF encoding runs *after* type-check + symbolic-eval and *before* `verifySingleEnv` / `extractObligations`. The walker never returns from ANF, so VC emission never starts. Matches the stuck-pre-VC profile exactly.
- **Recommended fix axis:** memoise `LMonoTy` hashes on `Expr` metadata; short-circuit the HashMap probe when `replacements.isEmpty`; consider a body-size threshold above which ANF encoding is skipped or done lazily per-block.

### v1to (VC-flooding, 391 `[obligation]` lines)

- **Dominant phase:** `Strata.Core.verifySingleEnv` → `Core.ObligationExtraction.extractObligations` → `List.foldlM` → recursive `Core.ObligationExtraction.extractGo` → `extractFromCmd` → `Imperative.PathConditions.addInNewest`.
- **Bottom-of-stack mechanism:** 23% `List.reverseAux` (inside `appendTR`); 19% `lean_dec_ref_cold`; 11% `mi_free`; 9% `mi_malloc_small`; 7% `lean_inc_heartbeat`.
- **Mechanism:** `PathConditions.addInNewest` (Strata/DL/Imperative/EvalContext.lean:91-94) does `newest ++ m` per call, and `extractGo` calls it once per command. Over a procedure with N commands, the path-condition list grows monotonically with each command processed, so total work is O(N²) per VC and O(N²·V) overall (V=391). With v1to's 2.5 MB / ~89k-line core.st, the inner `List.reverseAux` of `appendTR` swamps the wall clock.
- **Why VCs *do* emit but never finish:** extraction is the loop body of VC generation; each VC's per-command append phase pays the quadratic cost on path-condition length, so VCs trickle out but never complete.
- **Recommended fix axis:** represent `PathCondition` as a snoc-list / `Array` so append is O(1) amortised; or prepend `m` and reverse once at VC emission; or thread an accumulator down `extractGo` that builds the path condition in reverse and reverses on emission only.

## 5. What this re-frames

The current BACKLOG carries an entry roughly titled *"Body-eval cost regression on bodyOrContract"* attributing the SMACK-scale TIMEOUTs to body-evaluation expansion. The profile evidence above contradicts that framing for the two representative files:

- Neither `Procedure.eval` nor any body-eval frame appears in the dominant stacks at t≈25 s.
- Both root causes (`replaceExprs` HashMap probe; `PathConditions.addInNewest` snoc-append) are pre-existing data-structure choices in Core-to-Core post-eval transforms and would TIMEOUT on `--call-policy contract` too — they are not gated on body-eval expansion.
- The cost is **post-eval and pre-SMT**, in two specific transforms: ANF encoding (rw303 shape) and obligation extraction (v1to shape). Body-eval may *increase* the input size to these phases, but the asymptotic blow-up is in the transforms themselves.

This means the right BACKLOG framing is "Quadratic post-eval Core transform costs on SMACK-scale inputs," with body-eval as an amplifier rather than the root cause. The body-eval entry should be retitled / split.

## 6. BACKLOG impact

**Entries to flip:**

- *"Body-eval cost regression on bodyOrContract"* — re-scope away from body-eval as root cause. Body-eval is a contributing input-size amplifier; the asymptotic costs live in two specific post-eval transforms diagnosed above. Re-test on `--call-policy contract` should be added to confirm both shapes still TIMEOUT without body expansion.

**Entries to add (as siblings under "Quadratic post-eval transform costs on SMACK-scale inputs"):**

1. **ANFEncoder quadratic on deep procedure bodies** — `Strata/Transform/ANFEncoder.lean` `replaceExprs.go` recomputes `LMonoTy` hashes and probes the replacements `HashMap` at every subexpression node; combined with `Block.mapExpr`/`Stmt.mapExpr` recursion, this dominates wall time on multi-thousand-statement procedures. Mitigations: memoise hashes on `Expr` metadata; short-circuit HashMap probe when `replacements.isEmpty`; size-threshold bail-out.
2. **PathConditions.addInNewest quadratic in obligation extraction** — `Strata/DL/Imperative/EvalContext.lean:91-94` does `newest ++ m` per call; `Core.ObligationExtraction.extractGo` calls it per command, so total work is O(N²·V). Mitigations: snoc-list/`Array` representation; prepend-then-reverse-on-emit; reverse-accumulator threaded through `extractGo`.

**Entries to add (Track B follow-up):**

3. **Solver-perf ceiling on partial-clear files (#3, #5)** — both lost their e- symptom but still TIMEOUT. Now ripe for SMT-side profiling (Z3 `-st`, MBQI quantifier instantiation count) since the lexer is no longer a confound.
4. **Silent-TIMEOUT cluster (#1, #2, #8, #9)** — confirmed orthogonal to e-15. Need their own diagnostic axis; first-pass hypothesis: same ANFEncoder/PathConditions quadratic costs on smaller inputs that nonetheless tip over the 60 s ceiling.

## 7. Recommended next step

Pick **one** of:

- (a) **Mitigation spike on PathConditions.addInNewest** (Strata/DL/Imperative/EvalContext.lean:91-94) — represent `PathCondition` as a snoc-list, re-time v1to. Smallest blast radius, fastest signal: the call site is one function and the change is local. If this drops v1to from TIMEOUT to PASS, it confirms the diagnosis and clears one of the two long-tail shapes immediately.
- (b) **`--call-policy contract` re-run on rw303 + v1to** — confirm both still TIMEOUT without body-eval expansion. Cheapest evidence to formally close the body-eval-as-root-cause framing in BACKLOG.

Recommendation: do (b) first (≈2 min, 0 LoC), then (a) (estimated half-day spike with high confidence of clearing v1to).

## Files

- /tmp/claude/profile-2026-06-06/EQ_rw303ny41mm_out.sample.txt
- /tmp/claude/profile-2026-06-06/EQ_v1tojvpjjxs_out.sample.txt
- /tmp/claude/profile-2026-06-06/EQ_rw303ny41mm_out.profile.log (empty — buffered)
- /tmp/claude/profile-2026-06-06/EQ_v1tojvpjjxs_out.profile.log (empty — buffered)
- /tmp/claude/profile-2026-06-06/EQ_rw303ny41mm_out_fixed.core.st (697 KB, 25 k lines)
- /tmp/claude/profile-2026-06-06/EQ_v1tojvpjjxs_out_fixed.core.st (2.46 MB, 89 k lines)
- /tmp/claude/probe2_retest/results.tsv (Track B re-test, 10 files)
