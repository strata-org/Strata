# EQ-200 CFG Emit-Order Affected Count

Date: 2026-06-08
Branch: htd/smack
Sample: 200 .core.st files at /tmp/claude-503/eq200-cores/ (quartile-stratified by .bpl size from the ~3,529-file EQ corpus)
Question: how many files in the corpus exhibit at least one forward-flow `goto` rendered as a backward (lower source-position) target after SMACK -> Boogie -> Strata?

---

## 1. Headline

Two distinct numbers, with very different operational meaning:

(a) **Verification-blocked count: 0 / 200 files.**
The SMT verifier's CFG evaluator dispatches every block by label, not by list position. Verdict (any-fail vs all-pass) is invariant under reordering of `cfg.blocks`. Citations:
- /Users/htd/Documents/Strata-smack/Strata/Languages/Core/ProcedureEval.lean:92 — `evalCFGStep` dispatches via `cfg.blocks.lookup label`.
- /Users/htd/Documents/Strata-smack/Strata/Languages/Core/ProcedureEval.lean:160 — entry seeded as `(cfg.entry, preEnv)` (label, not head).
- /Users/htd/Documents/Strata-smack/Strata/Languages/Core/StatementEval.lean:967,973 — `runCFG` starts from `cfg.entry` and looks up by label each step.
- /Users/htd/Documents/Strata-smack/Strata/DL/Imperative/CFGSemantics.lean:129 — `StepCFG.eval_next` uses `List.lookup t cfg.blocks = .some b`.
- /Users/htd/Documents/Strata-smack/Strata/Languages/Core/StatementSemantics.lean:335 — `CoreCFGStep` has the same shape.
- /Users/htd/Documents/Strata-smack/Strata/Languages/Core/ObligationExtraction.lean:102-114 — obligations are independent per block ("Path conditions restart from the global pc for each block independently"); fold order does not change the obligation set.

The skeptic verdict-neutrality review (third skeptic) confirmed this for the SMT-verifier evaluator path explicitly. The cosmetic-order issue does **not** block any verification.

(b) **Exhibits-the-issue count: 195 / 200 files (97.5%)** have at least one forward-flow goto whose target appears earlier in source position than the source block, with no dominator/SCC justification (i.e. not a real loop back-edge).

The remaining 5 / 200 files are clean (zero forward-flow violations across all their procedures). Files: EQ_1ncwryiy1qx, EQ_f3xznsqn5oa, EQ_qk1tofyvuba, EQ_iwjr2x5ta4a, EQ_bbalcshq514.

---

## 2. Per-file and per-procedure detail

**Per-file totals (sum of n_violations over all procedures in the file):**
| stat | value |
|---|---|
| files processed | 200 |
| files with >= 1 violation | 195 |
| files clean | 5 |
| total violations (corpus sum) | 24,226 |
| min per file | 0 |
| p25 | 12 |
| median | 35 |
| p75 | 131 |
| p90 | 370 |
| p95 | 546 |
| p99 / max | 1,092 |

The distribution is heavy-tailed: the median file has 35 forward-flow violations, but the top 10% have >=370 each, and the worst two files have 1,092 violations each.

**Per-procedure totals (one row per `cfg <entry> { ... }` block in a file):**
| stat | value |
|---|---|
| total procedure rows | 3,293 |
| procedures with >= 1 violation | 2,317 (70.4%) |
| median violations per procedure | 2 |
| p90 | 14 |
| p95 | 26 |
| p99 | 131 |
| max (single procedure) | 271 |

**Loop back-edges (real cycles, classified by SCC > 1 or self-loop):**
- 214 / 3,293 procedure rows have at least one true loop back-edge (6.5%). 57 / 200 files contain at least one procedure with a real cycle. The remaining backward edges are forward-flow violations, i.e. the emit-order issue.

---

## 3. Corpus projection (200 -> ~3,529)

The 200-file sample is quartile-stratified by .bpl size, so a simple proportional estimate is sound (the strata-weighted mean of a balanced sample equals the simple mean).

**Files exhibiting the issue (>= 1 forward-flow violation):**
- Sample proportion: 195 / 200 = 0.9750
- Wilson SE = sqrt(p(1-p)/n) = 0.0110
- 95% CI on proportion: [0.9534, 0.9966]
- **Point estimate: 3,441 / 3,529 files**
- 95% CI: **[3,364, 3,517] files**

**Total forward-flow violations in the corpus:**
- Sample mean per file: 121.13 violations
- Sample stdev: 196.70 (very right-skewed)
- SEM = 13.91
- **Point estimate: ~427,000 violations**
- 95% CI: **[331,000, 524,000]** total violations across the ~3,529-file corpus.

The width of the violation-count CI reflects the heavy-tailed distribution; the file-count CI is tight because saturation is near 100%.

---

## 4. Confidence

**Overall confidence: high** for the headline counts; **load-bearing finding** is that none of these violations affect verifier verdict.

**Analyzer A vs B agreement: NONE.** A reports 24,226 violations across 195/200 files; B reports 0 violations across 0/200 files. However, the reconciliation determined B is **broken on this corpus format**, not a more conservative analyzer:
- B's `CFG_OPEN_RE` requires the literal keyword `cfg|block` and matched only the per-procedure `cfg <name>` outer wrapper. The inner `label: { ... }` blocks (which are the actual basic blocks in this corpus) carry no keyword, so B treated every procedure as a single giant block. Every B row has n_blocks=1, n_loop_back_edges=0, n_violations=0.
- B's n_gotos count is correct on every row and matches A exactly on all 3,293 rows, confirming the parsers see the same source bytes — B just doesn't decompose them.
- Per spec tiebreaker rules ("fewer violations wins only when both analyzers actually detect"), A's count is consensus.

**Skeptic 1 (random spot-check, 10 picks): confirms consensus.** All 10 manual recomputations matched the analyzer's edge lists, SCC decompositions, and violation classifications byte-for-byte. Picks spanned high (EQ_rkcfxh44yqx cfg#21: 25 violations across 102 blocks / 126 gotos, all from SMACK loop-elimination unrolling) and low (zero rows in mid-size procedures). Independent verifier at /tmp/claude-503/skeptic_verify.py reproduced the analyzer.

**Skeptic 2 (edge-cases): confirms consensus with one minor unrelated correction.** Found a self-loop counting bug at line 348 of cfg-order-analyzer-A.py (`if dst < src` should be `if dst <= src`), which causes `n_loop_back_edges` to undercount self-loop edges by 1 each. **The violation count is unaffected** — self-loops never reach the violation branch. All other edge cases (multi-back-edge, no-goto, single-finish, empty CFG, duplicate-entry procs, lambda braces, nondet mixed-target, quoted braces, unmatched braces) produced expected counts. No crashes. The headline 24,226 number stands.

**Skeptic 3 (verdict-neutrality): confirms consensus for the SMT-evaluator path.** The narrow claim — that verification verdict is independent of `cfg.blocks` order — is correct. Two upstream positional dependencies exist but do not affect SMACK-shaped input:
- /Users/htd/Documents/Strata-smack/Strata/Languages/Core/DDMTransform/Translate.lean:1814-1817 — `translateCFGProcedure` prepends locals to `cfg.blocks` head, assuming entry is first. Safe in practice for SMACK output.
- /Users/htd/Documents/Strata-smack/Strata/Languages/Core/ProcedureType.lean:85-118 — `typeCheckCFG` walks blocks in list order threading `currentEnv`. Comment at lines 85-89 acknowledges this is an over-approximation; the verdict guarantee is for the SMT-evaluator phase only.
- /Users/htd/Documents/Strata-smack/Strata/DL/Imperative/CFGToCProverGOTO.lean:65-69,80 — CBMC GOTO backend requires entry-first. Off the SMT-verifier path.

**Bottom line on confidence:** the 195/200 count is robust; the 0/200 verification-blocked count is robust **on the SMT-verifier path** (the only path that produces verdicts in the EQ run).

---

## 5. Notable findings

**Heavy-tail concentration.** Two files (EQ_kj1q4w52ojv, EQ_25x1ux2e1e4) carry 1,092 violations each — together they account for ~9% of all violations in the sample. Both contain procedures with ~1,943 blocks and ~2,217 gotos; SMACK's loop-unrolling appears to have produced a giant flattened CFG.

**The worst single procedure: 271 violations.** EQ_kj1q4w52ojv `anon0` (1,943 blocks, 2,217 gotos, 4 real loop back-edges, 271 forward-flow violations).

**Pattern: SMACK loop-elimination dominates the signal.** The most stress-testing skeptic spot-check (EQ_rkcfxh44yqx cfg#21: 102 blocks, 126 gotos, 25 violations, 0 real cycles) was an inlined Boogie `_loop1_0_*` construct that SMACK fully unrolled. After unrolling, 25 distinct exit edges fan back to a `_loop1_0_Return` block; none of these form cycles (every SCC is size 1), so the analyzer correctly classifies them all as forward-flow violations rather than loop back-edges. This pattern — exit-fan-in to a dominator-up-the-tree return block — appears to drive most violation counts.

**Diamonds and n-way switches are not the dominant pattern.** The largest contributors are unrolled-loop exit fan-ins, not branchy control flow. Median procedure has 2 violations; the long tail comes from a small number of procedures with massively unrolled loops.

**"Real loops" coexist with the issue.** 57 / 200 files contain at least one procedure with a true cycle. The analyzer's SCC machinery discriminates correctly between these and forward-flow violations on the picked examples.

---

## 6. Recommended next step

**Recommended: file an issue documenting the cosmetic emit-order divergence, and DO NOT prioritize a fix.**

Rationale:
- The verifier path is verdict-neutral (Skeptic 3, with citations). Reordering `cfg.blocks` cannot change pass/fail/timeout outcomes for the SMT evaluator.
- 195/200 prevalence means this is a systemic emitter behavior, not a corner case worth chasing per-file.
- The two real-positional consumers (Translate.lean:1814 prepending locals to head; CFGToCProverGOTO entry-first) both rely on SMACK's existing emission of entry-first; SMACK is already producing valid input. The forward-flow "violations" are downstream of entry, not at it.
- A fix (topo-sort blocks before emission, or after Strata import) would be small (~50 LoC in one place), but the absence of any verdict impact means the priority is cosmetic / readability / debuggability of generated `.core.st` files.

**If pursued, scope should be:** topo-sort `cfg.blocks` post-import in Strata's Boogie front-end so the rendered .core.st is more readable, with a regression test against this analyzer. Do NOT rewrite SMACK upstream — the Boogie this corpus came from is fine; the `.core.st` rendering is what people read.

**If extended measurement is wanted:** rerun analyzer A on the full ~3,529 corpus to nail down the projection (currently 95% CI [3,364, 3,517]), and fix Skeptic 2's self-loop counting bug at /tmp/claude-503/cfg-order-analyzer-A.py:348 to tighten the loop-back-edge stat (the violation stat is unaffected).

---

## 7. Files referenced

Analyzers:
- /tmp/claude-503/cfg-order-analyzer-A.py — primary analyzer (SCC-based, the one whose output is consensus)
- /tmp/claude/cfg-order-analyzer-B.py — secondary analyzer (dominator-based; broken on this corpus's `label: {` inner-block format)

Data:
- /tmp/claude-503/eq200-cores/ — 200 .core.st input files
- /tmp/claude-503/cfg-order-A-results.tsv — A's TSV (3,294 rows incl. header)
- /tmp/claude-503/cfg-order-B-results.tsv — B's TSV (degenerate; all rows n_blocks=1, n_violations=0)
- /tmp/claude-503/cfg-order-A-rollups.py — rollup script
- /tmp/claude-503/cfg-order-A-time.txt — wall-clock log
- /tmp/claude/cfg-order-AB.diff — A vs B unified diff (6,589 lines)
- /tmp/claude/cfg-order-AB-mismatches.tsv — per-row mismatch table
- /tmp/claude/reconcile.py, /tmp/claude/make_diff.py — reconciliation scripts
- /tmp/claude-503/skeptic_verify.py — independent verifier used by Skeptic 1
- /tmp/claude-503/cfg_edge_tests/ — 11 edge-case fixtures from Skeptic 2

Verifier-semantics citations (Skeptic 3):
- /Users/htd/Documents/Strata-smack/Strata/Languages/Core/ProcedureEval.lean:92,160
- /Users/htd/Documents/Strata-smack/Strata/Languages/Core/StatementEval.lean:795,967,973
- /Users/htd/Documents/Strata-smack/Strata/DL/Imperative/CFGSemantics.lean:129
- /Users/htd/Documents/Strata-smack/Strata/Languages/Core/StatementSemantics.lean:335
- /Users/htd/Documents/Strata-smack/Strata/Transform/CoreSpecification.lean:61
- /Users/htd/Documents/Strata-smack/Strata/Languages/Core/ObligationExtraction.lean:102-114

Caveats (positional but off the SMT-verifier path):
- /Users/htd/Documents/Strata-smack/Strata/Languages/Core/DDMTransform/Translate.lean:1814-1817
- /Users/htd/Documents/Strata-smack/Strata/Languages/Core/ProcedureType.lean:85-118
- /Users/htd/Documents/Strata-smack/Strata/DL/Imperative/CFGToCProverGOTO.lean:65-69,80
