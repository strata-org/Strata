# EQ-200 Qualitative Anomaly Analysis — 2026-06-06

Companion to `reports/eq-200-file-sweep-2026-06-06.md`. The mem-cap re-run produced four headline buckets (PASS=46, ELAB_FAIL=56, OTHER=9, TIMEOUT=89) on a quartile-stratified 200-file sample of the EQ corpus. This report is the qualitative drill-down: 8 parallel hunters worked one axis each, 4 skeptics independently challenged the load-bearing claims, and this synthesis captures the results.

---

## 1. Headline

- **The 56 ELAB_FAIL files are mechanically identical** — every one is the lean4 #1331 `Cannot find this fvar in the context! old <X>` pattern. Zero orthogonal errors hide in the bucket. (Confirmed independently by Skeptic 1 on 3 spot-checks.)
- **The 9 OTHER files are two clusters, one defect.** Five rc=2 files return Z3 `unknown` on `EQ_…_ensures_0` (residual incompleteness post-mbqi-strip); four rc=3 files hit a single previously-uncatalogued **SMT-emitter heap-vs-element type-confusion defect**. The same defect leaks into the TIMEOUT bucket (4 more files), giving true incidence **8/200 ≈ 4%**.
- **One TIMEOUT is misclassified.** `EQ_iwjr2x5ta4a_out` finished with "880 goals passed, 1 failed" + an SMT crash on a single obligation; rc=143 came from a post-completion SIGTERM. It belongs in OTHER. The mem-cap report's transition matrix has 14 off-diagonal cells but enumerates only 13 — this is the missing one.
- **Hunter 5's "host-jitter / RSS pressure" framing of cross-run transitions is wrong.** The same `strata` binary (mtime Jun 6 12:22) drove both runs; v6 had a wrapper-side **premature-SIGTERM bug** producing 34 rc=143 rows with elapsed < 60 s. The 5 cross-bucket flips are explained by that wrapper bug (4 files) plus tighter 20 s vs 60 s wall (2 files: `mcuatvyb42y`, `md0vcihaenm`).
- **The Q4 ELAB_FAIL "dip" (Q3=46% → Q4=22%) is partly real and partly artifact.** Hunter 4 argued 100% wall-clock-masking; Skeptic 3 found density inversions in the size-overlap zone refuting pure-(a). Best estimate: ~17 of 39 Q4 TIMEOUTs are latent ELAB_FAILs (high-density large-size cluster); the rest hang on a non-elab slow path. Range for projection: **Q4 elab-blocker rate ≈ 22% – 56%**, not 100%.

---

## 2. Setup

- **Data**: `/tmp/claude-503/eq200-joined-mem-cap.tsv` (200 rows × 13 cols), `/tmp/claude-503/eq200-verify-stdout/` and `/tmp/claude-503/eq200-verify-stderr/` (per-file driver output), `/tmp/claude-503/eq200-cores/` (per-file `.core.st`).
- **Sample composition**: quartile-stratified by `.bpl` byte size, 50 files per quartile (Q1 ≤ 232 KB, Q2 ≈ 232 – 530 KB, Q3 ≈ 530 KB – 2.0 MB, Q4 > 2.0 MB up to 7.3 MB). Each quartile has equal mass relative to the full 2 929-file EQ corpus.
- **Method**: 8 hunters dispatched in parallel, each owning one axis (ELAB composition, OTHER bimodality, Q1 non-PASSes, Q4 ELAB dip, transitions, elapsed distribution, stderr patterns, size outliers). 4 skeptics dispatched after with the same data + the relevant hunter's findings, asked to refute or corroborate. This synthesis merges them.
- **Same binary, two runs**: `/Users/htd/Documents/Strata-smack/.lake/build/bin/strata` (mtime Jun 6 12:22) drove both v6 (60 s wall) and the mem-cap re-run (20 s wall, gtimeout, ulimit). The wrapper differs; the binary does not.

---

## 3. Anomaly catalog

| # | Name | Evidence | Scope (of 200) | Open question | Action |
|--:|------|----------|---------------:|---------------|--------|
| A1 | lean4 #1331 cross-prefix `old <global>` | All 56 ELAB_FAIL `.out` files share a single fault line; 36 heap-family + 20 static-field family | 56 (28 %) | Whether full-corpus rate is 27–32 % (95 % CI ≈ ±60 files of ~820) | Already tracked upstream; widen-modifies fix would close all 56 |
| A2 | SMT-emitter heap-vs-element type confusion (NEW) | 8 stderrs share `argument type is not the type of the function's argument type` or `Subexpressions must have the same type`; offending operand is always `…ArrHeap@N` (`Map StrataRef (Map BV32 τ)`) where `StrataRef` is expected | 8 (4 %): 4 PARTIAL/rc=3 + 4 TIMEOUT-leakage | Single emitter site or two? Spot-check suggests one (heap-update + null-equality are surface variants) | **File one upstream issue.** Smallest reproducer: `EQ_1ncwryiy1qx_out` (`(= shortArrHeap@30 otherfile__null)`) |
| A3 | rc=2 solver-`unknown` on EQ post-condition | 5 files; each shows hundreds-to-thousands ✅ + exactly 1 ❓ on `EQ_…_ensures_0`; floats and nonlinear int equivalences | 5 (2.5 %) | Whether per-goal tactic tuning would close any | Tracking ticket only; **not** a regression of mbqi-strip |
| A4 | One verdict misclassification | `EQ_iwjr2x5ta4a_out`: stdout = "Finished with 880 goals passed, 1 failed" + SMT-crash stderr, rc=143 elapsed=2 s — bucket=TIMEOUT, true=OTHER | 1 | Driver heuristic (rc=143 → TIMEOUT) | Either re-bucket post-hoc or special-case rc=143 with non-empty stdout-final-line |
| A5 | v6 wrapper premature-SIGTERM bug | 34 v6 rows have rc=143 with elapsed < 60 s wall; mc rerun (clean wrapper) finishes 5 of them in non-TIMEOUT buckets | 34 v6 rows; 5 cross-bucket flips | Why v6 wrapper killed processes early (peer-OOM cascade?) | Disclose in any v6-vs-mc comparison; don't ascribe flips to "host jitter" |
| A6 | Q4 ELAB_FAIL dip is mixed-cause | Q4 ELAB rate 22 % vs Q3 46 %; size-overlap zone shows TIMEOUTs are 40 % LESS old-hit-dense than ELAB_FAILs of the same size | Q4 TIMEOUTs n=39 | Is the low-density TIMEOUT cluster stuck in translator, solver setup, or another front-end stage? | Run 60–180 s wall on Q4 low-density TIMEOUTs only; reclassify by outcome |
| A7 | Pre-solver elaboration TIMEOUT (Q1) | 4 Q1 TIMEOUTs (227–266 KB) emit zero stdout in 20 s; axiom/quantifier density 1.5–4× PASS peers | 4 | Same root cause as A6 low-density Q4 TIMEOUTs? | Same 60–180 s validator covers both |
| A8 | OTHER cluster at 11–13 s | 3 OTHER files form a distinct elapsed mode (11/12/13 s), separate from ELAB tail (1–4 s) and TIMEOUT wall (20–22 s) | 3 | Is this a Boogie-side OOM/abort signature? | Low priority; flag for next sweep |

---

## 4. Per-axis findings

### Axis 1 — ELAB composition
**Hunter 1**: All 56 ELAB_FAIL files match the `Cannot find this fvar in the context! old <X>` pattern; zero anomalies. Histogram of fvar stems: 27 × `otherfile__heap`, 9 × `otherfile__refArrHeap`, 7 × RocketMQ static, plus 13 long-tail Java static fields. **Skeptic 1**: Confirmed; verified that for 3 non-heap exemplars the missing fvar is a plain (non-`inout`) parameter, exactly the #1331 condition. The kind of global is irrelevant — only `inout`-ness gates fvar visibility under `old`. One mechanism, 56 instances. Sub-class observation: 36 heap-family + 20 static-field family — both fall to the same widen-modifies fix, but any upstream translator-side fix needs to handle both uniformly.

### Axis 2 — OTHER bimodality
**Hunter 2**: rc=2 cluster (5 files) returns Z3 `unknown` on the EQ post-condition; rc=3 cluster (4 files) hits an SMT-emitter heap-typing parse error. **Skeptic 2** corrected two attribution errors: (i) `EQ_3gff5oopjfl_out` belongs in PARTIAL/rc=3 (not TIMEOUT, as Hunter 2 logged), and (ii) `EQ_iwjr2x5ta4a_out` belongs in TIMEOUT/rc=143 (not the rc=3 cluster). Net: still **8 files / 4 distinct benchmarks** for the SMT bug (raytrace.Sphere, raytrace.Surface, alibaba.Excel, CLEVER_divide), 4 PARTIAL + 4 TIMEOUT-leakage. The hypothesised "two sub-classes" inside rc=3 are **grammatical, not semantic** — both error templates originate at one emitter site producing a heap-typed term where `StrataRef` is required. Smallest reproducer: `EQ_1ncwryiy1qx_out` (the comparison-with-null variant is most directly diagnostic, ~890-line stdout). The rc=2 unknowns are confirmed residual incompleteness (`Strata/Languages/Core/Verifier.lean:181-183` has the mbqi/auto_config setOption pins commented out on htd/smack ≥ 528fec0f2); not a regression.

### Axis 3 — Q1 non-PASSes
**Hunter 3**: 17 of 50 Q1 files don't PASS; broken down: 8 × #1331 ELAB_FAIL, 4 × Z3-unknown OTHER, 1 × SMT heap-shape parse error (`EQ_iwjr2x5ta4a_out`), 4 × elaboration TIMEOUT (zero stdout in 20 s). Two patterns first surface here: (i) **pre-solver elaboration TIMEOUT** — the 4 Q1 TIMEOUTs hang during frontend elaboration with axiom/assert/quantifier density 1.5–4× PASS peers, despite small `.bpl` byte size; disk size is a poor proxy for elaboration cost. (ii) **SMT heap-shape parse error** as a single Q1 occurrence (Hunter 2 then catalogued the full bucket). All 8 ELAB_FAILs are textbook #1331 — small Java-SMACK files happily exhibit it; size doesn't immunize.

### Axis 4 — Q4 ELAB dip
**Hunter 4**: Q4 ELAB_FAIL rate (22 %) is lower than Q3 (46 %), but Q4 TIMEOUTs all have stdout=0/stderr=0 in 20 s. Hunter 4 argued this is wall-clock-masking and recommended treating 100 % of Q4 TIMEOUTs as latent ELAB_FAIL. **Skeptic 3** refuted pure-(a):
- 22 of 39 Q4 TIMEOUTs are *smaller* than the largest ELAB_FAIL (2.93 MB) and would have elab-failed in 1–7 s like their same-size peers if (a) were dominant. They didn't.
- In the size-overlap zone, Q4 ELAB_FAILs are denser (mean 13 929 old-hits) than Q4 TIMEOUTs (mean 8 439 old-hits) — **40 % less dense, the inverse of (a)'s prediction**.
- Concrete counter-examples: `EQ_25x1ux2e1e4_out`, `EQ_dbt2jctmfup_out`, `EQ_dubxrqzdaln_out` (all 1.4–1.9 MB, 1130 old-hits) TIMEOUT at 20 s, while `EQ_5ieutjugp41_out` (1.53 MB, 1351 hits) ELAB_FAILs in 1 s.
- Same anomaly replicates in Q3 (`EQ_ctfgxavj3hd_out`, 621 KB / 740 hits / 20 s timeout vs `EQ_5crno1rwpko_out`, 677 KB / 5172 hits / 1 s elab-fail), so it's not Q4-specific.

Best-estimate posterior: **mixture (~80 %)** — ~17 high-density large-size files are latent ELAB_FAIL; ~15–20 low-density files are stuck on a different slow path (translator, solver setup, or other front-end stage). For the projection: report a **range** (Q4 elab-blocker rate 22 % – 56 %), not a point.

### Axis 5 — Transitions
**Hunter 5**: 14 off-diagonal cells in the v6 → mc transition matrix (1 TIMEOUT→PASS, 8 PARTIAL→OTHER, 1 PARTIAL→TIMEOUT, 2 ELAB→TIMEOUT, 1 TIMEOUT→ELAB, **1 unreported TIMEOUT→OTHER for `EQ_iwjr2x5ta4a_out`**). Hunter 5 hypothesised "different binary or cached result" for the rare flips. **Skeptic 4** refuted this:
- Same `strata` binary (mtime Jun 6 12:22) on both runs.
- v6 has 34 rc=143 records with elapsed < 60 s — premature-SIGTERMs misbucketed as TIMEOUT.
- The "rescued" PASS (`EQ_m4hnurfgtn4_out`) shows mc stdout "All 4083 goals passed" in 4 s rc=0; v6 SIGTERM'd it at 1 s. Real PASS, v6 wrapper bug.
- The 2 ELAB→TIMEOUT (`mcuatvyb42y`, `md0vcihaenm`) are **wall-budget tightening** (24 s in v6 → > 20 s wall in mc).
- The 8 PARTIAL→OTHER are bucket-rename only (mc folds rc∈{2,3} into OTHER); spot-checked `h44suj0j4uo` (4577 ✅ + 1 ❓) and `1ncwryiy1qx` (1760 ✅ + 1 ❓) — identical PARTIAL behaviour.
- **0 PASS regressions**: v6=45 PASS → mc=46 PASS (+1 rescue).

### Axis 6 — Elapsed distribution
**Hunter 6**: True structure is **5 modes**, not the report's 3:
1. 0 s instant (n=32, mostly Q1 PASS+ELAB).
2. **1 s spike (n=44, dominated by ELAB_FAIL)** — the report's "1–15 s" band is really a 1 s pile-up.
3. 2–4 s shoulder (n=23).
4. 6–15 s ELAB tail + 11–13 s OTHER cluster (n=11, anomaly A8).
5. 20–22 s timeout wall (n=89, 73 at exactly 20 s — sharp wall, no leak before 20 s).

PASS files cluster at 0–2 s with a thin tail to 4 s; **none beyond 4 s**. The "1–15 s middle band" the report describes is essentially a parsing-failure tail, not a verification-effort distribution. ELAB_FAIL owns 25 of 44 files at 1 s.

### Axis 7 — Stderr patterns
**Hunter 7**: 192 of 200 `.err` files are empty (verifier writes diagnostics to stdout, not stderr). The 8 non-empty stderrs are all the SMT heap-vs-element type-confusion defect (A2). Cross-cutting regression check: **0 hits** on `stack overflow`, `Symbol 'e-NN'`, `panic`, `Z3 returned`, `cvc5 returned` — the e-15 fix held; no SO escape; no Lean-internal escapes. Verdict-classifier audit found 1 firm misclassification (A4: `EQ_iwjr2x5ta4a_out`) plus 1 soft case (`EQ_m5zcwjuov4o_out` has Cannot-find-fvar in stdout but exit=143; ELAB_FAIL would fit better than TIMEOUT) and 2 ELAB_FAIL files with empty stdout/stderr (`mcuatvyb42y`, `md0vcihaenm`) classified on rc=3 alone — bucket plausible but unverified. Net classifier noise ≤ 2.5 %.

### Axis 8 — Size outliers
**Hunter 8**: PASS-rate-by-quartile decay misleading; **size is necessary but not sufficient**. Largest PASS = `EQ_m4hnurfgtn4_out` at 590 KB (Q3, lone Q3 PASS). Smallest non-PASS = `EQ_zxzz4qq0grw_out` at 187 KB (Q1, smaller than 5 PASS files). PASS rate by 100 KB bucket: 100–200 KB → 81.5 %, 200–300 → 44.4 %, 300–400 → 21.1 %, 400–500 → 13.3 %, 500–600 → **20.0 % bump**, **≥600 KB → 0 %**. Hard cutoff at 600 KB (76 / 76 fail). Expansion ratio (`.boogie.st` / `.bpl`) is 1.00 ± 0.04 across both PASS and TIMEOUT — not a distinguisher. The Q1 non-PASS verdict mix (8 ELAB / 5 OTHER / 4 TIMEOUT) is governed by **content patterns** (cross-prefix `old`), not size; Q4's mix is dominated by size pressure.

---

## 5. Validated headline numbers

| Bucket | Mem-cap report | Post drill-down | Net |
|---|---:|---:|---|
| PASS | 46 | 46 | unchanged |
| ELAB_FAIL | 56 | 56 (or 57 if `m5zcwjuov4o` re-bucketed) | ±1 soft |
| OTHER | 9 | 9 (or 10 if `iwjr2x5ta4a` re-bucketed; firm) | +1 firm |
| TIMEOUT | 89 | 88–89 | −1 firm or −2 soft |

The **bucket-level numbers hold up** with at most one firm re-bucket (`iwjr2x5ta4a` TIMEOUT→OTHER). Headline pass-rate (23 %) and ELAB_FAIL-rate (28 %) are unchanged.

The **lean4 #1331 leverage projection** in the report ("~820 files corpus-wide") is a sound point estimate but has a 95 % CI of roughly ±60 files (Q3=46 % vs Q1=16 % drives wide variance). For the Q4-specific ELAB_FAIL projection: **22 % is a lower bound, 56 % is an upper bound** under the mixture model from Skeptic 3; the report's framing of a clean Q4 dip should be replaced with the range.

---

## 6. Newly-surfaced patterns

1. **SMT-emitter heap-vs-element type confusion (A2)** — uncatalogued before this drill-down. 8 / 200 ≈ 4 % incidence. Single emitter site, two surface error guises. Crosses bucket boundaries (4 PARTIAL + 4 TIMEOUT). **Fileable.**
2. **Pre-solver elaboration TIMEOUT (A7 / part of A6)** — small files (sometimes < 1.5 MB) that hang during frontend elaboration. Density-driven, not size-driven. Distinct from #1331 (that one fails fast; this hangs). Validator: 60–180 s wall on Q1+Q3+Q4 low-density TIMEOUTs. **Tracking ticket.**
3. **OTHER cluster at 11–13 s (A8)** — 3 files form a distinct elapsed mode. Looks like a Boogie-side OOM or abort signature. Low priority.
4. **v6 wrapper premature-SIGTERM bug (A5)** — 34 v6 rows. Doesn't affect mc rerun. Disclose in any v6-vs-mc comparison.

---

## 7. What the data refutes

- **"All Q4 TIMEOUTs are latent ELAB_FAILs."** Refuted by Skeptic 3's density-inversion analysis. Best estimate: 17 of 39 are latent ELAB_FAIL; the rest are a separate slow path.
- **"v6 → mc transitions are host jitter / RSS pressure."** Refuted by Skeptic 4 — same binary, v6 wrapper-side premature-SIGTERM bug.
- **"Expansion ratio (`.boogie.st` / `.bpl`) explains exceptional PASSes."** Refuted by Hunter 8 — ratios cluster tightly at 1.00 ± 0.04 across all verdicts.
- **"PASS-rate decays smoothly with size."** Refuted — actual shape is bimodal-by-content-pattern in Q1/Q2, then a step function near 600 KB. Smooth-decay framing is correct only after content failures are excluded.
- **"Stderr is the diagnostic channel for ELAB_FAIL."** Refuted — diagnostics live in stdout; `.err` files are empty for all 56 ELAB_FAILs (only the 8 SMT-crash files have non-empty stderr).
- **"OTHER bucket is a single homogeneous group."** Refuted — bimodal (rc=2 unknowns + rc=3 SMT crashes), and the report's table mis-attributed `iwjr2x5ta4a` and `3gff5oopjfl`.

---

## 8. What's ready for upstream filing

1. **SMT-emitter heap-vs-element type confusion** (A2). One issue.
   - Title: *"SMT emitter passes heap-typed `…ArrHeap@N` where `StrataRef` is expected (init-method ensures, ~4 % of CLEVER eq200)"*.
   - Smallest reproducer: `EQ_1ncwryiy1qx_out` — `(= shortArrHeap@30 otherfile__null)`, alibaba.Excel benchmark.
   - Severity: soundness-adjacent / silent miscompilation. The verifier reports OTHER/TIMEOUT to the user, not "wrong SMT generated" — false-PASS risk on adjacent paths.
   - Note in the issue: the same defect poisons 4 TIMEOUT-classified runs, so true incidence is 8/200 ≈ 4 %, not 4/200.
   - Use `/draft-issue` to write up.

2. **(Optional, lower priority)** Pre-solver elaboration TIMEOUT tracking ticket, after a longer-wall validator confirms it's a distinct path.

The rc=2 solver-`unknown` cluster is **not** a defect — leave as residual incompleteness or a tracking ticket only.

---

## 9. BACKLOG impact

Entries to flip / add in `reports/BACKLOG.md`:

- **ADD**: "SMT-emitter heap-vs-element type confusion — file upstream issue (A2). Reproducer EQ_1ncwryiy1qx_out. Incidence 8/200 ≈ 4 %, soundness-adjacent."
- **ADD**: "Q4 TIMEOUT cluster — split into latent-ELAB-FAIL (~17 files) vs non-elab-slow-path (~15–20 files) via 60–180 s wall validator on low-density Q4 TIMEOUTs."
- **ADD**: "v6 driver wrapper premature-SIGTERM bug — disclose in v6-vs-mc comparisons; 34 affected rows; not host jitter."
- **FLIP**: "Q4 ELAB_FAIL dip is real" → "Q4 ELAB_FAIL rate is 22 %–56 %; the dip is a mixture of wall-clock-masking and a non-elab slow path."
- **FLIP**: "OTHER bucket is mostly residual incompleteness" → "OTHER bucket = 5 residual-incompleteness + 4 SMT-emitter defect; the defect leaks into TIMEOUT for 4 more files."
- **FLIP**: "TIMEOUT bucket is wall-clock pressure" → "TIMEOUT bucket = 1 firm misclassification (PARTIAL with SMT crash) + ~17 latent ELAB_FAIL + ~15–20 non-elab slow path + the genuine-large-file cluster."
- **NOTE**: lean4 #1331 leverage projection should carry a ±60-file CI band (point estimate ~820, range ~760–880).

---

## 10. Recommended next step

Run a **60–180 s wall validator on the low-density Q4 TIMEOUT cluster** (n ≈ 15–20 files: those with old-hits < 5 k *or* `.bpl` ≤ 2 MB). Outcome decides whether they're latent ELAB_FAIL (Hunter 4 right) or a distinct front-end slow path (Skeptic 3 right). In parallel, **file the SMT-emitter heap-vs-element type-confusion issue** (A2) using `EQ_1ncwryiy1qx_out` as the reproducer — that one is ready now.

---

## Appendix: file references

- `/Users/htd/Documents/Strata-smack/reports/eq-200-file-sweep-2026-06-06.md` — companion sweep report.
- `/tmp/claude-503/eq200-joined-mem-cap.tsv` — joined verdict + size + elapsed table.
- `/tmp/claude-503/eq200-verify-stdout/` — per-file driver stdout (where ELAB diagnostics live).
- `/tmp/claude-503/eq200-verify-stderr/` — per-file driver stderr (only non-empty for the 8 SMT-crash files).
- `/tmp/claude-503/eq200-cores/` — per-file `.core.st` (proc-decl source for Skeptic 1's modifies-set inspection).
- `/Users/htd/Documents/Strata-smack/Strata/Languages/Core/Verifier.lean:181-183` — confirms mbqi/auto_config pins are commented out on htd/smack.
- `/Users/htd/Documents/Strata-smack/.lake/build/bin/strata` (mtime Jun 6 12:22) — same binary on both runs.
- Smallest A2 reproducer: `/tmp/claude-503/eq200-cores/EQ_1ncwryiy1qx_out.core.st` + `/tmp/claude-503/eq200-verify-stderr/EQ_1ncwryiy1qx_out.err`.
- Firm misclassification: `/tmp/claude-503/eq200-verify-stdout/EQ_iwjr2x5ta4a_out.out` ("Finished with 880 goals passed, 1 failed").
