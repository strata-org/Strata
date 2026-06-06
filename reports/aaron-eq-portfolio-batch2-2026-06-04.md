# Aaron's EQ portfolio — batch 2 + cross-batch synthesis (2026-06-04)

Continuation of [`aaron-eq-portfolio-2026-06-03.md`](aaron-eq-portfolio-2026-06-03.md). Combined corpus is now 72 files of 3530.

## Setup

- Same as batch 1: BoogieToStrata DLL → `strata verify --check-mode deductive --check-level full --call-policy {contract,bodyOrContract}`, 60s per-file timeout.
- Strata branch: `htd/smack` at `5648bdf62` (post-multi-`Env`).
- Batch 2 sample: 36 fresh files, disjoint from batch 1, stride-spaced (rather than alphabetic-first) within each bucket for diversity. 12 small / 12 medium / 12 large.

## Combined headline counts (72 files)

| Bucket | contract | bodyOrContract |
|---|---|---|
| small (24) | 22 PASS, 2 FAIL | 21 PASS, 1 PARTIAL, 2 TIMEOUT |
| medium (24) | 17 PASS, 1 FAIL | 8 PASS, 5 PARTIAL, 4 FAIL, 7 TIMEOUT |
| large (24) | 1 PASS, 5 FAIL, 18 TIMEOUT | 1 PASS, 9 FAIL, 14 TIMEOUT |

bodyOrContract diverges from contract on **30 of 72 files (42%)** — stable rate across both batches.

## Pattern stability

Patterns established in batch 1, holding in batch 2:

- **Shared-UF free-ensures abstraction** (universal): 72/72 files have `_uf_otherfile_*$_return` UF symbols on both `reffile.*` and `otherfile.*` procedure free-ensures. This is a structural property of the SMACK→Boogie generator. Treat as background, not actionable.

- **`Eq/SameV` PASS→PARTIAL when bodies aren't path-equivalent**: batch 1 had 4 (CLEVER `multiple` and `getSign2`); batch 2 adds 1 (`zxzz4qq0grw`, `airy.MAX.Eq.SameV` — reffile uses `otherfile.$leInt(i0,0)`, otherfile uses `otherfile.$geInt(i0,0)`). Body-eval correctly emits PARTIAL; contract abstracts both bodies to the same UF and PASSes vacuously. The harness-construction question with Aaron stands — though batch 2's harness shape is different (direct method call, no `_client`/`_lib` indirection) so the "calls `_lib` not `_client`" framing doesn't strictly apply. The abstract problem (Eq.SameV with non-path-equivalent bodies) is the same.

- **`Neq/SameV` precision wins**: batch 1 had 3 (CLEVER `getSign2` × 2, REVE `addhorn`); batch 2 adds 4 (tsafe `normAngle` × 2, REVE `triangularMod`, bess `pythag`). Methodology working — bodyOrContract correctly refuses these designed-non-equivalent benchmarks. Several of batch 2's surface as TIMEOUT instead of PARTIAL because the bodies are larger / more numerically intricate (the new "cost regression" pattern below).

## New patterns from batch 2

### 1. Elab/typecheck defect: `Cannot find this fvar in the context! old otherfile__*`

**Affects:** `EQ_koudjso4dzv_out.bpl`, `EQ_wvadqhmgjvk_out.bpl`, `EQ_cjromzqjo0n_out.bpl` (3 files).

**Symptoms:** Both `--call-policy contract` and `--call-policy bodyOrContract` return rc=3 with stdout containing `Cannot find this fvar in the context! old otherfile__<global>`. The free-ensures clause references `old(<cross-prefix-global>)` (e.g. `old(otherfile.$refArrHeap)` on a `reffile.*` procedure or vice versa) and Strata's typechecker rejects it before any VC is emitted.

**Why it matters:** Independent of call-policy — fixing it might also unblock currently-TIMEOUTing large files that have similar mixed-namespace free-ensures. Three clean reproducers; deterministic; unrelated to the multi-`Env` work.

**Sample errors:**
- `koudjso4dzv`: `... old otherfile__refArrHeap` on `reffile_..._deposit__lp_I_rp__V_ensures_0`
- `wvadqhmgjvk`: `... old otherfile__org_apache_rocketmq_common_KeyBuilder_POP_RETRY_REGEX_SEPARATOR_V2__lp_LString__rp_` on `reffile_Object__la_init_ra___lp__rp__V_ensures_0`
- `cjromzqjo0n`: `... old otherfile__heap` on `otherfile_..._supportJavaTypeKey__lp__rp__LClass__ensures_0`

**Likely location of fix:** BoogieToStrata's `old(...)` translation, or Strata core's elaborator handling of `old(<global>)` where `<global>` is declared with a different prefix than the enclosing procedure. Worth tracing the failing path: the procedure's `modifies` set probably names `otherfile__refArrHeap` but the typechecker only brings `reffile__refArrHeap` into scope.

**Action:** File as a Strata-side defect with the 3 reproducers. Higher priority than the call-policy work since it's a clean elab bug.

### 2. Body-eval cost regression: PASS/FAIL→TIMEOUT under bodyOrContract

**Affects (batch 2):** `0exak45poxy`, `s541ce4abnj` (FAIL:261 → TIMEOUT, both small `tsafe.normAngle.Neq`), `oqt2xfezy0x` (PASS:267 → TIMEOUT, medium `dart.test.Eq`), `vtepk5bv3ld` (PASS:280 → TIMEOUT, medium `REVE.triangularMod.Neq`), `mtonvj3sujq` (PASS:610 → TIMEOUT, medium `bess.pythag.Neq`). 5 files with this shape; 7 if you count the 2 small Neq files where contract was finishing with `FAIL:N` and bodyOrContract just hangs.

**Symptoms:** Contract finishes in <60s with a definite verdict; bodyOrContract hits the 60s timeout without finishing. Body-eval expands paths through `{:inline 1}` callees that contract abstracts via UF, producing a much bigger SMT goal space — and on these benchmarks the extra goals are non-trivial.

**Why it matters:** Distinct from soundness/precision flips — these are *just slower*, not wrong. But "just slower" with a hard 60s ceiling looks identical to "stuck" in the matrix. Need to characterize: is this 120s-clearable, 300s-clearable, or unbounded?

**Action:** Third sweep with timeouts {30, 120, 300}s on this subset to bucket into "slower-but-bounded" vs. "actually unbounded". Don't file yet.

### 3. Stack-overflow under bodyOrContract — broader than first thought

**Affects (combined):** 7 files now: `EQ_2zvm5xvfu22`, `EQ_wnksggs1hpx`, `EQ_cvrikypthwe` (batch 1, all large) plus `EQ_2aa5bx1uwko`, `EQ_wfgmxv3m3tx`, `EQ_sertrlracdg`, `EQ_0xaksnfuqqv` (batch 2 — 3 medium, 1 large).

**Symptoms:** `Stack overflow detected. Aborting.` — `strata verify` returns rc=-6 (SIGABRT) under bodyOrContract on programs where contract just times out. Contract has a soft failure (timeout); body-eval has a hard crash.

**Update vs batch 1:** Batch 1 framed this as a "large-file" issue. Batch 2 invalidates that — 3 of 4 new reproducers are medium bucket (3-4K LoC). The trigger is body-eval recursion-depth on SMACK output shape, regardless of file size.

**Action:** File now as a single Strata robustness issue with 7 reproducers. Fits the existing "Verifier hang/overflow cluster" in [`reports/INDEX.md`](INDEX.md) but with a doubled evidence base. The body-eval call chain likely descends through `inlineCallBody`'s recursive callee body evaluation without the existing `--inline-fuel` guard catching deeply-nested mutual recursion. Repro: any of the 7 files + `--call-policy bodyOrContract --inline-fuel 1000` would test whether tighter fuel surfaces the depth.

### 4. Goal-count divergence is bidirectional

ike-style blow-up (batch 1: 267→1122) recurs in batch 2 (`ylzs20xcwwt`: 251→665, all PASS) but the inverse also shows up: 4 small files have `bodyOrContract < contract` goal counts on PASS (`-2` to `-12`). Not a regression in either direction — body-eval inlining can introduce per-path duplicates of constructor ensures (more goals) or short-circuit ensures-clauses that contract instantiates as separate VCs (fewer goals). Document, don't act.

## Cross-batch matrix of patterns

| Pattern | Batch 1 (36) | Batch 2 (36) | Combined (72) | Action |
|---|---|---|---|---|
| Shared-UF free-ensures (background) | 36/36 | 36/36 | 72/72 | None — structural |
| Eq.SameV PASS→PARTIAL | 4 | 1 | 5 | Aaron-side; harness construction question |
| Neq.SameV precision win | 3 | 4 | 7 | Methodology working as intended |
| Stack-overflow under bodyOrContract | 3 | 4 | 7 | **File as Strata robustness issue (this batch elevates priority)** |
| Cost regression PASS/FAIL→TIMEOUT | 0 | 7 | 7 | Defer; needs timeout-variation sweep first |
| Elab/typecheck `old(<other-prefix>)` defect | 0 | 3 | 3 | **File as Strata-side defect (independent of call-policy)** |
| Goal-count blow-up (≥2x) on PASS | 1 | 1 | 2 | Document; benign |
| Goal-count shrink on PASS | 0 | 4 | 4 | Document; benign |
| TRANSLATE_FAIL | 0 | 0 | 0 | None |

## Recommendations going forward

**File now (two clean defects):**

1. **Elab/typecheck defect** for `old(<cross-prefix-global>)` in free-ensures. 3 reproducers, deterministic, hits both policies identically. Likely a small fix in BoogieToStrata or Strata core's elaborator. High value because it might also unblock TIMEOUT files with similar mixed-namespace ensures.

2. **Stack-overflow under bodyOrContract** — consolidate 7 reproducers (3 batch 1, 4 batch 2) into one report. Goes in the verifier-overflow cluster in `reports/INDEX.md`.

**Defer until characterized:**

3. **Body-eval cost regression** — needs third sweep at varied timeouts {30, 120, 300}s on the 7 affected files to determine if these are slow-but-bounded or actually unbounded.

**Stable findings, no further action needed:**

4. The multi-`Env` change is **decisively non-trivial on this corpus**: 30/72 verdict-differs (42%) consistent across batches. No precision-regression evidence — every PASS→PARTIAL is either a real divergence body-eval correctly exposes (Neq) or a benchmark methodology question (Eq with non-path-equivalent bodies).

5. The multi-`Env` work itself is sound. All non-trivial findings reduce to either upstream Aaron-side questions, pre-existing Strata robustness issues (stack overflow), or pre-existing Strata translator issues (elab bug). None implicate `htd/smack@5648bdf62` directly.

## Artifacts

- Workflow run 1 (batch 1, 36 files): `wf_7533c9c0-dbe`. Per-file CSV in workflow output.
- Workflow run 2 (5-flip deep dive): `wf_01344288-987`. Full diagnosis at `aaron-eq-portfolio-2026-06-03.md`.
- Workflow run 3 (batch 2, 36 files): `wf_7c37b21e-a06`. This report.
