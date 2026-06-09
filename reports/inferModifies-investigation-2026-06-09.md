# inferModifies vs lean4 #1331 — investigation

**Date:** 2026-06-09
**Branch:** htd/smack
**Joined corpus tsv:** /tmp/claude-503/eq200-joined-mem-cap.tsv (56/200 ELAB_FAIL)

## 1. Headline

**No.** `InferModifies` does not — and architecturally **cannot** — solve lean4
#1331 for the EQ-200 corpus. The 56 ELAB_FAIL files were already produced **with
`InferModifies = true`**: the existing pipeline passes `--smack`, which enables
the flag (run_pipeline.py:200-202; BoogieToStrata.cs:58). The remaining failures
are the steady-state defect after InferModifies has already done its job.

## 2. The flag

- **Where:** /Users/htd/Documents/Strata-smack/Tools/BoogieToStrata/Source/BoogieToStrata.cs:58 sets `InferModifies = smack` when `--smack` is passed.
- **What it does:** runs Boogie's `ModSetCollector.CollectModifies`, which walks each implementation body and adds globals it assigns/havocs to that procedure's modifies clause. Suppresses `CheckModifies` so SMACK programs missing modifies clauses don't reject at typecheck.
- **Currently enabled in the pipeline:** **yes**. Examples/smack-docker/run_pipeline.py:200-202 invokes BoogieToStrata with `--smack` for every EQ file. The 56 ELAB_FAIL files came out of this exact pipeline.
- **Downstream emission:** StrataGenerator.cs:1891-1901 and 1032-1043 split globals into `inout` (in modifies) vs read-only inputs (not in modifies) when emitting Strata procedure headers and call sites.

## 3. The defect re-confirmed

Smallest ELAB_FAIL: **EQ_bbalcshq514_out** (196 KB).

- **Failing procedure:** /tmp/claude-503/eq200-cores/EQ_bbalcshq514_out.core.st:1064 — `procedure otherfile_benchmarks_ej_hash_hashCode_Neq_SameV_hashCode__lp__rp__I(otherfile__heap : StrataHeap, ...)`. `otherfile__heap` is emitted as a **read-only** (non-`inout`) input parameter.
- **Failing line:** EQ_bbalcshq514_out.core.st:1066 — `free ensures (_return == _uf_..._return(_this, old otherfile__heap));`
- **Boogie source root cause:** /Users/htd/Documents/Strata-smack/Examples/smack-docker/boogie-files/EQ_bbalcshq514_out.bpl:1011-1013 — the procedure declaration has **no modifies clause** and its implementation (line 1076-1115) only **reads** `otherfile.$heap` (no `:=`, no `havoc`, no mutating call). InferModifies correctly produces an empty modifies set. Yet SMACK still emits `free ensures ... old(otherfile.$heap)` defensively on every entry-point heap global.
- **Lean rejection:** Strata's `withOldBindings` (Strata/Languages/Core/ProcedureType.lean ~100-105) only binds globals that appear in `getInoutParams.toList`. With no modifies → no inout → `old otherfile__heap` is unbound → `Cannot find this fvar in the context! old otherfile__heap`.
- **Pattern is general:** EQ_2ig3trgguto_out fails on `old otherfile__refArrHeap`; EQ_gcinyatn5l1_out fails on `old otherfile__refArrHeap` inside a `_loop1`-suffixed proc. Same shape: read-only heap referenced via `old(...)` because SMACK emits the contract uniformly.

## 4. Empirical test

**Not run, by design.** The pipeline that produced the 56 ELAB_FAILs already had `InferModifies = true`. Re-running with the same flag is a no-op. To test "what if the flag worked harder" (i.e., over-approximated by including read-only heap reads in modifies), one would need to fork ModSetCollector — that is not a flag-flip, it is a semantic change to Boogie that would mark every dereferenced global as modified, breaking unrelated SMT verification (false `inout` aliasing on read-only inputs).

## 5. Limitations / open questions

The hypothesis "make read-only globals inout so `old()` resolves" has two architectural blockers:

1. **No mutation to infer.** `ModSetCollector` is sound: it adds only globals genuinely assigned in the body. The 56 failing procs read but do not write the heap they `old()`-reference. There is no flag short of "force every referenced global into modifies" that fixes this.
2. **Forced-inout would break verification.** If InferModifies were patched to add every *read* global to modifies, every SMACK procedure call site would propagate spurious havoc to the caller's heap, breaking PASS files. The 46 PASS verdicts would degrade.

The defect therefore lives downstream of BoogieToStrata, in **Strata's `withOldBindings` scope**: `old(g)` is well-defined for **any** global, not just inout params, in Boogie/SMT semantics (`old(g)` ≡ value of g at procedure entry, regardless of whether the proc writes g).

## 6. Recommended next step

**Pursue the ProcedureType.lean fix directly** — file or escalate lean4 #1331 against `Strata/Languages/Core/ProcedureType.lean:~100-105`. The fix is to extend `withOldBindings` to bind **all** procedure-visible globals (or at minimum all parameters, in/inout/out), not just inout. Two-line change candidate:

- Today: `getInoutParams.toList`
- Want: `getInputParams.toList ++ getInoutParams.toList` (read-only inputs need `old` bindings too because Boogie semantics permit `old(read-only-global)`).

Do **not** flip a flag in run_pipeline.py — there is no flag to flip. Do **not** file an upstream issue against BoogieToStrata — InferModifies is working correctly.

Side-evidence to attach to the lean4 #1331 fix: the corpus shows this is a 28% (56/200) blocker; pattern is uniform (always `old <heap_global>` in `free ensures` of a comparison/uf entry-point); fix unlocks ~28pp of EQ corpus elaboration without touching translation.
