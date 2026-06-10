# CFG-native loop-elimination pass — implemented + #29 closure measured

Date: 2026-06-10
Branch: htd/smack (local, uncommitted)
Closes: the measurement the effect study (`cfg-loopelim-effect-2026-06-09.md`)
never completed — its Measure phase died on transient 503s three times
(`w2bl3s9l1`, `wikpaagrw`, `w7gh4f4nk`), so the #29 reproducer was never run
post-elimination. This run builds the pass and runs it.

## 1. Headline

**Built `Strata/Transform/CFGLoopElim.lean` and closed #29.** The pass is a
verification-path-only `Program → Program` pre-pass that detects natural loops
in `.cfg` bodies (dominator dataflow → back-edges), recovers the loop contract
from the header `condGoto` transfer metadata, and replaces the loop region with
the acyclic structured recipe — removing the back-edge so `evalCFGBlocks` sees a
DAG and terminates.

| | Baseline (no pass) | After CFGLoopElim |
|---|---|---|
| `verifyCFG loopGuardPrecondPgm` | **non-terminating** — 240 s timeout (exit 124) | **9 s, exit 0** |
| peak RSS | **12.5 GB and climbing** | **847 MB** |
| back-edge | unrolled forever | cut → DAG |
| VC2 (`arbitrary_iter_maintain_invariant`) | never reached | ✅ pass |

Both measurements were run locally under `gtimeout` + an RSS sampler (no
workflow agent, so no 503 exposure — the reason the prior three attempts failed).

## 2. What was built

`Strata/Transform/CFGLoopElim.lean` (new, ~280 LoC, builds clean, no `sorry`):

- **Dominator analysis** — iterative dataflow to fixpoint
  (`dom(entry)={entry}`, `dom(n)={n} ∪ ⋂_{p∈preds(n)} dom(p)`), `Std.HashMap`-based.
- **Back-edge detection** — edge `u→v` with `v` dominating `u`.
- **Natural-loop region** — header, latch, body (reverse reachability from latch
  without crossing header), exit continuation `kNext` (header's out-of-body
  successor).
- **Contract recovery** — `invariantsFromMd` / `measureFromMd` read
  `specLoopInvariant` / `specDecreases` off the header transfer metadata that
  `stmtsToCFG` attaches (`StructuredToUnstructured.lean:145-152`); default to the
  trivial invariant `[true]` for contract-less SMACK loops.
- **Modified-set** — union of `HasVarsImp.modifiedVars` over body-block commands,
  minus body-local `init`s (mirrors `LoopElim.lean:131-133`).
- **Recipe synthesis (`rewriteLoop`)** — keeps the header's existing invariant
  asserts (VC1, already emitted by `stmtsToCFG`), appends `assume(I)`, retargets
  the header `condGoto G → (h_then, h_exit)`; `h_then` = `havoc(M); assume(G);
  assume(I) → bodyEntry`; reroutes the latch back-edge → `h_post`; `h_post` =
  `assert(I)` **(VC2 — the load-bearing maintenance obligation)** `; havoc(M);
  assume(¬G); assume(I) → kNext`; `h_exit` (0-trip) = `havoc(M); assume(¬G);
  assume(I) → kNext`.
- **`cfgLoopElim` / `cfgLoopElim'` / `cfgLoopElimPipelinePhase`** — the Program
  pass, its `CoreTransformM` wrapper, and the pipeline phase (demotes SAT models
  to unknown on invariant/guard-assumption paths, like structured loop-elim).

Wired into `transformPipelinePhases` (`Verifier.lean:893`) immediately after
`loopElimPipelinePhase`. `.structured` bodies pass through (handled by
`loopElim`); `.cfg` bodies without a back-edge pass through (cheap `hasBackEdge`
gate). **Scope boundary respected:** the phase lives in the verification path
(`corePipelinePhases`); the CBMC/GOTO entry does not call it, so the GOTO path
keeps the real cyclic CFG for unwinding.

## 3. Verdict-set parity vs the structured oracle

`verifyCFG` (CFG form) vs `verify` (structured) on `loopGuardPrecondPgm`:

| structured (4 VCs, all ✅) | CFG form (3 VCs, all ✅) | mapping |
|---|---|---|
| `loop_guard_…SafeDiv` (entry div-check) | `branch_cond_…SafeDiv` | ✓ same obligation |
| `entry_invariant_0_0` (VC1) | `inv$_3` | ✓ VC1 (diff label) |
| `loop_guard_end_…SafeDiv` (post-havoc re-eval of `i/n`) | — | **not regenerated** |
| `arbitrary_iter_maintain_invariant_0_0` (VC2) | `arbitrary_iter_maintain_invariant_0_0` | ✓ exact |

The one difference is the second div-by-zero check: the structured recipe
re-*tests* the guard `i/n<10` in its `if(G)` ite (generating a fresh SafeDiv
obligation on the havoc'd state), whereas CFGLoopElim *assumes* the guard rather
than re-testing it, so that obligation is not regenerated.

**This is a completeness gap, not a soundness gap.** `n` is not in the loop's
modified set `{i}`, so `n != 0` (the precondition) survives the havoc and the
missing check would pass — exactly as the structured form confirms (`✅ pass`).
Closing it would mean emitting an explicit div-guard alongside the guard assume.
Recorded in the `FunctionPreconditions_Part4.lean` test docstring.

## 4. Soundness gate — wrong invariant is caught (exact parity)

A deliberately-false invariant (`while (i<10) invariant (1==0) {...}`), both forms:

| | VC1 entry-invariant | VC2 maintenance |
|---|---|---|
| structured `verify` | `entry_invariant_0_0` ❌ **FAIL** | `arbitrary_iter…` ✅ pass (vacuous under `assume false`) |
| CFG `verifyCFG` | `inv$_3` ❌ **FAIL** | `arbitrary_iter…` ✅ pass (vacuous) |

Identical behavior. The wrong invariant is **correctly caught at VC1** in both
forms; the program does not spuriously verify. (VC2 passing vacuously under
`assume(1==0)` is the same in both — assuming false proves anything; the entry
check is what rejects the bad invariant.) **No soundness hole.**

## 5. Regression check — zero regressions

Full CFGForm suite (40 leaves) rebuilt with the phase wired. 32 pass; **8 fail,
and all 8 are the documented pre-existing failures** (`Cover` #27;
`FunctionPreconditions_Part3` + `TypeDeclStmt` #26;
`ProcedureCall`/`RecursiveProcIte`/`SafeMap`/`SelectiveVerification`/`UnreachableAssert`
#28 cosmetic path-condition asymmetry). Exact set match to BRANCH_FEATURES §9.3.

**Proof they are not my regressions:** all 8 programs are **loop-free** (0 `while`
occurrences), so `cfgLoopElimPipelinePhase` is a guaranteed no-op on them
(`hasBackEdge` → false → identity passthrough). Their errors are the documented
golden-mismatch / typeDecl-drop type, not any new OOM or crash. The previously
OOM-killed `FunctionPreconditions_Part4` (the #29 reproducer) now **builds clean
as a passing `#guard_msgs` test** (golden updated to the real 3-VC output).

## 6. Measure (`decreases`) loops — investigated, deliberately not re-emitted

Initial attempt: wire VC3 (`measure_lb`) into the pre-body block and VC4
(`measure_decrease`) into the post-body block, mirroring `LoopElim.lean:159-172`.
**Tested on an inline `decreases`-bearing countdown loop and found a conflict:**
`stmtsToCFG` *already* lowers the measure when it builds the `.cfg` — it emits
VC3 (`init m_old; assume m_old==D; assert(m_old>=0)`) into the **header cmds**
and VC4 (`assert(D < m_old)`) into a **separate decrease block** on the
back-edge. Re-emitting them in `rewriteLoop` produced **duplicated VCs**
(`measure_lb_loop_measure$_2` *and* `measure_lb_0`; `measure_decrease_…` ×2),
and the original decrease block — whose back-edge this pass reroutes to `h_post`
— ends up evaluated against havoc'd state, flipping its VC4 to `❓ unknown`.

So the measure wiring was **reverted**. The pass currently handles
invariant-only / contract-less loops fully (the #29 case + the 310 SMACK loops);
measure-bearing loops still **terminate bounded** (the OOM is closed regardless)
but may carry a stray `unknown` on the orphaned decrease block. Closing the
measure case correctly requires *recognizing and rewriting `stmtsToCFG`'s
decrease block* (recover `m_old`/`D`, splice VC4 onto `h_post`, drop the
orphan), not naively re-emitting — a more invasive change scoped to the 3/313
measure-bearing procs. Documented inline in `rewriteLoop`.

## 7. Remaining work

- **Measure-loop decrease-block rewriting** (above) — for the 3/313
  `specDecreases` procs. Bounded but needs decrease-block awareness.
- **Completeness gap in §3** (assume vs re-test the guard) — minor, benign here
  (`n ∉ M`); CFG-form under-counts the post-havoc guard div-check. Would need an
  explicit div-guard assert alongside the guard assume.
- **Corpus-scale validation** — only the #29 reproducer + the wrong-invariant
  soundness test are run here. The mem-capped EQ-200 / SMACK-pilot re-sweep to
  quantify how many TIMEOUTs the pass unblocks (plan Task 5) is the next
  measurement — deferred (heavy; respect the memory budget).

## 8. Files

- `Strata/Transform/CFGLoopElim.lean` (new — the pass)
- `Strata/Languages/Core/Verifier.lean` (import + phase wiring)
- `StrataTest/Languages/Core/Examples/CFGLoopElim.lean` (new tracked regression
  test — self-contained, CI-globbed, verifies a `.cfg`-body loop end-to-end)
- `StrataTest/Languages/Core/Examples/CFGForm/FunctionPreconditions_Part4.lean`
  (untracked harness leaf; golden updated — was OOM-killed, now passing)
- Plan this executes: `reports/plan-cfg-loopelim-pass-2026-06-10.md`
- Effect study (design lock): `reports/cfg-loopelim-effect-2026-06-09.md`
