# CFG loop-elim effect study

**Date:** 2026-06-09 · **Branch:** `htd/smack` @ c6f96e15c · **Tracks:** BRANCH_FEATURES.md §9.5 #29; BACKLOG *Investigations → CFG-eval memory profile #29*

A six-phase study (baseline → design → prototype → measure → skeptic → synthesis)
of the effect of a *would-be* CFG-level loop-elimination pass. The pass does not
exist today; this report establishes what building it would buy, which framing to
build, and a load-bearing soundness defect found in the prototype that any
implementation must avoid.

---

## 1. TL;DR

- **Is CFG loop-elim implemented today? No.** `Strata/Transform/LoopElim.lean:248-249`
  passes `.cfg` bodies through unchanged (`| .cfg _ => ((.proc proc md) :: acc, stats)`,
  comment: *"CFG bodies have no structured loops; pass through unchanged"*); the
  acyclic havoc-and-cut runs only on `.structured` bodies (LoopElim.lean:246). And
  `evalCFGBlocks` (ProcedureEval.lean:133-149) is a **fuel-only worklist** — no
  visited set, no fixpoint, no back-edge awareness — that forks both successors on a
  symbolic `condGoto` (ProcedureEval.lean:106-130, `:130`), so it literally unrolls
  reducible loop back-edges until fuel runs out. That is the #29 OOM root cause.
- **Effect if built (correctly).** A CFG-native loop-elim pre-pass that cuts the
  back-edge turns the cyclic CFG into a DAG, so `evalCFGBlocks` terminates in bounded
  steps. It is the only structural (not memory-bound-masking) fix for #29 and applies
  to **all 313 loop-bearing reducible procedures** in the three corpora.
- **Does it close #29?** **Partial / unproven by this study.** The back-edge removal
  is *structurally genuine* (verified: a prototype produces a DAG, `cfgHasBackEdge`
  toggles true→false), so the OOM cause is removed in principle. But the actual #29
  reproducer (`loopGuardPrecondPgm`) was **never run** — the Measure phase died on a
  transient API error, so neither OOM-closure, RSS delta, nor verdict-convergence was
  measured. Closure is plausible but unsubstantiated end-to-end.
- **Which framing?** **Framing A — a net-new CFG-native loop-elim pass.** Framing B
  (route through the structured `LoopElim` by reordering the pipeline) is ruled out:
  the corpus that actually OOMs is born as `.cfg` from the DDM/SMACK translator and
  never traverses `stmtsToCFG`, so there is no structured `while` to eliminate before
  lowering.
- **Soundness caveat (decisive).** The prototype's cut is sound for *termination* but
  **NOT sound for verification as built** — it drops the invariant-maintenance VC and
  would silently accept a program with a wrong invariant. A correct pass must replicate
  the *full* structured recipe, not merely redirect the back-edge. See §5.

---

## 2. Before-state: the gap and its population

### The gap (two confirmed root-cause sites)

1. **`LoopElim` does not touch CFG bodies.** `Strata/Transform/LoopElim.lean:248-249`
   — the `.cfg` arm is a pure passthrough. `loopElimPipelinePhase`
   (LoopElim.lean:263-270) therefore never rewrites a `.cfg` body. The structured arm
   (LoopElim.lean:246) runs `Block.removeLoopsM`, the acyclic havoc-and-assume-invariant
   recipe at LoopElim.lean:125-203.
2. **`evalCFGBlocks` is fuel-only.** `Strata/Languages/Core/ProcedureEval.lean:133-149`
   — its sole termination bound is `env.fuel` (`:139` `if env.fuel == 0`, `:145`
   `fuel := e.fuel - 1`). No visited set, no SCC/back-edge awareness, no
   `specLoopInvariant`/`specDecreases` consumption. `evalCFGStep`
   (ProcedureEval.lean:106-130) forks **both** successors on a symbolic `.condGoto`
   (`:130` `((lt, env_t) :: (lf, env_f) :: newActive, …)`), so a back-edge to the loop
   header is re-traversed each pseudo-iteration until fuel is exhausted — unbounded
   symbolic unrolling, one `Env` per iteration. (`Procedure.Body` is an inductive with
   `.structured`/`.cfg` variants at Procedure.lean:288-294; ProcedureEval.lean:237
   dispatches `.cfg` to `evalCFGBody`.)

The #29 OOM is therefore a *missing-loop-elim* problem, **not** an irreducibility
problem. This is htd/smack-only: `main` has no `.cfg` body shape and no
`evalCFGBlocks`.

### The population (census `wqlj6z95v`, 2026-06-09)

From `reports/irreducible-cfg-census-2026-06-09.md` §1: **313 loop-bearing procedures**,
all reducible single-header natural loops, across 250 files / 3,767 procedures:

| Corpus | Procs w/ loops | Natural loops |
|---|---:|---:|
| EQ-200 | 214 | 322 |
| SMACK pilot | 96 | 112 |
| StrataExamples | 3 | 4 |
| **Total** | **313** | **438** |

For every one of the 3,767 procedures `n_back_edges == n_natural_loops` (0 mismatches)
and **0 irreducible CFGs / 0 residual SCCs > 1**. Every loop is a clean reducible
single-header natural loop — exactly the shape a CFG loop-elim pass needs. Max nesting
depth observed: 2; deepest single proc up to 9 nested loops (EQ_xj4oiocoyjt), still
reducible.

### Where the loop contract lives — a correction to the original assumption

The study's working assumption was that the loop contract sits on the header
`condGoto` *transfer metadata*. That is true **only for structured-origin CFGs**:
`stmtsToCFG` attaches `specLoopInvariant`/`specDecreases` onto the header transfer
(`Strata/Transform/StructuredToUnstructured.lean:145-152`). But the **DDM/SMACK
translator emits bare `condGotos` with no metadata** — `translateTransfer`
(Translate.lean:1707-1736) attaches nothing and `translateCFGProcedure`
(Translate.lean:1808/1826) sets `body := .cfg cfg` directly.

Consequence, verified against the census: of the 313 loop-bearing procs, **only the 3
StrataExamples carry a contract; the 310 EQ-200 + SMACK procs do not** (SMACK relies
on bounded unwinding, not invariants). So a CFG loop-elim pass that requires a contract
fixes 3 of 313; one that defaults to a trivial `assume true` cut fixes all 313 (the
cut still breaks the cycle). **The #29 reproducer `loopGuardPrecondPgm` is
unrepresentative** — it runs via `verifyCFG → toCFGForm → stmtsToCFG`
(`StrataTest/Languages/Core/Examples/_CFGFormHelper.lean:26-33,40-56`), so it *does*
carry the contract, unlike the production SMACK corpus.

The prototype (§4) found an even more specific storage fact for the structured-origin
path: in `stmtsToCFG` output the invariants are emitted as **inline `assert [inv$…]`
commands inside the header block** (not in condGoto metadata), with the back-edge a
bare `condGoto true lentry lentry`. This matters for the soundness analysis in §5.

---

## 3. Design: two framings

### Framing A — net-new CFG-native loop-elim pass (RECOMMENDED)

A `cfgLoopElim : Program → Program × Statistics`, wrapped as a `cfgLoopElimPipelinePhase`
mirroring `loopElimPipelinePhase`, rewriting **only `.cfg` bodies** (structured and
non-proc decls pass through). Per CFG: (1) build the successor map from each block's
transfer and compute dominators by standard iterative forward dataflow; (2) identify
natural-loop regions (edge `t→H` is a back-edge iff `H` dominates `t`), innermost-first;
(3) recover the contract from the header (transfer metadata for structured-origin,
inline asserts for `stmtsToCFG` output), defaulting to `assume true` when absent;
(4) compute the loop-modified set `M = modifiedVars(region) \ definedVars(region)`
(the same discipline as LoopElim.lean:131-133); (5) synthesize an acyclic replacement
mirroring LoopElim.lean:125-203 in block form; (6) reassemble so the result is a DAG;
(7) wrap as a phase returning `.modelToValidate` on paths carrying
`loopElimInvariantPrefix`/`loopElimGuardPrefix` (copy LoopElim.lean:266-269).

Slots into `transformPipelinePhases` (Verifier.lean:876-893), **appended after
`loopElimPipelinePhase`** so the eliminated DAG is what `evalCFGBody`
(ProcedureEval.lean:151-171, dispatched at :237) sees.

**Pros.** Closes #29 for the entire loop-bearing corpus (all 313, reducible
single-header per census), even contract-less ones (havoc + assume-true cuts the
cycle). The CFG analog of what `loopElimPipelinePhase` already does for structured
bodies — generalizes a trusted recipe rather than inventing an abstraction. Stays
entirely on the SMT/symbolic-eval path by construction (lives in `corePipelinePhases`,
which the CBMC `GOTO.lean` entry never calls), satisfying the hard scope constraint.

**Cons.** Most LoC of the two framings: a dominator + natural-loop-region analyzer plus
a region-rewriter and block-splicer; nested loops require innermost-first iteration.
For the 310 contract-less procs the recovered invariant is `true`, so the pass only
*terminates* the eval without adding inductive strength (acceptable — SMACK never had
invariants). The havoc set must conservatively over-approximate `M` or it is unsound.
Changes program shape, so CFG-form goldens re-bless.

### Framing B — route through structured LoopElim (RULED OUT)

**B1 (reorder):** run loop elimination on the structured `.loop` Stmts *before*
`stmtsToCFG` lowers them. **B2 (reconstruct):** for a `.cfg` body, recognize the
lowered loop region, rebuild a structured `.loop`, run `Stmt.removeLoops`, re-lower.

**Why it fails.** The 310 EQ-200 + SMACK loop-bearing procs are born as `.cfg` directly
from the translator and **never pass through `stmtsToCFG`** — there is no structured
`while` to eliminate before lowering, so **B1 misses #29 entirely** (it touches only
structured-origin programs, which already verify fine through the structured eval
path). B2 is a full CFG-to-AST de-lowering — strictly harder and more fragile than
building the acyclic cut directly on the CFG, and the SMACK blocks don't even match the
recognizable lowered shape (no decrease block, no `loop_entry$` labels, no contract md).
The skeptic independently confirmed the B-failure rationale against Translate.lean:1707-1736.

**Recommendation: Framing A.** The census/BRANCH_FEATURES #29 recommendation
independently arrives at the same conclusion.

---

## 4. Prototype + measurement

**Prototype:** Framing A, as `Imperative.cfgLoopElim`, at
`/Users/htd/Documents/Strata/.claude/worktrees/wf_13fa5aa0-0f3-3/Strata/Transform/CFGLoopElim.lean`.
Demo test (`StrataTest/Transform/CFGLoopElimDemo.lean`) and evidence runner
(`cfg_loop_elim_runner.lean`) build green (`lake build Strata` = 293 jobs incl.
CFGLoopElim).

**Environment mismatch (load-bearing caveat).** The harness created the worktree from
`origin/main` @ 77f9a240e, **not** htd/smack — which is ~220 commits ahead and is where
`DetCFG`, the `.cfg` Procedure.Body, `evalCFGBlocks`, `loopElimPipelinePhase`, the
SMACK strata-files, and the #29 reproducer actually live. So the pass was prototyped
against equivalently-shaped `stmtsToCFG`-lowered CFGs of the same types
(`CFG String (DetBlock String Command Expression)` = htd/smack's `DetCFG`), and the
phase-wiring step was **not** exercised. The pass is generic over
`CFG String (DetBlock String CmdT P)`, so it imports verbatim to htd/smack's `.cfg`
proc bodies — but **it never ran the real `.cfg` eval path or the OOM reproducer.**

**Applies to test set? Yes for the structural metric only.** The runner (via
`lake env lean --run`, JIT-compiled) prints before/after CFG dumps and back-edge
verdicts for `countUp` and `nested`:

- `countUp`: `cfgHasBackEdge` BEFORE=true / AFTER=false.
- `nested` (2 nested loops, 2 back-edges): BEFORE=true / AFTER=false, **both** back-edges
  cut; havoc sets correctly scoped (inner `{r,y}`, outer `{r,y,x}` = modifiedVars minus
  block-local defs).
- Loop-free CFGs are left untouched (no back-edge → no rewrite).

**Before/after (countUp), the load-bearing shape:**

```
BEFORE (cyclic — latch back-edges to the dominating header):
  measure_decrease$_3:
    assert [measure_decrease_loop_measure$_2]: n < loop_measure$_2;
    condGoto true loop_entry$_1 loop_entry$_1     <-- BACK-EDGE
  => cfgHasBackEdge = true

AFTER (acyclic — back-edge redirected to a fresh havoc/assume-not-guard exit):
  measure_decrease$_3:
    assert [measure_decrease_loop_measure$_2]: n < loop_measure$_2;
    condGoto true cfg_loop_exit$0 cfg_loop_exit$0   <-- redirected, no longer to header
  cfg_loop_exit$0:
    havoc i;                                        <-- M = {i}
    assume [cfg_loop_not_guard$0]: !(i < n);        <-- assume not-guard
    condGoto true end$_0 end$_0                     <-- goto kNext
  => cfgHasBackEdge = false
```

The cut is `{ cmds := havocs ++ [assumeNotG], transfer := .goto kNext }`
(CFGLoopElim.lean:189-190). It leaves the header's inline VC asserts in place and only
redirects the latch's back-edge.

**Measurement: UNAVAILABLE.** The Measure phase died on a transient API error and
returned null. Therefore:

| Metric | Result |
|---|---|
| #29 OOM closure (`loopGuardPrecondPgm`) | **UNAVAILABLE — not run** |
| Verdict convergence with structured form | **UNAVAILABLE — not measured** |
| RSS delta | **UNAVAILABLE — not measured** |
| Per-program before/after verdicts | **UNAVAILABLE** |

The only evidence is the structural `cfgHasBackEdge` toggle from the runner. The
prototype **never ran `verify`** or compared obligation sets / verdicts. (Native `#eval`
on the freshly-built pass failed with *"Could not find native implementation … _redArg"*
— a downstream-interpretation limitation, not a pass defect; the runner via `lake env
lean --run` works.)

---

## 5. Soundness — skeptic verdict: PARTIAL

| Task | Verdict |
|---|---|
| Task 1 — before-state | **CONFIRMED** (no corrections) |
| Task 2 — soundness of eliminated form | **REFUTED as prototyped** |
| Task 3 — #29 closure | **PARTIAL / structurally plausible, unmeasured** |
| Task 4 — Framing B ruled out | **N/A (A chosen); B-failure rationale verified** |

**Task 1 — confirmed.** All before-state claims verified on htd/smack @ c6f96e15c:
the `.cfg` passthrough (LoopElim.lean:249), the fuel-only worklist
(ProcedureEval.lean:133-149), both-successor forking (`:130`), and the
`.structured`/`.cfg` dispatch (Procedure.lean:288-294, ProcedureEval.lean:237). The
study is not moot — CFG loop-elim genuinely does not exist.

**Task 2 — soundness REFUTED for the eliminated form as prototyped.** The cut
**drops the invariant-maintenance obligation (VC2 = `arbitrary_iter_maintain_invariant`)**
and would produce a **spurious PASS**. Evidence:

- The trusted structured recipe (LoopElim.lean:77-103, esp. :96-98, :144-153) checks
  VC2 by (a) `havoc(M)` *before* the body, (b) `assume(G ∧ I)` on that arbitrary
  mid-state, (c) run the body once, (d) **`assert I` again**. The gauss structured
  golden (Loops.lean:220-260) shows exactly this — VC `arbitrary_iter_maintain_invariant_0_2`
  with assumptions over fresh havoc vars and obligation
  `s@3+(i@1+1) == (i@1+1)*(i@1+1+1)/2`.
- The **lowered cyclic CFG** that `stmtsToCFG` produces (and that the prototype
  operates on) has **no** `arbitrary_iter_maintain_invariant` assert — only the
  header's entry-invariant asserts (Loops.lean:52-53) and the latch's measure_decrease
  assert (Loops.lean:65). Maintenance is checked *only* by the cyclic back-edge
  re-visiting the header assert on the post-body state during unrolling.
- The prototype (CFGLoopElim.lean:177-191) **cuts that back-edge**: latch `goto header`
  → fresh exit `havoc(M); assume(¬G); goto kNext`. With the back-edge gone, the header
  invariant assert is reached only **once**, on the concrete entry state (countUp:
  i=0). The post-body invariant check is silently dropped. A program with a **wrong
  invariant** that structured VC2 catches would be **accepted** by the eliminated CFG.
- Secondary divergences: the exit block omits the `assume(I)` the structured exit
  carries (LoopElim.lean:98), and the body executes over the **concrete entry state**
  instead of a havoced arbitrary mid-state, so body-region asserts (e.g.
  measure_decrease) evaluate over the first concrete iteration rather than the
  structured form's arbitrary havoced state. Not verdict-equivalent.

The termination/back-edge-removal aspect **is** sound (Floyd/Hoare havoc cut, over-
approximating). The **verification-condition aspect is not**, as built. **A sound CFG
loop-elim pass must replicate the full structured recipe** — emit a fresh
`havoc(M); assume(G ∧ I)` pre-body block AND a maintain-invariant `assert(I)` after the
body, then the `havoc(M); assume(¬G); assume(I)` exit — not merely redirect the
back-edge. The header's inline entry-invariant asserts are necessary but **not
sufficient**.

**Task 3 — #29 closure PARTIAL.** Back-edge removal is structurally genuine (DAG, no
residual cycle; `computeDom` recomputed, `cfgHasBackEdge` AFTER=false), so it is not a
bounded-wall mask. But the actual reproducer was **not run** — no OOM-closure, no
bounded-eval, no RSS delta (Measure phase died). Nested-loop havoc scoping was
smoke-checked via `cfgHasBackEdge` only, not verified for soundness of `M`.

---

## 6. Recommendation

**Build it — Framing A — but only after the prototype's soundness defect is fixed.**

1. **Build the full-recipe pass, not the prototype's cut.** A correct
   `cfgLoopElim` must emit, per loop region: a pre-body `havoc(M); assume(G ∧ I)`
   block, the body, a post-body `assert(I)` (the dropped VC2), and a
   `havoc(M); assume(¬G); assume(I)` exit feeding `kNext`. This mirrors
   LoopElim.lean:77-103 / :125-203 in block form. The prototype's back-edge redirect
   is the *termination* half done correctly; the *verification* half (re-emitting the
   maintenance obligation that the cut destroys) is missing and is the gating work.
2. **Default to `assume true` when no contract is present** (the 310 EQ-200 + SMACK
   procs). With `I = true`, VC1/VC2 are trivially valid and add no unsound assumption;
   the cut still soundly havocs `M` and assumes `true ∧ ¬G` at exit — the weakest sound
   summary. This is what fixes all 313 procs, not just the 3 structured-origin ones.
3. **Slot on the verification path only.** Append `cfgLoopElimPipelinePhase` after
   `loopElimPipelinePhase` in `transformPipelinePhases` (Verifier.lean:893). The CBMC/
   GOTO backend (`Strata/Backends/CBMC/GOTO.lean` → `CFGToCProverGOTO.lean` /
   `CoreCFGToGOTOPipeline.lean`) never calls `corePipelinePhases`/`transformPipelinePhases`
   and keeps the real cyclic CFG it needs for unwinding. Gate the pass to fire only when
   a `.cfg` body contains a back-edge.
4. **Re-run the Measure phase on htd/smack** (where `DetCFG`, the `.cfg` Procedure.Body,
   and `loopElimPipelinePhase` exist) with the corrected pass. **Gate acceptance on
   verdict-set equality with the structured form** on Loops.lean countUp/gauss/nested —
   especially the VC2 maintain-invariant obligations and the `measure_decrease` ❓
   unknown on `measureFailExamplePgm` — **not** just on `cfgHasBackEdge` toggling. Run
   the #29 reproducer under a guarded harness only (`gtimeout 60` + `maxHeartbeats`,
   single-thread Z3, never a default build — ~28.5 GB RSS / exit 137 risk).

**Effort estimate.** **2-3 days** (up from the BACKLOG's 1-2 day estimate): ~1-2 days
for the analyzer + region-rewriter + full-recipe block synthesis (the prototype already
has the dominator dataflow + region detection + havoc-set scoping working, ~40 LoC of
Lean dominator code, reusable), plus ~0.5-1 day to add the dropped VC2/pre-body-havoc
machinery that the prototype omits and to re-bless CFG-form goldens, plus measurement.

**Relationship to existing BACKLOG / workflow entries.**
- ***Investigations → CFG-eval memory profile #29*** (BACKLOG): this study answers the
  open question "does the recommended CFG-level loop-elim pass actually close the OOM"
  with **structurally yes, end-to-end unproven** — the back-edge removal is genuine but
  closure was not measured. The 2-3 day scoping estimate refines that entry's 1-2 days.
  The entry's "Next action" (scope as `Strata/Transform/CFGLoopElim.lean` + a
  `PipelinePhase` in Verifier.lean) stands, with the §6 soundness correction layered on.
- ***Investigations → CFG-eval loop-handling: havoc loop-modified-set on exit-branch***:
  this study confirms the BACKLOG hypothesis that the two are the same root fix — but
  with a sharper warning. The prototype's havoc-on-exit is precisely the narrow patch
  that entry describes, and the skeptic shows that the havoc-on-exit *alone* is unsound
  for invariant-bearing loops (drops VC2). The 15 PASS-? invariant-less `while(1)`
  programs (where `I = true`, so VC2 is vacuous) would be fixed soundly by the
  havoc-only cut; the invariant-bearing #29 reproducer needs the full recipe. The study
  did **not** measure the projected 68/15/11 → ~77/0/17 matrix shift (Measure died).
- ***wpqfi3man*** (paused evalCFGBody OOM TDD workflow): its net-new value was the
  TDD-Verify phase. That value is now partly delivered (a building prototype exists) but
  the soundness-gated, full-recipe pass and the actual reproducer run remain. Resume for
  the Measure/TDD-Verify-on-htd/smack step rather than re-deriving the root cause, and
  reconcile its fix candidate with the full-recipe requirement here.
- ***Block-coalescing applicability census*** (DONE): recommended folding coalescing into
  the same dominator/natural-loop machinery this pass needs, as a post-loop-elim cleanup.
  Bundling remains nearly free; standalone ROI does not justify a second framework.

---

## 7. Files referenced + prototype worktree

**Prototype worktree (base = origin/main, NOT htd/smack):**
`/Users/htd/Documents/Strata/.claude/worktrees/wf_13fa5aa0-0f3-3`
- Pass: `/Users/htd/Documents/Strata/.claude/worktrees/wf_13fa5aa0-0f3-3/Strata/Transform/CFGLoopElim.lean` (the unsound cut is at :177-191, exit block :189-190)
- Demo test (green): `/Users/htd/Documents/Strata/.claude/worktrees/wf_13fa5aa0-0f3-3/StrataTest/Transform/CFGLoopElimDemo.lean`
- Evidence runner: `/Users/htd/Documents/Strata/.claude/worktrees/wf_13fa5aa0-0f3-3/cfg_loop_elim_runner.lean`

**Source (htd/smack @ c6f96e15c):**
- `Strata/Transform/LoopElim.lean` — :248-249 (`.cfg` passthrough), :246 (`.structured` arm), :77-103 + :125-203 (the trusted recipe incl. VC2 maintain-invariant), :131-133 (havoc-set discipline), :263-270 (`loopElimPipelinePhase`), :266-269 (model-to-validate demotion)
- `Strata/Languages/Core/ProcedureEval.lean` — :106-130 (`evalCFGStep`, both-successor fork at :130), :133-149 (`evalCFGBlocks` fuel-only worklist), :151-171 (`evalCFGBody`), :237 (`.cfg` dispatch)
- `Strata/Languages/Core/Procedure.lean` — :288-294 (`Procedure.Body` inductive)
- `Strata/Transform/StructuredToUnstructured.lean` — :145-152 (contract attached to header transfer; inline asserts in `stmtsToCFG` output), :132 (back-edge `.goto lentry`)
- `Strata/Languages/Core/Verifier.lean` — :876-893 (`transformPipelinePhases`, slot point at :893), :899-913 (`corePipelinePhases`)
- `Tools/BoogieToStrata/.../Translate.lean` — :1707-1736 (`translateTransfer`, bare condGoto, no md), :1808/1826 (`translateCFGProcedure`, `body := .cfg cfg`)
- `Strata/Backends/CBMC/GOTO.lean`, `CFGToCProverGOTO.lean`, `CoreCFGToGOTOPipeline.lean` — the CBMC path that must NOT see the eliminated form

**Test set / reproducers:**
- `StrataTest/Languages/Core/Examples/Loops.lean` — countUp/measureFailExamplePgm (:24-43, CFG golden :46-68), gaussPgm (:108, golden :164, structured VC2 golden :220-260), nestedPgm (:346); structured measure_decrease ❓ unknown on measureFailExamplePgm
- `StrataTest/Languages/Core/Examples/FunctionPreconditions.lean` — loopGuardPrecondPgm (:479), the #29 OOM reproducer
- `StrataTest/Languages/Core/Examples/CFGForm/FunctionPreconditions_Part4.lean:84` — `#eval verifyCFG loopGuardPrecondPgm` (DO NOT build under default settings — OOM)
- `StrataTest/Languages/Core/Examples/_CFGFormHelper.lean` — :26-33 (`toCFGForm`), :40-56 (`verifyCFG`)

**Reports / ledger:**
- `reports/irreducible-cfg-census-2026-06-09.md` — §1 census (313/438/0-irreducible), §5/§6 (#29 root cause + Framing A recommendation)
- `Examples/smack-docker/BRANCH_FEATURES.md` — §9.5 #29 (:1003), open-issues roll-up (:1019)
- `reports/BACKLOG.md` — *Investigations → CFG-eval memory profile #29*, *CFG-eval loop-handling*, *Ready to execute → CFG-level loop-elimination effect study* + *wpqfi3man*

**Reusable artifact note:** the dominator/natural-loop analyzer at
`/tmp/claude/cfg-reducibility-analyzer.py` is **gone** (verified absent on disk —
transient /tmp artifact). The prototype re-derived the ~40-LoC dominator dataflow
directly in Lean, so the analyzer is not on the critical path.

---

*Read-only study per MEMORY directive: the #29 reproducer was NOT built/run; the OOM
characterization is from reports + static source, and the prototype evidence is the
`cfgHasBackEdge` structural toggle (not a verify run). Soundness analysis is static
against the Loops.lean goldens.*
