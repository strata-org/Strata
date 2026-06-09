# Irreducible-CFG Census + Loop-Elimination Applicability (2026-06-09)

Branch: htd/smack. Scope: do unstructured benchmark programs hit problems from
irreducible control flow, and would loop elimination help?

---

## 1. TL;DR

**Q1 — Are any benchmark programs running into problems due to irreducible
control flow?** **No.** Across all three corpora measured — 3,767 procedure
CFGs total — **zero** are irreducible. None of the observed failures (the #29
`evalCFGBody` OOM, timeouts, ELAB_FAILs) are attributable to irreducibility.
The OOM has a different, confirmed root cause: the CFG evaluator literally
unrolls reducible loop back-edges because it never performs the havoc-and-cut
that the structured path does.

**Q2 — Would loop elimination help?** **Yes — but for the reducible case, not
the irreducible one.**
- (a) **Irreducible loops:** moot — there are none. Classic structured
  loop-elim cannot apply (no single header) and would require node-splitting
  (exponential-blowup risk) or per-entry invariants. Not worth building against
  a confirmed zero-frequency case.
- (b) **Reducible CFG-form loops (the common case):** a **CFG-level loop-elim
  pre-pass** — consuming the loop-contract metadata already attached to the
  header `condGoto` transfer — would **structurally fix the #29 OOM** and align
  CFG-form verification with structured-form. This is the impactful finding.

### Census table

| Corpus | Files | Procedures | Procs w/ loops | Natural loops | Irreducible procs | Files w/ irreducible |
|---|---:|---:|---:|---:|---:|---:|
| EQ-200 | 200 | 3,293 | 214 | 322 | **0** | 0 |
| SMACK pilot | 48 | 469 | 96 | 112 | **0** | 0 |
| StrataExamples | 2 | 5 | 3 | 4 | **0** | 0 |
| **Total** | **250** | **3,767** | **313** | **438** | **0** | **0** |

---

## 2. Census methodology

Analyzer: `/tmp/claude/cfg-reducibility-analyzer.py`. For each per-procedure CFG
(`cfg <entry> { L: { ... goto/condGoto ...; } }`) it:

1. Parses labeled blocks + `goto`/`condGoto` targets with brace-depth +
   string-literal-aware tracking.
2. Computes every node's dominator set via iterative dataflow fixpoint rooted at
   the entry.
3. Runs an iterative DFS spanning tree, classifying each edge tree/forward/back/
   cross and flagging *retreating* edges (target is a DFS ancestor of source).
4. **Hecht-Ullman reducibility test:** reducible iff every retreating edge is a
   back-edge (its target dominates its source).
5. **Robust cross-check:** removes all dominator back-edges and runs Tarjan SCC
   on the residual reachable graph; declares irreducible if any residual SCC has
   size > 1 (or a residual self-loop).
6. Counts natural loops (one per dominator back-edge), distinct loop headers, and
   max loop-nesting depth (longest subset-containment chain over per-header loop
   bodies).

**Detector is sound, the zero is real (not a parse miss).** `--self-test` passes
all 4 fixtures including the deliberately irreducible two-entry fixture (`entry
-> {n1,n2}, n1->n2, n2->n1`), correctly flagged `is_reducible=no` with evidence
`n2->n1 (retreating, target does not dominate source)`. Loop detection is
genuinely active: on every one of the 3,767 procedures `n_back_edges ==
n_natural_loops` (0 mismatches), exactly as expected when each dominator
back-edge induces one natural loop. No empty/parse-failed CFGs skew the totals.

Independent skeptic re-trace of 3 loop-bearing procedures confirmed the verdict:
`EQ_yd35szseljm_out` anon0 (100 blocks, 5 back-edges / 3 headers — block15 is a
3-latch multi-loop, which is why 5 loops > 3 headers; residual SCC=0),
`EQ_xj4oiocoyjt_out` anon0 (729 blocks, 9/9, residual SCC=0), and
`jsmn_jsmn_parse_harness` _bb0 (138 blocks, 5/5, residual SCC=0) — every
back-edge target dominates its source.

### Per-corpus results

**EQ-200** (3,293 procedures across 200 files). 0 irreducible. 214 procedures
carry ≥1 back-edge, and the *same* 214 carry ≥1 natural loop. Back-edge
distribution: 3,079 procs with 0, 167 with 1, 24 with 2, 7 with 3, 10 with 4, 2
with 5, 4 with 9. Largest loop-bearing CFGs are 729-block procedures (e.g.
`EQ_xj4oiocoyjt_out.core.st`) with 9 nested natural loops each — all reducible.
SMACK lowers structured Java bytecode to reducible CFGs by construction.

**SMACK pilot** (469 procedures across 48 freshly translated files). 0
irreducible. 96 procedures with loops, 112 natural loops, `n_back_edges ==
n_natural_loops` for all 469. Sample was deliberately loop-weighted and
goto-heavy — the programs most likely to be irreducible: all 13 `sv_loops_*`,
`loop_sum`, the JSON/cJSON/jsmn parser harnesses (`jsmn_parse` has one proc with
5 natural loops; `cjson_Parse` has nested 2-header loops), `sv_rc_*`,
`sv_locks_*`, plus a spread of simple programs. Translation used
`/Users/htd/.dotnet/dotnet` against the built Release DLL with `--smack`.
**Coverage caveat:** 48 of 94 pilot `.bpl` translated; the 46 untranslated
(mostly `aws_*`/`base64`/`skip*`/`Sntp_*` variants) are the same SMACK-lowered
structured-loop shape, expected reducible but unmeasured.

**StrataExamples** (5 emitted CFGs from 2 source `.lean` files). 0 irreducible.
The 5 genuine `singleCFG` text goldens: `measureFailExamplePgm` (1 loop, 1
header), `gaussPgm` (1 loop), `nestedPgm` (2 loops, 2 headers, max-nest 2),
`exitPgm` n=0 and n=1 (0 loops, DAGs). Confirms `stmtsToCFG` gives every `while`
a single dominating `loop_entry$N` header — reducible even with nesting and
early-exit. **Not covered:** `loopGuardPrecondPgm`
(`FunctionPreconditions.lean:479`) has no printed `singleCFG` golden; by
construction it is the same single-while shape and is certainly reducible.

---

## 3. Irreducibility findings

**Count: 0 irreducible CFGs out of 3,767 procedures.** No examples to capture —
`irreducible_examples` is empty in every corpus.

**Attributability to observed failures: none.** No observed failure (OOM #29,
timeouts, ELAB_FAILs) is caused by irreducible control flow, because no
irreducible CFG exists in the benchmark set. The reason is structural and holds
across all three frontends: SMACK lowers C control flow (including
goto/break/continue/mid-test loops) into structured Boogie loops with a single
dominating header; `javac` lowers structured Java the same way; and Core's
`stmtsToCFG` gives every `while` a single `loop_entry` header. All three
pipelines produce reducible CFGs by construction.

**The "irreducible CFG motivation" design-doc premise is incorrect.**
`Tools/BoogieToStrata/Docs/cfg-emission-design.md` does **not** exist — the only
file in that Docs directory is `STATUS.md`. The accurate references are:
- `Tools/BoogieToStrata/Docs/STATUS.md` motivates CFG emission only as
  "procedures containing any goto are emitted using native cfg syntax"
  (re-structuring is not always possible) — no irreducibility claim.
- `Tools/BoogieToStrata/Source/StrataGenerator.cs:1329,1340` actively **rejects**
  irreducible control flow rather than handling it: the structured-recovery path
  (`BuildLoopRegions` / `InsertRegion`) throws
  `StrataConversionException("Irreducible control-flow: overlapping loop
  regions ...")` when back-edge loop regions overlap without nesting. The native
  CFG path (`EmitCFGBody`) emits each Boogie block verbatim and never calls
  `BuildLoopRegions`, so it can represent arbitrary flow but never reaches
  loop-elim.

---

## 4. Loop-elimination applicability

### 4(a) Irreducible loops — moot, and not worth chasing

Classic loop-elim (`Strata/Transform/LoopElim.lean`) cannot apply to an
irreducible loop: it rewrites structured `.loop guard measure invariants`
statements requiring a single header + invariant, and explicitly passes `.cfg`
bodies through unchanged (`LoopElim.lean:249`,
`| .cfg _ => ((.proc proc md) :: acc, stats)`). To handle a genuinely
irreducible loop you would first need **node-splitting** (controlled
duplication, risk of exponential blowup) to make it reducible, or a verifier
mechanism requiring **invariants at every loop entry**. Against a confirmed
0/3,767 frequency these are real engineering costs that buy nothing.
**Recommendation: do nothing.** The existing `StrataConversionException`
rejection is the correct safe behavior for a non-existent input.

### 4(b) Reducible CFG-form loops — the impactful case

This is the common case (313 loop-bearing procedures) and where loop-elim pays
off. The structured path performs a havoc-and-cut; the CFG path does not, and
the contract needed to build the same cut on the CFG **is already present on the
CFG**.

- **Structured path does the cut.** `LoopElim.removeLoopsM` for `.loop`
  (`LoopElim.lean:125-203`) replaces the loop node with an **acyclic** passive
  form: `assert I; assume I; if(G){ havoc(modified); assume G; assume I;
  [measure VCs]; body; assert I; [decrease]; havoc(modified); assume ¬G; assume
  I }`. No back-edge → structured eval does one bounded havoced iteration and
  never cycles.
- **CFG path does NOT.** `loopElimPipelinePhase` only rewrites `.structured`
  bodies; `.cfg` bodies pass through unchanged (`LoopElim.lean:249`).
- **The contract is already on the CFG.** `stmtsToCFG` attaches
  `MetaData.specLoopInvariant` and `MetaData.specDecreases` to the header
  `condGoto`'s transfer metadata
  (`StructuredToUnstructured.lean:146-151`, comment: "downstream CFG passes can
  recover the original spec"). The back-edge is a literal cycle — the header
  `lentry` transfer is `.condGoto e body kNext` and the decrease block's
  transfer is `.goto lentry` (`StructuredToUnstructured.lean:132`), with **no
  havoc anywhere** in this lowering.
- **The census proves the precondition.** Every loop region across all three
  corpora is a clean reducible natural loop with a single dominating header
  (`n_back_edges == n_natural_loops`, 0 irreducible) — exactly the shape a
  CFG-level loop-elim pass needs. No irreducible fallback is required.

---

## 5. The #29 connection — is the OOM a loop-elim-missing problem?

**Yes. #29 is the CFG path missing the havoc-cut, not a quadratic worklist or an
`addPositive` precondition red herring.** Mechanism, confirmed at file:line:

- `evalCFGBlocks` (`ProcedureEval.lean:133-149`) is a plain worklist whose
  **only** termination bound is `env.fuel` (`:139` `if env.fuel == 0`, `:145`
  decrement). There is **no** visited set, **no** fixpoint, **no** back-edge/SCC
  awareness. (`grep` for `invariant`, `havoc`, `visited`, `specLoopInvariant`,
  `specDecreases` in `ProcedureEval.lean` = 0 hits; only `fuel` appears.)
- `evalCFGStep` on a `.condGoto` (`ProcedureEval.lean:106-130`): when the guard
  is symbolic (not `.true`/`.false`) it forks **both** successors (`:130`,
  `((lt, env_t) :: (lf, env_f) :: newActive, ...)`). The true successor
  traverses body → back-edge → `lentry`, where the guard is still symbolic and
  forks again — **unbounded symbolic unrolling**, capped only by fuel, growing
  `cfgResultsRev` one `Env` per pseudo-iteration. That is exactly the heap
  blowup #29 describes. The header doc-comment (`:177-182`) itself notes that K
  paths × N visits consume K×N fuel.
- Contrast: structured eval runs the `LoopElim` acyclic cut, so it does one
  bounded symbolic iteration over a havoced state and never cycles.

So #28 and #29 share one parent — CFG eval does not perform the loop-elim cut
that structured eval does. #29 is the catastrophic form (no cut → unbounded
unrolling → OOM); #28 is the benign cosmetic form (straight-line `condGoto`
path-conditions differ in shape from structured `ite` path-conditions). The
existing mitigation at `ProcedureEval.lean:118-129` (clearing `deferred` on the
false branch) curbs the per-branch deferred-obligation doubling but does **not**
stop the loop unrolling itself.

> Caveat (design hypothesis, not a verified fact): a CFG loop-elim pass would
> also converge the two forms' path conditions and shrink the #28 cosmetic
> asymmetry for loop-bearing programs. Plausible and code-consistent, but
> forward-looking. The core #29 claim does not depend on it.

---

## 6. Recommendation

**Build the CFG-level loop-elim pass. It closes #29 and is the architecturally
correct way to make CFG-form verification match structured-form. Priority:
high** (it eliminates an OOM structurally rather than papering it over with
looser memory bounds / `maxHeartbeats`).

Recommended design — a `Program → Program` pre-pass on `.cfg` bodies, run before
`evalCFGBody`, mirroring `loopElimPipelinePhase`'s role for structured bodies.
Per procedure CFG:
1. Compute dominators + identify natural-loop regions from dominator back-edges.
   The census proves all loops are reducible, so this is well-defined — **no
   irreducible fallback needed**. (The census analyzer already implements
   dominators + natural-loop detection.)
2. Recover the loop contract from the header `condGoto`'s
   `specLoopInvariant`/`specDecreases` transfer metadata
   (`StructuredToUnstructured.lean:146-151`) — already present, no re-inference.
3. Splice the loop region with an acyclic block sequence emitting exactly
   `LoopElim`'s recipe (assert I at entry; havoc loop-modified set; assume I; one
   havoced body iteration with assert-I-maintained + measure VCs; exit with
   assume ¬G; assume I), removing the back-edge to `lentry`.

Payoffs: (a) `evalCFGBlocks` sees a DAG → terminates in bounded steps with the
same VCs structured eval produces → **#29 OOM eliminated structurally**; (b)
CFG and structured forms produce matching verdicts and matching
`loopElimInvariantPrefix`/`loopElimGuardPrefix` obligation labels, letting the
loopElim model-validation demotion (`LoopElim.lean:263-270`) apply uniformly to
both forms. Effort is moderate: dominator/natural-loop detection is standard and
already prototyped in the census analyzer; the splice reuses `LoopElim`'s
existing recipe. Sequence it as a new `PipelinePhase` on `.cfg` bodies before
`symbolicEval`, gated to fire only when a CFG carries loop-contract metadata.

**Scope boundary:** this is a *verification-path* transform. It must NOT touch
the CBMC/GOTO path, which wants the real cyclic CFG for its own unwinding.

Cheap non-code follow-ups: (1) Correct any planning/spec text citing
`Tools/BoogieToStrata/Docs/cfg-emission-design.md` — that file does not exist;
the accurate references are `STATUS.md` and the `StrataGenerator.cs` rejection.
(2) To close the SMACK coverage caveat, translate the 46 untranslated pilot
programs — expect the same all-reducible result.

Revisit irreducibility only if a future frontend emits raw irreducible Boogie
goto onto the native `EmitCFGBody` path, at which point the verifier (not
LoopElim) would need a per-entry-invariant mechanism.

---

## 7. Files referenced

Source (all under `/Users/htd/Documents/Strata-smack/`):
- `Strata/Languages/Core/ProcedureEval.lean:106-130` (`evalCFGStep` symbolic
  fork), `:133-149` (`evalCFGBlocks` fuel-only worklist), `:151-171`
  (`evalCFGBody`), `:177-182` (K×N fuel doc-comment).
- `Strata/Transform/LoopElim.lean:125-203` (`.loop` → acyclic havoc cut),
  `:249` (`.cfg` passthrough), `:263-270` (model-validation demotion).
- `Strata/Transform/StructuredToUnstructured.lean:132` (decrease block
  `.goto lentry`), `:146-151` (spec metadata on header condGoto), `:156`
  (header `condGoto`).
- `Tools/BoogieToStrata/Source/StrataGenerator.cs:1276-1340` (irreducible
  rejection in `BuildLoopRegions`/`InsertRegion`); `EmitCFGBody` (native CFG
  path, no `BuildLoopRegions`).
- `Tools/BoogieToStrata/Docs/STATUS.md` (the only Docs file;
  `cfg-emission-design.md` does NOT exist).

Census artifacts:
- Analyzer: `/tmp/claude/cfg-reducibility-analyzer.py` (`--self-test` passes 4/4).
- EQ-200: `/tmp/claude/eq200-reducibility-aggregate.tsv`,
  `/tmp/claude/eq200-reducibility-per-proc.tsv` (3,293 rows).
- SMACK pilot:
  `/Users/htd/Documents/Strata-smack/Examples/smack-docker/smack-pilot-reducibility.tsv`
  (469 rows).
- StrataExamples: `/tmp/claude/strata-examples-reducibility.tsv` (5 rows).
