# Block-Coalescing Applicability (2026-06-09)

Branch: htd/smack. Scope: do the benchmark CFGs contain trivial jump-chains a
block-coalescing pass could collapse, how much would it remove, and is the pass
worth building — for the SMT verify path, the CBMC/GOTO path, or just debugging?
The load-bearing question is whether `stmtsToCFG` (the structured→unstructured
lowering that feeds the proof corpus) emits coalesceable chains and which
constructs produce them.

---

## 1. TL;DR

**Q1 — SMACK: are there coalescing opportunities?** **Barely.** On the
48-file SMACK pilot (469 procedure CFGs, 52,248 blocks) a coalescing pass removes
only **170 blocks (0.33%)**. Only 93/469 procedures (19.8%) have any coalesceable
edge; chains cap at length 3. The C-derived control flow is structurally
*hostile* to this criterion — ~118× sparser than EQ. Root cause is verified, not
conjectured (Section 3).

**Q2 — Equalizer: are there coalescing opportunities?** **Yes, heavily.** On the
200-file EQ corpus (3,293 procedure CFGs, 206,860 blocks) a coalescing pass
removes **79,464 blocks (38.41%)**. *Every* procedure has ≥1 coalesceable edge.
81% of chains are the canonical length-2 trivial jump; a thin tail reaches
length 7. BoogieToStrata's emitted CFGs are full of trivial jump-chains.

**Q3 — StrataTest / `stmtsToCFG`: can the lowering's output be coalesced, and
which constructs produce the chains?** **Yes.** `stmtsToCFG`
(`StructuredToUnstructured.lean`) emits coalesceable chains from straight-line
command sequences, `.block`/`.exit` regions, and `ite`-then-sequence joins.
Loop *bodies* coalesce internally but the loop **entry** is never coalesceable —
it is a genuine conditional (distinct targets) and the back-edge gives it ≥2
predecessors, so the loop-contract metadata it carries is never erased (the md
guard is defensively correct but redundant with the 2-predecessor rule for this
producer). On the loop goldens: countUp 5 blocks / 1 removable, gauss 5/1,
nested 9/2; on straight-line `block_exit`, 4 of 5 removable. Roughly ~20% of
blocks are removable inside loop-heavy code, up to ~80% in straight-line code.

### Census table

| Corpus | Files | Procedures | Total blocks | Blocks removable | % removable | Procs w/ coalesceable | Max chain len |
|---|---:|---:|---:|---:|---:|---:|---:|
| EQ-200 | 200 | 3,293 | 206,860 | **79,464** | **38.41%** | 3,293 (100%) | 7 |
| SMACK pilot | 48 | 469 | 52,248 | **170** | **0.33%** | 93 (19.8%) | 3 |
| `stmtsToCFG` goldens | — | 5 | (per-proc, see §4) | countUp 1, gauss 1, nested 2, block_exit 4, ite_seq 1 | ~20–80% | all w/ ≥1 chain | 5 (block_exit) |

EQ chain-length histogram (66,747 maximal chains): len2 = 54,391 (81%), len3 =
12,080 (18%), len4 = 211, len5 = 51, len6 = 8, len7 = 6.
Cross-check: Σ (len−1)·count = 79,464 = total blocks removable.

### Value verdict — optimization vs cosmetic

Coalescing is **a small, real precision improvement on the current SMT path, not
purely cosmetic — but it becomes cosmetic once the already-planned dominator-based
path-condition propagation lands.** It does **not** change the *number* of SMT
queries (obligation count is invariant under merge). Its only verify-path benefit
is reducing false alarms from the per-block path-condition reset in
`extractFromDetCFG` (Section 5). It must **not** touch the CBMC/GOTO path. Its
clearest payoff is **debugging / readability** of the EQ CFGs (38% fewer blocks
to read) and shrinking the proof-corpus block count.

**Recommendation: do not build it as a standalone optimization now.** The verify
benefit is subsumed by the planned dominator pass, and the obligation count
doesn't move. If a cleanup pass is wanted for readability/proof-corpus size,
fold it into the same dominator/natural-loop machinery the CFG loop-elim pass
(`reports/irreducible-cfg-census-2026-06-09.md`) already needs — do not build a
second CFG-analysis framework for it (Section 6).

---

## 2. Coalesce criterion (against the IR's equal-target `condGoto`)

The Core CFG IR (`Strata/DL/Imperative/BasicBlock.lean:32-79`) has **only two**
transfer constructors — `condGoto (p) (lt lf) (md)` and `finish (md)`. There is
**no** single-target goto node. An unconditional branch is *definitionally*
`DetTransferCmd.goto l := condGoto HasBool.tt l l` (BasicBlock.lean:43-44): the
unconditional form is `condGoto` with **`lt == lf`**. Any matcher must test
target equality on a `condGoto`, not look for a distinct `goto` node.

Edge B (label lB) → C (label lC) is **coalesceable** iff ALL hold:

1. **B's transfer is unconditional to C:** `condGoto p lt lf` with `lt == lf == lC`.
   (Surface `goto L;`; in the IR `condGoto (boolConst true) L L`.) A
   distinct-target `condGoto` — whether `branch (c) goto Lt else Lf` or the
   nondet `goto L1, L2` — has two successors and is **not** a B-side.
2. **C has exactly one predecessor across the whole CFG, namely B.** Predecessors
   are not precomputed; derive them by scanning every block's transfer target
   slots. A block referencing lC in *either* slot of its `condGoto` is a
   predecessor. Count **distinct predecessor blocks**: an equal-target
   `condGoto c lC lC` counts lC once.
3. **Not a self-loop:** lB ≠ lC.
4. **C is not the entry:** `cfg.entry ≠ lC` (merging away the entry would lose the
   entry pointer).
5. **Neither B's nor C's transfer carries loop-contract metadata** —
   `MetaData.specLoopInvariant` (`#spec_loop_invariant`) or
   `MetaData.specDecreases` (`#spec_decreases`), attached to loop-entry transfers
   at `StructuredToUnstructured.lean:148-156`. Coalescing across such a transfer
   would erase the loop-header marker downstream passes recover from `md`.

**Merge operation:** new block at lB = `{ cmds := B.cmds ++ C.cmds, transfer :=
C.transfer }` (B inherits C's transfer **verbatim**, including C's metadata);
remove `(lC, C)` from `cfg.blocks`. Precondition 2 guarantees no other block
referenced lC, so no rewrite of other transfers is needed.

Coalesceable edges form **disjoint simple paths** (each coalesceable C has a
unique predecessor; each unconditional B a unique successor). A maximal chain of
m blocks collapses to 1, removing m−1 blocks. Hence **n_blocks_removable =
n_coalesceable_edges = Σ over chains (len−1)** — verified on all 3,293 EQ rows.

### Corpus transfer census (input grammar → IR)

Over the 200 EQ `.core.st`: `goto L;` (→ `condGoto true L L`, unconditional) =
114,154; `goto L1,L2;` (→ nondet `condGoto $k L1 L2`, distinct targets) = 57,147;
deterministic `branch (` = **0**; `return;` (→ `.finish`) in every file. So this
corpus's only B-side candidate is the equal-target `condGoto`. The
`stmtsToCFG`-produced loop-contract md is *absent* in the BoogieToStrata/EQ
corpus (Boogie already lowered loops to gotos upstream), so the precondition-5
guard is vacuous there — but it is load-bearing for the `stmtsToCFG` producer
(Section 4).

---

## 3. Per-corpus census results

Analyzer: `/tmp/claude/cfg-coalesce-analyzer.py` (reuses the brace-depth block
parser + successor extractor from the reducibility analyzer). `--self-test`
passes 4/4 fixtures (chain, diamond, loop, loop-md). `is_unconditional ==
(kind=="goto" and len(set(targets))==1)`; predecessor counting uses
`set(targets)` so an equal-target goto contributes one edge. Both invariants
match the criterion in Section 2.

### EQ-200 — 38.41% removable (heavy)

3,293 procedures, 206,860 blocks, **79,464 removable (38.41%)**. Every procedure
has ≥1 coalesceable edge. 66,747 maximal chains; 81% length-2 (the canonical
SMACK/Boogie `anonN: { …; goto next; }` single-pred/single-succ jump), 18%
length-3, thin tail to length 7. The savings come overwhelmingly from collapsing
huge numbers of short chains, not a few long ones.

Representative procedures:
- `/tmp/claude-503/eq200-cores/EQ_25x1ux2e1e4_out.core.st:anon0` — 2,912 of 7,911 blocks removable (most removable), maxchain 3.
- `/tmp/claude-503/eq200-cores/EQ_cxzwjm5spr1_out.core.st:anon0` — 2,269 of 5,729, maxchain 5.
- `/tmp/claude-503/eq200-cores/EQ_uyg2woc4jxc_out.core.st:anon0` — 521 of 1,298, maxchain 7.
- `/tmp/claude-503/eq200-cores/EQ_4yon4rr0mxl_out.core.st:anon0` — 319 of 772, maxchain 7 (hand-traced: a genuine inlined-method straight-line run).

The length-7 chain in EQ_4yon4rr0mxl was hand-verified link-by-link (every B a
single-target unconditional goto, every C exactly 1 pred, no self-loop, no loop
md, none the entry). EQ_3gff5oopjfl CFG#4 hand-trace confirms the two would-be
merges into a 2-predecessor join block are correctly excluded.

### SMACK pilot — 0.33% removable (~118× sparser)

48 files, 469 procedures, 52,248 blocks, **170 removable (0.33%)**. Only 93/469
procedures (19.8%) have any coalesceable edge; chains cap at length 3 (146 len-2
chains + 12 len-3). The 13 `sv_loops_*` files — the most loop-heavy — produce
**zero** coalesceable edges. Full 94-program pilot projects to ~330–340
removable of ~102k, still ~0.33% (the percentage is a structural invariant).

**Root cause (verified on skipString_harness's 577-block `_bb0`):** SMACK-derived
C CFGs have a strict **alternating-diamond** shape. That CFG has 384 blocks
ending in an unconditional goto *and* 384 blocks with exactly one predecessor —
yet **zero** unconditional edges target a single-pred block. Every unconditional
goto points at a 2-predecessor join; every single-pred block is reached from a
2-target (conditional) goto. The criterion needs unconditional-SOURCE *and*
single-pred-TARGET on the *same* edge; SMACK systematically splits those two
properties onto different edges (`cond-block[2 tgt] → fallthrough[1 pred] →
cond-block[2 tgt] → …`). EQ's Java equivalence harnesses instead emit long
straight-line runs that chain heavily. **The "expect a similar profile to EQ"
hypothesis is disconfirmed by the data** — C-derived control flow is fundamentally
less coalesceable.

Representative: `skipString_harness.core.st` (18 removable / 1,257 blocks),
`JSON_Iterate_harness.core.st` (17 / 1,679), `cjson_cJSON_Parse_harness.core.st`
(14, all len-2).

**Provenance:** `Examples/smack-docker/strata-files/` holds 3,529
`EQ_*.boogie.st` (the EQ corpus in *surface* Boogie form, zero non-EQ, zero `cfg`
headers → 0 analyzer rows; that is the pre-CFG form, not the pilot). The SMACK
numbers rest on 48 separately-translated `.core.st` at
`/tmp/claude-503/smack-corest/` (all 48 `.err` empty — clean translations),
51% of the 94 pilot `.bpl`, covering every loop/branch-heavy category.

---

## 4. `stmtsToCFG` source analysis — which constructs emit coalesceable chains

This is the load-bearing question: the proof corpus / StrataExamples goldens come
through `stmtsToCFG` (`Strata/Transform/StructuredToUnstructured.lean`), *not*
through the BoogieToStrata parser. Verified at file:line below.

| Construct | Transfer emitted | Coalesceable? | Why |
|---|---|---|---|
| `.cmd` straight-line run | accum flushed as `.goto k` (`:46-47`, `:68`) | **Yes** | single-pred/single-succ linear chain |
| `.block l … :: rest` | `(l, {cmds:=[], transfer:=.goto bl md})` (`:90`) | **Yes** (unless md present) | empty trampoline block into body label |
| `.exit l` | `flushCmds … (.goto bk md)` (`:178`) | **Yes** | unconditional jump to the looked-up continuation |
| `.ite c t f` join tail | then/else branches flush `.goto kNext` into the shared join (`:97-98`, via `:68`) | **Yes** | the join's single-pred tail coalesces (`join → end`) |
| `.loop` **body tail** | body flushes `.goto bodyK` (`:135`) | **Yes** | body's last block → measure-decrease block |
| `.loop` **measure-decrease block** | `(ldec, {…, transfer:=.goto lentry})` back-edge (`:132`) | **No** | target `lentry` has ≥2 preds (fallthrough + back-edge) |
| `.loop` **entry** | `.condGoto e bl kNext contractMd` (`:156`, nondet `:164`) | **No** | (a) conditional, distinct targets — not a B-side; (b) ≥2 preds; (c) carries `specLoopInvariant`/`specDecreases` md (`:148-156`) |
| `.finish` end block | `(lend, {cmds:=[], transfer:=.finish})` (`:186`) | **No** (as B) | no successor; *is* coalesceable as a C-target sink |

**Golden examples** (scored by `cfg-coalesce-analyzer.py`):
- **countUp** — 5 blocks, **1 removable**: the single coalesceable edge is body-tail
  `l$_N → measure_decrease$_N`. `loop_entry$` is excluded (2 preds:
  `before_loop$` + `measure_decrease$`); the back-edge `measure_decrease$ →
  loop_entry$` is excluded (2-pred target).
- **gauss** — 5 blocks, **1 removable** (same shape as countUp).
- **nested** — 9 blocks, **2 removable** (one body-tail coalesce per loop level).
- **block_exit** — 5-block straight-line chain, **4 removable** (max chain
  length 5; pure `.cmd`/`.block`/`.exit` straight line).
- **ite_seq** — the join → end tail coalesces (1 removable).
- **nomeasure_loop** — a bare `while` with no measure yields **0** coalesceable
  edges: the back-edge from `l$` gives `loop_entry$` ≥2 preds.

**Trap checked and cleared:** the worried-about shape `condGoto true loop_entry
loop_entry` (which would look unconditional and erase loop md) does **not**
occur — the loop entry is genuinely conditional (distinct targets `bl` vs
`kNext`), so it fails precondition 1 regardless, and the back-edge independently
gives it ≥2 preds. **The loop-md guard (precondition 5) is therefore redundant
with the 2-pred rule for `stmtsToCFG` output** — every loop entry already has ≥2
preds. The guard is defensively correct to keep (a future producer could emit a
single-pred md-bearing transfer), but the 2-pred rule is the load-bearing
exclusion for this producer. **No `stmtsToCFG` coalesce ever erases loop-contract
metadata.**

Net shape: inside loop-heavy code ~20% of blocks are removable (each loop level
contributes exactly the one body-tail link); in straight-line code up to ~80%.

---

## 5. Value assessment — does coalescing matter, and for which consumer?

### (a) SMT verify path — small real precision win, soon cosmetic

- **Obligation count is invariant under coalescing.**
  `Strata/Languages/Core/ObligationExtraction.lean:107-114` (`extractFromDetCFG`)
  folds over each block's `cmds`, and the obligation count = count of
  `assert`/`cover` commands (`extractFromCmd`, `:52-60`). Merging `B.cmds ++
  C.cmds` preserves every command, so the number of SMT queries does **not**
  change. Coalescing is *not* a query-count optimization.
- **But it is not purely cosmetic under the current extractor.**
  `extractFromDetCFG` resets path conditions to the global `pc` **per block**
  (`:109-110`, `init := pc` in the inner fold; comment `:102-106`: "Path
  conditions restart from the global pc for each block independently … obligations
  in block B that depend on assume from block A will fail to discharge, surfacing
  as false alarms"). Coalescing B into its predecessor's command stream lets C's
  asserts see B's `assume`/`init` in their path condition (`extractFromCmd`:
  `assume → pc.addInNewest` `:62`, `init → pc.addEntry` `:64`), which **reduces
  false alarms**.
- **The benefit is already slated to be subsumed.** There is an explicit
  `TODO` at `:106` for dominator-based path-condition propagation, which would
  give every obligation its real dominating path conditions regardless of block
  boundaries — making coalescing's precision benefit **cosmetic** once it lands.

So on the SMT path coalescing is a *temporary* precision improvement (fewer false
alarms under today's per-block reset), not a query-count optimization, and it is
on the chopping block the moment dominator-based propagation arrives.

### (b) CBMC / GOTO path — must NOT coalesce

The CBMC/GOTO consumer wants the real CFG block structure (it does its own
unwinding / block-level reasoning). Coalescing is a verification-path-only concern
and must not touch the GOTO path — the same scope boundary the loop-elim report
draws (`irreducible-cfg-census-2026-06-09.md` §6).

### (c) Debugging / readability / proof-corpus size — the clearest payoff

On EQ, 38% fewer blocks is a large readability win for anyone reading the emitted
CFGs, and it shrinks the proof-corpus block count materially. On SMACK it buys
almost nothing (0.33%). This is the most defensible motivation, and it is
cosmetic by nature.

### Is it worth implementing?

**Not as a standalone optimization right now.** It moves no SMT query count; its
verify-path precision benefit is real but small and is explicitly scheduled to be
made redundant by the dominator pass; and the corpus where it pays off (EQ) is
the equivalence-checking corpus, not the SMACK C-pipeline (0.33%). The honest
framing is: a *cosmetic / corpus-size* pass with a soon-expiring precision side
benefit, not a performance optimization.

---

## 6. If worth implementing — design sketch + shared machinery

A coalescing pass is a `Program → Program` transform over `.cfg` bodies (it
rewrites the in-memory `Imperative.CFG`, never text — no Lean printer builds the
surface `goto`/`return` ops; they are a parse target only). It would slot as a
`PipelinePhase` on `.cfg` bodies, before `evalCFGBody`/`symbolicEval`, gated to
fire only when a CFG actually contains a coalesceable edge.

Per procedure CFG:
1. Build a `label → distinct-predecessor-count` map once by folding over all
   transfers' target slots (`condGoto` contributes `lt` and `lf`, counted as one
   predecessor block when `lt == lf`). O(blocks).
2. Scan for B-side blocks: `condGoto p lt lf` with `lt == lf == lC`, where
   pred_count(lC) == 1, lB ≠ lC, lC ≠ entry, and neither B nor C carries
   `specLoopInvariant`/`specDecreases` md.
3. Assemble maximal chains (disjoint simple paths) and splice each: new block at
   the chain head with all bodies concatenated and the tail's transfer.

**Relationship to the proposed CFG-level loop-elim pass
(`reports/irreducible-cfg-census-2026-06-09.md`):** strong overlap — **they
should share machinery and ideally be one pass family.**
- **Same corpora, same analyzer lineage.** Both this census and the reducibility
  census run over EQ-200 + SMACK pilot, and `cfg-coalesce-analyzer.py` is derived
  from `cfg-reducibility-analyzer.py` (shared brace-depth block parser +
  successor extractor).
- **Same CFG-analysis primitives.** The loop-elim pass needs dominators +
  natural-loop detection (already prototyped in the census analyzer). Coalescing
  needs a predecessor-count map + chain assembly. Both walk every block's
  transfer target slots; the predecessor map coalescing needs is a strict subset
  of the dominator dataflow the loop-elim pass computes. A single
  `CFGAnalysis { dominators, predecessors, naturalLoops }` structure feeds both.
- **Same pipeline slot and scope boundary.** Both are `Program → Program`
  pre-passes on `.cfg` bodies, run before symbolic eval, and both are
  verification-path-only (must not touch CBMC/GOTO).
- **Natural ordering.** Run loop-elim first (it splices acyclic block sequences,
  *creating* fresh single-pred straight-line chains), then coalesce as a cleanup
  pass to collapse them. Coalescing after loop-elim would also tidy the
  loop-elim-emitted blocks for readability.

**Recommendation:** do not build a second CFG-analysis framework for coalescing.
If a cleanup pass is wanted, implement it as a thin consumer of the same
dominator/predecessor/natural-loop machinery the loop-elim pass introduces, run
as a post-loop-elim cleanup phase. Standalone, its ROI does not justify the
framework; bundled, it is nearly free.

---

## 7. Files referenced

Source (all under `/Users/htd/Documents/Strata-smack/`):
- `Strata/DL/Imperative/BasicBlock.lean:32-79` (data model; `:43-44`
  `goto := condGoto tt l l`; only `condGoto`/`finish`).
- `Strata/Languages/Core/Procedure.lean:283` (`DetCFG` binding), `:393-404`
  (`eraseTypes`/`stripMetaData` case only on `condGoto`/`finish`).
- `Strata/Languages/Core/DDMTransform/Grammar.lean:472-509` (surface Transfer
  grammar), `Translate.lean:1707-1784` (surface→IR mapping).
- `Strata/Transform/StructuredToUnstructured.lean:43-188` (the proof-corpus
  producer); `:90` block trampoline `.goto`; `:132` decrease-block back-edge
  `.goto lentry`; `:135` body tail; `:148-156` loop-contract md; `:156`/`:164`
  loop-entry `condGoto`; `:178` `.exit`; `:186` `.finish` end block.
- `Strata/Languages/Core/ObligationExtraction.lean:52-65` (`extractFromCmd`),
  `:107-114` (`extractFromDetCFG` — per-block `pc` reset, `:106` dominator-pass
  TODO).
- `Strata/DL/Imperative/MetaData.lean:333-337` (loop-md keys).

Census artifacts:
- Analyzer: `/tmp/claude/cfg-coalesce-analyzer.py` (`--self-test` 4/4).
- EQ-200: `/tmp/claude/eq200-coalesce.tsv` (3,293 rows; also
  `/tmp/claude/coalesce-corpus.tsv`).
- SMACK pilot:
  `/Users/htd/Documents/Strata-smack/Examples/smack-docker/smack-pilot-coalesce.tsv`
  (469 rows; also `/tmp/claude/smack-pilot-coalesce.tsv`).
- Sample corpus file: `/tmp/claude-503/eq200-cores/EQ_0gt5nr1o5pp_out.core.st`.

Related report:
- `/Users/htd/Documents/Strata-smack/reports/irreducible-cfg-census-2026-06-09.md`
  (CFG-level loop-elim proposal; shares the dominator/natural-loop machinery and
  the `Program → Program` `.cfg` pre-pass slot).
