# Implementation plan: CFG-native loop-elimination pass (`CFGLoopElim.lean`)

**Date:** 2026-06-10
**Status:** Design-locked, compile-ready. Not yet implemented (machine was busy with concurrent proof builds; this is the no-build deliverable to execute when clear).
**Branch (target):** htd/smack
**Closes:** BACKLOG #29 (evalCFGBlocks loop-with-invariant OOM) + the 15 PASS-? evaluator-gap cases (BACKLOG *CFG-eval loop-handling*).
**Effort:** 2–3 days.

## Why this pass exists

`evalCFGBlocks` (`Strata/Languages/Core/ProcedureEval.lean:133-149`) is a fuel-only
worklist with no back-edge awareness; `evalCFGStep` (`:106-130`) forks both
successors on a symbolic `condGoto` (`:130`). On a `.cfg` body with a loop
back-edge, it **unrolls** the loop until fuel runs out — heap grows one `Env`
per pseudo-iteration → the #29 OOM. The structured path never OOMs because
`loopElimPipelinePhase` runs the acyclic havoc-and-cut on `.loop` Stmts
(`LoopElim.lean:117-203`); the CFG path has no equivalent — `LoopElim.lean:249`
passes `.cfg` bodies through unchanged.

**Confirmed by the effect study (`reports/cfg-loopelim-effect-2026-06-09.md`):**
- **Framing A (net-new CFG pass), not B.** The 310-of-313 loop-bearing procs are
  born `.cfg` from the SMACK/DDM translator (`translateCFGProcedure`,
  `Translate.lean:1808/1826`) and never pass through `stmtsToCFG`, so reordering
  `loopElim` before lowering fixes nothing.
- **The naive cut is UNSOUND.** `havoc M; assume ¬G; goto kNext` drops VC2
  (`arbitrary_iter_maintain_invariant`) → a wrong-invariant program spuriously
  PASSes. The pass must emit the FULL structured recipe.
- **Default invariant = `true`.** Only 3/313 loops carry
  `specLoopInvariant`/`specDecreases` metadata; the other 310 are contract-less
  SMACK CFGs. `havoc M; assume true` is the sound no-invariant abstraction.

## The recipe to replicate (from `LoopElim.lean:73-104`)

For loop with guard `G`, invariants `I` (default `[true]` if none), measure `D`
(optional), modified-set `M`:

```
assert(I);                 -- VC1: entry
assume(I);
if (G) {
  havoc(M); assume(G); assume(I);
  [decreases:] init(m_old); assume(m_old == D); assert(!(m_old < 0));  -- VC3
  <BODY>
  assert(I);               -- VC2: maintenance  ← the one the naive cut drops
  [decreases:] assert(D < m_old);                                      -- VC4
  havoc(M); assume(¬G); assume(I);   -- exit state
}
assert(Q);                 -- whatever followed the loop
```

In CFG terms, the loop region (header block + body blocks + back-edge) is
replaced by a straight-line sequence of blocks ending in a `.goto` to the loop's
exit continuation (`kNext`), with no back-edge.

## CFG data model (from `BasicBlock.lean` + `ProcedureEval.lean`)

- `DetCFG = CFG String (DetBlock String Core.Command Core.Expression)`.
- `CFG` has `entry : String` and `blocks : List (String × Blk)`.
- `DetBlock` has `cmds : List Cmd` and `transfer : DetTransferCmd`.
- `DetTransferCmd` is `condGoto cond lt lf md | finish md` (a one-target goto is
  `condGoto true L L` — equal targets; see `BasicBlock.lean:43-44`).
- Loop-header transfer carries `specLoopInvariant`/`specDecreases` metadata when
  present (`StructuredToUnstructured.lean:146-151`).

## Tasks

### Task 1 — Dominator + natural-loop-region analysis (`CFGLoopElim.lean`)

**Files:** Create `/Users/htd/Documents/Strata-smack/Strata/Transform/CFGLoopElim.lean`.

- [ ] Compute the dominator tree of a `DetCFG` rooted at `cfg.entry` via iterative
  dataflow to fixpoint (`dom(entry)={entry}`, `dom(n)={n} ∪ ⋂_{p∈preds(n)} dom(p)`).
  Reuse the dominator code prototyped in the `w7gh4f4nk` worktree (~40 LoC) if
  recoverable; otherwise reimplement (it's standard).
- [ ] Identify back-edges: an edge `u → v` where `v` dominates `u`. Census proved
  every loop is reducible single-header, so each back-edge defines exactly one
  natural loop: header `v`, body = `{u} ∪ {nodes that reach u without going
  through v}`.
- [ ] Per natural loop, compute: header label, body block set, the modified-set
  `M` (union of `HasVarsImp`-modified vars across the body blocks' cmds, minus
  body-block-local `init`s — mirror `LoopElim.lean:131-133`), the exit
  continuation `kNext` (the header's non-loop successor), and the contract
  (`specLoopInvariant`/`specDecreases` from the header transfer md, or `[true]`).

**Test (unit, no SMT):** `#guard_msgs`-style `#eval` dumping detected loop regions
for the Loops.lean countUp/gauss/nested CFGs (obtained via `singleCFG`). Confirm
1 region for countUp, 1 for gauss (with measure), 2 for nested.

### Task 2 — Acyclic region synthesis (full recipe)

- [ ] Given a natural-loop region + contract, synthesize the replacement blocks
  implementing the **full** recipe above. Reuse the exact label scheme and
  command constructors from `LoopElim.lean:144-203` (`entry_invariant_*`,
  `arbitrary_iter_maintain_invariant_*` = VC2, `measure_lb_*`, `measure_decrease_*`,
  `not_guard_*`, etc.) so CFG-form goldens match structured-form labels.
- [ ] **VC2 is mandatory** — emit `assert(I)` after the body blocks. This is the
  defect the prototype had; gate a test on its presence.
- [ ] Default `I := [(\"\", HasBool.true)]` when the header transfer carries no
  `specLoopInvariant`. Default measure: none (skip VC3/VC4).
- [ ] Rewrite `cfg.blocks`: remove the loop's body+header blocks, splice in the
  synthesized acyclic blocks, redirect the header's predecessors to the new
  entry block, and ensure the new exit block `.goto`s `kNext`. Remove the
  back-edge. Result must satisfy: no edge `u → v` with `v` dominating `u`
  (no back-edge) — i.e. a DAG.

**Test:** `cfgHasBackEdge (rewritten) == false` on countUp/gauss/nested.

### Task 3 — Pipeline phase wiring

**Files:** Modify `/Users/htd/Documents/Strata-smack/Strata/Languages/Core/Verifier.lean`.

- [ ] Define `cfgLoopElimPipelinePhase : PipelinePhase` mirroring
  `loopElimPipelinePhase`, operating on `.cfg` bodies only (`.structured`
  passthrough — the inverse of `LoopElim.lean:249`).
- [ ] Slot it in `transformPipelinePhases` immediately AFTER `loopElimPipelinePhase`
  (`Verifier.lean:893` region). Gate: fire only when a `.cfg` body has a back-edge
  (cheap pre-check), so non-loop CFGs are untouched.
- [ ] **Scope boundary:** this lives in `corePipelinePhases` (the verification
  path). The CBMC GOTO entry (`coreToGotoFilesDispatch`) does NOT call
  `corePipelinePhases`, so the GOTO path keeps the real cyclic CFG for
  unwinding. Verify by grep that no GOTO-path entry invokes the new phase.

### Task 4 — Build + measure (the part that needs a clear machine)

- [ ] `lake build Strata.Transform.CFGLoopElim` then `lake build Strata` —
  **cap parallelism, single-thread, run when no other heavy builds are active**
  (per the `smt-test-memory-pressure` memory note; the EQ-200 sweep hit 28.5 GB).
- [ ] **Acceptance gate (the load-bearing measurement, never yet run):** under
  `gtimeout 60` + `set_option maxHeartbeats 400000`, single-thread Z3, verify
  Loops.lean countUp/gauss/nested in CFG form (via the `verifyCFG` helper) and
  gate on **verdict-set equality with the structured form** — NOT merely
  `cfgHasBackEdge` toggling. The structured goldens are in Loops.lean
  (`:45-104` etc.).
- [ ] Run the #29 reproducer `loopGuardPrecondPgm`
  (`CFGForm/FunctionPreconditions_Part4.lean`) under the same guarded harness.
  Expected: reaches a bounded verdict (no OOM/exit-137), RSS stays well under the
  box limit. **This is the measurement that died on transient 503s three times
  (`w2bl3s9l1`, `wikpaagrw`, `w7gh4f4nk`) — it must actually complete here.**

### Task 5 — Regression + soundness

- [ ] Full CFGForm suite (`StrataTest/Languages/Core/Examples/CFGForm/`) — the
  loop-bearing leaves should now converge to structured-form verdicts; the F3
  cosmetic-asymmetry leaves (#28) may also align (loop-elim normalizes the
  path-condition shape). Re-bless goldens where the convergence is real.
- [ ] **Soundness gate:** construct a deliberately-wrong-invariant test
  (`while c invariant (1 == 0) { ... }`); confirm the CFG form FAILs VC2
  (`arbitrary_iter_maintain_invariant`), matching the structured form. If it
  PASSes, the VC2 emission is broken — this is the exact defect that sank the
  prototype.
- [ ] Re-run the mem-capped EQ-200 sweep (workflow-queue budget, not concurrent)
  to quantify how many TIMEOUTs the loop-elim unblocks.

## Verification checklist

- `lake build Strata` green.
- countUp/gauss/nested: CFG-form verdict-set == structured-form verdict-set.
- `loopGuardPrecondPgm`: bounded verdict, no OOM (closes #29 — the measurement).
- wrong-invariant test: CFG form FAILs VC2 (soundness).
- CBMC/GOTO path unchanged (grep confirms phase not in that entry).
- 15 PASS-? programs: re-classify (would-be-PASS → PASS, would-be-FAIL →
  PARTIAL/FAIL) — the projected 68/15/11 → ~77/0/17 matrix shift.

## Files referenced

- `/Users/htd/Documents/Strata-smack/Strata/Transform/LoopElim.lean` (recipe `:73-104`, impl `:117-203`, `.cfg` passthrough `:249`)
- `/Users/htd/Documents/Strata-smack/Strata/Languages/Core/ProcedureEval.lean` (`evalCFGStep:106-130`, `evalCFGBlocks:133-149`)
- `/Users/htd/Documents/Strata-smack/Strata/DL/Imperative/BasicBlock.lean` (DetCFG / DetTransferCmd model)
- `/Users/htd/Documents/Strata-smack/Strata/Transform/StructuredToUnstructured.lean` (`:146-151` contract metadata on header transfer)
- `/Users/htd/Documents/Strata-smack/Strata/Languages/Core/Verifier.lean` (`transformPipelinePhases` `:893`)
- `/Users/htd/Documents/Strata-smack/reports/cfg-loopelim-effect-2026-06-09.md` (the study that locked this design)
- `/Users/htd/Documents/Strata-smack/StrataTest/Languages/Core/Examples/Loops.lean` (structured goldens for the acceptance gate)
