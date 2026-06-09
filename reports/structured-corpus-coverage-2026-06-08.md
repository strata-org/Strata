# Structured Corpus Coverage for `structuredToUnstructured_sound`

**Date:** 2026-06-08
**Branch under review:** `htd/structured-to-unstructured-small-step-proof`
**Worktree:** `/Users/htd/Documents/Strata-small-step-proof`
**Top-level theorem:** `structuredToUnstructured_sound` at `/Users/htd/Documents/Strata-small-step-proof/Strata/Transform/StructuredToUnstructuredCorrect.lean:7294`

---

## 1. TL;DR — Three Direct Answers

1. **How many current benchmarks satisfy the preconditions required by the proof?**
   - **~563 procedures** across the project's existing test corpora satisfy `Block.simpleShape` plus the related side-conditions checkable from text (`noFuncDecl`, no `.call`, no nondet `.ite`, no `.loop`).
   - This breaks down as: **400** in EQ200 (caveat: see below — these are SMACK labelled-block stubs that pass the regex but are not "authentically structured"), **129** in `StrataTest/Languages/Core/Examples` (the canonical pool), **9** in `Examples/*.core.st`, **9** in `Examples/expected/*.core.st`, **2** in CBMC fixtures, **14** in `wt-test`. Out-of-band side conditions (`uniqueInits`, store-clean ρ₀, NoGenSuffix, five `WellFormedSemanticEval*` hypotheses) are not statically checkable from `.core.st` text and are not asserted in this number.
   - **If we exclude the SMACK labelled-block confound in EQ200**, the number of *authentically* hand-written structured procedures satisfying the precondition is **~163**, concentrated almost entirely in `StrataTest/Languages/Core/Examples`.

2. **How many are structured programs?**
   - **~881 procedures** are classified "structured" across the existing parsed corpora (EQ200: 600, Lean Core Examples: 149, Lean Boole tests: 59, `Examples/*.core.st`: 14, `Examples/expected/*.core.st`: 9, `wt-test`: 22, CBMC: 2, `StructuredToUnstructuredTests.lean` inline: 7 — though those 7 are direct AST literals, not parsed surface syntax).
   - **Authentic** structured programs (excluding SMACK labelled-block-as-nested-block false positives in EQ200): **~281 procedures** from hand-written sources. The Boole tests (59) require a separate Boole→Core lowering pass to be eligible substrate for the Core soundness theorem.

3. **Is there a collection of structured programs we can pass through the structured-to-unstructured transformation for testing?**
   - **Yes.** The strongest ready-made pool is `/Users/htd/Documents/Strata-smack/StrataTest/Languages/Core/Examples/*.lean` — **47 files / 128 extracted `#strata` blocks / 149 structured procedures, of which 129 satisfy the precondition.**
   - This pool already imports `Strata.Transform.StructuredToUnstructured`, feeds programs through `Imperative.stmtsToCFG` via `#eval`, and verifies output against `#guard_msgs` goldens. `Loops.lean` is the canonical exemplar.
   - Secondary substrate: `Examples/*.core.st` (file-on-disk, 9 procs admit) and `Examples/expected/*.core.st` (9/9 — already post-loopElim, the exact shape `stmtsToCFG` consumes).
   - **Untapped:** `Tools/BoogieToStrata/Tests/*.bpl` is ~70% structured Boogie (Bubble, IfThenElse1, Gauss, McCarthy-91, Quantifiers, etc.); a one-time `dotnet`-run translation pass would expand the structured pool by ~30 procedures.

---

## 2. Proof Preconditions

The soundness theorem `structuredToUnstructured_sound` (`StructuredToUnstructuredCorrect.lean:7294`) gates on a structural shape predicate plus a battery of out-of-band side conditions.

### 2a. The shape predicate: `Block.simpleShape`

Defined at `/Users/htd/Documents/Strata-small-step-proof/Strata/DL/Imperative/Stmt.lean:215-235` (mutual block: `Stmt.simpleShape` line 217, `Block.simpleShape` line 230). The doc-comment block at lines 204-213 states the design intent: "no nondeterministic .ite, no .loop of any kind (the .loop arm discharges by contradiction)".

**Admitted statement shapes:**
- All five atomic `Cmd` constructors: `.init`, `.set`, `.assert`, `.assume`, `.cover` — including havoc-style `.nondet` RHS in init/set (`.cmd _ => true` unconditionally)
- `.ite (.det e) tss ess _` — deterministic ITE with both branches recursively `simpleShape`; non-empty else IS allowed
- `.block` — recurses into the body via `Block.simpleShape`; arbitrarily nested labelled blocks admitted
- `.exit` — unconditionally true
- `.funcDecl` — admitted by `simpleShape`, but rejected by the separate `noFuncDecl` side condition
- `.typeDecl` — unconditionally true

**Rejected statement shapes:**
- `.loop _ _ _ _ _ => false` — uniformly rejects all loops (with/without invariants, det/nondet guard, with/without measure)
- `.ite .nondet _ _ _ => false` — only deterministic guards admitted

**Note on `.call`:** The `Cmd` inductive on this branch (`Cmd.lean:52`) has only `init`, `set`, `assert`, `assume`, `cover`. There is no `.call` constructor; calls are eliminated by an earlier pass before this transform runs. So "is `.call` admitted?" is not a question `simpleShape` answers — but text-level `call` statements in raw Boogie/Core surface syntax indicate the file is pre-callElim.

### 2b. Out-of-band side conditions on the same theorem

From the theorem signature:
- `Block.noFuncDecl ss = true` — no `.funcDecl` anywhere
- `Block.uniqueInits ss` — every variable initialized by `.init` across all nesting is unique
- `∀ x ∈ Block.initVars ss, ρ₀.store x = none` — initialized vars fresh in start store
- `∀ ident, ρ₀.store ident = none` — entire start store empty
- `ρ₀.hasFailure = false`
- `∀ gen', Block.userLabelsDisjoint ss gen'` — user labels don't collide with generated ones
- Three `NoGenSuffix` hypotheses on `Block.initVars`, `transformBlockModVars`, `Block.getVars`
- Five `WellFormedSemanticEval*` hypotheses on `ρ₀.eval`: Bool, Val, Def, ExprCongr, Var
  - (Skeptic note: the inputs prose said "four"; the theorem signature shows five. The components list enumerates them correctly.)

These are all semantic/runtime conditions not derivable from `.core.st` text. The classifier necessarily ignores them.

### 2c. What the text-level classifier checks

`/tmp/claude-503/structured-shape-classifier.py` flags four classes derivable from surface syntax:
- **C1-loop:** any `while` keyword → `.loop`, rejected
- **C2-nondet-ite:** `if (*)` or `if *` → nondeterministic guard, rejected
- **C7-call:** any `call` statement → not in this `Cmd` dialect's constructors
- **C8-funcDecl:** any `function`/`func` declaration → forbidden by `noFuncDecl`

Self-test on four required fixtures (5 procedures): all matched expectations.

---

## 3. Per-Corpus Breakdown

| # | Corpus | Path | Files | Procs | Structured | CFG | Struct ∧ Precondition | Notes |
|---|---|---|---:|---:|---:|---:|---:|---|
| 1 | **Lean Core Examples (#strata DSL)** | `/Users/htd/Documents/Strata-smack/StrataTest/Languages/Core/Examples/*.lean` | 47 (128 #strata blocks) | 151 | 149 | 0 | **129** | **Canonical pool.** Already imports `Strata.Transform.StructuredToUnstructured` and uses `#guard_msgs` goldens. 20 fail-cases: 7 C1-loop, 12 C7-call, 1 C8-funcDecl — useful as negative tests. |
| 2 | Examples top-level (.core.st smoke) | `/Users/htd/Documents/Strata-smack/Examples/*.core.st` | 13 | 18 | 14 | 3 | **9** | Hand-written demos in Core surface syntax. 5 fail (2 C1-loop, 3 C7-call). Best small file-on-disk pool. |
| 3 | Examples/expected (transform goldens) | `/Users/htd/Documents/Strata-smack/Examples/expected/*.core.st` | 7 | 9 | 9 | 0 | **9** | Already post-loopElim/callElim — exactly the shape `stmtsToCFG` consumes. Includes `LoopSimple.loopElim` and `TwoLoops.loopElim`. |
| 4 | CBMC backend fixtures | `/Users/htd/Documents/Strata-smack/Strata/Backends/CBMC/tests/*.core.st`, `StrataTest/Backends/CBMC/contracts/*.core.st` | 2 | 2 | 2 | 0 | **2** | Tiny but clean. |
| 5 | wt-test transient artifacts | `/Users/htd/Documents/Strata-smack/wt-test/strata_*/` | 6 | 222 | 22 | 10 | **14** | SMACK-emitted helpers (`__SMACK_init_func_memory_model`, etc.). 8 struct-fail are all C7-call. Ad-hoc, mostly trivial. |
| 6 | EQ200 SMACK corpus (cores) | `/tmp/claude-503/eq200-cores/*.core.st` | 200 | 12,671 | 600 | 3,293 | **400** ⚠️ | **CAVEAT.** SMACK output is labelled-block-tree CFG (`_exit: { anon0: { ... } }`). Classifier reads nested `.block` as structured but in Strata reality these are emitted by the labelled-block CFG path. **Treat 400 with skepticism — they are flattened-CFG-via-labelled-blocks, not authentically structured.** 200 fail with C7-call. 8,778 spec-only. |
| 7 | reports/issue-3-mwe-15procs | `/Users/htd/Documents/Strata-smack/reports/issue-3-mwe-15procs.core.st` | 1 | 15 | 0 | 15 | 0 | All explicit cfg/goto. |
| 8 | StructuredToUnstructuredTests inline AST | `/Users/htd/Documents/Strata-smack/StrataTest/Transform/StructuredToUnstructuredTests.lean` | 1 | 7 | 0 (n/a) | 0 | 0 | Direct `Imperative.Stmt` AST literals — not parsed surface syntax. All 7 are `.loop`-rooted intentional metadata-preservation tests; by inspection none satisfy `simpleShape`. |
| 9 | Lean Boole tests | `/Users/htd/Documents/Strata-smack/StrataTest/Languages/Boole/*.lean` | 29 | 59 | 59 | 0 | **44** | **Caveat:** Boole language, not Core. Requires Boole→Core lowering before stmtsToCFG. Boole's `for` not recognized by classifier regex — true loop count is higher; 44 is optimistic. |
| **—** | **Totals (all parsed corpora)** | | **306** | **13,153** | **855** | **3,321** | **607** | |
| **—** | **Totals excluding EQ200 confound** | | **106** | **482** | **255** | **28** | **207** | |
| **—** | **Totals excluding EQ200 *and* Boole (Core-eligible only)** | | **77** | **423** | **196** | **28** | **163** | |

### Skipped corpora (not classified)

| Corpus | Path | Files | Reason |
|---|---|---:|---|
| smack-docker strata-files | `Examples/smack-docker/strata-files/*.boogie.st` | 3,529 | Boogie surface, not Core. Same SMACK provenance — expect 0% authentically structured. |
| smack-docker raw boogie | `Examples/smack-docker/boogie-files/*.bpl` | 3,529 | Above 20-file translation threshold. Same SMACK provenance — expect 0% structured. |
| smack-docker pilot programs | `Examples/smack-docker/programs/*.bpl` | 94 | Above 20-file threshold. Same SMACK provenance — expect 0% structured. |
| **BoogieToStrata translator unit tests** | `Tools/BoogieToStrata/Tests/*.bpl` | 43 | **HIGHEST-VALUE UN-CLASSIFIED.** Per FindCorpora notes ~70% structured (Bubble, IfThenElse1, Gauss, McCarthy-91, Quantifiers, BooleanQuantification, DivMod, Implies, Lambda, NestedLoops while-version, etc.). One-time dotnet-run pass would expand the structured pool by ~30 procedures. |
| BoogieToStrata IntegrationTests duplicates | `Tools/BoogieToStrata/IntegrationTests/bin/Debug/net8.0/*.bpl` | 43 | Build-output copy of Tests/. Skip. |

---

## 4. Recommended Test Corpus

**Primary recommendation:**

```
/Users/htd/Documents/Strata-smack/StrataTest/Languages/Core/Examples/*.lean
```

- 47 files, 128 extracted `#strata` blocks, 149 structured procedures, **129 satisfy the soundness precondition**.
- Already integrated with `Strata.Transform.StructuredToUnstructured` — `Loops.lean` imports the transform module, defines `#strata` programs with `while`/`invariant`/`decreases`, and verifies post-transform CFG via `#eval Std.format (singleCFG …)` against `#guard_msgs` goldens.
- 20 fail-cases (7 C1-loop, 12 C7-call, 1 C8-funcDecl) double as negative-test fixtures.
- Already in-repo, already in CI, no translation step required.

**Secondary substrate (file-on-disk):**

```
/Users/htd/Documents/Strata-smack/Examples/*.core.st
/Users/htd/Documents/Strata-smack/Examples/expected/*.core.st
```

- `Examples/*.core.st`: 9 structured procedures admit (across 7 of 13 files: SimpleProc, DoubleTwice/Double, HeapReasoning subset, IrrelevantAxioms/TestF, ProcedureTypeError/SumPositive, SafeBvOps, SarifTest, TypeError/foo). Cleanly hand-written Core surface syntax.
- `Examples/expected/*.core.st`: 9/9 admit — these are post-loopElim goldens (including `LoopSimple.loopElim` and `TwoLoops.loopElim`), exactly the shape `stmtsToCFG` consumes downstream.

**One-time expansion (untapped):**

```
/Users/htd/Documents/Strata-smack/Tools/BoogieToStrata/Tests/*.bpl
```

- 43 hand-rolled translator-unit-test inputs, ~70% use structured `while`/`if`. Translating through `BoogieToStrata.csproj` (one `dotnet` invocation per file or via the existing IntegrationTests harness) would yield ~30 additional structured procedures in Core surface syntax.

**Do NOT use for structured input:**

- EQ200 (`/tmp/claude-503/eq200-cores/`), `Examples/smack-docker/strata-files/`, `Examples/smack-docker/boogie-files/`, `Examples/smack-docker/programs/`, `wt-test/`. These are all SMACK-derived, exclusively flat-CFG/labelled-block output. Per project memory `project_cfg_emit_order_cosmetic`, 195/200 EQ200 files render as backward-flow gotos. The 400 EQ200 hits the classifier reports as "structured-OK" are labelled-block CFG that the regex misreads as nested `.block` — they cannot serve as authentic structured-program test inputs.

---

## 5. Files Referenced

**Lean (proof side):**
- `/Users/htd/Documents/Strata-small-step-proof/Strata/Transform/StructuredToUnstructuredCorrect.lean:7294` — `structuredToUnstructured_sound`
- `/Users/htd/Documents/Strata-small-step-proof/Strata/Transform/StructuredToUnstructuredCorrect.lean:4204,5558,7204` — related forward-simulation lemmas
- `/Users/htd/Documents/Strata-small-step-proof/Strata/DL/Imperative/Stmt.lean:204-213` — design-intent doc comment
- `/Users/htd/Documents/Strata-small-step-proof/Strata/DL/Imperative/Stmt.lean:215-235` — `Stmt.simpleShape` / `Block.simpleShape` mutual block (key lines: 217, 230)
- `/Users/htd/Documents/Strata-small-step-proof/Strata/DL/Imperative/Cmd.lean:52` — `Cmd` inductive (no `.call` constructor)

**Corpora (substrate):**
- `/Users/htd/Documents/Strata-smack/StrataTest/Languages/Core/Examples/*.lean` — 47 files, recommended primary
- `/Users/htd/Documents/Strata-smack/StrataTest/Languages/Core/Examples/Loops.lean` — canonical exemplar
- `/Users/htd/Documents/Strata-smack/Examples/*.core.st` — 13 files, file-on-disk secondary
- `/Users/htd/Documents/Strata-smack/Examples/expected/*.core.st` — 7 files, post-loopElim goldens
- `/Users/htd/Documents/Strata-smack/StrataTest/Languages/Boole/*.lean` — 29 files, requires lowering
- `/Users/htd/Documents/Strata-smack/Tools/BoogieToStrata/Tests/*.bpl` — 43 files, untapped
- `/Users/htd/Documents/Strata-smack/StrataTest/Transform/StructuredToUnstructuredTests.lean` — inline AST literals

**Tooling:**
- `/tmp/claude-503/structured-shape-classifier.py` — classifier
- `/tmp/claude-503/eq200-cores/` — EQ200 input set
- `/tmp/claude-503/eq200-classification.tsv` — classification output
- `/tmp/claude-503/extract-strata.py` — `#strata` block extractor (Lean → .core.st)

**Project memory (for context):**
- `project_cfg_emit_order_cosmetic` — explains why EQ200/SMACK output is uniformly CFG-shape
- `project_str_unstr_simple_shape_floor` — htd/structure-to-unstructure-correct simpleShape baseline
