# htd/smack Branch Cleanup — Design

## Goal

Reduce the additions in PR #1171 (`htd/smack` vs baseline `htd/unstructured-procedure`)
from ~199,575 lines to roughly ~1,500–2,000 lines by removing generated/binary
artifacts and consolidating documentation. The branch's actual code changes
(Lean sources, BoogieToStrata C# changes, pipeline scripts, small test fixtures)
remain unchanged.

## Context

PR #1171 currently shows **+199,575 / -101 / 79 files**. The bulk is:

- ~195,000 lines: 12× SMACK-generated `.bpl` files in `Examples/smack-docker/programs/`
  (each ~16k lines of SMACK prelude). These are reproducible from the matching
  `.c` files via the SMACK Docker toolchain documented in the README.
- ~3,500 lines: 5× `.bc` (LLVM bitcode, binary) and `.ll` (LLVM IR) files.
- ~2,000 lines: 14 markdown documents — design specs, implementation plans,
  experiment results, and per-issue write-ups for bugs that are already fixed
  or already tracked in GitHub issues.
- ~1,400 lines: code/scripts and small test fixtures — these stay.

## Approach

A single cleanup commit on top of the current branch tip. No history rewrite.
The commit deletes generated/binary artifacts, removes redundant docs, adds
a `.gitignore` for the artifact directory, and rewrites
`Examples/smack-docker/README.md` to serve as the pipeline-usage + current-results
doc. A new `Tools/BoogieToStrata/Docs/STATUS.md` captures what's shipped vs.
what's open in BoogieToStrata.

## Files to delete

### Generated artifacts (`Examples/smack-docker/programs/`)

- `aws_array_eq.bpl`
- `aws_byte_cursor_advance.bpl`
- `aws_ring_buffer.bpl`
- `abs_func.bpl`
- `array_sum.bpl`
- `loop_sum.bpl`
- `max_func.bpl`
- `nondet_branch.bpl`
- `pointer_arith.bpl`
- `simple_add.bpl`
- `simple_assert.bpl`
- `swap.bpl`
- `loop_sum.bc`, `loop_sum.ll`
- `pointer_arith.bc`, `pointer_arith.ll`
- `simple_add.bc`, `simple_add.ll`
- Any `*_stripped.bpl`, `*.core.st`, `*.symtab.json`, `*.goto.json`, `*.gb`
  if present (none currently tracked).

### Redundant docs

- `Tools/BoogieToStrata/Docs/BUGS.md`
- `Tools/BoogieToStrata/Docs/aws-c-common-test-results.md`
- `Tools/BoogieToStrata/Docs/boogie-to-strata-verification-experiment.md`
- `Tools/BoogieToStrata/Docs/cfg-emission-design.md`
- `Tools/BoogieToStrata/Docs/issues/cfg-locals-as-out-params.md`
- `Tools/BoogieToStrata/Docs/issues/github-issue-draft.md`
- `Tools/BoogieToStrata/Docs/issues/issue-namespace-collision.md`
- `Tools/BoogieToStrata/Docs/issues/issue-sanitization-collision.md`
- `Tools/BoogieToStrata/Docs/issues/issue-smack-assert-encoding.md`
- `Tools/BoogieToStrata/Docs/issues/issue-type-synonym-comparison.md`
- `Examples/smack-docker/multi-backend-pipeline-design.md`
- `Examples/smack-docker/pipeline-results-comparison.md`
- `docs/superpowers/plans/2026-05-13-boogie-cfg-emission.md`

The empty `Tools/BoogieToStrata/Docs/issues/` directory should also be removed.

## Files to create

### `Examples/smack-docker/programs/.gitignore`

```
*.bpl
*.bc
*.ll
*_stripped.bpl
*.symtab.json
*.goto.json
*.gb
*.core.st
```

`.c` files and `.gitignore` itself remain tracked.

### `Tools/BoogieToStrata/Docs/STATUS.md`

A single document describing the current state of BoogieToStrata. Sections:

- **Shipped**: CFG emission for procedures with gotos, name-collision fixes
  (sanitization + entity-prefix global set), type-synonym chain resolution,
  SMACK `assert_` encoding, `InferModifies` handling, etc.
- **Known issues**: one-line entries for any remaining bugs, each with a link
  to its GitHub issue (e.g. #1148, #1152) for details. No long-form repro
  steps in this doc — those live on the issues.
- **Test fixtures**: brief pointer to `Tools/BoogieToStrata/Tests/*.bpl` and
  the integration test runner.

Keep this doc terse — under ~80 lines.

## Files to modify

### `Examples/smack-docker/README.md`

Already exists (~144 lines). Rewrite as the single pipeline-status + usage doc.
Sections:

1. Overview of the SMACK → BoogieToStrata → Strata verify / CBMC pipeline.
2. How to regenerate `.bpl` from `.c` via Docker (the SMACK invocation).
3. How to run the multi-backend pipeline (`run_pipeline.py --backends ...`).
4. Current verification results — small table snapshot of the 12-program run
   (4 PASS deductive, 7 PARTIAL, 1 WARN; 0 PASS bugFinding; 0 PASS cbmc).
5. Known blockers — one-line entries pointing to GitHub issues. Specifically:
   - CBMC: pipeline still calls `procedureToGotoCtx` (structured-only) for
     CFG bodies; needs `procedureToGotoCtxViaCFG` dispatch.
   - CoreToGoto: inout parameters double-collected as locals (`LExpr.fvar`
     with `ty=none`).
   - Strata #1162 nondet goto type-check (resolved on this branch but
     mention if relevant for context).

## Files to keep unchanged

- All Lean source changes under `Strata/`.
- `Tools/BoogieToStrata/Source/StrataGenerator.cs`.
- `Tools/BoogieToStrata/Tests/*.bpl`, `*.expect`, `*.core.st` (small fixtures
  — ~400 lines total).
- `Tools/BoogieToStrata/IntegrationTests/*`.
- `Examples/smack-docker/{Dockerfile,run_pipeline.py,fix_core_st.py,strip_smack_prelude.py}`.
- 12× `Examples/smack-docker/programs/*.c` files (the original SMACK inputs,
  ~10 lines each).

## Commit

A single commit with message:

```
chore: remove generated artifacts and consolidate docs

Drop SMACK-generated .bpl/.bc/.ll files from Examples/smack-docker/programs/
since they are reproducible from the .c sources via the documented Docker
toolchain. Add a .gitignore so they don't get re-tracked.

Consolidate documentation: replace the per-issue/per-design files with a
single STATUS.md in Tools/BoogieToStrata/Docs/ and a refreshed
Examples/smack-docker/README.md that covers pipeline usage and current
verification results.
```

## Verification

1. `git diff --stat htd/unstructured-procedure..HEAD` shows <2,000 additions.
2. `git ls-files Examples/smack-docker/programs/` lists only `.c` files plus
   `.gitignore`.
3. `Examples/smack-docker/run_pipeline.py --help` still works.
4. `Examples/smack-docker/README.md` describes the pipeline accurately and
   instructions are runnable from a clean clone.
5. `Tools/BoogieToStrata/Docs/STATUS.md` exists and references open issues
   #1148 / #1152 (or whichever remain open at cleanup time).

## Out of scope

- No code changes to Lean, C#, or Python sources.
- No modifications to the test suite or build configuration.
- No history rewrite or force-push.
- No changes to the existing `Tools/BoogieToStrata/Tests/` fixtures.
