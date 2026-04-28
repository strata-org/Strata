# Rebase Plan: `jhx/python-static` onto `origin/main`

## Status: COMPLETED (Option B)

Rebased on 2026-04-28. 17 commits squashed into 3 logical phases, rebased onto `origin/main` (1ce75d0e).

| Commit | Description |
|--------|-------------|
| `7699fba8` | Add pyFeatures command and SSA IR design |
| `37a5ff13` | Add Python-to-SSA translator |
| `5618957e` | Add demand analysis, well-formedness checker, and SSA namespace |

Backup of original 17 commits preserved at `jhx/python-static-backup`.

### Conflict resolutions applied
- **StrataMain.lean (Phase 1)**: `pyTranslateCommand` was removed on main; kept main's state, added only `pyFeaturesCommand`. Kept main's `pyInterpretCommand` in command list.
- **StrataMain.lean (Phase 2)**: Merged command registrations from both sides (`pyInterpretCommand` from main + `pyBlockifyCommand`/`pyToSSACommand` from branch).
- **StrataMain.lean (Phase 3)**: Applied cleanly (namespace move from `Blockify`/`PythonToSSA`/`SSAFormat` to `SSA.Translate`/`SSA.Format`, removed `pyBlockifyCommand`).

---

## Original Situation

| Metric | Value |
|--------|-------|
| Branch commits | 17 (all by Joe Hendrix) |
| Commits behind `origin/main` | 158 |
| Merge base | `5125660` — 2026-03-28 "Add exhaustive tracking for Python class methods (#698)" |
| Branch date range | 2026-03-28 → 2026-03-31 (4-day burst) |
| Branch last touched | ~4 weeks ago |

## What the Branch Does

17 commits building a Python→SSA IR pipeline for static analysis, in three logical phases:

### Phase 1: Feature analysis & IR design (commits 1–5)
- `pyFeatures` command for Python feature-usage statistics
- SSA IR data types, pretty-printer, test suite (23 positive, 8 negative tests)
- Experiment report & design docs

### Phase 2: SSA translator (commits 6–10)
- Two-phase Python→SSA translator with TDD harness
- isinstance dispatch, try/except, `with` statement support
- Decouple from Blockify, replace v1 with strict block-argument SSA
- Performance improvements (Fwd struct, valInstrIdx, merge errors)

### Phase 3: Demand analysis & cleanup (commits 11–17)
- Free-variable / demand analysis with accumulator pattern
- SSA well-formedness checker
- Namespace reorganization → `Strata.Languages.Python.SSA.*`

## Files Touched

- **82 files changed**, 8,255 insertions, 1 deletion
- **Only conflict file: `StrataMain.lean`** — the single file modified on both sides
- All other files are **new** (added by this branch, never touched by main)

### New Lean modules (the core work)
```
Strata/Languages/Python/FeatureUsage.lean
Strata/Languages/Python/SSA/IR.lean
Strata/Languages/Python/SSA/Translate.lean
Strata/Languages/Python/SSA/Format.lean
Strata/Languages/Python/SSA/Check.lean
Strata/Languages/Python/SSA/Blockify.lean
StrataTest/Languages/Python/SSATest.lean
```

### Ancillary files
- `docs/PythonSSA.md`, `experiment_report.md`, `feature_plan_summarize.md`, `README_static.md`
- `coverage_check.py`, `tally_features.py`
- 57 test files under `StrataTest/Languages/Python/SSA/`

## Conflict Analysis

### `StrataMain.lean` (the only conflict)

**Main's changes** (522 insertions, 425 deletions across 28 PRs):
- Heavy restructuring: import reordering, `module` keyword added, new `ParsedFlags` struct
- Removed imports: `Strata.Languages.Laurel.LaurelFormat` (gone from repo)
- Added: Boole commands, Concrete Core interpreter, `transform` command, `--path-cap`, `--profile`, etc.
- `Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator` → `AbstractToConcreteTreeTranslator`

**Branch's changes** to StrataMain.lean:
- Added 3 imports (`FeatureUsage`, `SSA.Translate`, `SSA.Format`)
- Added 2 command definitions (`pyFeaturesCommand`, `pyToSSACommand`)
- Registered both commands in the Python `commandGroups` list

**Resolution**: The branch's additions are purely additive and self-contained. During rebase, take main's version of StrataMain.lean and then re-apply:
1. The 3 new imports (at appropriate position in main's sorted import list)
2. The `pyFeaturesCommand` and `pyToSSACommand` definitions
3. The command registrations in `commandGroups`

## Toolchain

| | Version |
|---|---|
| Branch | Lean 4.27.0 |
| Main | Lean 4.29.1 (upgraded in PR #967) |

The branch's new `.lean` files already use the `module` keyword (required by 4.29), so
the toolchain bump should not require changes to the new files. However, any API
differences between 4.27 and 4.29 may cause build errors that need fixing after rebase.

## Recommended Rebase Strategy

### Option A: Squash to 1 commit, then rebase (recommended)

Since there are no open PRs referencing individual commits, and the 17 commits form a
single coherent feature, squashing simplifies the rebase to a single conflict resolution:

```bash
# 1. Create a backup branch
git branch jhx/python-static-backup

# 2. Soft-reset to merge base, creating one big diff
git reset --soft $(git merge-base origin/main HEAD)

# 3. Commit as a single squashed commit
git commit -m "Add Python SSA IR pipeline: feature analysis, translator, demand analysis, and well-formedness checker"

# 4. Rebase onto origin/main (single conflict in StrataMain.lean)
git rebase origin/main

# 5. Resolve StrataMain.lean conflict:
#    - Accept main's version as base
#    - Add the 3 imports to the import block
#    - Add pyFeaturesCommand and pyToSSACommand definitions
#    - Add both commands to the Python commandGroups list
# 6. Build and test
```

### Option B: Squash into 3 logical commits, then rebase

If preserving some commit history is preferred, squash into the 3 phases:

1. **"Add pyFeatures command and SSA IR design"** (commits 1–5)
2. **"Add Python→SSA translator"** (commits 6–10)
3. **"Add demand analysis, well-formedness checker, and SSA namespace"** (commits 11–17)

Only commit 1 touches `StrataMain.lean` imports, and commit 3 registers the commands,
so conflicts would appear in those two commits.

```bash
git rebase -r origin/main   # after interactive squash into 3
```

### Option C: Rebase all 17 commits as-is

This would require resolving `StrataMain.lean` conflicts potentially multiple times
(commits 1, 9, and 17 all touch it). Not recommended given the heavy refactoring
main has done to that file.

## Risk Assessment

| Risk | Severity | Notes |
|------|----------|-------|
| `StrataMain.lean` conflict | **Low** | Branch changes are additive; main's version is the base |
| Lean 4.27→4.29 API breaks | **Medium** | New files use `module` already, but `HashMap`/`Array` APIs may have shifted |
| Removed `LaurelFormat` import | **None** | Branch doesn't import it; only main removed it |
| Python.PySpecPipeline changes | **None** | Branch doesn't modify it |
| Test breakage from main changes | **Low** | SSA tests are self-contained with expected-output files |

## Post-Rebase Checklist

- [ ] Resolve `StrataMain.lean` conflict (see instructions above)
- [ ] Verify `lean-toolchain` says `v4.29.1` (from main)
- [ ] Run `lake build` to catch any Lean 4.29 API issues
- [ ] Run SSA test suite to verify expected outputs still match
- [ ] Verify `pyFeatures` and `pyToSSA` commands work end-to-end
- [ ] Decide whether to keep ancillary files (`experiment_report.md`, `feature_plan_summarize.md`, etc.) or drop them from the PR
