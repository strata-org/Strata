# WF2 — SI1 follow-up small actionable items

Worker WF2 applying the 5 small still-actionable items from
`docs/_workers/SI1_shrink_audit_followup.md` §2.

Branch base: `htd/unstructured-to-goto` HEAD `87670ec22`.

## Plan

Five items, each evaluated independently:

### Item 1 — §1.2: Inline bridge_v1 into bridge_v2
- File: `Strata/Backends/CBMC/GOTO/TranslatorBridgeHypsDischarge.lean`
- Action: Inline `wellFormedTranslation_to_translatorBridgeHyps` into
  the v2 caller; preserve v2 public signature.
- Expected: ~50 LoC saving.
- Disposition: **TBD** (skim-then-decide).

### Item 2 — §2.2: Promote private patcher lemmas
- Files: `GotoTargetProvenance.lean` (lines ~144 / ~192) and the
  WF tree CondGotoClosures.lean (off-limits to WF2).
- Action: Skip — WF1 owns the WF tree. No public win possible
  without touching WF.
- Disposition: **Skip / defer to WF1**.

### Item 3 — §6.4: omega in 3 surviving Nat.le_of_not_lt sites
- Files: `NoDead.lean` (lines ~81, ~103) and
  `GotoTargetProvenance.lean` (line ~151).
- Action: Replace `Nat.le_of_not_lt h_lt` with `omega` where the
  resulting goal is reachable.
- Expected: ~10 LoC saving (or formatting churn).
- Disposition: **TBD** (apply if substitution succeeds).

### Item 4 — §6.2: case_contra_on_type macro
- File: `Strata/Backends/CBMC/GOTO/Tactics.lean`.
- Action: Add a macro that case-splits on `instr.type`, contradicts
  the impossible cases via `decide` or `cases`. Apply only to
  non-WF consumers (CmdProvenance.lean if any sites remain).
- Expected: 0-50 LoC.
- Disposition: **TBD** (check if any non-WF surviving sites exist).

### Item 5 — §1.3: drop wf-form everyGotoTargetIsLabelMapEntry_of_translator
- File: `Strata/Backends/CBMC/GOTO/GotoTargetProvenance.lean` (~line 526).
- SI1 said probably leave.
- Disposition: **Skip per SI1 recommendation.**

## Build/axioms baseline

- `lake build` green at `87670ec22`.
- `_v6` / `_v7` axioms unchanged at the start of the work.

## Per-item results

(Filled in as items land.)

## Final disposition + LoC totals

(Filled in at the end.)
