# SI1 — ShrinkAudit follow-up

Read-only audit of `docs/historical/CoreToGOTO_ShrinkAudit.md` (2026-05-22)
against the current state of `htd/unstructured-to-goto`
(HEAD `d10422c2b`, 2026-05-23).

## Methodology

For each recommendation in `ShrinkAudit.md` I:

1. Located the targeted file/lemma/lines in the current tree.
2. Searched `git log` for cleanup commits on the relevant file or
   keyword (e.g. "v1", "v2", "v3", "preservation combinator",
   "patcher lemmas", "OpDesc", "inj_subst", "_h_inj").
3. Read worker reports under `docs/_workers/*_report.md` (S1-S3,
   L1-L4, W1-W6, A1-A6) where they touch the audit's items.
4. Spot-checked the current state with `grep`/`wc` to verify whether
   the recommended change is in place, partial, or absent.

Status codes:

* **applied** — done; the recommendation is implemented.
* **partially applied** — some part landed; the residual is identified.
* **superseded** — file or design moved; recommendation no longer fits.
* **still actionable** — not done; could be done now.
* **declined** — investigated and decided against.

## 1. Per-recommendation status table

### 1.1 — Dead code (ShrinkAudit §1, §5)

| Recommendation | Status | Evidence |
|---|---|---|
| §1.1 / §5: Drop dead `_v1` / `_v2` / `_v3` of `coreCFGToGotoTransform_forward_simulation_concrete` | **applied** | Commit `5aab65ada refactor(goto-correct): drop dead v1/v2/v3 of concrete forward sim`. Subsequent A4 commits `b6f465f12` / `710ca1360` then inlined `_v4` into `_v5` and `_v5` into `_v6` (-486 LoC). Current file (`CoreCFGToGOTOConcrete.lean`, 710 LoC) only exposes `_v6` (line 188) and `_v7` (line 517). `_v6` is also called via `_v7`'s body at line 696. |
| §1.2: `wellFormedTranslation_to_translatorBridgeHyps` (bridge v1) — inline or trim | **declined / still actionable (~50 LoC)** | The v1 bridge still exists at `TranslatorBridgeHypsDischarge.lean:80` and is called only by the v2 form at line 319. The audit said "could be inlined into bridge_v2 OR kept as a private helper." A6's `2c9f1516e cleanup(A6): trim role/round archaeology in TranslatorBridgeHypsDischarge` did some trimming (-39 LoC) but kept the v1/v2 split intact. Inlining v1 into v2 would still net ~50 LoC. |
| §1.3: `everyGotoTargetIsLabelMapEntry_of_translator` (wf-form) | **declined** | The wf-form at `GotoTargetProvenance.lean:526` is still present (now ~40 LoC because of A5's trim). It's still referenced only by the axiom test (`GotoTargetProvenanceAxioms.lean:18`). The audit flagged it as a 50-LoC removal *if* the axiom-test entry is also dropped. The fact that no cleanup worker dropped it suggests an implicit decision to keep the wf-form available as a downstream interface. |
| §1.4: Drop unused `_h_inj` parameters in `InstructionLookups.lean` | **applied** | Commit `2d7b40db8 refactor(goto-correct): drop unused _h_inj params per audit (S1)`. Worker S1 report at `docs/_workers/S1_drop_h_inj_params.md`. `grep -n _h_inj Strata/Backends/CBMC/GOTO/InstructionLookups.lean` returns nothing. |
| §1.5: Round-2 `coreCFGToGotoTransform_wellFormed` markdown sketch + tristate naming concern | **superseded** | The audit flagged this as "not removable; the round-2 sketch is documentation." A1's WF split refactored `CoreCFGToGotoTransformWF.lean` from ~6900 LoC to a 142-LoC re-exporter file plus six modules under `CoreCFGToGotoTransformWF/`. The markdown-block `_wellFormed` sketch is no longer in the tree (`grep` returns no live theorem of that name). The tristate confusion (`_/_nonempty/_strengthened`) is now binary (`_nonempty` + `_strengthened`), addressed implicitly by A1's restructure. |

### 1.2 — Duplication (ShrinkAudit §2)

| Recommendation | Status | Evidence |
|---|---|---|
| §2.1 / §3.1: Generic predicate-preservation combinator (`InstrPredicateClosed`) for NoDead + GotoTargetProvenance | **applied** | L2 designed and L3 built `BlocksFoldClosed.lean` (commits `1eec598fc`, `54b3143a2`, `3b32345ef`); A5 then trimmed both consumers further. `BlocksFoldClosed.lean` is currently 465 LoC; `NoDead.lean` is 317 LoC (down from 716, -399); `GotoTargetProvenance.lean` is 567 LoC (down from 1116, -549). Combined: **NoDead + GotoTargetProvenance went from 1832 LoC → 884 LoC (-948 LoC)**, exceeding the audit's 600-800 LoC projection. Combinator overhead (465 LoC) means net saving across the three files is ~483 LoC. |
| §2.2: Patcher-lemma duplication between WF and `GotoTargetProvenance.lean` (private patch_one_*) | **still actionable (~50 LoC)** | Both files still define their own private `patch_one_other_index` and `patch_foldl_target_preserved_when_idx_unique_in_tail`: see `CondGotoClosures.lean:105` / `:118` and `GotoTargetProvenance.lean:144` / `:192`. The duplication has shrunk because A1's WF split moved the WF-side copies into `CondGotoClosures.lean`, but the bytes still live in two places. The audit's 140-LoC estimate was for a larger set of lemmas; the residue is closer to 50 LoC because A5 already removed `patch_foldl_target_at_last`, `patch_foldl_target_some_in_list`, `last_occurrence_split` from `GotoTargetProvenance.lean` (per A5 pass B). |
| §2.3 / §3.3: Per-operator skeleton in `ExprTranslationPreservesEvalBoolInt.lean` (OpDesc) | **applied** | L4 (`OpDesc full refactor`) shipped the `BoolIntBinOpDesc` + 2 generics design. A2's six-pass trim further reduced the file. Current size: **1198 LoC** (down from the audit baseline of ~2246 LoC, **-1048 LoC**). The audit's 600-800 LoC projection was beaten. See `docs/_workers/L4_opdesc_full_refactor.md` and `docs/_workers/A2_b3_trim.md`. |
| §2.4 / §6.1: `Option.some.inj` boilerplate in `CmdProvenance.lean` (`inj_subst` macro) | **applied** | Worker S2 report at `docs/_workers/S2_inj_subst_macro.md`. Macro is in `Strata/Backends/CBMC/GOTO/Tactics.lean:~12`. `grep -c Option.some.inj CmdProvenance.lean` is now **0** (was 11). 10 `inj_subst` invocations active; CmdProvenance is now 304 LoC (vs audit's 372 LoC baseline, **-68 LoC** including A6's archaeology trim). |
| §2.5: Six `Cmd_toGotoInstructions_*_ok` shape theorems | **declined (audit-flagged "not investigated deeply")** | All six (`init_det`, `init_nondet`, `set_det`, `set_nondet`, `assert`, `assume`) still live in `CoreCFGToGotoTransformWF/Preservation.lean`. The audit said "refactoring may not save much without a tactic that synthesises the conjunction shape." No cleanup worker took it on. Estimated saving: small; would need a non-trivial tactic. |

### 1.3 — Shrinkability via abstraction (ShrinkAudit §3)

| Recommendation | Status | Evidence |
|---|---|---|
| §3.2: `CmdEmitsLhs` field unification on `CmdEmittedAt`'s four lhs-shaped constructors | **still actionable (~80-150 LoC)** | `CoreCFGToGOTOInvariants.lean:145` still has the 7-constructor `inductive CmdEmittedAt` with no shared `CmdEmitsLhs` record. The audit explicitly called this "load-bearing; should be done in coordination with a planned round; not a free-lunch refactor." S2's `inj_subst` macro absorbed the immediate downstream pain, reducing the urgency. |
| §3.4: Single `LiftThroughFold` / `foldlM_preserves` combinator | **partially applied / superseded** | `BlocksFoldClosed` (L3) provides exactly this lift for **predicates over array-of-instructions**. The audit's broader recommendation (lift any `P : β → Prop` through any `foldlM`) was not done as a standalone Mathlib-style lemma — `grep foldlM_preserves` returns no top-level lemma. PcInversion (999 LoC) didn't adopt the BlocksFoldClosed combinator (A3 used a different design). The size_eq / locationNum chains in WF were declined as "Class C" by L3. **Residual: maybe 100-200 LoC if PcInversion's bodyPcCovered chain were forcibly ported, but A3 already chose a different route and got the file under 1k.** |

### 1.4 — Documentation duplication (ShrinkAudit §4)

| Recommendation | Status | Evidence |
|---|---|---|
| §4: Centralise round/Tier prose; trim docstrings to 5-line purpose statements | **applied** | A6 (`docs/_workers/A6_smaller_files_cleanup.md`, ~220 LoC of archaeology trimmed across 11 files) plus `ce47317e4 cleanup: strip round/worker archaeology from proof comments`, plus W2 (`9beff3efa refactor(goto-correct): strip stale running commentary in WF file (W2)`), plus the A1-A6 per-file trims. `grep` for "Round-7", "round-7", "round-8", "Tier 1", "Tier 2 deliverable" across `Strata/Backends/CBMC/GOTO/` returns **zero hits in active code** (a few residual mentions in BlocksFoldClosed and Bisim are factual current-state references, not archaeology). The "WellFormedTranslation is forward-only" caveat is still in 2-3 docstrings but each instance is now ~5 lines, not 30. Audit projection: ~80 LoC saved. Realised: substantially more (A6 alone ~220, A2 ~25, A3 ~76, A5 ~280 of doc/comment trim). |

### 1.5 — Tactic-level shrinks (ShrinkAudit §6)

| Recommendation | Status | Evidence |
|---|---|---|
| §6.1: `inj_subst` macro for `CmdProvenance.lean` | **applied** | Same as §2.4 above. |
| §6.2: `case_contra_on_type` macro for impossible-type cases | **still actionable (~50-80 LoC)** | `grep case_contra_on_type Strata/Backends/CBMC/GOTO/Tactics.lean` returns nothing — the macro was not added. A6's CmdProvenance trim (`156c1feb2`) reduced the file 351 → 304 LoC (-47), so some sites may have already been compressed manually. The audit's pattern still recurs in `CoreCFGToGotoTransformWF/Shape.lean` and `CoreCFGToGotoTransformWF/StepPreservation.lean`. |
| §6.3: Generic `cases h_emit using CmdEmittedAt.casesOnLhsAt` view | **still actionable (~40-60 LoC)** | No `casesOnLhsAt` view defined. The pain is now muted by `inj_subst`, so the marginal gain is smaller than the audit estimated. |
| §6.4: `omega` instead of explicit `Nat.le_of_not_lt` chains | **still actionable (~5-15 LoC)** | `grep -n Nat.le_of_not_lt NoDead.lean GotoTargetProvenance.lean` returns 3 hits across the two files (lines 81, 103 in NoDead; line 151 in GotoTargetProvenance). Down from ~28 hits the audit implied (one per `_preserves_*` lemma × ~14 lemmas). Most of the original sites were absorbed when L3 collapsed the per-step lemmas into one `BlocksFoldClosed` instance. The 3 surviving sites are inside the two `BlocksFoldClosed.ofPushSafe` bottom helpers (`hasNoDead'_push`, `hasNoDead'_append_two` and the GotoTargetProvenance manual instance) — small wins remain. |
| §6.5: `decide` instead of explicit `cases h_eq` for InstructionType inequalities | **applied (in spirit)** | The pattern `by intro instr h; rw [h]; decide` is now standard in `BlocksFoldClosed.ofPushSafe` instances (8 lines per instance × 2 = 16 sites in NoDead's `instBlocksFoldClosed_HasNoDead'` alone). Manual `cases h_eq` blocks for `InstructionType.LOCATION ≠ .GOTO` etc. were absorbed in the L3/A5 refactors. |

## 2. What's still actionable

Net of the above, the still-actionable items are short. With current
file sizes (not the audit's stale baselines):

| Item | LoC | Risk | Worth pursuing now? |
|---|---|---|---|
| **§1.2** Inline bridge_v1 into bridge_v2 in `TranslatorBridgeHypsDischarge.lean` | ~50 | low | **Maybe.** Single-file mechanical change; the v1 bridge is 1-line-delegate-fodder. Counterargument: keeping v1 is cheap once the doc archaeology is gone (post-A6), and v1's `WellFormedTranslation`-shaped statement is pedagogically useful as an "old shape" exhibit. Skim-then-decide. |
| **§1.3** Drop wf-form `everyGotoTargetIsLabelMapEntry_of_translator` if axiom test goes too | ~40 | low | **Probably leave.** Axiom test gives a smoke check on a slightly different shape; the cost is 40 LoC of theorem + 4 LoC of test. |
| **§2.2** Promote private patch_one_* lemmas into a shared `PatcherLemmas.lean` (or expose from WF) | ~50 | low | **Yes**, if doing any other GOTO-side cleanup. Cheap win, removes a real duplication. |
| **§3.2** `CmdEmitsLhs` record unification on `CmdEmittedAt`'s 4 lhs-shaped constructors | ~80-150 | medium | **Leave.** Touches `CoreCFGToGOTOInvariants.lean` + several downstream consumers. With `inj_subst` already in place, the call-site pain is gone; only the constructor field count would shrink. Not a free lunch. |
| **§6.2** `case_contra_on_type` tactic macro | ~50-80 | low-medium | **Maybe.** Another small Tactics.lean addition. The pattern still recurs in WF/Shape and WF/StepPreservation. Easy 50 LoC if you can prove the macro robust to hypothesis-name variation. |
| **§6.3** `CmdEmittedAt.casesOnLhsAt` recursor view | ~40-60 | medium | **Leave.** Custom recursors add cognitive load; with `inj_subst`, the case-block compression is from 5-6 to 3 lines (not 1-2). The audit's claimed 40-60 LoC saving assumes near-total absorption that probably won't materialize. |
| **§6.4** `omega` in 3 surviving `Nat.le_of_not_lt` sites | ~10 | low | **Yes.** Trivial. Almost a one-line per site change. |

**Total still-actionable, low-risk:** ~110 LoC of mechanical
simplification (§1.2 + §2.2 + §6.4) plus §6.2 if you want a new tactic
macro.

**Total still-actionable, medium-risk:** another ~120-200 LoC across
§3.2 / §6.3, but neither is a free lunch and the call-site pain has
already been absorbed.

The **big-ticket items the audit projected** — §1.1 dead-code dump
(~440 LoC), §2.1 predicate combinator (~700 LoC), §2.3 OpDesc
(~700 LoC), §4 doc trim (~80 LoC) — are all done, with realised
savings exceeding the audit's projections (the audit said
2,500-3,500 LoC across all items; the actual cleanup over 2026-05-22 →
2026-05-23 was a similar order of magnitude across the worker chain,
plus three structural refactors the audit hadn't quantified: A1's WF
split, A3's PcInversion trim, and W6's dead-lemma sweep).

## 3. Anything the audit missed

Things the audit didn't list, surfaced by walking the current state:

1. **PcInversion's `BlocksFoldClosed` opportunity.** The audit's §3.4
   said `LiftThroughFold` would touch "WF + NoDead + GotoTargetProvenance."
   It missed PcInversion (999 LoC, the biggest non-WF GOTO-correctness
   file outside the WF tree). A3 chose a different design and reached
   Tier 1, but it's worth flagging that PcInversion still has its own
   inlined `cmdsFoldlM`/`blocksFoldlM` prefix scaffolding (per A3 pass
   7). Whether porting it to `BlocksFoldClosed` would be net-negative
   or net-positive after A3 is unclear; A3's report doesn't say it was
   evaluated. **Estimated upside: 50-150 LoC if achievable, but
   non-trivial because PcInversion's predicate is binary
   (`BodyPcCovered` couples instructions array with PC range).**

2. **W4's stale-hypothesis findings.** Worker W4
   (`docs/_workers/W4_stale_hypotheses.md`) identified three unused
   parameters in WF and dropped them. The audit's §1.4 only caught
   `_h_inj`; W4 caught `h_run`, `h_fresh_dom`, `Env`. A future audit
   pass could re-grep for unused hypotheses with the same methodology
   — likely not many left, but the discipline is now established.

3. **Patcher chain still has direct `Imperative.patchGotoTargets` /
   `patchesFoldlM` lemmas in two files** (`NoDead.lean:152-241`,
   `GotoTargetProvenance.lean:294-502`). Combining them via a
   `PatchPreservesPredicate` typeclass parallel to `BlocksFoldClosed`
   could save ~50-100 LoC, but the patcher's reverse-direction
   reasoning in `GotoTargetProvenance` is genuinely asymmetric — the
   audit was right to call this out as "patcher-specific reverse-target
   stuff stays as-is" (§2.1 parenthetical). Probably not worth
   pursuing.

4. **`SteppingBridgesDischarge.lean` (357 LoC) was not audited.** The
   audit only mentioned this file in passing (§4 doc duplication).
   Worker C had built it and worker A6 trimmed -46 LoC of archaeology.
   Spot-check: 12 per-constructor handlers each ~25-30 LoC; structurally
   they're "case-split on `Imperative.SteppingBridge.<constructor>` then
   discharge", which **could** in principle factor through a per-bridge
   typeclass. But this is a much smaller pain than the 13-operator B3
   case the audit's §3.3 addressed. Likely not worth pursuing.

5. **Worker reports under `docs/_workers/` are themselves ~50 KB of
   cleanup-of-cleanup-of-cleanup archaeology** — useful as a record
   but also large. Many describe work superseded by later workers
   (e.g., L2's design plan was superseded by L3's actual port and
   A5's further trim; W5's audit was superseded by W6 doing the
   deletions). A future "consolidate worker reports into a single
   CHANGELOG.md" could trim ~30 KB of redundancy from
   `docs/_workers/`. Not LoC of proof code, but maintenance burden.

## 4. Verdict

**`docs/historical/CoreToGOTO_ShrinkAudit.md` has been substantially
exhausted.** Of the 17 distinct recommendations:

* **9 fully applied** (§1.1, §1.4, §1.5-superseded, §2.1, §2.3, §2.4,
  §4, §6.1, §6.5).
* **3 partially / declined-with-reason** (§1.2, §1.3, §3.4).
* **5 still actionable** but each is small, low-risk, and would
  collectively net at most ~200-300 LoC (§1.2, §2.2, §3.2, §6.2-6.4).

The audit's central thesis — that ~2,500-3,500 LoC could come out of
the round-6/7/8 surface — was validated and exceeded. The largest wins
predicted (dead `_v1`/`_v2`/`_v3`, predicate-preservation combinator,
operator-descriptor refactor, doc archaeology) all landed.

**Recommendation: retire `docs/historical/CoreToGOTO_ShrinkAudit.md`.**

It has served its purpose. Move it to a clearly-named "completed audit"
status in any future docs index, or strike it through. The five
still-actionable items above can be rolled forward into a single short
follow-up note (or just held in an issue tracker) — they don't warrant
a 30 KB audit's worth of context anymore.

If you want a successor audit, the natural target is the **WF tree**
(`Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF/*.lean`, currently
~6,720 LoC across 6 files). The audit explicitly said "the round-1-5
work in `CoreCFGToGotoTransformWF.lean` is largely out of scope for
this audit." A1 split that file into 6 pieces, but each is still ≥800
LoC and each was post-split rather than post-cleanup. A fresh
shrinkability pass on those 6 files (with the now-built combinators
and macros to draw on) could plausibly find another 1-2k LoC of
compressible code.
