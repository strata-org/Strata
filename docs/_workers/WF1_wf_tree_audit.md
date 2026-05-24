# WF1 — WF tree shrinkability audit + cleanup

## Context

SI1's follow-up audit (`SI1_shrink_audit_followup.md`) identified the
WF tree (`Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF/*.lean`,
~6,720 LoC across 6 files) as the natural successor target. None of
the 6 split files had received a post-A1-split shrinkability pass with
the now-built abstractions (`BlocksFoldClosed`, `inj_subst`, `OpDesc`)
to draw on.

SI2's feasibility analysis (`SI2_a_b_simplification.md`) sketched
specific candidates that touch this tree — (b-1) binary-property
combinator, (b-3) `blocksFoldlM_layout_*` cons-step skeleton, (b-4)
`block_step_intro` macro — and warned about the L3 calibration
(projected +1,200-1,600 LoC → delivered +201).

## Tier outcome

**Tier 3 — 100 LoC removed (1.5% of the WF tree).**

Below SI1's optimistic 1-2k LoC projection, in line with SI2's
realistic ceiling and the L3 empirical calibration. The WF tree is
substantially as compressed as it can be without changing the
underlying proof shape.

## What was applied

### Pass 1 — Drop `coreCFGToGotoBlockStep_location_at_pc` (-100 LoC)

The two theorems
`coreCFGToGotoBlockStep_location_at_pc` and
`coreCFGToGotoBlockStep_location_at_pc_with_labels` (in
`StepPreservation.lean`) were byte-for-byte parallel except the
latter additionally provides `instr.labels = [label]`. The single
caller of the weaker form (`FoldAndDecompose.lean:241`) only needed
the type witness; switching it to the stronger form costs one
unused-conjunct underscore. Net: -100 LoC.

Commit: `b0ccbbf22`.

This matches SI2 candidate (a-2) — "drop `_at_pc`, keep
`_at_pc_with_labels`" — though SI2 estimated ~180 LoC saving by
applying the same pattern across 3 theorems. I only found the one
true duplicate; `finish_at_pc` and `condGoto_at_pc` are *not*
parallel to `_with_labels` (they project different post-conditions).

## What was attempted and reverted

### `block_step_intro` macro (SI2 candidate b-4)

Designed and implemented a Lean 4 macro to capture the recurring
6-line `unfold/simp/generalize/match` boilerplate that opens
~10 `coreCFGToGotoBlockStep`-shape proofs in `StepPreservation.lean`.

**Blocker:** macro hygiene. The macro expansion contained
`Strata.coreCFGToGotoBlockStep`, but Lean 4's declarative macro
hygiene injects fresh `✝` suffixes on identifiers, producing the
unresolvable `Strata.coreCFGToGotoBlockStep✝` at the use site. This
would require switching from declarative `macro` to the elaborator-
level `elab` API with explicit `Lean.mkIdent`, which is a heavier
implementation than the ~40 LoC of net savings justifies.

Reverted; macro removed from `Tactics.lean`. Documented here as a
known dead-end for any future worker considering the same approach.

## What was investigated and declined

### (b-1) Binary-property combinator for paired
### (`size_eq`, `locationNum_eq_index`)

`Preservation.lean` has ~500 LoC of paired lemmas where each
property is proved separately for the same translator step
(`emitLabel_preserves_size_eq` + `emitLabel_preserves_locationNum_eq_index`,
etc.). SI2 sketched a `BlocksFoldClosed2` combinator that bundles both
predicates.

**Why declined:** L3's outcome on the unary `BlocksFoldClosed`
(projected +1,200-1,600 LoC, delivered +201 LoC) suggests the same
abstraction-tax pattern would apply: combinator infrastructure
(~150-200 LoC) plus per-call wiring (`h_admitted` plumbing,
`abbrev` vs `def` issues, eta-expansion of implicit binders) eats
most of the per-file savings. SI2 explicitly noted the medium-high
risk and "the 200-300 LoC saving estimate has the same risk profile
that turned L3's 1,200 LoC projection into a 201 LoC outcome."

The 1-2 weeks of refactor effort would deliver realistic ~100-200
LoC saving. Not worth the risk against the established codebase.

### `cmdEmittedAt_<shape>` wrapper compression

The 6 wrappers (`cmdEmittedAt_assert`, `cmdEmittedAt_assume`,
`cmdEmittedAt_init_det`, `cmdEmittedAt_init_nondet`,
`cmdEmittedAt_set_det`, `cmdEmittedAt_set_nondet`) in
`Shape.lean` are shallow plumbing into the inductive
`CmdEmittedAt.<shape>_emit` constructor. Each wrapper's body is
already a one-liner; the cost is the theorem signature
(~15 LoC each).

**Why declined:** Inlining each wrapper into its single caller
(`cmdEmittedAt_<shape>_of_toGotoInstructions`) saves the signature
(~15 LoC) but adds back the constructor's argument list at the
call site. Net is roughly a wash. SI1 §2.5 already flagged this:
"refactoring may not save much without a tactic that synthesises
the conjunction shape." With `inj_subst` already absorbing the
downstream pain, the marginal value is negligible.

### Import audit

Spot-checked `Shape.lean`'s `public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOCorrect`
— suggests an unusual layering (typically `Correct` depends on
`Invariants`, not vice versa). Tried removing the import; build
failed because `ExprTranslationPreservesEval` is defined in
`Correct.lean`. Restored the import. Layering inversion is real
but fixing it is out of scope for a shrinkability pass — it
requires moving `ExprTranslationPreservesEval` from `Correct.lean`
to `Invariants.lean`, which is a structural refactor with broader
downstream impact.

### Documentation strip

Doc-comment ratio per file: 11-17% of LoC. Not unreasonably high;
stripping would harm navigability. W2 already stripped the round
archaeology; what remains is genuine "what does this lemma do" docs.
Skipped.

### Per-property step-fold preservation chains

SI2 noted that `Preservation.lean` (1,023 LoC), `StepPreservation.lean`
(1,290 LoC), and `FoldAndDecompose.lean` (1,192 LoC) each have
multiple parallel preservation chains. Attempting to absorb them
into a unified abstraction has the same L3-style risk profile.
The chains are real structural work — each property's preservation
through each translator step is a distinct fact, even when the
proof skeletons look parallel.

## Verification

- `lake build` green at `b0ccbbf22`.
- `_v6` and `_v7` axioms unchanged: `[propext, Classical.choice, Quot.sound]`.
- All public API of the WF tree preserved
  (`coreCFGToGotoTransform_wellFormed_strengthened`,
  `coreCFGToGotoTransform_decompose`, `wellFormedTranslation_of_shadow`,
  `coreCFGToGotoInitState`, `CoreCFGToGotoTransformShadow`).

## Summary of the LoC breakdown

| File | Pre-WF1 | Post-WF1 | Δ |
|---|---:|---:|---:|
| `BlockBodyClosures.lean` | 862 | 862 | 0 |
| `CondGotoClosures.lean` | 1,412 | 1,412 | 0 |
| `FoldAndDecompose.lean` | 1,192 | 1,193 | +1 (one-line caller change) |
| `Preservation.lean` | 1,023 | 1,023 | 0 |
| `Shape.lean` | 941 | 941 | 0 |
| `StepPreservation.lean` | 1,290 | 1,190 | -100 (location_at_pc deletion) |
| `CoreCFGToGotoTransformWF.lean` (re-export) | 142 | 142 | 0 |
| **Total** | **6,862** | **6,763** | **-99** |

## Verdict

The WF tree is mostly as compressed as it can be. SI1's "1-2k LoC
plausibly findable" projection was optimistic; SI2's 80-85%-structural
estimate was the more accurate prediction.

The remaining ~6,763 LoC is real structural work:
- 144 named declarations (post-W6 dead-code sweep — none are dead).
- ~12% docstrings (already trimmed by W2 + A6).
- Per-property preservation chains that could in principle be
  absorbed by a binary combinator, but with high abstraction-tax
  risk and modest realistic savings.

**Recommendation:** retire active shrinkability hunting on this tree.
The proof has converged. Future LoC reductions, if pursued, would
need to come from changing the underlying proof structure (e.g.,
different `WellFormedTranslation` predicate shape, alternate
translator design) rather than from cleanup of the existing surface.
