# A1 — Split & Cleanup of `CoreCFGToGotoTransformWF.lean`

**Status:** stub plan
**Worker:** A1
**Base commit:** `a012a1c01` (W6-final)
**Target file:** `Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean` (6,665 LoC)
**Predecessors:** W4 (params), W5 (audit), W6 (deletion = 437 LoC), L3 (combinator).

## Goal

Get every Lean file in the GOTO directory to ≤ 1.5k LoC. The WF
file is 6,665 LoC = 4.4× over the limit. Use cleanup AND split
freely.

## Plan (live; will be amended as I work)

### Phase 0 — baseline & audit (this commit)

* Verify starting build green; record axioms of `_v6`/`_v7`.
* Catalogue every section break, structural boundary, and likely
  cleanup candidate. Estimate LoC for each.

### Phase 1 — cleanup passes (single-file)

Aim for as much LoC reduction as possible before splitting, so the
splits work on clean material. Candidates per the brief:

* **A. Single-caller lemmas.** Inline lemmas used exactly once.
* **B. Aggressive simp library.** Identify high-value simp tags.
* **C. Combinator extension for size_eq chain.** Re-examine L3's
  Class C verdict. If a paired-invariant combinator works,
  ~200-400 LoC.
* **D. Per-cmd shape lemma abstraction.** Possibly 7+ near-identical
  cmd-shape lemmas.
* **E. Patcher reverse-direction lemmas.** Cross-check internal
  redundancy.

### Phase 2 — split passes (multi-file)

Natural boundaries (all in `Strata/Backends/CBMC/GOTO/`):

1. `CoreCFGToGotoTransformWF/Lookups.lean` — labelMap helpers,
   hashMap conversions, basic infrastructure.
2. `CoreCFGToGotoTransformWF/CmdShape.lean` — per-Cmd shape lemmas.
3. `CoreCFGToGotoTransformWF/FoldPreservation.lean` — cmdsFoldlM/
   blocksFoldlM/patcher chain.
4. `CoreCFGToGotoTransformWF/LayoutClosures.lean` — `*_of_translator`
   closures.
5. `CoreCFGToGotoTransformWF.lean` (top-level remains) — top-level
   construction, strengthened theorem, public API.

### Discipline

* Lake build green at every commit.
* `_v6`/`_v7` axioms unchanged.
* Public API of `coreCFGToGotoTransform_wellFormed_strengthened`,
  `_decompose`, `_wellFormed_nonempty`, `coreCFGToGotoInitState`,
  `wellFormedTranslation_of_shadow`, `CoreCFGToGotoTransformShadow`
  preserved byte-for-byte.

## Pre-state (to fill in)

* WF file: 6,665 LoC.
* Other GOTO/.lean: TBD.

## Per-pass results

(Will append.)

## Tier verdict

(Pending.)
