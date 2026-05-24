# A3: PcInversion.lean aggressive cleanup (post-W3 plateau)

## Plan (stub)

W3 reduced `Strata/Backends/CBMC/GOTO/PcInversion.lean` 1,580 → 1,400 LoC
(three patterns, see `W3_pcinversion_local_audit.md`). User wants ≤1,200 LoC
for breathing room — i.e. another ≥200 LoC removed.

This audit looks at the residual 1,400 LoC for:

- **A. Dead lemmas.** Each named declaration grepped across `Strata/` and
  `StrataTest/`; usage count = 1 ⇒ candidate for inlining/removal.
- **B. Specialised helpers.** Re-examine W3's *declined* opportunity 4
  (Decl/Assn helpers): can a *single* helper covering both Decl and Assn
  cases break even where two separate helpers couldn't?
- **C. Top theorems as thin wrappers.** Are
  `declPcInversion_of_translator` / `assignPcInversion_of_translator` still
  needed alongside their `_abbrev` siblings, or can they be inlined?
- **D. Stale comments.** Round-archaeology comments after W3's restructuring.
- **E. Long proofs.** Any single-block proof >50 lines that factors cleanly?

### Constraints

- Only `Strata/Backends/CBMC/GOTO/PcInversion.lean` and this report.
- `declPcInversion_of_translator_abbrev` / `assignPcInversion_of_translator_abbrev`
  signatures unchanged (called by `_v6`/`_v7`).
- No new `axiom`, no `sorry`. Build green every commit.

### Tier targets

- **Tier 1**: ≤1,000 LoC final.
- **Tier 2**: 1,000–1,300 LoC.
- **Tier 3**: stuck >1,300 LoC.

(Filled in below as the audit proceeds.)
