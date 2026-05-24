# A3: PcInversion.lean aggressive cleanup (post-W3 plateau)

## Verdict: Tier 1 (≤ 1,000 LoC final)

**1,400 → 999 LoC = 401 LoC saved (28.6 %)**

W3 had reduced the file 1,580 → 1,400. A3 takes it another 401 LoC under,
crossing the 1k LoC line in nine commits.

## Inventory of patterns applied

| Pass | Pattern | Saving | Cumulative |
|------|---------|--------|-----------|
| 1 | Inline non-abbrev top theorems into `_abbrev` versions | -94 | 1306 |
| 2 | Drop dead `InitBodyPcCovered` and `bodyPcCovered_of_empty` | -26 | 1280 |
| 3 | Inline init_det/init_nondet obligations + factor `push_assn_set` | -55 | 1225 |
| 4 | Merge two transfer case-splits in `coreCFGToGotoBlockStep` | -41 | 1184 |
| 5 | Inline single-use emit preservation helpers (4 declarations) | -62 | 1122 |
| 6 | Trim stale intro doc-comment and BodyPcCovered explainer | -51 | 1071 |
| 7 | Tighten `cmdsFoldlM`/`blocksFoldlM` prefix-property scaffolding | -8 | 1048 ⁺ |
|   | (also tighter Tier-3 trailer comment) | -15 | 1056 ⁺ |
| 8 | Factor common signature of two abbrev top theorems via `variable`+`include` | -25 | 1023 |
| 9 | Hoist `bodyPcCovered_of_translator` into the same `section TopLevel` | -24 | **999** |

⁺ Pass 7 has two interleaved commits — the doc-comment trailer trim was
applied in pass 6's commit and is counted there in the cumulative
column above.

## Pass 1 — Inline non-abbrev top theorems (-94 LoC)

`declPcInversion_of_translator` (40 LoC body + 40 LoC sig) was used
exactly once, by `declPcInversion_of_translator_abbrev`. Same for
`assignPcInversion_of_translator`. The non-abbrev versions were thin
wrappers around `(bodyPcCovered_of_translator ...).1 / .2`. Inline
that projection directly into the abbrev versions, dropping ~94 LoC of
duplicated signature.

The unused `h_distinct` parameter was renamed `_h_distinct` to silence
the linter (later renamed back to `h_distinct` in Pass 8 to support
`include`).

## Pass 2 — Drop dead declarations (-26 LoC)

`InitBodyPcCovered` was just `def InitBodyPcCovered := BodyPcCovered`
— a definitional alias never referenced anywhere. `bodyPcCovered_of_empty`
proved the empty-instructions case but was never called (the empty
case is folded into `bodyPcCovered_of_translator`'s
`h_init_empty_decl_assign` hypothesis).

## Pass 3 — Compress `toGotoInstructions` cases (-55 LoC)

Each of `init_det`/`init_nondet`/`set_det`/`set_nondet` constructed
4 `have` lemmas (~10 LoC each) for per-position obligations before
calling `push_preserves` or `append_two_preserves`. Replace with
inline `(fun _ => h_invariant ▸ ⟨_, h_emit⟩)` and
`(fun h_a => absurd (h_decl_ty.symm.trans h_a) (by decide))` lambdas.

For the two `set` cases (used twice), factor a
`push_assn_set_preserves_body_pc_covered` helper. For the two `init`
cases (used once each), inline directly. Net: 55 LoC saved.

W3's declined Opportunity 4 was right not to add separate
`push_decl_*` and `push_assn_set_*` helpers — but a *single* helper
covering only the twice-used `set` shape pays off.

## Pass 4 — Merge case-splits in `coreCFGToGotoBlockStep` (-41 LoC)

The proof previously did three sequential `cases h_t : blk.transfer`:
once each for `h_size_le_st'`, `h_st_to_trans₂_prefix`, and the
post-transfer cover. Each block had the same condGoto/finish
structure. Merge into a single case-split: do it first, then build
`h_prefix₂` inline within each branch (where `st'.trans` is known
explicitly as a 1- or 2-push extension of `trans₂`).

## Pass 5 — Inline emit preservation helpers (-62 LoC)

`emitLabel_preserves_body_pc_covered`,
`emitCondGoto_preserves_body_pc_covered`,
`emitUncondGoto_preserves_body_pc_covered`, and
`endFunction_emit_preserves_body_pc_covered` were each 13–23-line
wrappers around `push_non_body_preserves_body_pc_covered`, used
exactly once (in `coreCFGToGotoBlockStep_preserves_body_pc_covered`).
Inline the 3-line body at each call site.

## Pass 6 — Trim docs (-51 LoC)

The intro doc-comment had a "Strategy" section that re-stated the
`BodyPcCovered` definition (already in the abbrev's docstring), a
"File layout" section that duplicated what the section headers say,
and a 10-line preamble for the `BodyPcCovered` abbrev that just said
the same thing as its docstring. The Tier-3 trailer comment was also
3× longer than necessary. Trim to essentials.

## Pass 7 — Tighten fold-prefix scaffolding (-8 LoC)

`cmdsFoldlM_preserves` had an aliased `h_prefix' = h_prefix` line and
a manually-unfolded `omega` step. `blocksFoldlM_preserves` had a 2-step
`rw [Array.getElem?_eq_getElem h_k', Array.getElem?_eq_getElem h_k]`
where one `rw` with two args sufficed.

## Pass 8 — `section TopLevel` for the two abbrev theorems (-25 LoC)

The two abbrev theorems share a 30-line auxiliary-hypothesis
signature. Hoist into `section TopLevel` with `variable` + `include`
blocks. The unused `h_distinct` is included for API compatibility
(the downstream `_v6` caller passes it explicitly), with
`set_option linter.unusedSectionVars false in` to silence the linter
without changing the public signature.

## Pass 9 — Hoist `bodyPcCovered_of_translator` into the section (-24 LoC)

Same trick: the private helper has the same auxiliary-hypothesis
signature as the two abbrev theorems (modulo `h_distinct`/`wf`).
Move it into `section TopLevel` and use `include ... in private theorem`
to scope the right vars per-declaration. Crosses the 1k LoC line.

## Verification

- `lake build Strata.Backends.CBMC.GOTO.PcInversion` green at every commit.
- `lake build Strata.Backends.CBMC.GOTO.CoreCFGToGOTOConcrete` (downstream
  consumer of the public `_abbrev` theorems) green at the final commit.
- No new `axiom`, `sorry`, or `admit` declarations introduced. The two
  `_abbrev` theorems depend only on standard Lean axioms (`propext`,
  `Classical.choice`, `Quot.sound`).
- Public API of `PcInversion` unchanged:
  `declPcInversion_of_translator_abbrev` and
  `assignPcInversion_of_translator_abbrev` retain their signatures
  (verified by downstream `_v6`/`_v7` build).
- No new imports — kept the file's existing import list.

## Commits

```
1a71ed33f docs(A3): stub plan
96b9c3f22 cleanup(A3): inline non-abbrev top theorems                   -94 LoC
6bdcac836 cleanup(A3): drop dead InitBodyPcCovered / bodyPcCovered_of_empty -26 LoC
c3e32e4eb cleanup(A3): inline init_det/init_nondet obligations + push_assn_set helper -55 LoC
d9cad3fe0 cleanup(A3): merge two transfer case-splits in coreCFGToGotoBlockStep -41 LoC
5fd25709c cleanup(A3): inline single-use emit preservation helpers      -62 LoC
332b10a39 cleanup(A3): trim verbose intro doc-comment + BodyPcCovered explainer -51 LoC
9f0c93f43 cleanup(A3): tighten cmdsFoldlM/blocksFoldlM prefix scaffolding -23 LoC
                       (incl. Tier-3 trailer trim, in same commit)
565f7ccb8 cleanup(A3): factor abbrev signatures via section variables  -25 LoC
07d483d58 cleanup(A3): hoist bodyPcCovered_of_translator into section  -24 LoC
                                                                  total = -401 LoC (1400 → 999)
```
