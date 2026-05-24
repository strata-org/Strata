# W3: PcInversion.lean local-reduction audit

## Plan (carried over from stub)

`Strata/Backends/CBMC/GOTO/PcInversion.lean` is 1,580 LoC. L2's design audit
classified its `BodyPcCovered` step as Class E (5+ auxiliary hypotheses per
step) and recommended skipping the `BlocksFoldClosed` combinator port. This
audit looked for **local** reductions that don't require the combinator:
near-duplicate step lemmas, dead `private theorem`s, verbose tactic chains,
repeated hypothesis bundles, and `Option.some.inj/subst` patterns that
`inj_subst` (from `Strata.Backends.CBMC.GOTO.Tactics`) could compress.

Threshold: only apply opportunities saving ≥10 LoC each. If the running total
was <30 LoC by the halfway mark, declare Tier 3 and stop.

## Verdict: Tier 1 (≥150 LoC saved)

**1,580 → 1,400 LoC = 180 LoC saved (11.4 %)**

The file *is* lean for what it does, but had three repeated patterns that
each compressed cleanly without needing the heavy combinator.

## Inventory of patterns discovered

| # | Category | Sites | Per-site cost | Verdict |
|---|---|---|---|---|
| 1 | Type-disjoint instruction obligation pattern | 7 | 10–15 LoC | **Applied** — saved 119 LoC |
| 2 | Duplicate body in two top theorems (DECL/ASSIGN inversion) | 2 | ~70 LoC | **Applied** — saved 30 LoC |
| 3 | Unused `h_preserves` parameter + 27-line construction | 1 | 31 LoC | **Applied** — saved 31 LoC |
| 4 | Asymmetric `push_decl/push_assn_set` helpers (init_nondet, set_det, set_nondet) | 3 | ~14 LoC each | **Declined** — net +6 LoC after helper sigs (helpers cost 50 LoC, savings 44) |
| 5 | `inj_subst` macro applicability | 0 | – | Not applicable; only 1 borderline `injection h with h; subst h` site |
| 6 | Dead `private theorem`s | 0 | – | All 3 private theorems have callers in-file |

## Opportunity 1 (commit 294c59133)

**Pattern.** Twelve sites had the boilerplate

```lean
have h_new_decl : new_instr.type = .DECL → ... := by
  intro h_eq
  have : InstructionType.X = InstructionType.DECL := h_eq
  cases this
have h_new_assn : new_instr.type = .ASSIGN → ... := by
  intro h_eq
  have : InstructionType.X = InstructionType.ASSIGN := h_eq
  cases this
exact push_preserves_body_pc_covered ... h_new_decl h_new_assn h
```

where `X` is some non-DECL, non-ASSIGN type (LOCATION / GOTO / END_FUNCTION /
FUNCTION_CALL / ASSERT).

**Helper.** Added `push_non_body_preserves_body_pc_covered` (15 lines) taking
`new_instr.type ≠ .DECL` and `new_instr.type ≠ .ASSIGN` Props directly:

```lean
private theorem push_non_body_preserves_body_pc_covered
    ... (h_not_decl : new_instr.type ≠ .DECL)
        (h_not_assn : new_instr.type ≠ .ASSIGN) ... :=
  push_preserves_body_pc_covered ... h_cov
    (fun h => absurd h h_not_decl) (fun h => absurd h h_not_assn)
```

**Application sites** (7):
- `toGotoInstructions_preserves_body_pc_covered`: assert, assume, cover branches
- `coreCFGToGotoCmdStep_preserves_body_pc_covered`: call branch
- `emitLabel_preserves_body_pc_covered`
- `emitCondGoto_preserves_body_pc_covered`
- `emitUncondGoto_preserves_body_pc_covered`
- `endFunction_emit_preserves_body_pc_covered`

**Saving.** 1,580 → 1,461 LoC (119 LoC).

## Opportunity 2 (commit 920fbb689)

**Pattern.** `declPcInversion_of_translator` (lines 1132–1238) and
`assignPcInversion_of_translator` (lines 1287–1388) had nearly-identical
70-line bodies — both decompose the translator output, build
`BodyPcCovered ans pgm` by composing blocks-fold preservation and patcher
preservation, and finally project. They differed only in the final line:
`(h_cov_ans h_at_pgm).1 h_ty` (DECL) vs `.2 h_ty` (ASSIGN).

**Helper.** Extracted `private theorem bodyPcCovered_of_translator` (~70
lines) returning the full `BodyPcCovered ans pgm` predicate. Both public
theorems now reduce to a one-line projection.

**Saving.** 1,461 → 1,431 LoC (30 LoC). Modest because the helper itself is
~70 lines — net win is only the duplication that vanished.

**Note.** Both top theorems take an `h_distinct : BlockLabelsDistinct` arg
that turns out unused. Couldn't drop it (would change the public API of
`_abbrev` wrappers), so I added a no-op `let _ := h_distinct` to silence the
linter.

## Opportunity 3 (commit eb6639ddc)

**Pattern.** `cmdEmittedAt_preserved_target_only` (private) takes both
`h_preserves` (forward) and `h_preserves_back` (backward) bidirectional
preservation lemmas. The body matches on `CmdEmittedAt` and only ever uses
`h_preserves_back` to find the post-patcher witness — `h_preserves` is unused.
The lone caller `patchGotoTargets_preserves_body_pc_covered` constructs both
in 27 lines.

**Action.** Dropped the `h_preserves` parameter (9 lines) and the 27-line
construction at the call site, plus updated three call sites.

**Saving.** 1,431 → 1,400 LoC (31 LoC).

## Declined opportunity 4

I prototyped `push_decl_preserves_body_pc_covered` and
`push_assn_set_preserves_body_pc_covered` to compress the
`init_nondet`, `set_det`, `set_nondet` cases of
`toGotoInstructions_preserves_body_pc_covered`. Each call site goes from 17
lines to 3 — saves ~42 LoC across three sites — but the two helper
signatures cost ~50 LoC. Net **+6 LoC**. Stashed and abandoned.

The `init_det` case (with `append_two_preserves_body_pc_covered`) is a fourth
candidate. A specialised "append-two-with-init-det-witness" helper *might*
break even (~45 saved at site, ~30 LoC helper sig = net +15 saved). Not
worth a full helper for a single application site — would only cross the
≥10-LoC bar marginally and add an extra named lemma to the file. Declined.

## Verification

- `lake build Strata.Backends.CBMC.GOTO.PcInversion` green at every commit.
- `lake build Strata.Backends.CBMC.GOTO.CoreCFGToGOTOConcrete` (downstream
  consumer of the public `_abbrev` theorems) green at the final commit.
- No new `axiom`, `sorry`, or `admit` declarations introduced. (`grep` for
  the bare keywords in the file finds only the function name `isAdmittedCmd`
  and the `admitted-fragment` comments.)
- Public API of `PcInversion` unchanged:
  `declPcInversion_of_translator_abbrev` and
  `assignPcInversion_of_translator_abbrev` retain their signatures.
- No new imports — kept the file's existing import list.

## Commits

```
1cb601334 docs(W3): stub plan
294c59133 refactor(W3): factor non-DECL/ASSIGN push into push_non_body_...  -119 LoC
920fbb689 refactor(W3): extract bodyPcCovered_of_translator helper          -30  LoC
eb6639ddc refactor(W3): drop unused h_preserves parameter from ...           -31  LoC
                                                                  total =  -180 LoC (1580 → 1400)
```
