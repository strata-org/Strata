# Worker A2 — B3 trim of `ExprTranslationPreservesEvalBoolInt.lean`

**Branch base:** `htd/unstructured-to-goto` (a012a1c01).
**Target file:** `Strata/Backends/CBMC/GOTO/ExprTranslationPreservesEvalBoolInt.lean`.
**Tier verdict: Tier 1.** Final 1198 LoC ≤ 1200 (target).

## TL;DR

* Baseline: **1527 LoC** (post-L4 OpDesc refactor).
* After A2: **1198 LoC**.
* **Net saving: 329 LoC** (-21.5%).
* Six commits, each `lake build` green.
* Axioms unchanged: `_v6` and `_v7` still
  `[propext, Classical.choice, Quot.sound]` (verified via
  `StrataTest/Backends/CBMC/GOTO/CoreCFGToGOTOConcreteAxioms.lean`).
* Public API preserved: every consumer in
  `CoreCFGToGOTOConcrete.lean` (and the `_v6`/`_v7` axiom-test file)
  still type-checks.

## Per-pass progression

| Commit | Pass | Δ LoC | Cumulative LoC |
|---|---|---|---|
| `267a3eb1a` | stub report | — | 1527 |
| `6a04e0ef0` | **Pass 1** — inline 5 private bridge helpers | **−169** | 1358 |
| `25c6c473e` | **Pass 2** — eliminate pre-extracted `h_gty` projections | **−27** | 1331 |
| `b8696dea4` | **Pass 3** — collapse `intConst`/`boolConst` `_translated` via `ofValueAgree` | **−93** | 1238 |
| `bec208291` | **Pass 4** — collapse `binOp_translated_of_corr` lambda wrappers | **−6** | 1232 |
| `6e8de137f` | **Pass 5** — collapse not-in-fragment cases via OR-pattern | **−9** | 1223 |
| `84d0e2be7` | **Pass 6** — trim descriptor docs and section headers | **−25** | 1198 |

## What each pass did

### Pass 1 (−169 LoC) — inline 5 private bridge helpers

Removed five `private theorem isBoolIntTranslated_of_toGotoExprCtx_<X>`
helpers (`const`, `fvar`, `eq`, `boolNot`, `ite`) and inlined their
proof bodies into the corresponding `match` arms of
`toGotoExprCtx_preservesEval_boolInt`. The helpers each had a 15-25 LoC
signature plus a 12-25 LoC body; the dispatch site already had the
relevant hypotheses (h_gty/h_frag/h_red), so the IH-thunk plumbing
disappeared. Recursive calls now go directly to
`toGotoExprCtx_preservesEval_boolInt h_red e1c e1g h_gty1 h_frag1 h_e1g`.

### Pass 2 (−27 LoC) — eliminate pre-extracted `h_gty` projections

The binary-op dispatch had three `have h_gty_int_arith / h_gty_int_cmp /
h_gty_bool_bin` blocks pre-extracting implications from `h_gty` because
`subst h_name` happened later in each per-op branch. After `subst h`
inside each branch (now via `<;> subst h`), the OR-chain navigation
`(h_gty_int_arith (Or.inr (Or.inr (by simp))))` collapses to
`(h_gty.1 (by simp))`/`(h_gty.2.1 (by simp))`/`(h_gty.2.2.1 (by simp))`
— Lean simplifies the `("Int.X" == "Int.X" ∨ ...)` OR after substitution.

### Pass 3 (−93 LoC) — collapse `intConst`/`boolConst` `_translated`

`intConst_translated` and `boolConst_translated` were 60 + 59 LoC of
hand-written `refine ⟨?vagree, ?ttagree, ?ffagree⟩` with explicit
contradiction proofs for the `bool_tt`/`bool_ff` cases. Replaced both
with a single `ExprTranslated.ofValueAgree h _ _ <| by intro σ v; …`
call (15 LoC total). The bool-view agreement is automatically derived
by `ofValueAgree` via `goto_bool_agrees_value` + the value-agree proof.

### Pass 4 (−6 LoC) — collapse `binOp_translated_of_corr` lambda wrappers

Reordered `binOp_translated_of_corr` so `h_corr` matches the shape of
`BoolIntOpHypotheses.<op>_corr` directly (quantified over all of
`σ m₁ m₂ ty e1c e2c e1g e2g v`). Then in `IsBoolIntTranslated.translated`,
each call site `(fun σ v => h.X_corr σ m₁ m₂ ty e1c e2c e1g e2g v)`
becomes simply `h.X_corr`. 12 wrapper lambdas eliminated.

### Pass 5 (−9 LoC) — collapse not-in-fragment cases via OR-pattern

The `match e_core, h_gty, h_frag, h_tx with` in
`toGotoExprCtx_preservesEval_boolInt` had 21 separate `| .X _, _, h_frag, _ =>
simp [isBoolIntFragment] at h_frag` patterns for shapes outside the
fragment (op, bvar, abs, quant, app-with-non-op, etc.). Lean 4 supports
OR-patterns inside `match`: collapsed into a single multi-`|`
alternative sharing one RHS. (A bare wildcard `_` doesn't work — Lean
can't unfold `isBoolIntFragment` without the constructor head, so each
pattern must be enumerated; OR-pattern syntax keeps them concrete
while sharing the body.)

### Pass 6 (−25 LoC) — trim descriptor docs and section headers

* Removed the 12 single-line per-descriptor docstrings (each redundant
  with the descriptor literal itself); kept one summary docstring.
* Trimmed two verbose section-header comment blocks (the "Per-operator
  binary integer lemmas" 12-line note and the "Binary operator
  descriptor" 8-line note).

## Public API preserved

External consumers (verified by `grep`):

* `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` references
  `ExprTranslationBoolInt.{FnToGotoIDReductions, BoolIntOpHypotheses,
  IsBoolIntTranslated, isBoolIntFragment, BoolIntGtyAgrees,
  toGotoExprCtx_preservesEval_boolInt, IsBoolIntTranslated.translated}`.
  All retained, with unchanged signatures.
* `StrataTest/Backends/CBMC/GOTO/CoreCFGToGOTOConcreteAxioms.lean`
  consumes `_v6`/`_v7` from `CoreCFGToGOTOConcrete.lean` (transitive).
  Axiom set unchanged.
* `<op>_translated` family (`intConst_translated`,
  `boolConst_translated`, `boolNot_translated`, `ite_translated`,
  `eq_translated`, `fvar_translated`, `binOp_translated_of_corr`):
  none are publicly consumed (verified via grep across `Strata/` and
  `StrataTest/`); all are still in the file as bridge lemmas used
  internally by `IsBoolIntTranslated.translated`. **No deletions** in
  this family — only body simplifications.

## Internal helpers removed (deletion)

* `isBoolIntTranslated_of_toGotoExprCtx_const` — inlined.
* `isBoolIntTranslated_of_toGotoExprCtx_fvar` — inlined.
* `isBoolIntTranslated_of_toGotoExprCtx_eq` — inlined.
* `isBoolIntTranslated_of_toGotoExprCtx_boolNot` — inlined.
* `isBoolIntTranslated_of_toGotoExprCtx_ite` — inlined.

(`isBoolIntTranslated_of_toGotoExprCtx_binOp`, `op_id_ne_funApp_multiary`,
`op_id_ne_funApp_binary` retained — used 12 times each in the binary
dispatch, where they remain a net savings vs. inlining.)

## Dead-code audit (no findings to remove)

`grep` over `Strata/` and `StrataTest/` for each named declaration.
No dead lemmas were found — every named theorem in the file is used
at least once (most internally by either `IsBoolIntTranslated.translated`
or `toGotoExprCtx_preservesEval_boolInt`).

## Build verification

* Per-target build (`lake build Strata.Backends.CBMC.GOTO.ExprTranslationPreservesEvalBoolInt`):
  201/201 green at every commit.
* Full repo build (`lake build`): 585/585 green at HEAD.
* Axiom test: `lake build StrataTest.Backends.CBMC.GOTO.CoreCFGToGOTOConcreteAxioms`
  prints `[propext, Classical.choice, Quot.sound]` for both `_v6` and
  `_v7`. No new axioms.

## What stayed put

The L4 doc explicitly listed these as out-of-scope for L4 and worth
re-examining for A2:

* **Unary OpDesc for `boolNot`**: not pursued. The unary-bridge body
  was already inlined into the dispatch in Pass 1, removing the
  per-op helper without needing a unary-OpDesc abstraction. Net
  saving from Pass 1 captured the unary case directly (~25 LoC).
* **Ternary OpDesc for `ite`**: same — inlined in Pass 1.
* **`eq` special-case helper**: same — inlined in Pass 1.
* **`BoolIntOpHypotheses` 23-field collapse / `FnToGotoIDReductions`
  26-field collapse**: not pursued. These are user-facing interfaces
  (the bundles a Gap-B user supplies), and collapsing them changes
  the API surface for hypothesis discharge. The L4 doc flagged this
  as a "Tier 2 follow-up with real API churn" — leaving alone.

## Tier verdict — Tier 1

Final 1198 LoC, comfortably under the 1200 target. -329 LoC total
(-21.5% of the L4 baseline). All six passes are independently
verifiable and each commit builds clean.

The biggest wins came from inlining private bridge helpers (Pass 1)
and recognizing that `intConst`/`boolConst` proofs reduce trivially
via `ofValueAgree` (Pass 3), which together account for 262 of the
329 LoC saved.
