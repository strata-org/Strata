# Worker L1 — OpDesc smoke test

**Branch base:** `htd/unstructured-to-goto`
**Target file:** `Strata/Backends/CBMC/GOTO/ExprTranslationPreservesEvalBoolInt.lean` (2246 LoC pre-smoke).
**Audit reference:** `docs/CoreToGOTO_ShrinkAudit.md` §2.3 + §3.3 (claims ~600-800 LoC reducible).

## TL;DR

Smoke test succeeded. `OpDesc` abstracts the 12 nearly-identical
binary operator lemmas cleanly; both the per-op `_translated` lemmas
and the per-op bridge helpers can be reduced to one-line invocations
of two generic theorems plus a 3-field descriptor.

* **Per-op `_translated` refactor (alone):** saves ~120 LoC if the 12
  per-op wrapper lemmas are *deleted* and dispatch sites call the
  generic directly. Saves ~0 LoC if the wrappers are *kept*
  (signatures dominate; the body was already one line).
* **Per-op bridge refactor:** saves ~80 LoC keeping wrappers, ~640
  LoC deleting wrappers. The bridge body shrinks from ~25 lines of
  proof to ~5 lines.
* **Combined extrapolation:** ~110 LoC keeping all wrappers, ~760
  LoC if wrappers deleted. The audit's "~600-800 LoC" estimate is
  achievable but only via the more aggressive (delete-wrappers)
  refactor; the conservative refactor saves much less.

**Verdict: Tier 2.** Worth doing for the 12 binary bridge helpers
(largest single win in the file, ~640 LoC if wrappers are deleted).
Marginal return for the per-op `_translated` lemmas in isolation
unless wrappers are deleted. The unary `boolNot`, the ternary `ite`,
and the special-shape `eq` / `const` / `fvar` lemmas don't fit
`BoolIntBinOpDesc` and need separate generics if covered at all.

## 1. Audit confirmation

The audit's claim — "13 nearly-identical `<op>_translated` theorems
(lines 517-712, ~12 LoC each)" — is approximately correct but the
count is off:

* **12 truly parallel binary ops** at lines 517-700 (intAdd, intSub,
  intMul, intDivT, intModT, intLt, intLe, intGt, intGe, boolAnd,
  boolOr, boolImplies). Each lemma is exactly the same shape:
  ```lean
  ExprTranslated.ofValueAgree h _ _
    (fun σ v => h.<op>_corr σ m₁ m₂ ty e1c e2c e1g e2g v)
  ```
  with only the operator-name string in the LExpr pattern, the
  GOTO `Expr.Identifier` constructor, the GOTO output type
  (`.Integer` for arith, `.Boolean` for comparisons / bool ops),
  and the `_corr` field name varying.
* **1 unary op (boolNot, line 702)** — same body but different
  source/target shape (no `m₂`, only one operand). Doesn't fit a
  binary-OpDesc.
* **1 ternary op (ite, line 754)** — completely different shape,
  one `m`, three operands.
* **1 equality op (eq, line 768)** — uses `LExpr.eq m e1c e2c`
  source shape (not `LExpr.app … (LExpr.op …)`).

For the **bridge helpers** (lines 1111-1962): the audit's 13 count
matches if we count boolNot. Bridges break down as:

* **12 truly parallel binary bridges** (lines 1111-1853): same proof
  skeleton modulo per-op data.
* **1 unary bridge** (boolNot, lines 1862-1900): different shape.
* **1 ternary bridge** (ite, lines 1905-1954): different shape.
* (Plus const, fvar, eq bridges at 900-985 with their own shapes.)

The audit's parallel-skeleton claim is **correct for the 12 binary
ops**. boolNot is genuinely different shape (would need a separate
unary OpDesc); ite/eq are different enough that grouping them into
the same abstraction is not natural.

## 2. Design sketch

### `BoolIntBinOpDesc`

```lean
structure BoolIntBinOpDesc where
  opName : String           -- e.g. "Int.Add"
  opId   : Expr.Identifier  -- e.g. `.multiary .Plus`
  outTy  : Ty               -- e.g. `.Integer` or `.Boolean`
```

Three fields. No proof obligations — those are passed separately as
function arguments to the generic theorems.

### Per-op `_translated` generic

```lean
theorem binOp_translated_of_corr
    {δ ...} (h : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (od : BoolIntBinOpDesc)
    (h_corr : ∀ σ m₁ m₂ ty e1c e2c e1g e2g v,
        δ σ (LExpr.app m₂ (LExpr.app m₁
              (LExpr.op () ⟨od.opName, ()⟩ ty) e1c) e2c) = some v ↔
        δ_goto σ ⟨od.opId, od.outTy, [e1g, e2g], .nil, []⟩ = some v)
    (m₁ m₂ ty e1c e2c e1g e2g) :
    ExprTranslated δ δ_goto δ_goto_bool
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨od.opName, ()⟩ ty) e1c) e2c)
      ⟨od.opId, od.outTy, [e1g, e2g], .nil, []⟩ :=
  ExprTranslated.ofValueAgree h _ _
    (fun σ v => h_corr σ m₁ m₂ ty e1c e2c e1g e2g v)
```

The `h_corr` argument has the same shape as the existing
`BoolIntOpHypotheses.intAdd_corr` etc. — so each of the 23 fields of
that bundle is directly usable.

### Bridge generic

```lean
private theorem isBoolIntTranslated_of_toGotoExprCtx_binOp
    (od : BoolIntBinOpDesc)
    (h_red_op  : fnToGotoID od.opName = .ok od.opId)
    (h_signed  : isSignedBvOp od.opName = false)
    (h_funApp  : ∀ s, (od.opId == Expr.Identifier.functionApplication s) = false)
    (h_not_old : (od.opName == "old") = false)
    (m_op : Core.ExpressionMetadata)
    (mk : ∀ m_inner m_outer ty e1c e2c e1g e2g,
        IsBoolIntTranslated e1c e1g →
        IsBoolIntTranslated e2c e2g →
        IsBoolIntTranslated
          (LExpr.app m_outer (LExpr.app m_inner
            (LExpr.op m_op ⟨od.opName, ()⟩ ty) e1c) e2c)
          ⟨od.opId, od.outTy, [e1g, e2g], .nil, []⟩)
    (m_outer m_inner id_meta mty e1c e2c e_goto)
    (h_op_gty : mty.destructArrow.getLast!.toGotoType = .ok od.outTy)
    (ih1 ih2 : ∀ e_goto, ...) (h_frag1 h_frag2 : ... = true)
    (h_tx : LExpr.toGotoExprCtx [] <pattern> = .ok e_goto) :
    IsBoolIntTranslated <pattern> e_goto := by
  simp only [LExpr.toGotoExprCtx, bind, Except.bind, pure, Except.pure] at h_tx
  simp only [show (toString (⟨od.opName, id_meta⟩ : ...) = od.opName from rfl,
             h_not_old, h_red_op, h_signed] at h_tx
  simp only [h_funApp] at h_tx
  rw [h_op_gty] at h_tx
  cases h_e1g : ...; cases h_e2g : ...
  exact mk m_inner m_outer (some mty) e1c e2c e1g e2g (ih1 ...) (ih2 ...)
```

### What forces into the structure

* **Operator name** as a `String`: dictates the LExpr pattern and
  drives the `fnToGotoID` / `isSignedBvOp` reductions.
* **GOTO operator identifier** (`Expr.Identifier`): dictates the
  GOTO output term shape. Three sub-constructors (`.multiary`,
  `.binary`, `.unary`) — for binary OpDesc, all three actually
  appear (multiary for `.Plus`/`.Mult`/`.And`/`.Or`, binary for
  `.Minus`/`.Div`/`.Mod`/`.Lt`/`.Le`/`.Gt`/`.Ge`/`.Implies`).
* **GOTO output type** (`Ty`): `.Integer` for arith, `.Boolean` for
  comparisons + bool ops.

### Side conditions that don't fit cleanly into the structure

The bridge generic needs four extra hypotheses that *could* be in
the structure but are easier as separate function arguments:

* `h_red_op`: a `fnToGotoID od.opName = .ok od.opId` proof.
* `h_signed`: `isSignedBvOp od.opName = false`.
* `h_funApp`: `∀ s, (od.opId == .functionApplication s) = false` —
  a property of the GOTO identifier shape, not the descriptor.
* `h_not_old`: `(od.opName == "old") = false`.
* `mk`: the `IsBoolIntTranslated` constructor for this operator,
  which has the operator name baked into its conclusion's LExpr
  pattern. This *cannot* be derived generically because the
  inductive `IsBoolIntTranslated` has one constructor per literal
  operator name.

The `mk` parameter is the load-bearing complexity: the inductive's
per-operator constructors carry the operator name in their type
signature, so the generic's caller must hand the constructor in
explicitly.

## 3. Smoke test result

For `intAdd` / `Int.Add`:

* **Original `intAdd_translated`** (per-op `_translated` lemma): 12
  LoC (1 doc + 11 of signature + body).
* **Original `isBoolIntTranslated_of_toGotoExprCtx_intAdd`** (bridge
  helper): 66 LoC (1 doc + 65 of signature + 25-line proof body).

* **Refactored `intAdd_translated`**: 12 LoC (signature unchanged,
  body is now one call to `binOp_translated_of_corr` with
  `intAddDesc` and `h.intAdd_corr`). Body shrunk from 1 to 1 line —
  **no per-op saving**. The win is that the body is no longer
  per-operator boilerplate; the work moved into the shared generic.
* **Refactored `isBoolIntTranslated_of_toGotoExprCtx_intAdd`**: 50
  LoC (signature unchanged; proof body shrunk from 25 lines to 10
  lines: just `h_frag1`/`h_frag2` extraction + one call to
  `isBoolIntTranslated_of_toGotoExprCtx_binOp`). **Per-op saving:
  ~16 LoC.**

Plus shared generics added:
* `BoolIntBinOpDesc` structure: 8 LoC.
* `binOp_translated_of_corr`: 26 LoC.
* `isBoolIntTranslated_of_toGotoExprCtx_binOp`: 71 LoC.
* Total fixed overhead: **~105 LoC**.

The smoke-test commit (a single operator) is a **net +133 LoC
addition** because we kept the original per-op signatures and added
the new generics on top. The savings only materialize once the
other 11 operators are also rewritten via the generics.

## 4. Extrapolation

If all 12 binary `<op>_translated` lemmas use `binOp_translated_of_corr`:

| Approach | LoC change |
|---|---|
| Keep all 12 wrapper signatures, just rewrite bodies | 0 saved (signatures dominate) |
| Delete all 12 wrappers, inline calls into dispatch | -120 LoC saved (12 × 12 deleted, +6 LoC generic overhead) |

If all 12 binary bridges use `isBoolIntTranslated_of_toGotoExprCtx_binOp`:

| Approach | LoC change |
|---|---|
| Keep wrappers, just rewrite bodies (~50 LoC each, was ~66) | ~125 LoC saved (12 × ~16) - 71 LoC generic = ~120 LoC saved |
| Delete wrappers, inline `binOp` into dispatch sites | ~640 LoC saved (12 × 65 deleted, +72 LoC dispatch growth, -71 LoC generic) |

| Strategy | Per-op _translated | Bridge helpers | Combined |
|---|---|---|---|
| Conservative (keep wrappers, rewrite bodies) | 0 | ~120 LoC | **~120 LoC** |
| Aggressive (delete wrappers, inline calls) | ~120 LoC | ~640 LoC | **~760 LoC** |

The audit's projected "~600-800 LoC" matches the **aggressive**
path, where the per-op wrappers are deleted entirely and the
dispatch site calls the generics directly with descriptor literals.

The conservative path saves much less (~120 LoC) and is mostly
not worth the API churn.

The boolNot (unary), ite (ternary), and eq (`LExpr.eq` shape)
operators do NOT fit `BoolIntBinOpDesc`. Each would need its own
mini-generic (a unary OpDesc, an eq-specific helper, or — for ite —
left as-is). Per-op savings on those would be much smaller (~30 LoC
together).

## 5. Feasibility verdict — Tier 2

This refactor is **worth doing for the 12 binary bridge helpers**
(saves ~640 LoC under the aggressive path, ~120 LoC under the
conservative). The same OpDesc generalises the 12 per-op
`_translated` lemmas at no extra design cost.

**Recommendation:** if a future round wants to land the audit's §3.3
refactor, follow the **aggressive path**:

1. Land the OpDesc + two generics + `intAddDesc` (this smoke-test
   PR; ~150 LoC added).
2. Add 11 more `<op>Desc` literals (one per remaining binary op).
3. Replace all 12 binary per-op `_translated` lemmas in
   `IsBoolIntTranslated.translated` with one-line `binOp_translated_of_corr`
   calls; delete the 12 wrapper lemmas. (Saves ~120 LoC.)
4. Replace all 12 binary per-op bridge helpers in
   `toGotoExprCtx_preservesEval_boolInt` with one-line
   `isBoolIntTranslated_of_toGotoExprCtx_binOp` calls; delete the
   12 wrapper bridges. (Saves ~640 LoC.)
5. Leave boolNot (unary), ite (ternary), eq, const, fvar
   alone — different shapes, not worth a second OpDesc.

Estimated final saving: **~600-700 LoC** in the 2246-LoC file
(file shrinks to ~1550-1650 LoC). Aligns with the audit's claim
modulo accounting for the descriptor literals + dispatch growth.

**Tier 2 rather than Tier 1** because:

* The conservative path saves only ~120 LoC, which is much less
  than the audit's headline number. Calling this "Tier 1" would
  oversell.
* The aggressive path requires deleting public-facing per-op
  lemmas (`intAdd_translated` etc. are exported), which is a
  breaking API change for any caller outside this file. *No live
  callers were found in this branch* but a search of the whole
  Strata tree should be done before deletion.
* The `mk` parameter on the bridge generic is a non-trivial bit
  of complexity: each refactored bridge call passes a 3-line
  lambda invoking the operator's `IsBoolIntTranslated` constructor.
  This is mechanical but the verbosity offsets some of the saving
  in the dispatch.

## 6. Edge cases discovered

### 6.1 The `mk` parameter — inductive constructors are per-operator

`IsBoolIntTranslated`'s 13 binary constructors (lines 773-892) each
hardcode the operator name in their conclusion's LExpr pattern.
There is no way to generically apply `.intAdd` / `.intSub` / etc.
without case-splitting on the operator. The `mk` argument is a
clean workaround: the caller provides the constructor as a
function. This is mechanical but adds verbosity.

An alternative would be to **restructure `IsBoolIntTranslated`** to
have a single binary case parameterised by an OpDesc:

```lean
| binOp (od : BoolIntBinOpDesc) (m₁ m₂ : ...) (...) :
    IsBoolIntTranslated
      (LExpr.app m₂ (LExpr.app m₁ (LExpr.op () ⟨od.opName, ()⟩ ty) e1c) e2c)
      ⟨od.opId, od.outTy, [e1g, e2g], .nil, []⟩
```

This would compress the 12 binary constructors to 1, saving ~110
LoC. But it changes the inductive interface — every consumer that
currently does `induction h_tx with | intAdd ... | intSub ... | ...`
would need to be rewritten to inspect the descriptor. The trade-off
is real and probably not worth it; the inductive's per-operator
constructors are pedagogically clearer.

### 6.2 `boolNot` — unary, doesn't fit the binary OpDesc

`boolNot_translated` and its bridge use a different LExpr pattern
(`.app m (.op _ fn (some ty)) e1` — only one outer `.app`) and a
different translator code path (the unary case in
`LExpr.toGotoExprCtx` has a `parseBvExtractLo` check, not a
`fnToGotoID/isSignedBvOp` check).

A separate `BoolIntUnaryOpDesc` + `unaryOp_translated_of_corr` +
`isBoolIntTranslated_of_toGotoExprCtx_unaryOp` would be needed
to fold boolNot in. Since boolNot is the *only* unary in the
fragment, the saving from doing this is < 60 LoC. Not worth it.

### 6.3 `ite` — ternary, completely different shape

`ite_translated` and its bridge work on `LExpr.ite m cc tc ec` →
`Expr.ite cg tg eg`. The translator has a separate ternary path. No
abstraction needed; it's a single instance.

### 6.4 `eq` — uses `LExpr.eq` constructor, not `LExpr.app`

Same as ite: different shape, no point in collapsing.

### 6.5 `intConst` / `boolConst` / `fvar` — non-operator shapes

These have hand-written proofs that handle constructors of `LConst`
and bool/int constant view. Not abstracted by `BoolIntBinOpDesc`.

### 6.6 The `signedBvOp` / `parseBvExtractLo` divergence

The 12 binary bridges all need `h_red.isSignedBvOp_<op> = false`.
The unary bridge for boolNot needs `h_red.parseBvExtractLo_boolNot
= none` instead. This is another reason boolNot doesn't fit the
binary OpDesc.

### 6.7 The `BoolIntOpHypotheses` bundle is *not* simplified

`BoolIntOpHypotheses` has 23 fields. The audit (§3.3) suggested
collapsing those into a single `agrees_at : ∀ op ∈ supportedOps,
BoolIntOpAgreesAt _ _ _ op` field. This smoke test does NOT touch
`BoolIntOpHypotheses` because:

* The current API is still useful — callers project specific
  fields with named-record syntax.
* Collapsing would change the *user-facing* interface (the
  hypothesis bundle the user supplies when discharging Gap B).
* The 23 fields aren't all parallel anyway: 7 of them are
  `bool_corr` companions for the 4 boolean operators; another
  is `goto_bool_agrees_value` (a generic alignment field). The
  raw 13 binary fields could be collapsed but that's a smaller
  saving (~140 LoC) than the bridges.

This is a Tier 2 follow-up; not part of the smoke test.

## Process notes

* Worktree branch: `worktree-agent-a908e0fa8edb47149`, reset to
  `htd/unstructured-to-goto`.
* Three commits:
  1. Stub report + audit doc copy.
  2. OpDesc + generics + intAdd refactor (smoke test).
  3. Final report.
* `lake build` green at every commit (585 jobs).
* No `sorry`. No `git push`.
* Touched only `ExprTranslationPreservesEvalBoolInt.lean` and
  `docs/_workers/L1_opdesc_smoke_test.md` (plus the audit doc copy
  in commit 1).
