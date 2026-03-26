# PR #488 — Reviewer Comments & Recommendations

## Comment 1 — `Strata/Languages/Core/DDMTransform/Translate.lean:255`
> "Are we ever using this parameter for anything anymore?"

**Answer:** The reviewer is asking about the `IDMeta` type parameter on `LDatatype` (and `LConstr`, `LFunc`, etc.) — since `Visibility` was removed, it's always `Unit` everywhere. You replied that yes, it's no longer needed, and it will be removed in a follow-up PR. **No action needed on this PR.**

---

## Comment 2 — `Strata/Languages/Core/ProcedureEval.lean:61`
> "Given that the `old ` ++ pattern occurs in several places, it would be nice to encapsulate it behind a function."

**Recommendation: Address.** The pattern `⟨"old " ++ name, ()⟩` appears in 6 places:
- `ProcedureEval.lean:61`
- `ProcedureType.lean:132`
- `StatementEval.lean:199`
- `CallElim.lean:53`
- `StatementSemantics.lean:188,191`
- `DDMTransform/Translate.lean:841`

Add to `Identifiers.lean`:
```lean
def CoreIdent.mkOld (name : String) : CoreIdent := ⟨"old " ++ name, ()⟩
```
Then replace all occurrences. Also the string equality check in `CallElim.lean:34`:
```lean
id.name == "old " ++ g.name
```
becomes:
```lean
id == CoreIdent.mkOld g.name
```

---

## Comment 3 — `Strata/Languages/Core/StatementEval.lean:199`
> "Is this logic to build a substitution duplicated in several parts of this PR?"

**Answer:** Yes, there are two places that build `old g` substitutions:
1. `ProcedureEval.lean:58-61` — builds `old_g_subst` from `old_var_subst` filtered to globals
2. `StatementEval.lean:197-200` — builds `old_g_subst` from `current_globals`

They're not identical (different input types), but the pattern is similar. The reviewer has a point. However, extracting a shared helper would require threading more context. **Recommendation: reply explaining the difference, and note that `CoreIdent.mkOld` (from comment 2) already addresses the naming part.**

---

## Comment 4 — `Strata/Languages/Laurel/Grammar/LaurelGrammar.lean:10`
> "This doesn't seem related to this PR?"

**Done:** Reverted the extra comment line. The cache reload mechanism will be fixed properly in a separate PR.

---

## Comment 5 — `StrataTest/Languages/Core/OldExpressionsTests.lean:1`
> "You could probably just remove this file."

**Recommendation: Address.** The file is a placeholder (the module was deleted). Check its current content:

The file exists as a stub. It can be deleted entirely — the module `OldExpressions` is gone, so there's nothing to test. Remove the file and its entry from any test manifest.

---

## Comment 6 — `StrataTest/Languages/Core/ProcedureEvalTests.lean:21`
> "What led to this change?"

**Answer:** The `Subst Map` in the test output changed from `(x, ($__x0 : int)) (y, ($__y1 : int))` to empty. This is because `substMap` in `Env` now only contains `"old g"` entries (set by `ProcedureEval`), whereas before it contained the full `old_var_subst` including parameter substitutions. The test is for a procedure with no globals, so `substMap` is correctly empty. **Reply to explain this.**

---

## Comment 7 — `Tools/BoogieToStrata/Source/StrataGenerator.cs:305`
> "I'd really like to handle more cases than the two above. I think Boogie may have code in it already to normalize `old` expressions that you could call."

**Recommendation: Investigate and address if feasible.** The current `EmitOldExpr` handles:
- `IdentifierExpr` → `old v`
- `NAryExpr { Fun: MapSelect }` → `(old A)[i]`
- fallback → `old <expr>` (may not parse)

The reviewer wants more cases handled. Boogie's `OldExpr` normalization is in `Boogie.Core.Expr`. The relevant Boogie API is `Expr.Old` and the `Substituter` class. **Recommendation: look at `Boogie.Core.Substituter` or `StandardVisitor` to recursively distribute `old` through arithmetic/boolean expressions too, e.g. `old(a + b)` → `old a + old b`.**

This is the most open-ended comment. A reasonable response is to file a follow-up issue and note the limitation in a code comment.

---

## Summary of Actions

| # | Action | Priority |
|---|--------|----------|
| 1 | Reply: `block` is still used | Reply only |
| 2 | Add `CoreIdent.mkOld` helper, replace 6 occurrences | **Do it** |
| 3 | Reply: explain the two substitutions differ | Reply only |
| 4 | Revert the LaurelGrammar.lean comment change | **Do it** |
| 5 | Delete `OldExpressionsTests.lean` | **Do it** |
| 6 | Reply: explain substMap is now only "old g" entries | Reply only |
| 7 | Add comment about limitation + file follow-up issue | **Do it** |
