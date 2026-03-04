# PR #475 — Open Comments & Resolution Plan

## Status key
- ✅ Already resolved in thread
- 🔧 Needs implementation

---

## 1. `Strata/Languages/Core/DDMTransform/Translate.lean` — SourceRange.none
**Reviewer:** No more `Strata.SourceRange.none` in this file; source ranges should come from DDM metadata.
**Status:** ✅ Already done in the merge — `grep` confirms zero occurrences of `SourceRange.none` in `Translate.lean`.
**Action:** None needed. Reply to close the thread.

---

## 2. `StrataMain.lean` — Duplicate imports (our comment)
**Lines 22-24 duplicated on 26-28:** `CoreSMT.Verifier`, `CoreSMT.State`, `SolverInterface`.
**Fix:** Remove lines 26-28 (the duplicate block).

---

## 3. `Strata/Languages/Core/StatementSemantics.lean:19` — Indentation (our comment)
**`| const` missing two leading spaces.**
**Fix:** Add two spaces before `| const`.

---

## 4. `Strata/Languages/Core/Verifier.lean:158` — DiagnosisInfo layering (our comment)
**`DiagnosisInfo` references `CoreSMT.DiagnosedFailure`, forcing `Core.Verifier` to import `CoreSMT.Diagnosis`.**
**Fix:** Create `Strata/Languages/Core/CoreSMT/DiagnosisTypes.lean` containing:
- `DiagnosisResultType`
- `DiagnosisContext`
- `DiagnosisReport`
- `DiagnosedFailure`
- `DiagnosisResult`

Then:
- `CoreSMT.Diagnosis` imports `CoreSMT.DiagnosisTypes` instead of defining them
- `Core.Verifier` imports `CoreSMT.DiagnosisTypes` instead of `CoreSMT.Diagnosis`
- `DiagnosisInfo` stays in `Core.Verifier` next to `Outcome`/`VCResult`

---

## 5. `Strata/DL/SMT/TermType.lean:54` — Unused `TermType.toSMTString` (our comment)
**`TermType.toSMTString` is never called; `SMTDDM.termTypeToString` and `Solver.typeToSMTString` already exist.**
**Fix:** Remove `TermType.toSMTString`.

---

## 6. `Strata/DL/SMT/SolverInterface.lean:115` — Unused helpers (our comment)
**`mkCvc5Solver`, `mkSolverFromPath`, `mkSolverFromEnv` are never called outside the file.**
**Fix:** Remove all three (and the private `initializeSolver` which only serves them).

---

## 7. `Strata/Languages/B3/Verifier.lean:63` — `Option Unit` in ProcedureReport (our comment)
**`results : List (VerificationReport × Option Unit)` — second element always `none`, always ignored.**
**Fix:** Change to `results : List VerificationReport`. Update `programToSMT` and all callers (`StrataVerify.lean`, `StrataTest/Languages/B3/Verifier/VerifierTests.lean`, `TranslationTests.lean`).

---

## 8. `StrataTest/Languages/Python/expected_incremental/` — Orphaned directory (our comment)
**`expected_incremental/` is identical to `expected_interactive/` and never referenced by any script.**
**Fix:** Delete `StrataTest/Languages/Python/expected_incremental/test_incremental_simple.expected` (and the directory).
