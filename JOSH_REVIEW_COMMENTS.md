# Josh's Review Comments on PR #307

**Reviewer:** @joscoh (Josh)  
**Date:** January 15, 2026  
**Status:** Pending response

---

## Comment 1: Use List.map instead of for loop ✅ DONE

**File:** `Strata/Languages/B3/Verifier/Program.lean`  
**Line:** 106  
**Comment:**
> I think it's nicer to have `let results := results ++ List.map .error conversionErrors`

**Status:** ✅ Fixed

**Change Applied:**
```lean
results := results ++ conversionErrors.map .error
```

**Commit:** (pending)

---

## Comment 2: Remove unnecessary mutable variable ✅ DONE

**File:** `Strata/Languages/B3/Verifier/Program.lean`  
**Line:** 94  
**Comment:**
> This does not need to be mutable.

**Status:** ✅ Fixed

**Change Applied:**
```lean
let initialState ← initVerificationState solver
...
let (state, conversionErrors) ← addDeclarationsAndAxioms initialState transformedProg
```

**Commit:** (pending)

---

## Comment 3: Remove duplicate section header ✅ DONE

**File:** `Strata/Languages/B3/Verifier/Program.lean`  
**Line:** 119  
**Comment:**
> Repeated section

**Status:** ✅ Fixed

**Change Applied:** Removed duplicate header.

**Commit:** (pending)

---

## Comment 4: Remove unused section header ✅ DONE

**File:** `Strata/Languages/B3/Verifier/State.lean`  
**Line:** 63  
**Comment:**
> Is this section header used?

**Status:** ✅ Fixed

**Change Applied:** Removed unused "Verification State" header that was immediately followed by "Verification Context and Results" header.

**Commit:** (pending)

---

## Comment 5: Use reverse list building pattern ✅ DONE

**File:** `Strata/Languages/B3/Verifier/Program.lean`  
**Line:** 202  
**Comment:**
> Again, it would be better to build the reverse list with `::` and reverse the whole thing at the end.

**Status:** ✅ Fixed

**Change Applied:**
```lean
let mut reportsRev := []
...
reportsRev := {procedureName := name, results := resultsWithDiag} :: reportsRev
...
return reportsRev.reverse
```

**Commit:** (pending)

---

## Comment 6: Same optimization for Statements.lean ✅ DONE

**File:** `Strata/Languages/B3/Verifier/Statements.lean`  
**Line:** 98  
**Comment:**
> Same as above

**Status:** ✅ Fixed

**Change Applied:** Used `::` and reverse pattern in both `statementToSMTWithoutDiagnosis` (Statements.lean) and `statementToSMT` (Diagnosis.lean).

**Commit:** (pending)

---

## Comment 7: No partial evaluation in B3? ✅ RESPONDED

**File:** `StrataTest/Languages/B3/Verifier/VerifierTests.lean`  
**Line:** 485  
**Comment:**
> I take it from this test this is no B3 partial evaluation, right?

**Status:** ✅ Clarified by user

**Response:** User confirmed this is correct - B3 doesn't do partial evaluation, it translates directly to SMT terms and lets the SMT.Factory layer handle constant folding.

---

## Comment 8: Declaration ordering and dependencies ✅ RESPONDED

**File:** `Strata/Languages/B3/Transform/FunctionToAxiom.lean`  
**Line:** 154  
**Comment:**
> Makes sense, but it seems a little strange to me that getting things in the correct order is bound up with generating axioms for functions (with another function encoding, we would still need to make sure the order is consistent). And this doesn't even completely enforce the right order, since I don't think it deals with dependencies between e.g. two functions, one of which calls the other.

**Status:** ✅ Clarified

**Note:** The ordering is: types → function declarations → axioms → other. This is correct for SMT-LIB where sorts must come before functions, and function declarations before axioms. Function-to-function dependencies don't matter for declarations (only for axioms), and the current ordering handles this correctly.

---

## Comment 9: Remove bullet points from Formatter.lean docstring

**File:** `Strata/Languages/B3/Verifier/Formatter.lean`  
**Comment:**
> I don't think we need these bullets here personally.

**Current Code:**
```lean
This module uses `SMTDDM.toString` which translates SMT terms to the SMT dialect's
AST and then uses the dialect's formatter to generate SMT-LIB strings. This approach:
- Is more efficient than string interpolation
- Produces direct, readable SMT-LIB output (no A-normal form)
- Leverages the existing SMT dialect infrastructure
- Ensures consistency with other SMT formatting in Strata
```

**Recommendation:** **Accept** - Simplify the docstring to be more concise without the bullet points.

**Effort:** Trivial

---

## Comment 9: Remove bullet points from Formatter.lean docstring ✅ DONE

**File:** `Strata/Languages/B3/Verifier/Formatter.lean`  
**Comment:**
> I don't think we need these bullets here personally.

**Status:** ✅ Fixed

**Change Applied:** Simplified docstring to remove bullet points, keeping just the essential description.

**Commit:** (pending)

---

## Summary

**Total Comments:** 9

**Status:**
- ✅ **Fixed:** 6 (Comments 1, 2, 3, 4, 5, 6, 9)
- ✅ **Responded:** 2 (Comments 7, 8)

**All comments addressed!**
