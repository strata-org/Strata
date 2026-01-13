# PR #307 Review Comments - Action Plan

**PR Title:** Add B3 Verifier: SMT-based verification for B3 programs  
**Branch:** b3-to-smt-converter  
**Reviewers:** atomb, shigoel

---

## Overview

This PR adds a B3 verification pipeline that translates B3 programs to SMT and verifies them. The architecture includes:
- Streaming symbolic execution (not batch VCG)
- Automatic diagnosis for failed verifications
- Support for proof checks and reachability checks
- Function-to-axiom transformation for mutually recursive functions

---

## Review Comments Summary

### 1. **Use SMT Dialect Pretty-Printer Instead of String Interpolation** ✅ COMPLETED

**File:** `Strata/Languages/B3/Verifier/Formatter.lean`  
**Reviewer:** atomb  
**Comment:** "You could still generate terms using the AST for the SMT dialect, and use its pretty-printer to generate strings. That way you'll still have full control over the structure of the generated SMT-LIB, but also have a more efficient translation to strings. The `s!\"...\"` interpolation used below is slower."

**Implementation:**
- Replaced custom `formatTermDirect` function with `SMTDDM.toString`
- Uses the new SMT dialect pretty-printer from `Strata/DL/SMT/DDMTransform/Translate.lean`
- Produces direct, readable SMT-LIB output (no ANF)
- More efficient and maintainable than string interpolation
- Committed in: `b8747dc2`

**Priority:** Medium (performance improvement, better maintainability) - ✅ DONE

---

### 2. **Refactor Large IO Functions to Extract Pure Logic**

**File:** `Strata/Languages/B3/Verifier/Diagnosis.lean`  
**Reviewer:** atomb  
**Comment:** "There are a number of places in this PR where slightly large `IO` functions appear. When it's feasible, I'd recommend breaking out any non-trivial logic into pure functions that are then called from the `IO` function. Sometimes it's hard to disentangle the logic, but I think it's at least worth attempting."

**Current Implementation:**
- `diagnoseFailureGeneric` is a large `partial def` in `IO`
- Mixes pure logic (expression analysis, conjunction splitting) with IO operations (solver calls)

**Proposed Action:**
- Extract pure logic into separate helper functions:
  - Conjunction splitting logic
  - Expression analysis
  - Result aggregation
- Keep only solver interactions in IO
- This improves testability and clarity

**Priority:** Medium (code quality, testability)

**Files to Refactor:**
- `Strata/Languages/B3/Verifier/Diagnosis.lean` - `diagnoseFailureGeneric`
- `Strata/Languages/B3/Verifier/Statements.lean` - `symbolicExecuteStatements` (if applicable)
- Any other large IO functions in the verifier

---

### 3. **Rename `getStatementMetadata` to `B3AST.Statement.metadata`**

**File:** `Strata/Languages/B3/Verifier/Statements.lean` (line 102)  
**Reviewer:** atomb  
**Comment:** "I'd call this `B3AST.Statement.metadata`, to allow you to say things like `s.metadata` for a statement `s`, as is done elsewhere in the codebase."

**Current Implementation:**
```lean
def getStatementMetadata : B3AST.Statement M → M
  | .check m _ => m
  | .assert m _ => m
  -- ... etc
```

**Proposed Action:**
- Rename to `B3AST.Statement.metadata` 
- Move to `Strata/Languages/B3/DDMTransform/DefinitionAST.lean` (where B3AST is defined)
- This follows the pattern used elsewhere in the codebase
- Allows dot notation: `stmt.metadata` instead of `getStatementMetadata stmt`

**Priority:** Low (naming convention, consistency)

---

### 4. **Update Documentation to Say "SMT Solvers" Not Specific Solver Names**

**File:** `Strata/Languages/B3/Verifier.lean`  
**Reviewer:** shigoel  
**Locations:**
- Line 20: "Converts B3 programs to SMT and verifies them using Z3/CVC5."
- Line 43: "Solver (Z3/CVC5)"

**Comment:** "Let's say SMT solvers, instead of calling out specific ones. We aren't aiming to tie ourselves to them."

**Proposed Action:**
- Line 20: Change to "Converts B3 programs to SMT and verifies them using SMT solvers."
- Line 43: Change to "Solver (e.g., Z3/CVC5)" or just "SMT Solver"
- Review entire file for other instances

**Priority:** Low (documentation clarity)

---

### 5. **Clarify "Possibly Wrong" Wording in Error Messages**

**File:** `Strata/Languages/B3/Verifier.lean` (line 99)  
**Reviewer:** shigoel  
**Comment:** "Nitpick, but maybe it's just me: 'possibly wrong' made me think that the counterexample can be construed as false. I don't think that's the case. You mean the goal is possibly invalid. Right? If so, mind changing the wording to indicate as such?"

**Current Implementation:**
```lean
| .error .counterexample => IO.println "✗ Counterexample (possibly wrong)"
```

**Proposed Action:**
- Change to: "✗ Counterexample (goal may be invalid)" or
- "✗ Counterexample found (assertion may not hold)" or
- "✗ Could not prove (counterexample found)"
- The key is to clarify that the goal/assertion might be wrong, not the counterexample

**Priority:** Low (clarity in user-facing messages)

---

### 6. **Note About `define-fun-rec` for Mutually Recursive Functions**

**File:** `Strata/Languages/B3/Transform/FunctionToAxiom.lean` (line 14)  
**Reviewer:** shigoel  
**Comment:** "That's right. I'll note anyway that there's `define-fun-rec` for mutually recursive definitions."

**Current Documentation:**
```
This is necessary because SMT solvers do not support mutually recursive function definitions
using the `define-fun` syntax.
```

**Proposed Action:**
- Update documentation to acknowledge `define-fun-rec` exists
- Explain why we still use axioms (e.g., broader solver support, or other technical reasons)
- Example: "While SMT-LIB 2.6 provides `define-fun-rec` for mutually recursive definitions, we use quantified axioms for broader solver compatibility and flexibility."

**Priority:** Low (documentation accuracy)

---

### 7. **Future Enhancement: Config Option for Non-Recursive Functions**

**File:** `Strata/Languages/B3/Transform/FunctionToAxiom.lean` (line 30)  
**Reviewer:** shigoel  
**Comment:** "As we chatted offline, one day we ought to have a config option that allows the definition of at least non-recursive functions using `define-fun` instead of using quantified axioms."

**Proposed Action:**
- Add a TODO comment in the code
- Document this as a future enhancement in the PR description or a follow-up issue
- This is not blocking for the current PR

**Priority:** Low (future enhancement, not blocking)

**Suggested TODO:**
```lean
-- TODO: Add config option to use `define-fun` for non-recursive functions
-- instead of quantified axioms. This can improve solver performance for
-- simple function definitions.
```

---

### 8. **Positive Comment: Unused Variable Fix**

**File:** `Strata/Languages/B3/DDMTransform/DefinitionAST.lean` (line 294)  
**Reviewer:** shigoel  
**Comment:** "Thanks -- this was bugging me. :)"

**Change:** `match ho: o with` → `match _: o with`

**Action:** No action needed - this is already fixed in the PR.

---

## Implementation Priority

### High Priority (Should be done before merge)
None - all comments are medium to low priority improvements

### Medium Priority (Recommended before merge)
1. **Use SMT dialect pretty-printer** (#1) - Performance and maintainability
2. **Refactor IO functions** (#2) - Code quality and testability

### Low Priority (Can be done in follow-up PRs)
3. **Rename metadata function** (#3) - Consistency
4. **Update solver documentation** (#4) - Clarity
5. **Clarify error messages** (#5) - User experience
6. **Update function-to-axiom docs** (#6) - Accuracy
7. **Add TODO for define-fun config** (#7) - Future work

---

## Investigation Tasks Before Implementation

### For Comment #1 (SMT Pretty-Printer)
- [ ] Read `Strata/DL/SMT/Format.lean` (if it exists)
- [ ] Check `Strata/DL/SMT/Encoder.lean` for existing formatting
- [ ] Understand how to use SMT dialect's pretty-printer
- [ ] Verify output format matches requirements (no ANF)
- [ ] Check if `Strata.DDM.Util.Format` can be used

### For Comment #2 (Refactor IO Functions)
- [ ] Identify all pure logic in `diagnoseFailureGeneric`
- [ ] Design pure helper functions for:
  - Conjunction detection and splitting
  - Expression traversal
  - Result aggregation
- [ ] Ensure solver calls remain in IO
- [ ] Consider adding unit tests for pure functions

---

## Testing Plan

After implementing changes:
1. Run existing tests: `lake test`
2. Verify B3 verifier examples still work
3. Check that diagnosis output is unchanged (for #1)
4. Ensure refactored code produces same results (for #2)
5. Test dot notation works (for #3)

---

## Notes

- The PR is marked as **Draft** with 1/11 checks failing
- Overall reviewer feedback is positive ("I like the overall approach")
- atomb mentioned they will follow up with a more thorough review
- Most comments are about code quality and maintainability, not correctness
- The architecture and approach are sound

---

## Questions for PR Author

1. For #1: Do you have a preference for which SMT formatting infrastructure to use?
2. For #2: Are there specific reasons the logic is in IO (e.g., performance, debugging)?
3. For #6: What are the technical reasons for preferring axioms over `define-fun-rec`?

---

## Estimated Effort

- Comment #1 (SMT pretty-printer): 2-4 hours (investigation + implementation)
- Comment #2 (Refactor IO): 3-5 hours (careful refactoring + testing)
- Comments #3-7 (Documentation/naming): 1-2 hours total

**Total estimated effort:** 6-11 hours

---

## Next Steps

1. **Review this document** and modify as needed
2. **Prioritize** which comments to address in this PR vs follow-ups
3. **Investigate** SMT formatting infrastructure (Comment #1)
4. **Implement** changes in priority order
5. **Test** thoroughly after each change
6. **Update PR** and request re-review
