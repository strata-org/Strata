# PR 499 Review: Add recursive functions to Strata Core

## Overall Assessment: APPROVE ✅

This is a high-quality PR that adds comprehensive recursive function support to Strata Core. The implementation is well-structured, thoroughly tested, and properly documented.

## Summary

The PR successfully adds recursive functions with:
- New `@[scopeSelf]` DDM metadata attribute for bringing function names into scope
- Per-constructor axiom generation for SMT-based verification
- Grammar and translation support in Strata Core
- Proper error handling for unsupported cases (polymorphic recursion, missing decreases clauses)
- ITE evaluation improvement (always reduces both branches for better partial evaluation)

## Strengths

1. **Clean architecture**: Changes are logically separated across DDM, Lambda dialect, and Core language layers
2. **Excellent test coverage**: Includes positive tests, error cases, and complex examples (BinaryTreeSize)
3. **Clear documentation**: The `@[scopeSelf]` attribute is well-documented in DDMDoc.lean
4. **Good error messages**: Unsupported features are rejected with helpful messages
5. **Well-commented code**: Complex sections (binding order, trigger patterns) have explanatory comments

## Comments (4 total - all minor suggestions)

All comments are suggestions for improving clarity and documentation. None are blocking.

### 1. RecursiveAxioms.lean:60 - Name intermediate results for clarity
The index arithmetic is subtle. Suggest naming intermediate results like `numOtherParams` and `paramPos` to make the calculation self-documenting.

### 2. RecursiveAxioms.lean:82 - Improve PE error message
Make the error message more actionable by explaining what to check when PE doesn't reduce.

### 3. Env.lean:210 - Explain polymorphic recursion limitation
Add why polymorphic recursive functions aren't supported (SMT solvers require monomorphic axioms).

### 4. RecursiveFunctionTests.lean:1 - Positive feedback
Excellent test coverage! Tests progress nicely from simple to complex.

## Recommendation

**APPROVE** - Ready to merge after author reviews suggestions. The suggestions are optional improvements; the PR is already in excellent shape.

## Files Reviewed (27 total)

All files have been reviewed and checked off in REVIEW_PR499.md.
