# B3 Grammar Conformance Issues

This document tracks issues found when comparing the B3 implementation against the official B3 grammar specification.

## Verified Issues (Tests Failing)

### 1. Missing "then" keyword in if-then-else
**Grammar:** `"if" Expr Expr "else" Expr`  
**Implementation:** `"if " c:0 " then " ... " else " ...`  
**Status:** ❌ Test fails with "unexpected token; expected 'then'"  
**Fix Required:** Remove " then " from the syntax

### 2. if-then-else precedence too low
**Grammar:** `PrimaryExpr ::= EndlessExpr | AtomicExpr` (high precedence)  
**Implementation:** `@[prec(3)]` (very low precedence)  
**Status:** ❌ Test fails - adds unnecessary parentheses  
**Expected:** `1 + if true then 2 else 3`  
**Actual:** `1 + (if true then 2 else 3)`  
**Fix Required:** Change to high precedence (e.g., `@[prec(40)]`)

## Tests Added

The following tests were added to `StrataTest/Languages/B3/DDMFormatExpressionsTests.lean`:

1. `if true 1 else 0` - Tests if-then-else syntax (no "then")
2. `true <== false <== true` - Tests <== left-associativity
3. `true ==> false ==> true` - Tests ==> right-associativity  
4. `true <==> false ==> true` - Tests <==> vs ==> precedence
5. `1 + if true then 2 else 3` - Tests if-then-else precedence

## Next Steps

1. Fix the "then" keyword issue in `ParseCST.lean`
2. Fix the if-then-else precedence
3. Verify <== associativity (may already be correct)
4. Verify <==> associativity and precedence
5. Re-run tests to confirm all pass
