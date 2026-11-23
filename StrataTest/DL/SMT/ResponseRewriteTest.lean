/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Imperative.SMTUtils

meta section

/-! ## The rewrites applied to a solver's `get-value` response before it is parsed

Each rewrite copies string literals and quoted symbols unchanged. Each runs in constant
stack space, so a response of two million characters is rewritten as well as a short one.
-/

open Imperative.SMT

-- A bitvector literal becomes its indexed form; `#` inside a string literal or a quoted symbol
-- is copied, and so is a `#` that starts no literal.
#guard rewriteBVLiterals "((x #b101) (y #xFf) (s \"#b1\"\"#x2\") (|#b1| #) (z #q))" ==
  "((x (_ bv5 3)) (y (_ bv255 8)) (s \"#b1\"\"#x2\") (|#b1| #) (z #q))"

-- A bare symbol that starts with `@` is quoted; a `@` inside a symbol, a string literal or a
-- quoted symbol is copied.
#guard quoteSolverSymbols "((x@1 @S_0) (s \"@a\") (|@b| (f @c)))" ==
  "((x@1 |@S_0|) (s \"@a\") (|@b| (f |@c|)))"

-- A bare `/` token is quoted; a `/` inside a longer symbol, a string literal or a quoted
-- symbol is copied.
#guard quoteDivisionSymbol "((r (/ 1 2)) (a/b 1) (s \"/\") (|/| 2))" ==
  "((r (|/| 1 2)) (a/b 1) (s \"/\") (|/| 2))"

-- A closing `"` or `|` ends a token, so a bare `@` symbol or `/` token right after it is quoted.
#guard quoteSolverSymbols "(\"a\"@S_0 |b|@S_1)" == "(\"a\"|@S_0| |b||@S_1|)"
#guard quoteDivisionSymbol "(\"a\"/ |b|/)" == "(\"a\"|/| |b||/|)"

/-- A response of 2,160,000 characters, every kind of token repeated. -/
private def largeResponse : String :=
  String.ofList (List.replicate 60000 "(x #b101 |a\"b| \"q\"\"r\" @S_0 (/ 1 2)) ".toList).flatten

#guard largeResponse.length == 2160000

#guard (rewriteBVLiterals largeResponse).length == 2400000

#guard (quoteSolverSymbols largeResponse).length == 2280000

#guard (quoteDivisionSymbol largeResponse).length == 2280000

end -- meta section
