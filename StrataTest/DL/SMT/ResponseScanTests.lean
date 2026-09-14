/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.SMT.IncrementalSolver

meta section

/-! ## Scanning a response that may contain quoted symbols

A symbol we emit can hold any character inside `|…|`, `(`, `)` and a space
included. The incremental solver reads a `get-value` response by paren depth and a
`get-unsat-assumptions` response by tokens, so both have to know where a quoted
symbol begins and ends.

The failures these pin are silent. A `)` inside a name ends the s-expression early,
returning a truncated model; a space inside one splits a literal in two, so it
matches no assumption that was sent. -/

open Strata.SMT.IncrementalSolver

/-! ### Paren depth

Only parens outside a quoted symbol or a string literal count. -/

#guard (scanParens "((a 1))" {}).1 == 0
#guard (scanParens "((|a)b| 1))" {}).1 == 0
#guard (scanParens "((|a(b| 1))" {}).1 == 0
#guard (scanParens "((x \"a)b\"))" {}).1 == 0

/-! A genuinely unbalanced line still reports its depth, which is what keeps the
reader going to the next line. -/

#guard (scanParens "((a 1)" {}).1 == 1

/-! The scan state carries across lines, so a symbol is not misread because the
response was wrapped. -/

#guard
  let (d1, st1) := scanParens "((|a)b|" {}
  let (d2, _) := scanParens " 1))" st1
  d1 + d2 == 0

/-! ### Tokens

A quoted symbol stays one token, delimiters included, because that is the spelling
the emitter sent and the spelling the solver echoes. -/

#guard splitTopLevelTokens "(a b)" == ["a", "b"]
#guard splitTopLevelTokens "(|a b| c)" == ["|a b|", "c"]
#guard splitTopLevelTokens "(|a)b| c)" == ["|a)b|", "c"]
#guard splitTopLevelTokens "()" == []
#guard splitTopLevelTokens "" == []

/-! An element need not be an atom. `check-sat-assuming` takes negated literals, so a
nested s-expression is one token; splitting on every paren would tear `(not p)` into
two tokens matching no assumption that was sent. -/

#guard splitTopLevelTokens "((not p) q)" == ["(not p)", "q"]
#guard splitTopLevelTokens "(p (not q) r)" == ["p", "(not q)", "r"]
#guard splitTopLevelTokens "((not |a b|))" == ["(not |a b|)"]

end
