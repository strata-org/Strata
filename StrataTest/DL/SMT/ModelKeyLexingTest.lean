/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Imperative.SMTUtils

meta section

/-! ## Which `get-value` response keys the SMT-response dialect can read

A counterexample survives only if the solver's answer parses. Every response
below is well-formed SMT-LIB; what varies is the *spelling* of the key, and the
solver chooses that spelling: it echoes a symbol bare whenever the symbol is a
legal SMT-LIB simple symbol, and pipe-quoted otherwise.

The two alphabets differ. SMT-LIB admits `~ ! @ $ % ^ & * _ - + = < > . ? /` in
a bare simple symbol; the identifier alphabet this dialect parses with admits
only `_ . ? ! @ $` beyond alphanumerics. Every character in the gap
(`%`, `-`, `+`, `*`, `^`, `&`, `=`, `<`, `>`, `/`, `~`) is one a solver may echo bare and
this parser cannot read.

A key that fails to lex takes the whole response with it: `parseModelDDM` catches
the parse error and returns `[]`, so the model is silently empty rather than
wrong. That is why these are pinned: the failure is invisible at the call site,
and the count is the only signal.

Pipe-quoted keys always parse, whatever they contain. That is the property worth
relying on: forcing a quoted echo is what makes a name readable back, not
choosing "safe" characters.
-/

open Imperative.SMT

/-- Report how many valuation pairs a response yields, and under which keys.
    `0 pair(s)` means the response did not parse. -/
private def probe (label : String) (resp : String) : IO Unit := do
  let pairs ← parseModelDDM resp
  IO.println s!"{label}: {pairs.length} pair(s), keys {repr (pairs.map (·.1))}"

/--
info: plain                 : 1 pair(s), keys ["ab"]
quoted apostrophe     : 1 pair(s), keys ["|v'|"]
quoted, interior space: 1 pair(s), keys ["|a b|"]
quoted, leading space : 1 pair(s), keys ["| ax|"]
quoted percent        : 1 pair(s), keys ["|a%pb|"]
quoted hyphen         : 1 pair(s), keys ["|a-b|"]
bare percent          : 0 pair(s), keys []
bare hyphen           : 0 pair(s), keys []
bare leading ?        : 0 pair(s), keys []
bare leading !        : 0 pair(s), keys []
bare interior ?       : 1 pair(s), keys ["x?y"]
-/
#guard_msgs in
#eval do
  -- Keys this parser reads.
  probe "plain                 " "((ab 1))"
  probe "quoted apostrophe     " "((|v'| 1))"
  probe "quoted, interior space" "((|a b| 1))"
  probe "quoted, leading space " "((| ax| 1))"
  probe "quoted percent        " "((|a%pb| 1))"
  probe "quoted hyphen         " "((|a-b| 1))"
  -- Keys it does not: legal SMT-LIB simple symbols outside its alphabet, which
  -- is exactly how a solver echoes them.
  probe "bare percent          " "((a%pb 1))"
  probe "bare hyphen           " "((a-b 1))"
  -- Keys whose *first* character is the problem: `?` and `!` are legal SMT-LIB
  -- simple-symbol characters, so a solver echoes these bare, but this parser
  -- admits only a letter, `_` or `$` first. The same character later is fine,
  -- which is why escaping is confined to the first position.
  probe "bare leading ?        " "((?x 1))"
  probe "bare leading !        " "((!x 1))"
  probe "bare interior ?       " "((x?y 1))"

end
