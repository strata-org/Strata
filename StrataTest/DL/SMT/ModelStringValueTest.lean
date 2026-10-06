/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Imperative.SMTUtils
meta import Strata.DL.SMT.StringLit
meta import Strata.DL.SMT.DDMTransform.Translate

meta section

/-! ## Which `get-value` string *values* a counterexample survives

The companion to `ModelKeyLexingTest`, which covers the keys. A value is read from an
external source, so the parser must either preserve its exact string value or reject the
response.

Every response below is well-formed SMT-LIB. What varies is the spelling of the value, and
the solver chooses that spelling. Measured with `(get-value ...)` over known strings on
z3 4.8.17, cvc5 1.2.1 and cvc5 1.3.4:

```
 é                 both: "a\u{e9}b"
 soft hyphen       both: "a\u{ad}b"
 "   (one char)    both: "q""r"
 \   (one char)    z3: "a\"        cvc5: "a\u{5c}"
 \ n (two chars)   z3: "a\ny"      cvc5: "a\u{5c}ny"
 \ b (two chars)   z3: "a\b"       cvc5: "a\u{5c}b"
```

The SMT-response dialect installs `StringLit.decodeSMTStringLit` as its string parser,
so the response structure and the solver's literal syntax are parsed in one pass.

The rendered values below come from `SMTDDM.termToString`, i.e. from the *emitter*, so each
line is a round trip: solver spelling in, our spelling out. A value that reads back as a
different string shows up as a different spelling here.
-/

open Imperative.SMT
open Strata.SMTDDM (termToString)

/-- Report what a replayed `(get-value ...)` response yields. -/
private def probe (label : String) (resp : String) : IO Unit := do
  match ← parseModelDDMExcept resp with
  | .ok pairs =>
    let rendered := pairs.map fun (k, v) =>
      (k, (termToString v).toOption.getD "<unrenderable>")
    IO.println s!"{label}: {pairs.length} pair(s) {rendered}"
  | .error _ => IO.println s!"{label}: unreadable"

/-! ### Representative solver spellings round-trip -/

/--
info: ascii            : 1 pair(s) [(s@1, "aXb")]
raw non-ascii    : 1 pair(s) [(s@1, "a\u{e9}b")]
hex escape       : 1 pair(s) [(s@1, "a\u{e9}b")]
soft hyphen      : 1 pair(s) [(s@1, "a\u{ad}b")]
above the BMP    : 1 pair(s) [(s@1, "a\u{1f600}b")]
doubled quote    : 1 pair(s) [(s@1, "a\u{22}b")]
four-digit escape: 1 pair(s) [(s@1, "a\u{e9}b")]
NUL              : 1 pair(s) [(s@1, "a\u{0}b")]
newline escape   : 1 pair(s) [(s@1, "a\u{a}b")]
two pairs        : 2 pair(s) [(s@1, "a\u{e9}b"), (t@1, "a\u{22}b")]
-/
#guard_msgs in
#eval do
  probe "ascii            " "((s@1 \"aXb\"))"
  probe "raw non-ascii    " "((s@1 \"aéb\"))"
  probe "hex escape       " "((s@1 \"a\\u{e9}b\"))"
  probe "soft hyphen      " "((s@1 \"a\\u{ad}b\"))"
  probe "above the BMP    " "((s@1 \"a\\u{1f600}b\"))"
  probe "doubled quote    " "((s@1 \"a\"\"b\"))"
  probe "four-digit escape" "((s@1 \"a\\u00e9b\"))"
  probe "NUL              " "((s@1 \"a\\u{0}b\"))"
  probe "newline escape   " "((s@1 \"a\\u{a}b\"))"
  probe "two pairs        " "((s@1 \"a\\u{e9}b\") (t@1 \"a\"\"b\"))"

/-! ### Raw backslashes in solver responses

SMT-LIB treats a raw `\` as a literal character, while a Lean-style string reader treats
it as the start of an escape. The SMT-LIB reader preserves the backslash, and the emitter
then re-spells it as `\u{5c}`. Equivalent z3 and cvc5 spellings therefore produce the
same rendered value below. -/

/--
info: z3 backslash-n     : 1 pair(s) [(s@1, "a\u{5c}ny")]
cvc5 backslash-n   : 1 pair(s) [(s@1, "a\u{5c}ny")]
z3 backslash-b     : 1 pair(s) [(s@1, "a\u{5c}b")]
cvc5 backslash-b   : 1 pair(s) [(s@1, "a\u{5c}b")]
z3 trailing \      : 1 pair(s) [(s@1, "a\u{5c}")]
cvc5 trailing \    : 1 pair(s) [(s@1, "a\u{5c}")]
z3 \ then quote    : 1 pair(s) [(s@1, "a\u{5c}\u{22}b")]
-/
#guard_msgs in
#eval do
  probe "z3 backslash-n     " "((s@1 \"a\\ny\"))"
  probe "cvc5 backslash-n   " "((s@1 \"a\\u{5c}ny\"))"
  probe "z3 backslash-b     " "((s@1 \"a\\b\"))"
  probe "cvc5 backslash-b   " "((s@1 \"a\\u{5c}b\"))"
  probe "z3 trailing \\      " "((s@1 \"a\\\"))"
  probe "cvc5 trailing \\    " "((s@1 \"a\\u{5c}\"))"
  probe "z3 \\ then quote    " "((s@1 \"a\\\"\"b\"))"

/-! ### The adversarial cases

A malformed or hostile response must fail. Decoding one would trust a counterexample
containing a string that the program does not contain.

The refusals follow `StringLit.decodeSMTStringLit`: the letter of the standard would read a
malformed `\u{` as literal characters, and we refuse instead, because a conforming producer
escapes the backslash whenever what follows could begin an escape — measured on both
solvers, which echo the 6-character string `\u{ad}` as `"\u{5c}u{ad}"` and give `str.len`
4, 6 and 9 for `\u{}`, `\u{zz}` and `\u{30000}`. So a bare malformed `\u{` means the
response is truncated, hostile, or from a producer whose rules we do not know. -/

/--
info: unterminated     : unreadable
unterminated, esc: unreadable
empty escape     : unreadable
non-hex escape   : unreadable
unclosed brace   : unreadable
six hex digits   : unreadable
long hex run     : unreadable
truncated \u     : unreadable
short \u         : unreadable
above the alphabet: unreadable
raw above alphabet: unreadable
above Unicode    : unreadable
surrogate        : unreadable
surrogate, 4-digit: unreadable
z3 sign-extended : unreadable
lone quote       : unreadable
unterminated pipe: unreadable
-/
#guard_msgs in
#eval do
  probe "unterminated     " "((s@1 \"abc))"
  probe "unterminated, esc" "((s@1 \"abc\\u{41}))"
  probe "empty escape     " "((s@1 \"a\\u{}b\"))"
  probe "non-hex escape   " "((s@1 \"a\\u{zz}b\"))"
  probe "unclosed brace   " "((s@1 \"a\\u{41b\"))"
  probe "six hex digits   " "((s@1 \"a\\u{000041}b\"))"
  probe "long hex run     " "((s@1 \"a\\u{0000000041}b\"))"
  probe "truncated \\u     " "((s@1 \"a\\u0g41b\"))"
  probe "short \\u         " "((s@1 \"a\\u0\"))"
  probe "above the alphabet" "((s@1 \"a\\u{30000}b\"))"
  probe "raw above alphabet" <|
    "((s@1 \"a" ++ String.ofList [Char.ofNat 0x30000] ++ "b\"))"
  probe "above Unicode    " "((s@1 \"a\\u{110000}b\"))"
  probe "surrogate        " "((s@1 \"a\\u{d800}b\"))"
  probe "surrogate, 4-digit" "((s@1 \"a\\udfffb\"))"
  probe "z3 sign-extended " "((s@1 \"h\\u{ffffffc3}\\u{ffffffa9}\"))"
  probe "lone quote       " "((s@1 \"))"
  probe "unterminated pipe" "((|s@1 \"ab\"))"

/-! ### Parsing stops after the model

A quote inside a quoted symbol is not a string delimiter, and malformed trailing output
does not invalidate a complete model parsed before it. -/

/--
info: quote inside a key: 1 pair(s) [(|a"b|, "v")]
junk after model  : 1 pair(s) [(s@1, "ok")]
junk before model : unreadable
-/
#guard_msgs in
#eval do
  probe "quote inside a key" "((|a\"b| \"v\"))"
  probe "junk after model  " "((s@1 \"ok\"))\n(error \"stray \\u{zz} here\")"
  probe "junk before model " "(error \"stray \\u{zz} here\")\n((s@1 \"ok\"))"

end
