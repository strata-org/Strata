/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.SMT.StringLit
meta import Strata.DL.SMT.DDMTransform.Translate

meta section

/-! ## Tests for escaping arbitrary strings into SMT-LIB string literals

These tests pin exact spellings, rejection outside the `String` alphabet, injectivity,
and composition with the escaping applied by `StrataDDM.Format`. Solver verdicts are
covered by `StrataTest.Languages.Core.Tests.SMTStringLiteralEscapingTest`.
-/

open Strata.SMT

/-- `escapeBody`'s result as an `Option`, since `Except` carries no `BEq`. `none` is the
    refusal of a code point outside the `String` sort's alphabet. -/
private def esc (s : String) : Option String := (StringLit.escapeBody s).toOption

/-! ### Printable ASCII is untouched -/

#guard esc "" == some ""
#guard esc "hello" == some "hello"
#guard esc "Hello, World!" == some "Hello, World!"
#guard esc "~!@#$%^&*()_+-={}[]|:;'<>,.?/" == some "~!@#$%^&*()_+-={}[]|:;'<>,.?/"
#guard esc " " == some " "

/-! ### The two characters that must not be emitted as themselves

A backslash names itself as `\u{5c}` and so can no longer begin a `\u{...}` the solver
would interpret. The source strings `\u{41}` and `A` therefore retain distinct spellings. -/

#guard esc "\\" == some "\\u{5c}"
#guard esc "\\u{41}" == some "\\u{5c}u{41}"
#guard esc "A" == some "A"
#guard esc "C:\\tmp" == some "C:\\u{5c}tmp"

/-! A double quote. SMT-LIB's own spelling is `""`; `\u{22}` denotes the same single
    character, and is used instead so the result holds no `"` at all — see the fixed-point
    section below. -/
#guard esc "a\"b" == some "a\\u{22}b"

/-! ### Everything above printable ASCII -/

#guard esc "héllo" == some "h\\u{e9}llo"
#guard esc "α" == some "\\u{3b1}"
#guard esc "日本" == some "\\u{65e5}\\u{672c}"

/-! Above the BMP. Five hex digits is `\u{...}`'s limit and the alphabet's, so an emoji
    is representable and needs no surrogate pair. -/
#guard esc "😀" == some "\\u{1f600}"

/-! ### Control characters, including the ones with no printable spelling

A newline is escaped rather than emitted, which keeps a literal on one line; our reading
of solver output is line-oriented, so a literal that spanned lines would be split. -/

#guard esc "a\nb" == some "a\\u{a}b"
#guard esc "a\tb" == some "a\\u{9}b"
#guard esc "a\rb" == some "a\\u{d}b"
#guard esc (String.ofList [Char.ofNat 0]) == some "\\u{0}"
#guard esc (String.ofList [Char.ofNat 0x7F]) == some "\\u{7f}"
#guard esc (String.ofList [Char.ofNat 0x80]) == some "\\u{80}"
#guard esc (String.ofList [Char.ofNat 0xA0]) == some "\\u{a0}"
#guard esc (String.ofList [Char.ofNat 0xAD]) == some "\\u{ad}"

/-! ### Above the alphabet: refused, not encoded

The `String` sort's alphabet stops at `0x2FFFF`, so `escapeBody` rejects larger code
points rather than emitting text that denotes a different string. -/

#guard esc (String.ofList [Char.ofNat 0x2FFFF]) == some "\\u{2ffff}"
#guard esc (String.ofList [Char.ofNat 0x30000]) == none
#guard esc (String.ofList [Char.ofNat 0x10FFFF]) == none

/-! A lone surrogate needs no rule: `Char` excludes `0xD800`-`0xDFFF`, so `Char.ofNat`
    maps one to `'\0'` and it can never reach the escaping as a surrogate. -/
#guard (Char.ofNat 0xD800).toNat == 0

/-! Complete literals use the same lossless escaping as term strings. -/
#guard (StringLit.toSMTString "a\"b").toOption == some "\"a\\u{22}b\""
#guard (StringLit.toSMTString (String.ofList [Char.ofNat 0x30000])).toOption == none

/-! Diagnostic strings remain reportable even when they contain a code point the solver
cannot represent. The marker exposes which value was replaced instead of hiding the
original error behind a second encoding failure. -/
#guard StringLit.toDiagnosticSMTString "a\"b" == "\"a\\u{22}b\""
#guard
  StringLit.toDiagnosticSMTString (String.ofList ['a', Char.ofNat 0x30000, 'b']) ==
    "\"a<U+30000>b\""

/-! ### The escaping is injective on what it accepts

What soundness needs. Two distinct source strings must not share a spelling, or a
solver may equate terms the program keeps apart. Spot-checked on the pairs that an
under-escaping collapses. -/

private def distinct : List String :=
  ["A", "\\u{41}", "\\", "\\\\", "é", "\\u{e9}", "\"", "\\u{22}", "a\nb", "a\\u{a}b",
   "", " ", "😀"]

#guard
  let bodies := distinct.filterMap esc
  bodies.length == distinct.length && bodies.eraseDups.length == distinct.length

/-! ### The formatter callback owns the concrete syntax

The DDM AST keeps the raw string. `SMTDDM.termToString` installs
`StringLit.escapeSMTStringLit`, which applies the same lossless escaping as
`toSMTString`. -/

private def formatCorpus : List String :=
  ["", "hello", "Hello, World!", "héllo", "α", "日本", "😀", "a\"b", "\\", "\\u{41}",
   "C:\\tmp", "a\nb", "a\tb", String.ofList [Char.ofNat 0], String.ofList [Char.ofNat 0x7F],
   String.ofList [Char.ofNat 0xAD], "~!@#$%^&*()_+-={}[]|:;'<>,.?/"]

#guard
  formatCorpus.all fun s =>
    match StringLit.toSMTString s with
    | .error _ => false
    | .ok literal => StringLit.escapeSMTStringLit s == literal

/-! ### The whole emission path

`SMTDDM.termToString` is what `Solver.termToSMTString` calls, so this is the exact text
that reaches the `.smt2` file. -/

open Strata.SMTDDM (termToString)
open Strata.SMT (Term TermPrim)

private def strTerm (s : String) : Term := .prim (.string s)

#guard (termToString (strTerm "hello")).toOption == some "\"hello\""
#guard (termToString (strTerm "héllo")).toOption == some "\"h\\u{e9}llo\""
#guard (termToString (strTerm "😀")).toOption == some "\"\\u{1f600}\""
#guard (termToString (strTerm "\\u{41}")).toOption == some "\"\\u{5c}u{41}\""
#guard (termToString (strTerm "a\"b")).toOption == some "\"a\\u{22}b\""
#guard (termToString (strTerm "a\nb")).toOption == some "\"a\\u{a}b\""

/-! An unrepresentable code point fails the conversion rather than emitting anything. -/
#guard (termToString (strTerm (String.ofList [Char.ofNat 0x30000]))).toOption == none

/-! ### Reading a literal back

A counterexample travels the same path in reverse, and a reader that disagrees with the
producer does not fail — it yields a *different string*. `StringLit.decodeSMTStringLit`
is installed as the response parser's string callback.

What belongs here is the composition of the two directions — the property that makes a
counterexample trustworthy at all. Every accepted string must read back as *that string*;
this is a property of the whole round trip rather than either half in isolation. -/

private def roundTripCorpus : List String :=
  formatCorpus ++ ["\\\\", "a\\u{5c}b", "\\n", "é\\u{41}", "\"\"", "😀\\",
                       String.ofList [Char.ofNat 0x1F, Char.ofNat 0x20, Char.ofNat 0x7E],
                       String.ofList [Char.ofNat 0x2FFFF]]

#guard
  roundTripCorpus.all fun s =>
    match termToString (strTerm s) with
    | .error _ => false
    | .ok lit => (StringLit.unescapeSMTStringLit lit).toOption == some s

/-! A string the emission path *refuses* is refused there, not silently round-tripped
through a different spelling. -/

#guard (termToString (strTerm (String.ofList [Char.ofNat 0x30000]))).toOption == none

/-! ### Solver spellings accepted by the decoder -/

private def mkStr (cs : List Nat) : String := String.ofList (cs.map Char.ofNat)
private def dec (s : String) : Option String := (StringLit.unescapeSMTStringLit s).toOption
private def decPrefix (s : String) : Option (String × String) := do
  let (value, stopPos) ← (StringLit.decodeSMTStringLit s).toOption
  return (value, String.Pos.Raw.extract s stopPos s.rawEndPos)

#guard dec "\"\"" == some ""
#guard dec "\"hello\"" == some "hello"
#guard dec "\"a\\u{e9}b\"" == some "aéb"
#guard dec "\"a\\u{ad}b\"" == some (mkStr [0x61, 0xAD, 0x62])
#guard dec "\"\\u{1f600}\"" == some "😀"
#guard dec "\"\\u{0}\"" == some (mkStr [0])
#guard dec "\"\\u{2ffff}\"" == some (mkStr [0x2FFFF])
#guard dec "\"a\\u{a}b\"" == some "a\nb"

/-! Uppercase digits and the four-digit form are also legal. -/

#guard dec "\"a\\u{AD}b\"" == some (mkStr [0x61, 0xAD, 0x62])
#guard dec "\"a\\u00e9b\"" == some "aéb"
#guard dec "\"a\\u00E9b\"" == some "aéb"

/-! A doubled quote denotes one quote. -/

#guard dec "\"a\"\"b\"" == some "a\"b"
#guard dec "\"\"\"\"" == some "\""

/-! A backslash that does not begin a valid Unicode escape stands for itself. -/

#guard dec "\"a\\ny\"" == some "a\\ny"
#guard dec "\"a\\b\"" == some "a\\b"
#guard dec "\"a\\\"" == some "a\\"
#guard dec "\"a\\u{5c}ny\"" == some "a\\ny"

/-! Solvers should escape non-ASCII output, but accepting the raw character is unambiguous. -/

#guard dec "\"aéb\"" == some "aéb"
#guard dec (mkStr [0x22, 0x2FFFF, 0x22]) == some (mkStr [0x2FFFF])

/-! ### Malformed or unrepresentable literals -/

#guard dec "\"abc" == none
#guard dec "\"abc\\u{41}" == none
#guard dec "\"a\\u{}b\"" == none
#guard dec "\"a\\u{zz}b\"" == none
#guard dec "\"a\\u{41\"" == none
#guard dec "\"a\\u{41" == none
#guard dec "\"a\\u00\"" == none
#guard dec "\"a\\u0g41b\"" == none
#guard dec "\"a\\u\"" == none
#guard dec "\"\\u{110000}\"" == none
#guard dec "\"\\u{000041}\"" == none
#guard dec "\"\\u{ffffffff}\"" == none
#guard dec "\"\\u{30000}\"" == none
#guard dec (mkStr [0x22, 0x61, 0x30000, 0x62, 0x22]) == none
#guard dec "\"\\u{d800}\"" == none
#guard dec "\"\\u{dfff}\"" == none
#guard dec "\"\\ud800\"" == none
#guard dec "\"h\\u{ffffffc3}\\u{ffffffa9}\"" == none
#guard dec "abc" == none
#guard dec "" == none
#guard dec "\"" == none
#guard dec "\"ab\" trailing" == none

/-! The prefix decoder returns the unconsumed input after a complete literal. -/

#guard decPrefix "\"ab\" trailing" == some ("ab", " trailing")
#guard decPrefix "\"a\"b\"" == some ("a", "b\"")

end
