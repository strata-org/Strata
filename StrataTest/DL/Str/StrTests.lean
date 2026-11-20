/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Str
meta import Strata.DL.SMT.StringLit

meta section

/-! # Tests for the string carriers and their functions

The functions agree with SMT-LIB's: every expected value below was checked against
cvc5 1.3.4 and z3 4.12.6, the solvers Strata ships, on the same SMT-LIB term, edge cases included (`str.substr` and `str.at`
outside the string, `str.indexof` with a negative or too large offset or an empty
pattern, `str.replace` and `str.replace_all` with an empty pattern, `str.from_code`
outside SMT-LIB's alphabet). The UTF-16 tests pin both round trips, including the one
that fails: two lone surrogates in a code-point string become one code point. -/

namespace Strata.Str.Tests

/-- The elements of a string written in Lean: its code points. -/
private def u (s : String) : List Nat := ofLeanString s

/-! ## SMT-LIB's string functions -/

#guard (substr (u "abcdef") 1 3) == (u "bcd")
#guard (substr (u "abcdef") 4 10) == (u "ef")
#guard (substr (u "abc") 3 1) == (u "")
#guard (substr (u "abc") (-1) 2) == (u "")
#guard (substr (u "abc") 0 0) == (u "")
#guard (charAt (u "abc") 1) == (u "b")
#guard (charAt (u "abc") 3) == (u "")
#guard (indexOf (u "abcabc") (u "c") 3) == 5
#guard (indexOf (u "abc") (u "") 3) == 3
#guard (indexOf (u "abc") (u "") 4) == (-1)
#guard (indexOf (u "abc") (u "b") (-1)) == (-1)
#guard (indexOf (u "abc") (u "x") 0) == (-1)
#guard (replace (u "abcabc") (u "b") (u "XY")) == (u "aXYcabc")
#guard (replace (u "abc") (u "") (u "Z")) == (u "Zabc")
#guard (replace (u "abc") (u "x") (u "Z")) == (u "abc")
#guard (replaceAll (u "aaa") (u "aa") (u "b")) == (u "ba")
#guard (replaceAll (u "abab") (u "b") (u "")) == (u "aa")
#guard (replaceAll (u "abc") (u "") (u "Z")) == (u "abc")
#guard (contains (u "abc") (u "")) == true
#guard (contains (u "abc") (u "bc")) == true
#guard (prefixOf (u "ab") (u "abc")) == true
#guard (suffixOf (u "bc") (u "abc")) == true
#guard (suffixOf (u "ab") (u "abc")) == false
#guard (lt (u "ab") (u "abc")) == true
#guard (lt (u "abc") (u "abd")) == true
#guard (lt (u "b") (u "abc")) == false
#guard (le (u "abc") (u "abc")) == true
#guard (toCode (u "a")) == 97
#guard (toCode (u "ab")) == (-1)
#guard (fromCode .smt 196608) == (u "")
#guard (fromCode .smt 97) == (u "a")
#guard (toInt (u "0042")) == 42
#guard (toInt (u "")) == (-1)
#guard (toInt (u "4a")) == (-1)
#guard (fromInt 120) == (u "120")
#guard (fromInt (-3)) == (u "")
#guard (isDigit (u "7")) == true
#guard (isDigit (u "77")) == false

#guard (substr (u "hello") 1 (-2)) == (u "")
#guard (substr (u "hello") 5 1) == (u "")
#guard (indexOf (u "abcabc") (u "bc") 2) == 4
#guard (replace (u "abcabc") (u "bc") (u "X")) == (u "aXabc")
#guard (fromCode .smt 0xD800) == [0xD800]
#guard (fromCode .smt (-1)) == []
#guard (toInt (u "007")) == 7
#guard (toInt (u "1_0")) == (-1)

#guard (indexOf (u "abc") (u "") 0) == 0
#guard (indexOf (u "abc") (u "") (-1)) == (-1)
#guard (charAt (u "abc") (-1)) == (u "")
#guard (indexOf (u "abcabc") (u "bc") 0) == 1
#guard (indexOf (u "abcabc") (u "bc") 5) == (-1)
#guard (contains (u "abcabc") (u "ca")) == true
#guard (contains (u "abc") (u "cb")) == false

/-! ## Carriers -/

-- The library's SMT-LIB alphabet is the SMT encoder's.
#guard Carrier.smt.bound == SMT.StringLit.maxCodePoint + 1

#guard Carrier.smt.wf [0x2FFFF] && !Carrier.smt.wf [0x30000]
#guard Carrier.units.wf [0xD83D] && !Carrier.units.wf [0x1F600]
#guard Carrier.codePoints.wf [0x10FFFF] && !Carrier.codePoints.wf [0x110000]
#guard Carrier.bytes.wf [0xFF] && !Carrier.bytes.wf [0x100]
#guard Carrier.all.all fun c => Carrier.codePoints.includes .smt && c.includes .bytes
#guard (StrOf.cast? .smt (⟨[0x61, 0xE007F], rfl⟩ : StrOf .codePoints)).isNone
#guard (StrOf.cast? .smt (⟨[0x61, 0xD800], rfl⟩ : StrOf .codePoints)).map (·.val) == some [0x61, 0xD800]
#guard fromCode .codePoints 0xE007F == [0xE007F] && fromCode .smt 0xE007F == []

/-! ## Predicates -/

#guard scalar (u "é😀") && !scalar [0xD800] && !scalar [0x110000]
#guard inSmt (u "é😀") && !inSmt [0xE007F]
#guard escOnly [0x61, 0xDCE9] && !escOnly [0xD83D]
#guard noAstralHigh [0xD83D, 0xDE00] && !noAstralHigh [0xDB40, 0xDC67]
#guard noPairing [0xDE00, 0xD83D] && !noPairing [0xD83D, 0xDE00]
#guard wfUtf16 [0x61, 0xD83D, 0xDE00] && !wfUtf16 [0xD83D] && !wfUtf16 [0xDE00, 0xD83D]

/-! ## UTF-16 -/

#guard encodeUtf16 (u "a😀") == [0x61, 0xD83D, 0xDE00]
#guard encodeUtf16 [0x10FFFF] == [0xDBFF, 0xDFFF]
#guard encodeUtf16 [0x30000] == [0xD880, 0xDC00]
#guard decodeUtf16 [0x61, 0xD83D, 0xDE00] == u "a😀"
-- A lone surrogate, and a low surrogate before a high one, decode to themselves.
#guard decodeUtf16 [0xD83D, 0x61] == [0xD83D, 0x61]
#guard decodeUtf16 [0xDE00, 0xD83D] == [0xDE00, 0xD83D]
-- Units always survive the round trip; code points only without a high-low pair.
#guard encodeUtf16 (decodeUtf16 [0xDE00, 0xD83D, 0xDE00]) == [0xDE00, 0xD83D, 0xDE00]
#guard decodeUtf16 (encodeUtf16 [0xDE00, 0xD83D]) == [0xDE00, 0xD83D]
#guard decodeUtf16 (encodeUtf16 [0xD83D, 0xDE00]) == [0x1F600]

/-! ## Lean strings -/

#guard toLeanString? (u "é😀") == some "é😀"
#guard toLeanString? [0xD800] == none
#guard ofLeanString "😀" == [0x1F600]

end Strata.Str.Tests

end
