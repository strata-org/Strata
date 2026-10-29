/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.String

public section

namespace Strata.SMT.StringLit

/-!
# SMT-LIB string literals

SMT-LIB strings contain code points from `0x0` through `0x2FFFF`. Printable ASCII
characters other than `"` and `\` may stand for themselves; every other character is
written as a `\u{...}` escape. Rejecting values outside the alphabet preserves string
identity instead of silently sending a different value to the solver.
-/

/-- The largest code point in the alphabet of SMT-LIB's `String` sort. -/
def maxCodePoint : Nat := 0x2FFFF

namespace Chars

/-- Whether `c` may stand for itself inside an SMT-LIB string literal. -/
def emitAsSelf (c : Char) : Bool :=
  0x20 ≤ c.toNat && c.toNat ≤ 0x7E && c != '"' && c != '\\'

/-- Whether `c` belongs to the SMT-LIB `String` alphabet. -/
def inAlphabet (c : Char) : Bool := c.toNat ≤ maxCodePoint

/-- The shortest lowercase hexadecimal spelling of `n`. -/
def hexDigits (n : Nat) : List Char :=
  let width := (Nat.toDigits 16 n).length
  (_root_.hexDigits width n).map Char.toLower

/-- Escape one character as `\u{h…}`. -/
def esc (c : Char) : List Char :=
  '\\' :: 'u' :: '{' :: (hexDigits c.toNat ++ ['}'])

/-- Escape every character that cannot stand for itself. -/
def escape (cs : List Char) : List Char :=
  cs.flatMap fun c => if emitAsSelf c then [c] else esc c

end Chars

/-- Check that every character can occur in an SMT-LIB string. -/
def validate (s : String) : Except String Unit :=
  match s.toList.find? (fun c => !Chars.inAlphabet c) with
  | some c =>
    .error s!"string literal contains code point U+\
      {String.ofList (Chars.hexDigits c.toNat)}, which is outside the alphabet of \
      SMT-LIB's String sort (0x0-0x2FFFF) and has no literal spelling"
  | none => .ok ()

/-- The body of an SMT-LIB string literal, without its surrounding quotes. -/
def escapeBody (s : String) : Except String String := do
  validate s
  return String.ofList (Chars.escape s.toList)

/-- Render a raw string as a complete SMT-LIB string literal. -/
def toSMTString (s : String) : Except String String :=
  return "\"" ++ (← escapeBody s) ++ "\""

/-- Escape every character that cannot stand for itself and wrap the result in SMT-LIB quotes. -/
def escapeSMTStringLit (s : String) : String :=
  "\"" ++ String.ofList (Chars.escape s.toList) ++ "\""

/-- Replace characters outside the SMT-LIB string alphabet with visible code-point markers. -/
private def makeDiagnosticSafe (s : String) : String :=
  String.ofList <| s.toList.flatMap fun c =>
    if Chars.inAlphabet c then [c]
    else s!"<U+{String.ofList (Chars.hexDigits c.toNat)}>".toList

/-- Render arbitrary diagnostic text without allowing string encoding to hide the original error. -/
def toDiagnosticSMTString (s : String) : String :=
  escapeSMTStringLit (makeDiagnosticSafe s)

/-!
## Reading SMT-LIB string literals

A solver's answer is text we did not write, so the decoder must agree with the
producer about both character values and literal boundaries. SMT-LIB differs
from Lean here: `\n` denotes two characters, `""` denotes one quote, and `\"`
is a backslash followed by the closing quote.

The decoder accepts SMT-LIB's braced and four-digit Unicode escapes and rejects
malformed escapes, surrogate code points, values above `maxCodePoint`, and
unterminated literals. Rejecting ambiguous solver output is safer than accepting
a counterexample containing a different string from the one the solver meant.
-/

private def hexDigitValue? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The character a `\u` escape denotes, or an error naming why it has none. -/
private def escapeChar (n : Nat) : Except String Char :=
  if 0xD800 ≤ n && n ≤ 0xDFFF then
    .error s!"string literal escapes the surrogate code point \
      U+{String.ofList (Nat.toDigits 16 n)}, which no character can hold"
  else if n ≤ maxCodePoint then
    .ok (Char.ofNat n)
  else
    .error s!"string literal escapes the code point \
      U+{String.ofList (Nat.toDigits 16 n)}, which is outside the alphabet of SMT-LIB's \
      String sort (0x0-0x2FFFF)"

/-- Read a `\u{h…h}` body after consuming `\u{`. -/
private partial def takeBracedHex (input : String) (pos : String.Pos.Raw)
    (acc count : Nat) : Option (Nat × String.Pos.Raw) :=
  if pos = input.rawEndPos then
    none
  else
    let c := pos.get input
    let next := pos.next input
    if c = '}' then
      if count = 0 then none else some (acc, next)
    else
      match hexDigitValue? c with
      | some v =>
        if count ≥ 5 then none else takeBracedHex input next (acc * 16 + v) (count + 1)
      | none => none

private def takeHexDigits (input : String) (pos : String.Pos.Raw) :
    (count : Nat) → Option (Nat × String.Pos.Raw)
  | 0 => some (0, pos)
  | count + 1 =>
    if pos = input.rawEndPos then
      none
    else
      match hexDigitValue? (pos.get input) with
      | none => none
      | some digit =>
        match takeHexDigits input (pos.next input) count with
        | none => none
        | some (suffix, stopPos) => some (digit * 16 ^ count + suffix, stopPos)

/-- Read a `\u` escape after consuming the `\u`. -/
private def decodeUEscape (input : String) (pos : String.Pos.Raw) :
    Except String (Char × String.Pos.Raw) :=
  if pos = input.rawEndPos then
    .error "truncated `\\u` escape at the end of a string literal"
  else if pos.get input = '{' then
    match takeBracedHex input (pos.next input) 0 0 with
    | some (n, stopPos) => (escapeChar n).map (·, stopPos)
    | none =>
      .error "malformed `\\u{…}` in a string literal: expected one to five hex digits \
             and a closing `}`"
  else
    match takeHexDigits input pos 4 with
    | some (n, stopPos) => (escapeChar n).map (·, stopPos)
    | none =>
      .error "malformed `\\u` in a string literal: expected `{` or exactly four hex digits"

private partial def decodeAux (input : String) (pos : String.Pos.Raw)
    (acc : List Char) : Except String (String × String.Pos.Raw) :=
  if pos = input.rawEndPos then
    .error "unterminated string literal: the input ends before the closing `\"`"
  else
    let c := pos.get input
    let next := pos.next input
    if c = '"' then
      if next != input.rawEndPos && next.get input = '"' then
        decodeAux input (next.next input) ('"' :: acc)
      else
        .ok (String.ofList acc.reverse, next)
    else if c = '\\' && next != input.rawEndPos && next.get input = 'u' then
      match decodeUEscape input (next.next input) with
      | .error e => .error e
      | .ok (escaped, stopPos) => decodeAux input stopPos (escaped :: acc)
    else if !Chars.inAlphabet c then
      .error s!"string literal contains the raw code point \
        U+{String.ofList (Chars.hexDigits c.toNat)}, which is outside the alphabet of \
        SMT-LIB's String sort (0x0-0x2FFFF)"
    else
      decodeAux input next (c :: acc)

/--
Decode the SMT-LIB string literal at `startPos`, returning its value and the
position immediately after its closing `"`.
-/
def decodeSMTStringLit (input : String) (startPos : String.Pos.Raw := 0) :
    Except String (String × String.Pos.Raw) :=
  if startPos = input.rawEndPos || startPos.get input != '"' then
    .error "expected a string literal to begin with `\"`"
  else
    decodeAux input (startPos.next input) []

/-- Decode a string expected to contain exactly one complete SMT-LIB literal. -/
def unescapeSMTStringLit (s : String) : Except String String :=
  match decodeSMTStringLit s with
  | .error e => .error e
  | .ok (v, stopPos) =>
    if stopPos = s.rawEndPos then
      .ok v
    else
      .error "unexpected characters after the closing `\"` of a string literal"

/-- A semantic value that cannot be serialized as SMT-LIB text. Keeping the
serialization site structured lets callers classify it without inspecting a
human-readable error message. -/
inductive EncodingError where
  | termSerialization (detail : String)
  | typeSerialization (detail : String)
  deriving Repr, BEq

instance : ToString EncodingError where
  toString
    | .termSerialization detail =>
      s!"SMT text encoding failed: term serialization: {detail}"
    | .typeSerialization detail =>
      s!"SMT text encoding failed: type serialization: {detail}"

end Strata.SMT.StringLit
