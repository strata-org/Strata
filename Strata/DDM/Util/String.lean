/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Init.Data.String.Defs

/-
This file contains auxillary definitions for String.

If they are general purpose, we keep them as private symbols
that could be imported via import all.  Otherwise they are
added to Strata.
-/

namespace String

@[simp]
theorem isEmpty_eq (s : _root_.String) : s.isEmpty = (s == "") := by
  simp only [String.isEmpty, BEq.beq, String.utf8ByteSize_eq_zero_iff]

def replicate (n : Nat) (c : Char) := n.repeat (a := "") (·.push c)

/--
Indicates s has a substring at the given index.

Requires a bound check that shows index is in bounds.
-/
private def hasSubstringAt (s sub : String) (i : Pos.Raw) (index_bound : i.byteIdx + sub.utf8ByteSize ≤ s.utf8ByteSize) : Bool :=
  sub.bytes.size.all fun j jb =>
    have p : i.byteIdx + j < s.bytes.size := by
      change i.byteIdx + sub.bytes.size ≤ s.bytes.size at index_bound
      grind
    s.bytes[i.byteIdx + j]'p == sub.bytes[j]

/--
Auxiliary for `indexOf`. Preconditions:
* `sub` is not empty
* `i` is an indexes into `s`
* `j` is an index into `sub`, and not at the end

It represents the state where the first `j` bytes of `sep` match the bytes `i-j .. i` of `s`.
-/
private def Pos.Raw.indexOfAux (s sub : String) (subp : sub.utf8ByteSize > 0) (i : Pos.Raw) : Option Pos.Raw :=
  if h : i.byteIdx + sub.utf8ByteSize ≤ s.utf8ByteSize then
    if s.hasSubstringAt sub i h then
      some i
    else
      (i.next s).indexOfAux s sub subp
  else
    none
termination_by s.rawEndPos.byteIdx - i.byteIdx
decreasing_by
  simp only [Pos.Raw.next, Pos.Raw.add_char_eq, rawEndPos]
  have p : (i.get s).utf8Size > 0 := Char.utf8Size_pos _
  grind

/--
This return the first index in `s` greater than or equal to `b` that contains
the bytes in `sub`.

N.B. This will potentially read the same character multiple times.  It could be
made more efficient by using Boyer-Moore string search.
-/
def indexOfRaw (s sub : String) (b : Pos.Raw := 0) : Option Pos.Raw :=
  if subp : sub.utf8ByteSize > 0 then
    b.indexOfAux s sub subp
  else
    some b

def splitLines (s : String) := s.splitToList (· ∈  ['\n', '\r'])

/--
info: [" ab", "cd", "", "de", ""]
-/
#guard_msgs in
#eval " ab\ncd\n\nde\n".splitLines

/--
info: [""]
-/
#guard_msgs in
#eval "".splitLines

end String

public section
namespace Strata

/--
Return true if this is a non-printable 8-bit character
-/
private def useXHex ( c : Char) : Bool :=
  c < '\x20' ∨ '\x7f' ≤ c ∧ (c < '\xa1' ∨ c == '\xad')

private def escapeStringLitAux (acc : String) (c : Char) : String :=
  if c == '"' then
    acc ++ "\\\""
  else if c == '\\' then
    acc ++ "\\\\"
  else if c == '\n' then
    acc ++ "\\n"
  else if c == '\r' then
    acc ++ "\\r"
  else if c == '\t' then
    acc ++ "\\t"
  else if useXHex c then
    let i := c.toNat
    let digits := Nat.toDigits 16 i
    if i < 16 then
      s!"{acc}\\x0{digits[0]!}"
    else
      assert! digits.length = 2
      s!"{acc}\\x{digits[0]!}{digits[1]!}"
  else
    acc.push c

def escapeStringLit (s : String) : String :=
  s.foldl escapeStringLitAux "\"" ++ "\""

end Strata
end
