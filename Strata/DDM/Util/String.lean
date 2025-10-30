/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
This file contains auxillary definitions for Lean core types that could be
potentially useful to add.
-/

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

namespace String

/--
Auxiliary for `indexOf`. Preconditions:
* `sub` is not empty
* `i` is an indexes into `s`
* `j` is an index into `sub`, and not at the end

It represents the state where the first `j` bytes of `sep` match the bytes `i-j .. i` of `s`.
-/
def indexOfAux (s sub : String) (i : Pos) (j : Pos) : Option Pos :=
  if s.atEnd i then
    none
  else
    if s.get i == sub.get j then
      let i := s.next i
      let j := sub.next j
      if sub.atEnd j then
        some (i - j)
      else
        indexOfAux s sub i j
    else
      indexOfAux s sub (s.next (i - j)) 0
termination_by (s.endPos.1 - (i - j).1, sub.endPos.1 - j.1)
decreasing_by
  focus
    rename_i i₀ j₀ _ eq h'
    rw [show (s.next i₀ - sub.next j₀).1 = (i₀ - j₀).1 by
      show (_ + Char.utf8Size _) - (_ + Char.utf8Size _) = _
      rw [(beq_iff_eq ..).1 eq, Nat.add_sub_add_right]; rfl]
    right; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.le_add_right ..) (Nat.gt_of_not_le (mt decide_eq_true h')))
      (lt_next sub _)
  focus
    rename_i h _
    left; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.gt_of_not_le (mt decide_eq_true h)))
      (lt_next s _)

/--
This return the first index in `s` greater than or equal to `b` that contains
the bytes in `sub`.

N.B. This will potentially read the same character multiple times.  It could be
made more efficient by using Boyer-Moore string search.
-/
def indexOf (s sub : String) (b : Pos := 0) : Option Pos :=
  if sub.isEmpty then
    some b
  else
    indexOfAux s sub b 0

theorem le_def (p q : String.Pos) : p ≤ q ↔ p.byteIdx ≤ q.byteIdx := by
  trivial

theorem Pos.le_of_lt {p q : String.Pos} (a : p < q) : p ≤ q := by
  simp at a
  simp [String.le_def]
  omega

@[simp]
theorem pos_le_refl (pos : String.Pos) : pos ≤ pos := by
  unfold LE.le
  simp [instLEPos]

theorem next_mono (s : String) (p : String.Pos) : p < s.next p := by
  simp [String.next, Char.utf8Size]
  repeat (split; omega)
  omega

theorem findAux_mono (s : String) (pred : Char → Bool) (stop p : String.Pos)
  : p ≤ s.findAux pred stop p := by
  unfold String.findAux
  split
  case isFalse _ =>
    simp
  case isTrue p2_le_stop =>
    split
    case isTrue _ =>
      simp
    case isFalse _ =>
      have termProof : sizeOf (stop - s.next p) < sizeOf (stop - p) := by
        have g : p < (s.next p) := String.next_mono _ _
        simp at g
        simp at p2_le_stop;
        simp [sizeOf, String.Pos._sizeOf_1]
        omega
      apply String.Pos.le_trans
      apply String.Pos.le_of_lt
      apply String.next_mono s
      apply String.findAux_mono
  termination_by (stop - p)

def splitLines (s : String) := s.split (· ∈  ['\n', '\r'])

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
