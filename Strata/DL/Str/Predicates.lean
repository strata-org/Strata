/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Str.Ops

/-! # Predicates on strings

What a language guarantees, checks or ignores about its strings is a predicate on
values, which a front end assumes, asserts or leaves out at each program point.

*Pointwise* predicates say that every element is in a set: `scalar` (no surrogate,
below `0x110000`, which Lean's and Rust's characters are), `inSmt` (below `0x30000`,
SMT-LIB's alphabet), `escOnly` (scalar values and the `U+DC80` to `U+DCFF` that
Python's `surrogateescape` writes back as bytes), `ascii`, `latin1`, and
`noAstralHigh` (no high surrogate of a code point at or above `0x30000`). Every
operation of `Strata.DL.Str.Ops` that builds a string from its arguments keeps each
of them (`substr_all` and its siblings).

*Structural* predicates constrain neighbors: `wfUtf16` (every high surrogate directly
followed by a low one, and every low one directly preceded by a high one), and
`noPairing` (no high surrogate directly followed by a low one), the condition under
which a code-point string survives a round trip through UTF-16.

The four lemmas here are one-line characterizations of the definitions, so they stay
beside them. -/

@[expose] public section

namespace Strata.Str

/-- Whether `u` is a surrogate, `U+D800` to `U+DFFF`. -/
def isSurrogate (u : Nat) : Bool := 0xD800 ≤ u && u ≤ 0xDFFF

/-- Whether `u` is a high surrogate, `U+D800` to `U+DBFF`, the first half of a pair. -/
def isHighSurrogate (u : Nat) : Bool := 0xD800 ≤ u && u ≤ 0xDBFF

/-- Whether `u` is a low surrogate, `U+DC00` to `U+DFFF`, the second half of a pair. -/
def isLowSurrogate (u : Nat) : Bool := 0xDC00 ≤ u && u ≤ 0xDFFF

/-- Whether `u` is a Unicode scalar value: a code point that is not a surrogate. -/
def isScalarValue (u : Nat) : Bool := u < 0x110000 && !isSurrogate u

/-- Every element is a scalar value: the strings Lean's `String` and Rust's `str` hold. -/
def scalar (s : List Nat) : Bool := s.all isScalarValue

/-- Every element is below `0x30000`: the code-point strings SMT-LIB holds. -/
def inSmt (s : List Nat) : Bool := Carrier.smt.wf s

/-- Every element is a scalar value or one of the 128 code points `U+DC80` to `U+DCFF`
    that Python's `surrogateescape` decodes an undecodable byte to. -/
def escOnly (s : List Nat) : Bool :=
  s.all fun u => isScalarValue u || (0xDC80 ≤ u && u ≤ 0xDCFF)

/-- Every element is below `0x80`. -/
def ascii (s : List Nat) : Bool := s.all (· < 0x80)

/-- Every element is below `0x100`. -/
def latin1 (s : List Nat) : Bool := s.all (· < 0x100)

/-- No element is a high surrogate `U+D880` to `U+DBFF`: those are exactly the first
    halves of the UTF-16 pairs of the code points at or above `0x30000`. -/
def noAstralHigh (s : List Nat) : Bool := s.all fun u => !(0xD880 ≤ u && u ≤ 0xDBFF)

/-- No high surrogate is directly followed by a low one. -/
def noPairing : List Nat → Bool
  | a :: b :: rest => !(isHighSurrogate a && isLowSurrogate b) && noPairing (b :: rest)
  | _ => true

/-- Well-formed UTF-16: every high surrogate is directly followed by a low one, and
    every low surrogate directly preceded by a high one. -/
def wfUtf16 : List Nat → Bool
  | [] => true
  | [a] => !isSurrogate a
  | a :: b :: rest =>
    if isHighSurrogate a then isLowSurrogate b && wfUtf16 rest
    else !isLowSurrogate a && wfUtf16 (b :: rest)

/-- A string is `scalar` exactly when every element is a scalar value. -/
theorem scalar_iff (s : List Nat) : scalar s = true ↔ ∀ u ∈ s, isScalarValue u = true :=
  List.all_eq_true

/-- A string is `inSmt` exactly when every element is below `0x30000`. -/
theorem inSmt_iff (s : List Nat) : inSmt s = true ↔ ∀ u ∈ s, u < 0x30000 := by
  rw [inSmt, Carrier.wf_iff, Carrier.bound]

/-- A scalar value is a valid Lean `Char`, and conversely. -/
theorem isScalarValue_iff_isValidChar (u : Nat) : isScalarValue u = true ↔ u.isValidChar := by
  simp only [isScalarValue, isSurrogate, Nat.isValidChar, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

/-- A string of scalar values is a code-point string. -/
theorem codePoints_wf_of_scalar {s : List Nat} (h : scalar s = true) :
    Carrier.codePoints.wf s = true := by
  rw [scalar_iff] at h
  rw [Carrier.wf_iff, Carrier.bound]
  intro u hu
  have hsv := h u hu
  simp only [isScalarValue, Bool.and_eq_true, decide_eq_true_eq] at hsv
  exact hsv.1

end Strata.Str

end
