/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Str.Carrier

/-! # The SMT-LIB string functions, over any carrier

The functions of SMT-LIB 2.6's theory of strings, defined on lists of naturals, so
that one definition serves every carrier: for a carrier, "a character" reads as "an
element of the list". Each function takes SMT-LIB's value outside its usual domain:
`substr "abc" 5 1` is `""`, `indexOf "abc" "" 4` is `-1`, `replace s "" u` is
`u ++ s`.

Each function that builds a string from its arguments' elements keeps those
elements: if every element of every argument satisfies a test `p`, so does every
element of the result (`substr_all`, `replace_all`, …). Taking `p` to be a carrier's
bound gives the string operations on `StrOf c`; taking it to be "below `0x30000`"
says the operation keeps a code-point string in SMT-LIB's alphabet. Only
`fromCode` and `fromInt` introduce new elements, and both are bounded.

These preservation lemmas stay beside the functions, rather than in a companion file,
because the functions on `StrOf c` below are defined with them. -/

@[expose] public section

namespace Strata.Str

/-- `str.len`. -/
def len (s : List Nat) : Int := s.length

/-- `str.++`. -/
def concat (s t : List Nat) : List Nat := s ++ t

/-- `str.substr s i n`: the longest substring of `s` of length at most `n` starting at
    position `i`, and the empty string unless `0 ≤ i < len s` and `0 < n`. -/
def substr (s : List Nat) (i n : Int) : List Nat :=
  if 0 ≤ i ∧ i < s.length ∧ 0 < n then (s.drop i.toNat).take n.toNat else []

/-- `str.at s i`: the element at position `i`, as a string of length one, and the empty
    string outside `s`. -/
def charAt (s : List Nat) (i : Int) : List Nat := substr s i 1

/-- `str.prefixof t s`: whether `t` is a prefix of `s`. -/
def prefixOf (t s : List Nat) : Bool := t.isPrefixOf s

/-- `str.suffixof t s`: whether `t` is a suffix of `s`. -/
def suffixOf (t s : List Nat) : Bool := t.reverse.isPrefixOf s.reverse

/-- The first position `j + k`, with `s'` the suffix of `s` at position `j`, at which `t`
    occurs in `s'` at offset `k`. -/
def findFrom (t : List Nat) : List Nat → Nat → Option Nat
  | s, j =>
    if t.isPrefixOf s then some j
    else
      match s with
      | [] => none
      | _ :: s' => findFrom t s' (j + 1)

/-- `str.contains s t`: whether `t` occurs in `s`. -/
def contains (s t : List Nat) : Bool := (findFrom t s 0).isSome

/-- `str.indexof s t i`: the first position at or after `i` at which `t` occurs in `s`,
    and `-1` when there is none or `i` is outside `0` to `len s`. -/
def indexOf (s t : List Nat) (i : Int) : Int :=
  if 0 ≤ i ∧ i ≤ s.length then
    match findFrom t (s.drop i.toNat) i.toNat with
    | some j => j
    | none => -1
  else -1

/-- `str.replace s t u`: `s` with its first occurrence of `t` replaced by `u`; `u ++ s`
    when `t` is empty, and `s` when `t` does not occur. -/
def replace (s t u : List Nat) : List Nat :=
  if t.isEmpty then u ++ s
  else
    match findFrom t s 0 with
    | some j => s.take j ++ u ++ s.drop (j + t.length)
    | none => s

/-- Replace each leftmost non-overlapping occurrence of the non-empty `t` by `u`. -/
def replaceAllGo (t u : List Nat) (ht : 0 < t.length) : List Nat → List Nat
  | [] => []
  | c :: cs =>
    if t.isPrefixOf (c :: cs) then u ++ replaceAllGo t u ht ((c :: cs).drop t.length)
    else c :: replaceAllGo t u ht cs
termination_by s => s.length
decreasing_by all_goals (simp only [List.length_drop, List.length_cons]; omega)

/-- `str.replace_all s t u`: `s` with every leftmost non-overlapping occurrence of `t`
    replaced by `u`, and `s` when `t` is empty. -/
def replaceAll (s t u : List Nat) : List Nat :=
  if ht : 0 < t.length then replaceAllGo t u ht s else s

/-- Lexicographic order on lists of naturals. -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)

/-- `str.<`. -/
def lt (s t : List Nat) : Bool := lexLt s t

/-- `str.<=`. -/
def le (s t : List Nat) : Bool := s == t || lexLt s t

/-- `str.to_code s`: the element of a string of length one, and `-1` otherwise. -/
def toCode : List Nat → Int
  | [u] => u
  | _ => -1

/-- `str.from_code n` for carrier `c`: the string of the one element `n`, and the empty
    string when `n` is not an element `c` holds. SMT-LIB's own is `fromCode .smt`. -/
def fromCode (c : Carrier) (n : Int) : List Nat :=
  if 0 ≤ n ∧ c.ok n.toNat then [n.toNat] else []

/-- Whether `u` is a decimal digit, `0` (`0x30`) to `9` (`0x39`). -/
def isDigitUnit (u : Nat) : Bool := 0x30 ≤ u && u ≤ 0x39

/-- `str.is_digit s`: whether `s` is one decimal digit. -/
def isDigit : List Nat → Bool
  | [u] => isDigitUnit u
  | _ => false

/-- `str.to_int s`: the number the decimal digits `s` spell, and `-1` when `s` is empty
    or holds anything else. -/
def toInt (s : List Nat) : Int :=
  if s.isEmpty || !s.all isDigitUnit then -1
  else Int.ofNat (s.foldl (fun acc u => acc * 10 + (u - 0x30)) 0)

/-- `str.from_int n`: the decimal digits of `n`, and the empty string when `n < 0`. -/
def fromInt (n : Int) : List Nat :=
  if n < 0 then [] else (Nat.toDigits 10 n.toNat).map Char.toNat

/-! ## The functions keep their arguments' elements -/

section Keep

variable (p : Nat → Bool)

/-- Concatenation keeps a pointwise property `p` of its arguments. -/
theorem concat_all {s t : List Nat} (hs : s.all p = true) (ht : t.all p = true) :
    (concat s t).all p = true := by
  simp only [concat, List.all_append, hs, ht, Bool.and_self]

/-- A prefix keeps a pointwise property `p` of the string. -/
theorem take_all {s : List Nat} (n : Nat) (hs : s.all p = true) : (s.take n).all p = true := by
  simp only [List.all_eq_true] at hs ⊢
  exact fun x hx => hs x (List.mem_of_mem_take hx)

/-- A suffix keeps a pointwise property `p` of the string. -/
theorem drop_all {s : List Nat} (n : Nat) (hs : s.all p = true) : (s.drop n).all p = true := by
  simp only [List.all_eq_true] at hs ⊢
  exact fun x hx => hs x (List.mem_of_mem_drop hx)

/-- `substr` keeps a pointwise property `p` of the string. -/
theorem substr_all {s : List Nat} (i n : Int) (hs : s.all p = true) :
    (substr s i n).all p = true := by
  unfold substr
  split
  · exact take_all p _ (drop_all p _ hs)
  · rfl

/-- `charAt` keeps a pointwise property `p` of the string. -/
theorem charAt_all {s : List Nat} (i : Int) (hs : s.all p = true) :
    (charAt s i).all p = true := substr_all p i 1 hs

/-- `replace s t u` keeps a pointwise property `p` that `s` and `u` have. -/
theorem replace_all {s t u : List Nat} (hs : s.all p = true) (hu : u.all p = true) :
    (replace s t u).all p = true := by
  unfold replace
  split
  · simp only [List.all_append, hs, hu, Bool.and_self]
  · split
    · simp only [List.all_append, take_all p _ hs, hu, drop_all p _ hs, Bool.and_self]
    · exact hs

/-- `replaceAllGo` keeps a pointwise property `p` that the string and the replacement have. -/
theorem replaceAllGo_all (t u : List Nat) (ht : 0 < t.length) (hu : u.all p = true) :
    ∀ (s : List Nat), s.all p = true → (replaceAllGo t u ht s).all p = true
  | [] => fun _ => by rw [replaceAllGo]; rfl
  | c :: cs => fun hs => by
    rw [replaceAllGo]
    split
    · rw [List.all_append, hu, replaceAllGo_all t u ht hu _ (drop_all p _ hs)]
      rfl
    · simp only [List.all_cons, Bool.and_eq_true] at hs ⊢
      exact ⟨hs.1, replaceAllGo_all t u ht hu cs hs.2⟩
termination_by s => s.length
decreasing_by all_goals (simp only [List.length_drop, List.length_cons]; omega)

/-- `replaceAll s t u` keeps a pointwise property `p` that `s` and `u` have. -/
theorem replaceAll_all {s t u : List Nat} (hs : s.all p = true) (hu : u.all p = true) :
    (replaceAll s t u).all p = true := by
  unfold replaceAll
  split
  · exact replaceAllGo_all p t u _ hu s hs
  · exact hs

end Keep

/-- `fromCode c n` is a string of carrier `c`. -/
theorem fromCode_wf (c : Carrier) (n : Int) : c.wf (fromCode c n) = true := by
  unfold fromCode
  split
  · rename_i h
    simp only [Carrier.wf_cons, h.2, Carrier.wf_nil, Bool.and_self]
  · rfl

/-- The decimal digits of a number are digit units. -/
private theorem toDigits_all_isDigit (n : Nat) :
    ((Nat.toDigits 10 n).map Char.toNat).all isDigitUnit = true := by
  simp only [List.all_map, List.all_eq_true, Function.comp_apply]
  intro ch hch
  have h := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hch
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [isDigitUnit, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h.1, h.2⟩

/-- `fromInt n` is a string of decimal digits, so a string of every carrier. -/
theorem fromInt_all_isDigit (n : Int) : (fromInt n).all isDigitUnit = true := by
  unfold fromInt
  split
  · rfl
  · exact toDigits_all_isDigit _

/-- `fromInt n` is a string of every carrier: its elements are decimal digits. -/
theorem fromInt_wf (c : Carrier) (n : Int) : c.wf (fromInt n) = true := by
  have h := fromInt_all_isDigit n
  simp only [Carrier.wf, List.all_eq_true, Carrier.ok, decide_eq_true_eq] at h ⊢
  intro u hu
  have hdigit := h u hu
  simp only [isDigitUnit, Bool.and_eq_true, decide_eq_true_eq] at hdigit
  have hbound := c.bound_ge_bytes
  omega

/-! ## The functions on the strings of a carrier -/

namespace StrOf

variable {c : Carrier}

def len (s : StrOf c) : Int := Str.len s.val

def concat (s t : StrOf c) : StrOf c := ⟨Str.concat s.val t.val, concat_all c.ok s.property t.property⟩

def substr (s : StrOf c) (i n : Int) : StrOf c := ⟨Str.substr s.val i n, substr_all c.ok i n s.property⟩

def charAt (s : StrOf c) (i : Int) : StrOf c := ⟨Str.charAt s.val i, charAt_all c.ok i s.property⟩

def prefixOf (t s : StrOf c) : Bool := Str.prefixOf t.val s.val

def suffixOf (t s : StrOf c) : Bool := Str.suffixOf t.val s.val

def contains (s t : StrOf c) : Bool := Str.contains s.val t.val

def indexOf (s t : StrOf c) (i : Int) : Int := Str.indexOf s.val t.val i

def replace (s t u : StrOf c) : StrOf c :=
  ⟨Str.replace s.val t.val u.val, replace_all c.ok s.property u.property⟩

def replaceAll (s t u : StrOf c) : StrOf c :=
  ⟨Str.replaceAll s.val t.val u.val, replaceAll_all c.ok s.property u.property⟩

def lt (s t : StrOf c) : Bool := Str.lt s.val t.val

def le (s t : StrOf c) : Bool := Str.le s.val t.val

def toCode (s : StrOf c) : Int := Str.toCode s.val

def fromCode (c : Carrier) (n : Int) : StrOf c := ⟨Str.fromCode c n, fromCode_wf c n⟩

def isDigit (s : StrOf c) : Bool := Str.isDigit s.val

def toInt (s : StrOf c) : Int := Str.toInt s.val

def fromInt (c : Carrier) (n : Int) : StrOf c := ⟨Str.fromInt n, fromInt_wf c n⟩

/-- `widen` commutes with `concat`, as with every operation: it is the identity on the list. -/
theorem widen_concat {d : Carrier} (h : c.includes d = true) (s t : StrOf d) :
    widen h (concat s t) = concat (widen h s) (widen h t) := rfl

/-- `widen` commutes with `substr`. -/
theorem widen_substr {d : Carrier} (h : c.includes d = true) (s : StrOf d) (i n : Int) :
    widen h (substr s i n) = substr (widen h s) i n := rfl

/-- `widen` commutes with `replace`. -/
theorem widen_replace {d : Carrier} (h : c.includes d = true) (s t u : StrOf d) :
    widen h (replace s t u) = replace (widen h s) (widen h t) (widen h u) := rfl

/-- `widen` commutes with `replaceAll`. -/
theorem widen_replaceAll {d : Carrier} (h : c.includes d = true) (s t u : StrOf d) :
    widen h (replaceAll s t u) = replaceAll (widen h s) (widen h t) (widen h u) := rfl

/-- Widening keeps the length. -/
theorem len_widen {d : Carrier} (h : c.includes d = true) (s : StrOf d) :
    len (widen h s) = len s := rfl

/-- Widening both arguments keeps `contains`. -/
theorem contains_widen {d : Carrier} (h : c.includes d = true) (s t : StrOf d) :
    contains (widen h s) (widen h t) = contains s t := rfl

/-- Widening both arguments keeps the order. -/
theorem lt_widen {d : Carrier} (h : c.includes d = true) (s t : StrOf d) :
    lt (widen h s) (widen h t) = lt s t := rfl

end StrOf

end Strata.Str

end
