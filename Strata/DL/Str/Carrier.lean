/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

/-! # String carriers

Every string Strata holds is a list of natural numbers, each below a bound that its
*carrier* fixes. Which numbers a string holds, and what they mean, is the source
language's business: a Java string is a list of UTF-16 units, a Python `str` a list
of code points, and SMT-LIB's `String` a list of code points below `0x30000`.

| Carrier      | Elements                    | Holds                                        |
| ------------ | --------------------------- | -------------------------------------------- |
| `bytes`      | `0` to `0xFF`               | Python `bytes`, Go strings, UTF-8 data       |
| `units`      | `0` to `0xFFFF`             | Java and JavaScript strings, UTF-16 data     |
| `units32`    | `0` to `0xFFFFFFFF`         | C and C++ wide strings                       |
| `codePoints` | `0` to `0x10FFFF`           | Python `str`; Lean and Rust strings          |
| `smt`        | `0` to `0x2FFFF`            | SMT-LIB strings                              |

A carrier bounds its elements and nothing more. A lone surrogate is a `units`,
`codePoints` or `smt` value, and ill-formed UTF-8 a `bytes` value: validity is a
predicate on a value (`Strata.DL.Str.Predicates`), never part of its carrier.

The lemmas about carriers stay beside the definitions, rather than in a companion
file: they are few and short, and `StrOf.widen` is defined with one of them. -/

@[expose] public section

namespace Strata.Str

/-- The kind of a string: which numbers its elements may be. -/
inductive Carrier where
  /-- Bytes, below `0x100`. -/
  | bytes
  /-- UTF-16 code units, below `0x10000`. -/
  | units
  /-- 32-bit units, below `0x100000000`. -/
  | units32
  /-- Unicode code points, below `0x110000`, surrogates included. -/
  | codePoints
  /-- SMT-LIB characters: code points below `0x30000`, surrogates included. -/
  | smt
  deriving DecidableEq, Repr, Inhabited

namespace Carrier

/-- Every carrier, in declaration order. -/
def all : List Carrier := [.bytes, .units, .units32, .codePoints, .smt]

/-- The first number a carrier's elements may not be. -/
def bound : Carrier → Nat
  | .bytes => 0x100
  | .units => 0x10000
  | .units32 => 0x100000000
  | .codePoints => 0x110000
  | .smt => 0x30000

/-- Whether `u` may be an element of a string of carrier `c`. -/
def ok (c : Carrier) (u : Nat) : Bool := u < c.bound

/-- Whether every element of `s` may be an element of a string of carrier `c`. -/
def wf (c : Carrier) (s : List Nat) : Bool := s.all c.ok

/-- An element fits carrier `c` exactly when it is below `c`'s bound. -/
theorem ok_iff (c : Carrier) (u : Nat) : c.ok u = true ↔ u < c.bound := by
  simp [ok]

/-- A string fits carrier `c` exactly when every element is below `c`'s bound. -/
theorem wf_iff (c : Carrier) (s : List Nat) : c.wf s = true ↔ ∀ u ∈ s, u < c.bound := by
  simp [wf, ok]

/-- Every carrier holds the bytes, so every byte string is a string of any carrier. -/
theorem bound_ge_bytes (c : Carrier) : 0x100 ≤ c.bound := by
  cases c <;> decide

/-- `c` holds every element `d` holds: `d`'s bound is at most `c`'s. -/
def includes (c d : Carrier) : Bool := d.bound ≤ c.bound

/-- An element of `d` is an element of every carrier that includes `d`. -/
theorem ok_of_includes {c d : Carrier} (h : c.includes d = true) {u : Nat}
    (hu : d.ok u = true) : c.ok u = true := by
  rw [ok_iff] at hu ⊢
  simp only [includes, decide_eq_true_eq] at h
  omega

/-- A string of `d` is a string of every carrier that includes `d`. -/
theorem wf_of_includes {c d : Carrier} (h : c.includes d = true) {s : List Nat}
    (hs : d.wf s = true) : c.wf s = true := by
  rw [wf_iff] at hs ⊢
  simp only [includes, decide_eq_true_eq] at h
  exact fun u hu => Nat.lt_of_lt_of_le (hs u hu) h

/-- The empty string is a string of every carrier. -/
theorem wf_nil (c : Carrier) : c.wf [] = true := rfl

/-- A non-empty string fits `c` when its first element and the rest do. -/
@[simp] theorem wf_cons (c : Carrier) (u : Nat) (s : List Nat) :
    c.wf (u :: s) = (c.ok u && c.wf s) := rfl

/-- A non-empty string fits `c` exactly when its first element is below `c`'s bound and
    the rest fits. -/
theorem wf_cons_iff (c : Carrier) (u : Nat) (s : List Nat) :
    c.wf (u :: s) = true ↔ u < c.bound ∧ c.wf s = true := by
  rw [wf_cons, Bool.and_eq_true, ok_iff]

/-- A concatenation fits `c` exactly when both parts do. -/
@[simp] theorem wf_append (c : Carrier) (s t : List Nat) :
    c.wf (s ++ t) = (c.wf s && c.wf t) := List.all_append

end Carrier

/-- A string of carrier `c`: a list of naturals, each below `c`'s bound. -/
abbrev StrOf (c : Carrier) := { s : List Nat // c.wf s = true }

namespace StrOf

/-- A string hashes as its list. -/
instance (c : Carrier) : Hashable (StrOf c) := ⟨fun s => hash s.val⟩

/-- The empty string of any carrier. -/
def empty (c : Carrier) : StrOf c := ⟨[], rfl⟩

/-- The string of carrier `c` holding `s`, if every element of `s` fits. -/
def ofList? (c : Carrier) (s : List Nat) : Option (StrOf c) :=
  if h : c.wf s = true then some ⟨s, h⟩ else none

/-- Reading a string's own list back as a string of its carrier gives the string. -/
theorem ofList?_val {c : Carrier} (s : StrOf c) : ofList? c s.val = some s := by
  simp [ofList?, s.property]

/-- A string of carrier `d`, read as one of a carrier `c` that holds all of `d`'s
    elements. The list is unchanged. -/
def widen {c d : Carrier} (h : c.includes d = true) (s : StrOf d) : StrOf c :=
  ⟨s.val, Carrier.wf_of_includes h s.property⟩

/-- Widening leaves the list unchanged. -/
@[simp] theorem widen_val {c d : Carrier} (h : c.includes d = true) (s : StrOf d) :
    (widen h s).val = s.val := rfl

/-- `widen` loses nothing: two strings that widen to the same string are equal. -/
theorem widen_injective {c d : Carrier} (h : c.includes d = true) {s t : StrOf d}
    (heq : widen h s = widen h t) : s = t :=
  Subtype.ext (congrArg (fun x : StrOf c => x.val) heq)

/-- A string of carrier `d`, read as one of carrier `c`, when every element fits.
    The list is unchanged. -/
def cast? (c : Carrier) {d : Carrier} (s : StrOf d) : Option (StrOf c) := ofList? c s.val

/-- Casting back a widened string gives it back. -/
theorem cast?_widen {c d : Carrier} (h : c.includes d = true) (s : StrOf d) :
    cast? d (widen h s) = some s := by
  simp [cast?, ofList?_val]

/-- A string that casts to `t` is `t` widened. -/
theorem widen_of_cast? {c d : Carrier} (h : c.includes d = true) {s : StrOf c} {t : StrOf d}
    (hc : cast? d s = some t) : widen h t = s := by
  simp only [cast?, ofList?] at hc
  split at hc
  · cases hc; rfl
  · cases hc

end StrOf

end Strata.Str

end
