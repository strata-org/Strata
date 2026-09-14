/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.SMT.Symbol
public import StrataDDM.Format
public import Strata.Util.StringProps
import all Strata.Util.String
public import Strata.DL.SMT.Symbol

public section

namespace Strata.SMT.Symbol

open StrataDDM.Parser (strataIsIdFirst strataIsIdRest)

/-!
# Properties of the SMT-LIB symbol escaping

See `Strata.DL.SMT.Symbol` for the escaping table, why it is shaped that way, and
what emission relies on it for.

Four results are exported, each carrying its own statement below:
`escapeForSMT_isLegalSMTSymbol`, `escapeForSMT_isReadableBack`,
`escapeForSMT_injective` and `escapeForSMT_alphabetsAgree`.

They share an approach. Legality and readability are proved through the
character-level functions in `Chars`, on lists rather than strings, since that is
where the recursion is. Injectivity is derived from the round trip rather than
proved directly, so the lemmas below establish the left inverse first. Agreement
needs an inclusion in each direction, and only one of them holds of every
character; the other is what escaping buys.
-/

namespace Chars

/-- Exactly the shape `isLegalSMTSymbol`'s predicate needs: a hex digit is a
    character a quoted symbol may contain, so escaping never introduces one that
    would itself need escaping. -/
private theorem hexDigit_legalChar (n : Nat) :
    (hexDigit n != '|' && hexDigit n != '\\' && !isControlChar (hexDigit n)) = true := by
  unfold hexDigit
  split <;> decide

/-- One escaped character round-trips. -/
private theorem esc_roundtrip (c : Char) (h : c.toNat ≤ 0x7F) (rest : List Char) :
    unescape (esc c rest) = c :: unescape rest := by
  have hd1 : c.toNat / 16 < 16 := by omega
  have hd2 : c.toNat % 16 < 16 := by omega
  simp [esc, unescape, isHexDigit_hexDigit, hexVal_hexDigit _ hd1, hexVal_hexDigit _ hd2]
  have hsplit : c.toNat / 16 * 16 + c.toNat % 16 = c.toNat := by omega
  rw [hsplit]
  simp

/-- `unescape` recovers the original characters from `escapeAfterFirst`. -/
private theorem unescape_escapeAfterFirst (cs : List Char) :
    unescape (escapeAfterFirst cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : mustEscape c = true
    · have hle : c.toNat ≤ 0x7F := by
        simp [mustEscape] at h; omega
      simp [escapeAfterFirst, h, esc_roundtrip c hle, ih]
    · simp at h
      have hns : c ≠ '`' := by
        intro he; subst he; simp [mustEscape] at h
      simp [escapeAfterFirst, h, unescape, hns, ih]

/-- `unescape` recovers the original characters from `escape`, first position
    included. One inverse suffices because the hex body names the character, so
    there is no positional rule to undo. -/
private theorem unescape_escape (cs : List Char) : unescape (escape cs) = cs := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    by_cases h : (mustEscape c || (isSmtBare c && !strataIsIdFirst c)) = true
    · have hle : c.toNat ≤ 0x7F := by
        rcases Bool.or_eq_true _ _ |>.mp h with h' | h'
        · simp [mustEscape] at h'; omega
        · have hs : isSmtBare c = true := (Bool.and_eq_true _ _ |>.mp h').1
          simp [isSmtBare] at hs; omega
      simp [escape, h, esc_roundtrip c hle, unescape_escapeAfterFirst]
    · rw [Bool.not_eq_true, Bool.or_eq_false_iff] at h
      obtain ⟨hm, hf⟩ := h
      have hns : c ≠ '`' := by
        intro he; subst he
        simp [mustEscape] at hm
      simp [escape, hm, hf, unescape, hns, unescape_escapeAfterFirst]

/-- A character left unescaped is one a quoted symbol may contain. Escaping
    covers `|`, `\` and the controls, and everything outside ASCII is none of
    them. -/
private theorem unescaped_legal (c : Char) (h : mustEscape c = false) :
    (c != '|' && c != '\\' && !isControlChar c) = true := by
  by_cases hascii : c.toNat ≤ 0x7F
  · simp [mustEscape, hascii] at h
    simp [h]
  · have hbig : 0x7F < c.toNat := by omega
    have hctl : isControlChar c = false := by
      simp [isControlChar]; omega
    have h1 : c ≠ '|' := by intro he; subst he; simp at hbig
    have h2 : c ≠ '\\' := by intro he; subst he; simp at hbig
    simp [h1, h2, hctl]

/-- `escapeAfterFirst` never emits a character an SMT-LIB quoted symbol may not
    contain: no `|`, no `\` and no control character survives it. -/
private theorem escapeAfterFirst_legalChars (cs : List Char) :
    (escapeAfterFirst cs).all (fun c => c != '|' && c != '\\' && !isControlChar c) = true := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : mustEscape c = true
    · simp [escapeAfterFirst, h, esc, ih, hexDigit_legalChar]
      decide
    · simp at h
      simp [escapeAfterFirst, h, ih, unescaped_legal c h]

/-- Every escaped name is a legal SMT-LIB symbol: no `|`, no `\`, no control
    character, and no reserved first character. -/
private theorem escape_isLegalSMTSymbol (cs : List Char) :
    isLegalSMTSymbol (escape cs) = true := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    by_cases h : (mustEscape c || (isSmtBare c && !strataIsIdFirst c)) = true
    · simp [escape, h, esc, isLegalSMTSymbol, escapeAfterFirst_legalChars,
            hexDigit_legalChar]
      decide
    · rw [Bool.not_eq_true, Bool.or_eq_false_iff] at h
      obtain ⟨hm, hf⟩ := h
      have hat : c ≠ '@' := by intro hc; subst hc; simp [isSmtBare, StrataDDM.Parser.strataIsIdFirst] at hf
      have hdot : c ≠ '.' := by intro hc; subst hc; simp [isSmtBare, StrataDDM.Parser.strataIsIdFirst] at hf
      simp [escape, hm, hf, isLegalSMTSymbol, escapeAfterFirst_legalChars,
            unescaped_legal c hm, hat, hdot]

/-- A hex digit is also one DDM can read bare, which is what keeps an escaped
    name readable back. -/
private theorem hexDigit_ddmBare (n : Nat) : strataIsIdRest (hexDigit n) = true := by
  unfold hexDigit
  split <;> decide

/-- A hex digit is readable back: DDM admits it in a bare identifier, so it never
    makes an escaped name unreadable. -/
private theorem hexDigit_readable (n : Nat) :
    isSmtBare (hexDigit n) = false ∨ strataIsIdRest (hexDigit n) = true :=
  Or.inr (hexDigit_ddmBare n)

/-- A character left unescaped that a solver would echo bare is one DDM can read
    bare. Outside ASCII nothing is bare-legal for SMT-LIB, so such a symbol is
    quoted and the question does not arise. -/
private theorem unescaped_readable (c : Char) (h : mustEscape c = false) :
    isSmtBare c = false ∨ strataIsIdRest c = true := by
  by_cases hascii : c.toNat ≤ 0x7F
  · simp [mustEscape, hascii] at h
    by_cases hs : isSmtBare c = true
    · exact Or.inr (h.2 hs)
    · simp at hs; exact Or.inl hs
  · left; simp [isSmtBare]; omega

/-- Every character `escapeAfterFirst` produces that a solver would echo bare is
    one DDM can read bare. This is the per-character half of `isReadableBack`;
    `escapeAfterFirst` never sees the first position, so it owes nothing about the
    head rule. -/
private theorem escapeAfterFirst_readableChars (cs : List Char) :
    (escapeAfterFirst cs).all (fun c => !isSmtBare c || strataIsIdRest c) = true := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : mustEscape c = true
    · simp [escapeAfterFirst, h, esc] at ih ⊢
      exact ⟨by decide, hexDigit_readable _, hexDigit_readable _, ih⟩
    · simp at h
      simp [escapeAfterFirst, h] at ih ⊢
      exact ⟨unescaped_readable c h, ih⟩

/-- Every escaped name can be read back: each of its characters that a solver
    would echo bare is one DDM can read bare. An escape introduces a backtick, which
    is not bare-legal for SMT-LIB, so an escaped name is echoed quoted, and a
    quoted symbol parses whatever it contains. -/
private theorem escape_isReadableBack (cs : List Char) :
    isReadableBack (escape cs) = true := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    have ht := escapeAfterFirst_readableChars cs
    by_cases h : (mustEscape c || (isSmtBare c && !strataIsIdFirst c)) = true
    · simp [escape, h, esc, isReadableBack] at ht ⊢
      exact ⟨⟨by decide, hexDigit_readable _, hexDigit_readable _, ht⟩, by decide⟩
    · rw [Bool.not_eq_true, Bool.or_eq_false_iff] at h
      obtain ⟨hm, hf⟩ := h
      have hhead : (!isSmtBare c || strataIsIdFirst c) = true := by
        rcases Bool.and_eq_false_iff.mp hf with hs | hd
        · simp [hs]
        · simp at hd; simp [hd]
      simp [escape, hm, hf, isReadableBack, hhead] at ht ⊢
      exact ⟨unescaped_readable c hm, ht⟩


/-! ### The two alphabets that meet at an emission site

A declaration is quoted by `isBareSmtSymbol`, which asks what SMT-LIB admits bare.
A reference is printed by DDM, which asks what *its* formatter admits bare. Neither
path consults the other, so what follows establishes that they cannot disagree in a
way that matters: everything DDM emits bare is legal bare SMT-LIB, and on an escaped
name the two alphabets coincide outright.

The first of those is an invariant across a package boundary, and `isIdContinue`'s
own docstring states it informally, `'` being excluded there precisely because the
solvers reject it unquoted. Proving it means a later widening of DDM's alphabet
fails this file rather than emitting an illegal script. -/

/-- Every alphanumeric character is ASCII, since Lean's `isAlpha` and `isDigit` are
    the `A-Z`, `a-z` and `0-9` ranges. -/
private theorem isAlphanum_ascii (c : Char) (h : c.isAlphanum = true) :
    c.toNat ≤ 0x7F := by
  simp [Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower, Char.isDigit,
        Char.toNat, UInt32.le_iff_toNat_le] at h ⊢
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩ <;> omega

/-- A letter is not a digit; the two ranges are disjoint. -/
private theorem isAlpha_not_isDigit (c : Char) (h : c.isAlpha = true) :
    c.isDigit = false := by
  simp [Char.isAlpha, Char.isUpper, Char.isLower, UInt32.le_iff_toNat_le] at h
  simp [Char.isDigit, UInt32.le_iff_toNat_le]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- Every character DDM admits in a bare identifier, SMT-LIB admits in a bare simple
    symbol. This is what makes it safe to leave a reference's quoting to DDM: if DDM
    declines to quote, SMT-LIB accepts what it wrote. -/
private theorem isIdContinue_isSmtBare (c : Char) (h : StrataDDM.isIdContinue c = true) :
    isSmtBare c = true := by
  by_cases ha : c.isAlphanum = true
  · simp [isSmtBare, ha, isAlphanum_ascii c ha]
  · simp [StrataDDM.isIdContinue, ha] at h
    rcases h with ((((h | h) | h) | h) | h) | h <;> subst h <;> decide

/-- Every character DDM admits *first* in a bare identifier, SMT-LIB also admits
    first: bare-legal, not a digit, and neither of the reserved `@` and `.`. -/
private theorem isIdBegin_isBareSmtFirst (c : Char) (h : StrataDDM.isIdBegin c = true) :
    isSmtBare c = true ∧ c.isDigit = false ∧ (c != '@') = true ∧ (c != '.') = true := by
  by_cases ha : c.isAlpha = true
  · have hb : c.isAlphanum = true := by simp [Char.isAlphanum, ha]
    refine ⟨by simp [isSmtBare, hb, isAlphanum_ascii c hb], isAlpha_not_isDigit c ha, ?_, ?_⟩
    · simp only [bne_iff_ne, ne_eq]
      intro he; subst he; simp [Char.isAlpha, Char.isUpper, Char.isLower] at ha
    · simp only [bne_iff_ne, ne_eq]
      intro he; subst he; simp [Char.isAlpha, Char.isUpper, Char.isLower] at ha
  · simp [StrataDDM.isIdBegin, ha] at h
    rcases h with h | h <;> subst h <;> exact ⟨by decide, by decide, by decide, by decide⟩

/-- The parser's alphabet and the formatter's differ only by `'`, which SMT-LIB does
    not admit bare, so on any character a solver would echo bare the two coincide. -/
private theorem isIdContinue_of_strataIsIdRest (c : Char)
    (hr : strataIsIdRest c = true) (hs : isSmtBare c = true) :
    StrataDDM.isIdContinue c = true := by
  by_cases ha : c.isAlphanum = true
  · simp [StrataDDM.isIdContinue, ha]
  · simp [strataIsIdRest, ha] at hr
    rcases hr with (((((h | h) | h) | h) | h) | h) | h <;> subst h <;> first
      | decide
      | (exfalso; revert hs; decide)

end Chars

/-- `unescapeFromSMT` recovers the original name from `escapeForSMT`. This is
    what lets a symbol echoed back by a solver be matched against the id the
    encoder holds. -/
private theorem unescapeFromSMT_escapeForSMT (name : String) :
    unescapeFromSMT (escapeForSMT name) = name := by
  simp [unescapeFromSMT, escapeForSMT, Chars.unescape_escape]

/-- Distinct names escape to distinct symbols. -/
theorem escapeForSMT_injective : Function.Injective escapeForSMT := by
  intro a b h
  have h' : unescapeFromSMT (escapeForSMT a) = unescapeFromSMT (escapeForSMT b) := by rw [h]
  rwa [unescapeFromSMT_escapeForSMT, unescapeFromSMT_escapeForSMT] at h'

/-- The string `escapeForSMT` produces always satisfies `isLegalSMTSymbol`: none of
    `|`, `\` or an ASCII control character, and no reserved first character. See
    that predicate for what it deliberately does not cover, namely non-ASCII code
    points the standard would call non-printable, which both solvers accept. -/
theorem escapeForSMT_isLegalSMTSymbol (name : String) :
    isLegalSMTSymbol (escapeForSMT name).toList = true := by
  simp [escapeForSMT, Chars.escape_isLegalSMTSymbol]

/-- The string `escapeForSMT` produces can always be read back: if a solver would
    echo it bare, which it does exactly when every character is one SMT-LIB
    admits in a bare simple symbol, then every character is also one DDM admits
    in a bare identifier, so the answer parses.

    This is what the escape character being outside SMT-LIB's bare alphabet buys.
    Any escaped name contains a backtick, a backtick is not a bare simple-symbol
    character, so such a name is echoed quoted and parses whatever it contains; and
    a name with no escapes contains only characters both alphabets admit. -/
theorem escapeForSMT_isReadableBack (name : String) :
    isReadableBack (escapeForSMT name).toList = true := by
  simp [escapeForSMT, Chars.escape_isReadableBack]

/-- On an escaped name the two quoting rules agree character for character: DDM
    admits it in a bare identifier exactly when SMT-LIB admits it in a bare simple
    symbol.

    That is what lets a declaration and a reference to the same name be quoted by
    different code and still come out as the same symbol. Either both quote or
    neither does, and both spellings denote the same symbol in any case, so the
    agreement is what keeps the *script* stable rather than what keeps it correct.

    Neither inclusion is free. Left to right holds of every character. Right to left
    holds only because the name is escaped: `-` is bare-legal for SMT-LIB and not for
    DDM, and escaping is what removes it. -/
theorem escapeForSMT_alphabetsAgree (name : String) (c : Char)
    (hc : c ∈ (escapeForSMT name).toList) :
    StrataDDM.isIdContinue c = true ↔ Chars.isSmtBare c = true := by
  constructor
  · exact Chars.isIdContinue_isSmtBare c
  · intro hs
    have h := escapeForSMT_isReadableBack name
    simp only [isReadableBack, Bool.and_eq_true, List.all_eq_true] at h
    have hr := h.1 c hc
    simp only [Bool.or_eq_true, Bool.not_eq_true', hs, Bool.true_eq_false, false_or] at hr
    exact Chars.isIdContinue_of_strataIsIdRest c hr hs

end Strata.SMT.Symbol
