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

Four results are exported for SMT-LIB text, each carrying its own statement below:
`escapeForSMT_isLegalSMTSymbol`, `escapeForSMT_isReadableBack`,
`escapeForSMT_injective` and `escapeForSMT_alphabetsAgree`.

Four more hold for any `EscapeScheme`, so a second target gets them by
constructing one: `unescapeWith_escapeWith`, `escapeWith_injective`,
`escapeWith_chars` and `escapeWith_cons`. They are proved from the laws a scheme carries and say nothing
about any particular alphabet.

They share an approach. Legality and readability are proved through the
character-level functions in `Chars`, on lists rather than strings, since that is
where the recursion is. Injectivity is derived from the round trip rather than
proved directly, so the lemmas below establish the left inverse first. Agreement
needs an inclusion in each direction, and only one of them holds of every
character; the other is what escaping buys.
-/

namespace Chars

/-! ### Generic: the round trip -/





/-- One escaped character round-trips. -/
private theorem esc_roundtrip (s : EscapeScheme) (c : Char)
    (h : c.toNat < 16 ^ s.hexWidth) (rest : List Char) :
    unescape s (esc s c rest) = c :: unescape s rest := by
  have hlen := length_hexDigits s.hexWidth c.toNat
  have htake : (hexDigits s.hexWidth c.toNat ++ rest).take s.hexWidth
      = hexDigits s.hexWidth c.toNat := List.take_left' hlen
  have hdrop : (hexDigits s.hexWidth c.toNat ++ rest).drop s.hexWidth = rest :=
    List.drop_left' hlen
  simp [esc, unescape, htake, hdrop, hlen, hexDigits_all_isHexDigit,
        hexValue_hexDigits _ _ h]

/-- A character a scheme leaves alone is not its escape character, so `unescape`
    cannot mistake it for the start of an escape sequence. This is what
    `escapeChar_mustEscape` buys. -/
private theorem ne_escapeChar (s : EscapeScheme) {c : Char} (h : s.mustEscape c = false) :
    c ≠ s.escapeChar := by
  intro he
  subst he
  simp [s.escapeChar_mustEscape] at h

/-- `unescape` recovers the original characters from `escapeAfterFirst`. -/
private theorem unescape_escapeAfterFirst (s : EscapeScheme) (cs : List Char) :
    unescape s (escapeAfterFirst s cs) = cs := by
  induction cs with
  | nil => simp [escapeAfterFirst, unescape]
  | cons c cs ih =>
    by_cases h : s.mustEscape c = true
    · simp [escapeAfterFirst, h, esc_roundtrip s c (s.mustEscape_inRange c h), ih]
    · simp at h
      simp [escapeAfterFirst, h, unescape, ne_escapeChar s h, ih]

/-- `unescape` recovers the original characters from `escape`, first position
    included. One inverse suffices because the hex body names the character, so
    there is no positional rule to undo. -/
private theorem unescape_escape (s : EscapeScheme) (cs : List Char) :
    unescape s (escape s cs) = cs := by
  cases cs with
  | nil => simp [escape, unescape]
  | cons c cs =>
    by_cases h : (s.mustEscape c || s.mustEscapeFirst c) = true
    · have hle : c.toNat < 16 ^ s.hexWidth := by
        rcases Bool.or_eq_true _ _ |>.mp h with h' | h'
        · exact s.mustEscape_inRange c h'
        · exact s.mustEscapeFirst_inRange c h'
      simp [escape, h, esc_roundtrip s c hle, unescape_escapeAfterFirst]
    · rw [Bool.not_eq_true, Bool.or_eq_false_iff] at h
      obtain ⟨hm, hf⟩ := h
      simp [escape, hm, hf, unescape, ne_escapeChar s hm, unescape_escapeAfterFirst]


/-- Every character of an escaped name is either the escape character or one the
    scheme emits as itself. Hex digits are covered by `hexDigit_not_mustEscape`,
    which is what that law is for. -/
private theorem escape_chars (s : EscapeScheme) (cs : List Char) {c : Char}
    (hc : c ∈ escape s cs) :
    c = s.escapeChar ∨ s.mustEscape c = false := by
  have digits : ∀ (n : Nat), c ∈ hexDigits s.hexWidth n → s.mustEscape c = false := by
    intro n hn
    obtain ⟨k, hk, he⟩ := mem_hexDigits _ _ hn
    exact he ▸ s.hexDigit_not_mustEscape k hk
  have after : ∀ (ds : List Char), c ∈ escapeAfterFirst s ds →
      c = s.escapeChar ∨ s.mustEscape c = false := by
    intro ds
    induction ds with
    | nil => intro h; simp [escapeAfterFirst] at h
    | cons d ds ih =>
      intro h
      by_cases hd : s.mustEscape d = true
      · simp [escapeAfterFirst, hd, esc] at h
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (digits _ h)
        · exact ih h
      · simp at hd
        simp [escapeAfterFirst, hd] at h
        rcases h with h | h
        · exact Or.inr (h ▸ hd)
        · exact ih h
  cases cs with
  | nil => simp [escape] at hc
  | cons d ds =>
    by_cases hd : (s.mustEscape d || s.mustEscapeFirst d) = true
    · simp [escape, hd, esc] at hc
      rcases hc with h | h | h
      · exact Or.inl h
      · exact Or.inr (digits _ h)
      · exact after ds h
    · rw [Bool.not_eq_true, Bool.or_eq_false_iff] at hd
      obtain ⟨hm, hf⟩ := hd
      simp [escape, hm, hf] at hc
      rcases hc with h | h
      · exact Or.inr (h ▸ hm)
      · exact after ds h

/-! ### The SMT-LIB text instance

The scheme's fields are exposed as simp lemmas rather than unfolding `smtScheme`
itself: unfolding replaces it with a record literal, which then no longer matches
an induction hypothesis or a lemma stated about `smtScheme`. -/

/-- The SMT-LIB scheme escapes with a backtick, `smtEscapeChar`. -/
@[simp] private theorem smtScheme_escapeChar : smtScheme.escapeChar = smtEscapeChar := rfl

/-- The SMT-LIB scheme names an escaped character in two hex digits. -/
@[simp] private theorem smtScheme_hexWidth : smtScheme.hexWidth = 2 := rfl

/-- The SMT-LIB scheme escapes the characters `smtMustEscape` describes. -/
@[simp] private theorem smtScheme_mustEscape : smtScheme.mustEscape = smtMustEscape := rfl

/-- In first position the SMT-LIB scheme additionally escapes the characters
    `smtMustEscapeFirst` describes. -/
@[simp] private theorem smtScheme_mustEscapeFirst :
    smtScheme.mustEscapeFirst = smtMustEscapeFirst := rfl

/-- Exactly the shape `isLegalSMTSymbol`'s predicate needs: a hex digit is a
    character a quoted symbol may contain, so escaping never introduces one that
    would itself need escaping. -/
private theorem hexDigit_legalChar (n : Nat) :
    (hexDigit n != '|' && hexDigit n != '\\' && !isControlChar (hexDigit n)) = true := by
  unfold hexDigit
  split <;> decide

/-- Every character of an escape body is one an SMT-LIB quoted symbol may contain:
    no `|`, no `\\` and no control character. -/
private theorem hexDigits_legalChars (w n : Nat) :
    (hexDigits w n).all (fun c => c != '|' && c != '\\' && !isControlChar c) = true := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [hexDigits, ih, hexDigit_legalChar]

/-- A character left unescaped is one a quoted symbol may contain. Escaping
    covers `|`, `\` and the controls, and everything outside ASCII is none of
    them. -/
private theorem unescaped_legal (c : Char) (h : smtMustEscape c = false) :
    (c != '|' && c != '\\' && !isControlChar c) = true := by
  by_cases hascii : c.toNat ≤ 0x7F
  · simp [smtMustEscape, hascii] at h
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
    (escapeAfterFirst smtScheme cs).all
      (fun c => c != '|' && c != '\\' && !isControlChar c) = true := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : smtMustEscape c = true
    · simp [escapeAfterFirst, h, esc, ih, hexDigits_legalChars]
      decide
    · simp at h
      simp [escapeAfterFirst, h, ih, unescaped_legal c h]

/-- Every escaped name is a legal SMT-LIB symbol: no `|`, no `\`, no control
    character, and no reserved first character. -/
private theorem escape_isLegalSMTSymbol (cs : List Char) :
    isLegalSMTSymbol (escape smtScheme cs) = true := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    by_cases h : (smtMustEscape c || smtMustEscapeFirst c) = true
    · simp [escape, h, esc, isLegalSMTSymbol, escapeAfterFirst_legalChars,
            hexDigits_legalChars]
      decide
    · rw [Bool.not_eq_true, Bool.or_eq_false_iff] at h
      obtain ⟨hm, hf⟩ := h
      have hat : c ≠ '@' := by
        intro hc; subst hc
        simp [smtMustEscapeFirst, isSmtBare, StrataDDM.Parser.strataIsIdFirst] at hf
      have hdot : c ≠ '.' := by
        intro hc; subst hc
        simp [smtMustEscapeFirst, isSmtBare, StrataDDM.Parser.strataIsIdFirst] at hf
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

/-- Every character of an escape body is readable back: a hex digit is one DDM
    admits in a bare identifier. -/
private theorem hexDigits_readableChars (w n : Nat) :
    (hexDigits w n).all (fun c => !isSmtBare c || strataIsIdRest c) = true := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [hexDigits, ih, hexDigit_ddmBare]

/-- Every character of an escape body is either not bare-legal for SMT-LIB or one
    DDM admits in a bare identifier. -/
private theorem hexDigits_readable_mem (w n : Nat) {x : Char} (h : x ∈ hexDigits w n) :
    isSmtBare x = false ∨ strataIsIdRest x = true := by
  obtain ⟨k, _, he⟩ := mem_hexDigits _ _ h
  exact he ▸ hexDigit_readable k

/-- A character left unescaped that a solver would echo bare is one DDM can read
    bare. Outside ASCII nothing is bare-legal for SMT-LIB, so such a symbol is
    quoted and the question does not arise. -/
private theorem unescaped_readable (c : Char) (h : smtMustEscape c = false) :
    isSmtBare c = false ∨ strataIsIdRest c = true := by
  by_cases hascii : c.toNat ≤ 0x7F
  · simp [smtMustEscape, hascii] at h
    by_cases hs : isSmtBare c = true
    · exact Or.inr (h.2 hs)
    · simp at hs; exact Or.inl hs
  · left; simp [isSmtBare]; omega

/-- Every character `escapeAfterFirst` produces that a solver would echo bare is
    one DDM can read bare. This is the per-character half of `isReadableBack`;
    `escapeAfterFirst` never sees the first position, so it owes nothing about the
    head rule. -/
private theorem escapeAfterFirst_readableChars (cs : List Char) :
    (escapeAfterFirst smtScheme cs).all
      (fun c => !isSmtBare c || strataIsIdRest c) = true := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : smtMustEscape c = true
    · simp [escapeAfterFirst, h, esc] at ih ⊢
      exact ⟨by decide, fun x hx => hexDigits_readable_mem _ _ hx, ih⟩
    · simp at h
      simp [escapeAfterFirst, h] at ih ⊢
      exact ⟨unescaped_readable c h, ih⟩

/-- Every escaped name can be read back: each of its characters that a solver
    would echo bare is one DDM can read bare. An escape introduces a backtick, which
    is not bare-legal for SMT-LIB, so an escaped name is echoed quoted, and a
    quoted symbol parses whatever it contains. -/
private theorem escape_isReadableBack (cs : List Char) :
    isReadableBack (escape smtScheme cs) = true := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    have ht := escapeAfterFirst_readableChars cs
    by_cases h : (smtMustEscape c || smtMustEscapeFirst c) = true
    · simp [escape, h, esc, isReadableBack] at ht ⊢
      exact ⟨⟨by decide, fun x hx => hexDigits_readable_mem _ _ hx, ht⟩, by decide⟩
    · rw [Bool.not_eq_true, Bool.or_eq_false_iff] at h
      obtain ⟨hm, hf⟩ := h
      have hhead : (!isSmtBare c || strataIsIdFirst c) = true := by
        simp [smtMustEscapeFirst] at hf
        by_cases hb : isSmtBare c = true
        · simp [hf hb]
        · simp at hb; simp [hb]
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
        UInt32.le_iff_toNat_le] at h ⊢
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

/-- An escaped name is non-empty, and its first character is either the escape
    character or one the scheme leaves alone in first position.

    A target's first-character rule is `mustEscapeFirst`, so a first character this
    leaves in place already satisfies it. -/
theorem escapeWith_cons (s : EscapeScheme) (name : String) (h : name ≠ "") :
    ∃ c cs, (escapeWith s name).toList = c :: cs ∧
      (c = s.escapeChar ∨ (s.mustEscape c = false ∧ s.mustEscapeFirst c = false)) := by
  have hne : name.toList ≠ [] := fun hnil => h (String.toList_eq_nil_iff.mp hnil)
  simp only [escapeWith, String.toList_ofList]
  match hl : name.toList with
  | [] => exact absurd hl hne
  | d :: ds =>
    by_cases hd : (s.mustEscape d || s.mustEscapeFirst d) = true
    · refine ⟨s.escapeChar, hexDigits s.hexWidth d.toNat ++ Chars.escapeAfterFirst s ds, ?_, Or.inl rfl⟩
      simp [Chars.escape, hd, Chars.esc]
    · rw [Bool.not_eq_true, Bool.or_eq_false_iff] at hd
      refine ⟨d, Chars.escapeAfterFirst s ds, ?_, Or.inr ⟨hd.1, hd.2⟩⟩
      simp [Chars.escape, hd.1, hd.2]

/-- `unescapeWith` recovers the original name from `escapeWith` for the same
    scheme. This is what lets a symbol echoed back by a target be matched against
    the id the encoder holds. -/
theorem unescapeWith_escapeWith (s : EscapeScheme) (name : String) :
    unescapeWith s (escapeWith s name) = name := by
  simp [unescapeWith, escapeWith, Chars.unescape_escape]

/-- Distinct names escape to distinct symbols, for any scheme. Injectivity is what
    lets escaping apply at emission alone: a name is rendered independently at each
    site that mentions it, so a collision could only be repaired by a rename those
    sites would not see. -/
theorem escapeWith_injective (s : EscapeScheme) : Function.Injective (escapeWith s) := by
  intro a b h
  have h' : unescapeWith s (escapeWith s a) = unescapeWith s (escapeWith s b) := by rw [h]
  rwa [unescapeWith_escapeWith, unescapeWith_escapeWith] at h'

/-- Every character of an escaped name is either the escape character or one the
    scheme emits as itself.

    This is the generic half of a legality claim. A target states legality in terms
    of its own alphabet, and this reduces the work to two checks: that its alphabet
    admits the escape character, and that `mustEscape` covers everything the
    alphabet excludes. -/
theorem escapeWith_chars (s : EscapeScheme) (name : String) {c : Char}
    (hc : c ∈ (escapeWith s name).toList) :
    c = s.escapeChar ∨ s.mustEscape c = false := by
  simp only [escapeWith, String.toList_ofList] at hc
  exact Chars.escape_chars s name.toList hc

/-- `unescapeFromSMT` recovers the original name from `escapeForSMT`. This is
    what lets a symbol echoed back by a solver be matched against the id the
    encoder holds. -/
private theorem unescapeFromSMT_escapeForSMT (name : String) :
    unescapeFromSMT (escapeForSMT name) = name :=
  unescapeWith_escapeWith smtScheme name

/-- Distinct names escape to distinct symbols. -/
theorem escapeForSMT_injective : Function.Injective escapeForSMT :=
  escapeWith_injective smtScheme

/-- The string `escapeForSMT` produces always satisfies `isLegalSMTSymbol`: none of
    `|`, `\` or an ASCII control character, and no reserved first character. See
    that predicate for what it deliberately does not cover, namely non-ASCII code
    points the standard would call non-printable, which both solvers accept. -/
theorem escapeForSMT_isLegalSMTSymbol (name : String) :
    isLegalSMTSymbol (escapeForSMT name).toList = true := by
  simp [escapeForSMT, escapeWith, Chars.escape_isLegalSMTSymbol]

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
  simp [escapeForSMT, escapeWith, Chars.escape_isReadableBack]

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
