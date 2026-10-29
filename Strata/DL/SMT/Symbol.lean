/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.Parser
public import Strata.Util.Name
public import Strata.Util.String
-- `import all` so a scheme's `hexDigit_not_mustEscape` can unfold `hexDigit`,
-- here and in a consumer defining its own scheme.
import all Strata.Util.String

public section

namespace Strata.SMT

/-!
# Escaping arbitrary names into the SMT-LIB symbol alphabet

Core names are arbitrary `String`s; SMT-LIB symbols are not. Emitted unrepaired, a
name supplies the structure of the command it sits in: one that closes its own
declaration's parens can append `(assert false)`, and since a verification condition
asserts the negation of its goal and reads `unsat` as proved, that discharges every
obligation.

Three things can make a character unemittable, and one escaping covers all of them.

```
forbidden         | \ and the C0 controls and DEL
                    a quoted symbol is printable and whitespace between two |,
                    containing neither | nor \, and the grammar has no escape
forbidden first   @ .          reserved for solver-generated symbols; cvc5 rejects
                               @x and |@x| alike, and a @N suffix cannot change a
                               first character
                  ? ! digits   a solver echoes ?x bare and the answer parser takes
                               only a letter, _ or $ first
unreadable back   ~ ^ & * - + = < > / %
                    bare-legal for SMT-LIB, not for DDM, so a solver echoes it bare,
                    the answer fails to parse, and the counterexample is lost
```

Everything else quoting handles, and `|abc|` and `abc` denote the *same* symbol, so
quoting is presentational and never opens a second namespace.

## The rules

```
mustEscape c  ⇔  c ∈ {`, |, \} ∨ isControlChar c ∨ (isSmtBare c ∧ ¬strataIsIdRest c)

anywhere      c ↦ '`' ++ hex2 c   when mustEscape c
first only    c ↦ '`' ++ hex2 c   when isSmtBare c ∧ ¬strataIsIdFirst c
```

and what that produces:

```
a-b            ↦  |a`2Db|          echoed bare otherwise, and then unreadable
a|b            ↦  |a`7Cb|          no legal spelling as itself
@x             ↦  |`40x|           reserved first
?x             ↦  |`3Fx|           the parser takes only a letter, _ or $ first
a b            ↦  |a b|            not bare-legal, so quoted and readable as it is
v@1            ↦  v@1              @ is unreserved after the first character
Box..x'        ↦  |Box..x'|        ' is not bare-legal, so quoting suffices
$__mono#f#int  ↦  |$__mono#f#int|  likewise #
```

Decoding needs no positional rule and no mnemonic table: the hex body names the
character, so one inverse serves both positions, and a backtick is never a hex
digit.

## Why a backtick

`\` is the one character that must *not* be used, and it fails unsoundly. cvc5
reads it literally inside `|…|` and ends a symbol at a bare `|`, while z3 unescapes
`\\` and `\|` as an extension, so `a|` and `a\p` both arrive as `a\p` under z3.
Merging two names into one symbol lets a false obligation be proved.

Beyond that the requirement is the one `escapeForSMT_isReadableBack` proves: every
character of an escaped name is not bare-legal for SMT-LIB, or bare-legal for DDM.
Two families qualify. Characters outside SMT-LIB's bare alphabet force a quoted
echo, which always parses: `space tab LF CR " # ' ( ) , : ; [ ] ` { }`. Characters
inside DDM's own alphabet make the escaped name bare-readable instead, `_` being the
clearest, taking `a-b` to `a_2Db`, echoed bare and lexed.

So the choice is preference, not correctness. The second family is pervasive in
generated names, so one of those would escape itself everywhere, taking
`$__mono#f#int` to `$_5F_5Fmono#f#int`, and `@` and `.` are the reserved-first
characters this exists to repair. In the first family, `#` and `'` also occur in
generated names, `LF` and `CR` would put a line break inside a symbol that our
line-oriented reading of solver output would split, `tab` and space are hard to see,
and `"` `;` `(` `)` `:` carry meaning elsewhere in the grammar. That leaves
`, [ ] ` { }`, and a backtick is visible and appears in no generated name.

A space consequently needs no escaping at all.

## What is proved

`Strata.DL.SMT.SymbolProps` establishes that every escaped name is a legal symbol
(`escapeForSMT_isLegalSMTSymbol`) and can be read back
(`escapeForSMT_isReadableBack`); that escaping is injective
(`escapeForSMT_injective`), which is what lets it apply at emission alone while each
mention of a name is rendered independently; and that the two bare alphabets agree
on an escaped name (`escapeForSMT_alphabetsAgree`), so a declaration quoted here and
a reference quoted by DDM come out as the same symbol.

`unescapeFromSMT` inverts the escaping, for reading a symbol back out of an answer.
Parsing SMT-LIB *into* Strata does not unescape, so a parse-then-emit round trip
adds a level rather than reproducing its input: `|a%b|` denotes `a%b` and is
re-emitted as `` |a`25b| ``. That is intentional. Correctness needs injectivity, not
idempotence.

## One escaping, several targets

The rules above are SMT-LIB text's, and they are not the only possible ones: a
target with a different bare-symbol alphabet needs a different must-escape set, and
with it a different escape character, since an escape character outside the target's
bare alphabet would leave every escaped name needing to be quoted, which is what
escaping is there to avoid.

`EscapeScheme` is therefore the parameter — escape character, must-escape set,
must-escape-first set — and `smtScheme` is the instance for SMT-LIB text.
`escapeWith` and `unescapeWith` take a scheme; `escapeForSMT` and `unescapeFromSMT`
are those at `smtScheme`. The round trip and injectivity are proved once for any
scheme from the three laws a scheme carries, while legality and readability are
stated per target, since only the target knows its alphabet.
-/

namespace Symbol

open StrataDDM.Parser (strataIsIdFirst strataIsIdRest)

/-- The escape character; see the module docstring for why it is a backtick. -/
def smtEscapeChar : Char := '`'

/-- How names are escaped for one emission target: the character that introduces
    an escape, how many hex digits name an escaped character, which characters
    cannot be emitted as themselves, and which cannot *start* a symbol.
    `smtScheme` is the instance for SMT-LIB text.

    The three laws are what the round trip and injectivity need. Carrying them
    here means an instance discharges them once, at construction, instead of
    every theorem restating them as hypotheses. -/
structure EscapeScheme where
  /-- Introduces an escape sequence: this character, then `hexWidth` hex digits
      naming the escaped character. -/
  escapeChar : Char
  /-- How many hex digits name an escaped character. Two suffice for a target that
      escapes only ASCII, which is what SMT-LIB text needs since quoting covers
      the rest; a target with no quoting to fall back on has to be able to name an
      arbitrary code point, and needs six. -/
  hexWidth : Nat
  /-- Characters that cannot be emitted as themselves, at any position. -/
  mustEscape : Char → Bool
  /-- Characters that cannot *start* a symbol. Read as an addition to
      `mustEscape`, which applies at every position including the first. -/
  mustEscapeFirst : Char → Bool
  /-- `escapeChar` is itself escaped, so one appearing in an escaped name can
      only begin an escape sequence. Without this the decoding is ambiguous and
      two names can escape alike. -/
  escapeChar_mustEscape : mustEscape escapeChar = true
  /-- `hexWidth` digits have to be enough to name what is escaped. -/
  mustEscape_inRange : ∀ c, mustEscape c = true → c.toNat < 16 ^ hexWidth
  /-- The same bound for the first position, escaped by the same sequence. -/
  mustEscapeFirst_inRange : ∀ c, mustEscapeFirst c = true → c.toNat < 16 ^ hexWidth
  /-- A hex digit is emitted as itself. This is what keeps an escape sequence
      from being escaped again, and what lets a target conclude that an escaped
      name stays inside its alphabet: the only characters the escaping
      introduces are `escapeChar` and hex digits. -/
  hexDigit_not_mustEscape : ∀ n, n < 16 → mustEscape (hexDigit n) = false

/-! The escaping algorithm, on character lists, parameterised by an
`EscapeScheme`. The `String` entry points `escapeWith` and `unescapeWith` are thin
wrappers over these; the proofs live here, where the recursion is. -/
namespace Chars

/-! ### The SMT-LIB text alphabet

Tab, newline and carriage return count as whitespace to SMT-LIB and are escaped
anyway, which is stricter than the standard on purpose: a newline inside a symbol
would break the line-oriented reading of solver output.

Reading a solver's answer goes through a DDM dialect, so what DDM's lexer
admits bare is what limits which names can be read back. Those two predicates are
`StrataDDM.Parser.strataIsIdFirst` and `strataIsIdRest`, used directly rather than
mirrored here: a copy could drift from the lexer it is supposed to describe, and
the drift would be silent, costing a counterexample rather than failing.

The lexer has two rules, one for the first character and a wider one for the rest,
which is why a scheme has both `mustEscape` and `mustEscapeFirst`. -/

/-- Characters SMT-LIB admits in a *bare* simple symbol. A solver echoes a symbol
    bare exactly when every character is one of these, and pipe-quoted
    otherwise, which is what decides whether we can read it back.

    Bounded to ASCII, which SMT-LIB's own alphabet is: its letters are `A-Z a-z`,
    so a character like `α` is not bare-legal and its symbol is always quoted. -/
def isSmtBare (c : Char) : Bool :=
  c.toNat ≤ 0x7F &&
    (c.isAlphanum || c == '~' || c == '!' || c == '@' || c == '$' || c == '%' ||
     c == '^' || c == '&' || c == '*' || c == '_' || c == '-' || c == '+' ||
     c == '=' || c == '<' || c == '>' || c == '.' || c == '?' || c == '/')

/-- A character that cannot be emitted as itself into SMT-LIB text, for one of
    three reasons: SMT-LIB forbids it outright (`|`, `\`, the controls) and offers
    no escape for it; it is the escape character; or a solver would echo it *bare*
    while DDM cannot read it bare, which is the `~ ^ & * - + = < > / %` gap, where
    leaving it alone costs the counterexample silently.

    Bounded to ASCII by construction, which is what lets two hex digits name it. -/
def smtMustEscape (c : Char) : Bool :=
  c.toNat ≤ 0x7F &&
    (c == '`' || c == '|' || c == '\\' || isControlChar c || (isSmtBare c && !strataIsIdRest c))

/-- A character SMT-LIB text cannot *start* a symbol with: one a solver echoes
    bare that DDM will not accept first, which covers the `@` and `.` SMT-LIB
    reserves there as well as `?`, `!` and the digits. -/
def smtMustEscapeFirst (c : Char) : Bool :=
  isSmtBare c && !strataIsIdFirst c

/-! ### The algorithm

Parameterised by the scheme, so a target with a different alphabet reuses the
recursion, the decoder and the proofs. -/

/-- Escape one character: the scheme's escape character, then the hex digits
    naming it. -/
def esc (s : EscapeScheme) (c : Char) (rest : List Char) : List Char :=
  s.escapeChar :: (hexDigits s.hexWidth c.toNat ++ rest)

/-- Escape the characters that cannot be emitted as themselves. Applies at every
    position, so it does not handle the first position; see `escape`. -/
def escapeAfterFirst (s : EscapeScheme) : List Char → List Char
  | [] => []
  | c :: cs =>
    if s.mustEscape c then esc s c (escapeAfterFirst s cs) else c :: escapeAfterFirst s cs

/-- Escape a name. The first character additionally has to be one the target
    admits first. See the module docstring for why that position is special. -/
def escape (s : EscapeScheme) : List Char → List Char
  | [] => []
  | c :: cs =>
    if s.mustEscape c || s.mustEscapeFirst c then esc s c (escapeAfterFirst s cs)
    else c :: escapeAfterFirst s cs

/-- Inverse of both `escape` and `escapeAfterFirst`. One function suffices
    because the hex body names the character outright, so there is no positional
    rule to invert and no mnemonic to disambiguate.

    An escape character not followed by `hexWidth` hex digits is passed through,
    so this is total rather than defined only on the image. -/
def unescape (s : EscapeScheme) (cs : List Char) : List Char :=
  match cs with
  | [] => []
  | c :: rest =>
    let body := rest.take s.hexWidth
    if c == s.escapeChar && body.length == s.hexWidth && body.all isHexDigit then
      have : (rest.drop s.hexWidth).length < (c :: rest).length := by
        simp only [List.length_cons, List.length_drop]
        omega
      Char.ofNat (hexValue body) :: unescape s (rest.drop s.hexWidth)
    else
      have : rest.length < (c :: rest).length := by simp
      c :: unescape s rest
termination_by cs.length

end Chars

/-- Escaping for SMT-LIB text: a backtick escape, two hex digits (the escaped
    characters are all ASCII, since quoting covers the rest), the characters
    SMT-LIB cannot emit as themselves, and the first-position rule DDM's lexer
    imposes. -/
def smtScheme : EscapeScheme where
  escapeChar := smtEscapeChar
  hexWidth := 2
  mustEscape := Chars.smtMustEscape
  mustEscapeFirst := Chars.smtMustEscapeFirst
  escapeChar_mustEscape := by decide
  mustEscape_inRange := by
    intro c h
    simp [Chars.smtMustEscape] at h
    omega
  mustEscapeFirst_inRange := by
    intro c h
    simp [Chars.smtMustEscapeFirst, Chars.isSmtBare] at h
    omega
  hexDigit_not_mustEscape := by
    intro n _
    unfold hexDigit
    split <;> decide

/-- What SMT-LIB legality requires beyond what quoting supplies: none of `|`, `\`
    or an ASCII control character, and no reserved first character.

    The ASCII bound is deliberate, and makes this weaker than the letter of the
    standard, which also excludes the C1 controls at `0x80-0x9F` and other
    non-printable code points. `escapeForSMT` does not escape those, since two hex
    digits cannot name an arbitrary code point, and both cvc5 and z3 accept them
    inside `|…|` as they accept `α`. The gap is between this claim and the standard,
    not between this claim and a working script. -/
def isLegalSMTSymbol (cs : List Char) : Bool :=
  cs.all (fun c => c != '|' && c != '\\' && !isControlChar c) &&
    (match cs with
     | [] => true
     | c :: _ => c != '@' && c != '.')

/-- What reading an answer back requires: every character a solver would echo bare
    is one DDM can read bare, and the first is additionally one DDM admits first.
    DDM's lexer has two rules, so this has two conjuncts.

    Stated per character, which is stronger than needed and easier to compose, and
    gives what matters: a symbol a solver echoes bare, which is exactly one whose
    every character is bare-legal for SMT-LIB, is then lexable by DDM. -/
def isReadableBack (cs : List Char) : Bool :=
  cs.all (fun c => !Chars.isSmtBare c || strataIsIdRest c) &&
    (match cs with
     | [] => true
     | c :: _ => !Chars.isSmtBare c || strataIsIdFirst c)

/-! ### The `String` interface -/

/-- Escape `name` for the target `s` describes. Distinct names escape to distinct
    symbols, and every character of the result is either the escape character or
    one `s` does not escape. Both hold for any scheme, from the laws a scheme
    carries.

    Whether the result is *legal*, and whether it can be read back, depends on the
    alphabet and so is a claim each target makes about its own scheme. -/
def escapeWith (s : EscapeScheme) (name : String) : String :=
  String.ofList (Chars.escape s name.toList)

/-- Inverse of `escapeWith` for the same scheme. -/
def unescapeWith (s : EscapeScheme) (symbol : String) : String :=
  String.ofList (Chars.unescape s symbol.toList)

/-- Escape `name` into the SMT-LIB symbol alphabet. Distinct names escape to
    distinct symbols, and the result is always a legal symbol: no `|`, no `\`, no
    ASCII control character, and no reserved first character. -/
def escapeForSMT (name : String) : String :=
  escapeWith smtScheme name

/-- Inverse of `escapeForSMT`. -/
def unescapeFromSMT (symbol : String) : String :=
  unescapeWith smtScheme symbol

/-- Whether `s` may be emitted without pipe delimiters: every character is one
    SMT-LIB admits in a bare simple symbol, and the first may also start one, so not
    a digit and not the reserved `@` or `.`.

    This asks what *SMT-LIB* admits bare, which is the question at an emission site
    into an SMT-LIB script; DDM's `needsPipeDelimiters` answers the same question for
    DDM's own alphabet. `escapeForSMT_alphabetsAgree` proves the two coincide on an
    escaped name, so a declaration quoted here and a reference quoted by DDM agree.

    Reserved words are not this predicate's concern; they are words rather than
    spellings, and the encoder's uniquifier keeps names off them. -/
def isBareSmtSymbol (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs =>
    Chars.isSmtBare c && !c.isDigit && c != '@' && c != '.' && cs.all Chars.isSmtBare

/-- Render `name` as an SMT-LIB symbol: escape it, then pipe-quote unless the
    result is already a legal bare simple symbol.

    This is the only correct way to emit a name into a script. Interpolating a
    name directly lets it supply the surrounding command's structure. -/
def toSMTString (name : String) : String :=
  let escaped := escapeForSMT name
  if isBareSmtSymbol escaped then escaped else "|" ++ escaped ++ "|"

/-- Drop the pipe delimiters a solver may put around a symbol it echoes.
    `|abc|` and `abc` denote the same symbol, so this loses nothing. -/
private def stripPipeDelimiters (symbol : String) : String :=
  if symbol.length ≥ 2 && symbol.startsWith "|" && symbol.endsWith "|" then
    ((symbol.drop 1).dropEnd 1).toString
  else
    symbol

/-- Recover a name from the spelling a solver echoes back: drop the pipe
    delimiters and undo `escapeForSMT`, so the echoed symbol matches the id the
    encoder holds.

    Without this, quoted names match nothing and their models are silently
    dropped. -/
def ofSMTString (symbol : String) : String :=
  unescapeFromSMT (stripPipeDelimiters symbol)

/-- Recover a name from a symbol inside a solver's *answer*, where not every symbol
    is one we emitted. A solver names the elements of an uninterpreted sort itself,
    cvc5 answering with the likes of `@_S_0`; those never passed through
    `escapeForSMT`, so unescaping one could corrupt it, and they are left as they
    came. Telling them apart needs no lookup: SMT-LIB reserves a leading `@` and
    `.`, which is why `escapeForSMT` rewrites both, so
    `escapeForSMT_isLegalSMTSymbol` gives that no name of ours begins with either.

    `declaredNames` are the names already in play. A solver-invented symbol that
    would collide with one gets a fresh `@N` suffix, which is safe because such a
    symbol is opaque: it stands for "some element of this sort" rather than for
    anything named in the source. Our own names are never renamed, and never need to
    be, since the escaping is injective. -/
def ofSolverSymbol (declaredNames : Std.HashSet String) (symbol : String) : String :=
  let bare := stripPipeDelimiters symbol
  if bare.startsWith "@" || bare.startsWith "." then
    if declaredNames.contains bare then
      Strata.Name.findUnique bare 1 declaredNames
    else
      bare
  else
    unescapeFromSMT bare

end Symbol

end Strata.SMT
