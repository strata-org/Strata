/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.Parser
public import Strata.Util.Name
public import Strata.Util.String

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
-/

namespace Symbol

open StrataDDM.Parser (strataIsIdFirst strataIsIdRest)

/-- The escape character; see the module docstring for why it is a backtick. -/
def smtEscapeChar : Char := '`'

/-! The escaping algorithm, on character lists. The `String` entry points
`escapeForSMT` and `unescapeFromSMT` are thin wrappers over these; the proofs
live here, where the recursion is. -/
namespace Chars

/-! Tab, newline and carriage return count as whitespace to SMT-LIB and are escaped
anyway, which is stricter than the standard on purpose: a newline inside a symbol
would break the line-oriented reading of solver output.

Reading a solver's answer goes through a DDM dialect, so what DDM's lexer
admits bare is what limits which names can be read back. Those two predicates are
`StrataDDM.Parser.strataIsIdFirst` and `strataIsIdRest`, used directly rather than
mirrored here: a copy could drift from the lexer it is supposed to describe, and
the drift would be silent, costing a counterexample rather than failing.

The lexer has two rules, one for the first character and a wider one for the rest,
and `escape` answers to both. -/

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

/-- A character that cannot be emitted as itself, for one of three reasons: SMT-LIB
    forbids it outright (`|`, `\`, the controls) and offers no escape for it; it is
    the escape character; or a solver would echo it *bare* while DDM cannot read it
    bare, which is the `~ ^ & * - + = < > / %` gap, where leaving it alone costs the
    counterexample silently.

    Bounded to ASCII by construction, which is what lets two hex digits name it. -/
def mustEscape (c : Char) : Bool :=
  c.toNat ≤ 0x7F &&
    (c == '`' || c == '|' || c == '\\' || isControlChar c || (isSmtBare c && !strataIsIdRest c))

/-- Escape one character: the escape character, then two hex digits naming it. -/
def esc (c : Char) (rest : List Char) : List Char :=
  '`' :: hexDigit (c.toNat / 16) :: hexDigit (c.toNat % 16) :: rest

/-- Escape the characters that cannot be emitted as themselves. Applies at every
    position, so it does not handle the reserved first position; see `escape`. -/
def escapeAfterFirst : List Char → List Char
  | [] => []
  | c :: cs =>
    if mustEscape c then esc c (escapeAfterFirst cs) else c :: escapeAfterFirst cs

/-- Escape a name. The first character additionally has to be one DDM admits
    first, which covers the `@` and `.` SMT-LIB reserves there as well as `?`, `!`
    and the digits. See the module docstring for why that position is special. -/
def escape : List Char → List Char
  | [] => []
  | c :: cs =>
    if mustEscape c || (isSmtBare c && !strataIsIdFirst c) then esc c (escapeAfterFirst cs)
    else c :: escapeAfterFirst cs

/-- Inverse of both `escape` and `escapeAfterFirst`. One function suffices
    because the hex body names the character outright, so there is no positional
    rule to invert and no mnemonic to disambiguate.

    An escape character not followed by two hex digits is passed through, so this
    is total rather than defined only on the image. -/
def unescape : List Char → List Char
  | [] => []
  | '`' :: d1 :: d2 :: cs =>
    if isHexDigit d1 && isHexDigit d2 then
      Char.ofNat (hexVal d1 * 16 + hexVal d2) :: unescape cs
    else
      '`' :: unescape (d1 :: d2 :: cs)
  | c :: cs => c :: unescape cs

end Chars

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

/-- Escape `name` into the SMT-LIB symbol alphabet. Injective, and its result is
    always a legal symbol; both are proved in `Strata.DL.SMT.SymbolProps` as
    `escapeForSMT_injective` and `escapeForSMT_isLegalSMTSymbol`. -/
def escapeForSMT (name : String) : String :=
  String.ofList (Chars.escape name.toList)

/-- Inverse of `escapeForSMT`. -/
def unescapeFromSMT (symbol : String) : String :=
  String.ofList (Chars.unescape symbol.toList)

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
