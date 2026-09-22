/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.SMT.Symbol

meta section

/-! ## Tests for escaping names into the SMT-LIB symbol alphabet

Three things can make a character unemittable. SMT-LIB forbids `|`, `\` and the
control characters outright, with no escape mechanism. `@` and `.` are legal but
may not appear *first*, which quoting does not lift and a `@N` suffix cannot
repair. And a character that SMT-LIB admits in a *bare* symbol but DDM does not
admit in a bare identifier would be echoed bare by a solver and then fail to
parse, losing the counterexample. That is the `~ ^ & * - + = < > / %` group.

Each is escaped as a backtick followed by two hex digits naming the character. The
backtick is what makes this work: it cannot appear in a bare simple symbol, so any
escaped name is necessarily quoted, in the echo as well as in the script, and a
quoted symbol always parses.

The general facts (that escaping is injective, that its result is a legal
symbol, and that its result is readable back) are proved in
`Strata.DL.SMT.SymbolProps`. What is worth testing here is the concrete spelling.
-/

open Strata.SMT

/-! ### Names needing no escaping are untouched

Every internally generated name lives in the `$__` namespace, and `$`, `_`, `.`
and `@` are in both alphabets, so none is rewritten. `#` and `'` are in neither
bare alphabet, so a solver quotes them and they need no escape either. -/

#guard Symbol.escapeForSMT "x" == "x"
#guard Symbol.escapeForSMT "$__cse.0" == "$__cse.0"
#guard Symbol.escapeForSMT "$__nondet_ite$_0" == "$__nondet_ite$_0"
#guard Symbol.escapeForSMT "$__mono#Cons#int" == "$__mono#Cons#int"
#guard Symbol.escapeForSMT "Box..x'" == "Box..x'"
#guard Symbol.escapeForSMT "v@1" == "v@1"
#guard Symbol.escapeForSMT "α" == "α"

/-! ### Characters SMT-LIB forbids outright -/

#guard Symbol.escapeForSMT "a|b" == "a`7Cb"
#guard Symbol.escapeForSMT "a\\b" == "a`5Cb"

/-! ### Control characters

Tab, newline and carriage return are escaped even though SMT-LIB counts them as
whitespace: a newline inside a symbol would break the line-oriented reading of
solver output. -/

#guard Symbol.escapeForSMT "a\u0000b" == "a`00b"
#guard Symbol.escapeForSMT "a\tb" == "a`09b"
#guard Symbol.escapeForSMT "a\nb" == "a`0Ab"
#guard Symbol.escapeForSMT "a\u007Fb" == "a`7Fb"
#guard Symbol.escapeForSMT "\u001Bx" == "`1Bx"

/-! ### The escape character itself, so the escaping stays injective

A space needs no escaping: it is not bare-legal, so a name containing one is
quoted and readable back as it stands. -/

#guard Symbol.escapeForSMT "a`b" == "a`60b"
#guard Symbol.escapeForSMT "a b" == "a b"

/-! ### Characters a solver echoes bare that DDM cannot read bare

These are legal SMT-LIB symbol characters, so nothing rejects them, but left
alone the model comes back unreadable, because the solver echoes them bare and
the answer parser admits a narrower alphabet. Escaping them forces a quoted echo,
which always parses. -/

#guard Symbol.escapeForSMT "a%b" == "a`25b"
#guard Symbol.escapeForSMT "a-b" == "a`2Db"
#guard Symbol.escapeForSMT "a+b" == "a`2Bb"
#guard Symbol.escapeForSMT "a*b" == "a`2Ab"
#guard Symbol.escapeForSMT "a=b" == "a`3Db"
#guard Symbol.escapeForSMT "a<b" == "a`3Cb"
#guard Symbol.escapeForSMT "a>b" == "a`3Eb"
#guard Symbol.escapeForSMT "a/b" == "a`2Fb"
#guard Symbol.escapeForSMT "a~b" == "a`7Eb"
#guard Symbol.escapeForSMT "a^b" == "a`5Eb"
#guard Symbol.escapeForSMT "a&b" == "a`26b"

/-! ### A reserved first position

Only the first character is rewritten; the same character later is not, which is
what keeps the uniquifier's `@N` suffix and the `..` selector separator intact. -/

#guard Symbol.escapeForSMT "@x" == "`40x"
#guard Symbol.escapeForSMT ".x" == "`2Ex"
#guard Symbol.escapeForSMT "x@y" == "x@y"
#guard Symbol.escapeForSMT "x.y" == "x.y"

/-! The first position answers to DDM's lexer as well as to SMT-LIB. `?` and `!`
are legal SMT-LIB simple-symbol characters anywhere, so a solver echoes `?x` bare,
but DDM admits only a letter, `_` or `$` first and cannot lex it. A leading digit
needs the same treatment for the same reason, even though SMT-LIB quotes such a
symbol of its own accord. Later positions are untouched. -/

#guard Symbol.escapeForSMT "?x" == "`3Fx"
#guard Symbol.escapeForSMT "!x" == "`21x"
#guard Symbol.escapeForSMT "0x" == "`30x"
#guard Symbol.escapeForSMT "x?y" == "x?y"
#guard Symbol.escapeForSMT "x!y" == "x!y"
#guard Symbol.escapeForSMT "x0y" == "x0y"

/-! ### Pairs that collided under a rejected scheme

Distinctness in general is `escapeForSMT_injective`, so there is nothing to gain
from asserting it again on examples. What these pin is the *spelling* each name
gets, for the two pairs a rejected design would have merged.

A backslash escape (`\ ↦ \\`, `| ↦ \p`) sent both of these to the symbol `a\p`,
because z3 unescapes `\\` (cvc5 does not), and merging two names into one symbol
lets a false obligation be proved. -/

#guard Symbol.escapeForSMT "a\\p" == "a`5Cp"
#guard Symbol.escapeForSMT "a|" == "a`7C"

/-! Repairing the reserved first position with a `$` prefix instead of escaping it
would send both of these to `$@x`, which is why the first character is escaped
rather than prefixed. -/

#guard Symbol.escapeForSMT "@x" == "`40x"
#guard Symbol.escapeForSMT "$@x" == "$@x"

/-! ### Round-trip, legality and readability on a corpus

`unescapeFromSMT` recovers the name, which is what lets a symbol echoed back by a
solver be matched against the id the encoder holds. `isLegalSMTSymbol` and
`isReadableBack` are proved for all inputs; checking them here guards the corpus
itself. -/

private def corpus : List String :=
  ["x", "a|b", "a\\b", "a%b", "a|", "a\\", "a%", "@x", ".x", "@", ".", "$@x",
   "a-b", "a+b", "a*b", "a=b", "a<b", "a>b", "a/b", "a~b", "a^b", "a&b",
   "a|b\\c%d", "|", "\\", "%", "", "$__cse.0", "v'", "a b", "  ", "α", "a`b", "`", "``",
   "@a b_0", "a\u0000b", "a\tb", "a\nb", "a\u007Fb", "\u001B", "\u0000",
   "MkBox) ) ) (assert false) (declare-datatype Junk ((J"]

#guard corpus.all fun s => Symbol.unescapeFromSMT (Symbol.escapeForSMT s) == s

/-! Round-tripping also survives the pipe delimiters a solver echoes back. -/
#guard corpus.all fun s => Symbol.ofSMTString (Symbol.toSMTString s) == s

#guard corpus.all fun s => Symbol.isLegalSMTSymbol (Symbol.escapeForSMT s).toList

#guard corpus.all fun s => Symbol.isReadableBack (Symbol.escapeForSMT s).toList

/-! ### Reading symbols back out of a solver's answer

A model value can name something we declared, or something the solver invented
for an element of an uninterpreted sort. Only the former is unescaped; the latter
is recognized by its leading `@` or `.`, which escaping never produces. -/

#guard Symbol.ofSolverSymbol {} "a`7Cb" == "a|b"
#guard Symbol.ofSolverSymbol {} "|a`7Cb|" == "a|b"
#guard Symbol.ofSolverSymbol {} "|`40x|" == "@x"

/-! Symbols the solver invented are returned as they came, pipes aside. -/
#guard Symbol.ofSolverSymbol {} "@_S_0" == "@_S_0"
#guard Symbol.ofSolverSymbol {} "|@_a b__0|" == "@_a b__0"
#guard Symbol.ofSolverSymbol {} ".hidden" == ".hidden"

/-! Theory symbols need no special case: none contains an escaped character, so
unescaping is the identity on them. -/
#guard Symbol.ofSolverSymbol {} "true" == "true"
#guard Symbol.ofSolverSymbol {} "bv12" == "bv12"
#guard Symbol.ofSolverSymbol {} "str.++" == "str.++"
#guard Symbol.ofSolverSymbol {} "set.insert" == "set.insert"

/-! A solver-invented symbol that collides with a declared name is given a fresh
suffix, so a counterexample cannot show it as a name the program already uses.
Renaming is safe because such a symbol stands for "some element of this sort" and
names nothing in the source. -/
#guard Symbol.ofSolverSymbol (Std.HashSet.ofList ["@_S_0"]) "@_S_0" == "@_S_0@1"
#guard Symbol.ofSolverSymbol (Std.HashSet.ofList ["@_S_0", "@_S_0@1"]) "@_S_0" == "@_S_0@2"
#guard Symbol.ofSolverSymbol (Std.HashSet.ofList ["x"]) "@_S_0" == "@_S_0"

/-! Our own names are never renamed, even when declared. That is the point of
the collision check being restricted to the solver's symbols. Unescaping is
injective, so two of ours can never need it. -/
#guard Symbol.ofSolverSymbol (Std.HashSet.ofList ["a|b"]) "a`7Cb" == "a|b"
#guard Symbol.ofSolverSymbol (Std.HashSet.ofList ["@x"]) "`40x" == "@x"

/-! ### Quoting

Pipe delimiters are added only when the escaped name is not already a simple
symbol. An escaped name always contains a backtick, so it is always quoted, which
is exactly why it can be read back. -/

#guard Symbol.toSMTString "x" == "x"
#guard Symbol.toSMTString "v@1" == "v@1"
#guard Symbol.toSMTString "v'" == "|v'|"
#guard Symbol.toSMTString "α" == "|α|"
#guard Symbol.toSMTString "a b" == "|a b|"
#guard Symbol.toSMTString "a|b" == "|a`7Cb|"
#guard Symbol.toSMTString "@x" == "|`40x|"
#guard Symbol.toSMTString "a-b" == "|a`2Db|"

end
