/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

/-! # Finding the next `check-sat` answer in a solver's output

A query written to a file asks the solver several questions in a row: each `check-sat` (or
`check-sat-assuming`) is followed by a `get-value` when there are values to report. The solver's
output is therefore an answer (`sat`, `unsat` or `unknown`), then the `get-value` response (a
model, or an `(error …)` after `unsat`), then the next answer, and so on. SMT-LIB's
general response to any other command is `success`, `unsupported`, or an s-expression.

A model can name a user datatype constructor called `sat`, `unsat` or `unknown`, and a solver
may print a model over several lines, one value per line. So the next answer cannot be found by
looking for the next line that reads like one: it is the first top-level atom after the
responses that follow the previous answer, read as balanced s-expressions, `success` and
`unsupported`. `dropToVerdict` finds that atom and skips nothing else, so each answer stays at
its own position: any other atom (such as `timeout`) is returned like an answer, for the caller
to reject, rather than skipped in favor of a later check's answer.
`Strata.DL.SMT.VerdictReaderProps` proves this.

The model itself is parsed by the DDM parser, which reads a whole `get-value` response and does
not report where it ends; `dropToVerdict` lexes the same text only to find that end.
-/

public section

namespace Strata.SMT

/-- Where `dropToVerdict` stands in the SMT-LIB text it is skipping: in code, in a string
    literal, in a `|…|` quoted symbol, in a `;` comment, or in a `success` or `unsupported`
    response. -/
inductive ResponseLex where
  | code | str | sym | comment | generalAtom

/-- A solver's answer to a `check-sat`. `timeout` is not an SMT-LIB answer; it stands for a
    check that ran out of time. -/
inductive Decision where
  | sat
  | unsat
  | unknown
  | timeout
deriving DecidableEq, Repr

/-- The `check-sat` answer a token spells, if any: `sat`, `unsat` or `unknown`. Every reader of
    solver output decodes answers with this function. -/
def decodeVerdict : List Char → Option Decision
  | ['s', 'a', 't'] => some .sat
  | ['u', 'n', 's', 'a', 't'] => some .unsat
  | ['u', 'n', 'k', 'n', 'o', 'w', 'n'] => some .unknown
  | _ => none

/-- Whether `cs` starts with the atom `success` or `unsupported`, the two general responses
    that are not s-expressions. -/
def isGeneralAtom (cs : List Char) : Bool :=
  let tok := cs.takeWhile fun c =>
    !c.isWhitespace && c != '(' && c != ')' && c != '"' && c != '|' && c != ';'
  tok == "success".toList || tok == "unsupported".toList

/--
Drop the responses that precede the next `check-sat` answer, returning the text from the first
top-level atom on, or nothing when none follows.

The responses skipped are whitespace, `success`, `unsupported` and balanced s-expressions, such
as a `(get-value …)` model or an `(error …)`. An atom is recognized only at nesting depth 0, so a model spread over several
lines is skipped whole even when one of its lines reads `sat`, `unsat` or `unknown`.
Parentheses inside string literals, quoted symbols and comments do not count; SMT-LIB writes a
quote inside a string as `""`, which leaves the string and enters it again.

`Strata.SMT.IncrementalSolver.scanParens` balances parentheses in a live solver's replies with
the same rules for strings and quoted symbols; keep the two in step.
-/
def dropToVerdict (depth : Nat) (lex : ResponseLex) : List Char → List Char
  | [] => []
  | c :: cs =>
    match lex with
    | .str => dropToVerdict depth (if c == '"' then .code else .str) cs
    | .sym => dropToVerdict depth (if c == '|' then .code else .sym) cs
    | .comment => dropToVerdict depth (if c == '\n' then .code else .comment) cs
    | .code | .generalAtom =>
      if c == '"' then dropToVerdict depth .str cs
      else if c == '|' then dropToVerdict depth .sym cs
      else if c == ';' then dropToVerdict depth .comment cs
      else if c == '(' then dropToVerdict (depth + 1) .code cs
      else if c == ')' then dropToVerdict (depth - 1) .code cs
      else if lex matches .generalAtom then
        dropToVerdict depth (if c.isWhitespace then .code else .generalAtom) cs
      else if depth == 0 && !c.isWhitespace then
        if isGeneralAtom (c :: cs) then dropToVerdict 0 .generalAtom cs else c :: cs
      else dropToVerdict depth .code cs

/-- The first line of `cs`, without surrounding whitespace, decoded as an answer, and the text
    after that line. -/
def splitFirstLine (cs : List Char) : Option Decision × List Char :=
  let line := cs.takeWhile (· != '\n')
  (decodeVerdict ((line.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse,
   (cs.dropWhile (· != '\n')).drop 1)

/-- The answer at the next top-level atom, after skipping the responses that precede it. -/
def readVerdict (cs : List Char) : Option Decision :=
  (splitFirstLine (dropToVerdict 0 .code cs)).1

-- A two-sided answer as z3 prints it, with a model value spread over several lines, one of
-- which reads `unsat`. The answer after the model is `sat`.
#guard String.ofList (dropToVerdict 0 .code
  "((x (MkBig sat\n       unsat\n       unknown)))\nsat\n((x (MkBig sat\n       sat)))\n".toList)
  == "sat\n((x (MkBig sat\n       sat)))\n"

-- An `(error …)` response after an `unsat` answer, and parentheses inside a string literal and
-- inside a quoted symbol, are skipped.
#guard readVerdict "(error \"no model :) here\")\n((|a)b| unsat))\nunknown\n".toList
  == some .unknown

-- A string value holding a doubled quote and a parenthesis, `"""("`.
#guard readVerdict "((s \"\"\"(\"))\nunsat\n".toList == some .unsat

-- A quoted symbol holding a parenthesis and a line break, and a comment naming an answer.
#guard readVerdict "((|a (\nsat| 1) ; sat\n)\nunknown\n".toList == some .unknown

-- An answer that is not `sat`, `unsat` or `unknown` is returned in its place, not skipped in
-- favor of the next check's `unsat`.
#guard String.ofList (dropToVerdict 0 .code "((x 1))\ntimeout\nunsat\n".toList)
  == "timeout\nunsat\n"
#guard readVerdict "((x 1))\ntimeout\nunsat\n".toList == none

-- `success` and `unsupported` are responses and are skipped; any other word is returned.
#guard readVerdict "unsupported\n((x 1))\nsuccess\nunsat\n".toList == some .unsat
#guard String.ofList (dropToVerdict 0 .code "((x 1))\nsuccessful\nunsat\n".toList)
  == "successful\nunsat\n"
#guard readVerdict "((x 1))\nsuccessful\nunsat\n".toList == none

-- A line ending in CRLF.
#guard readVerdict "((x 1))\r\nunsat\r\n".toList == some .unsat

-- No answer follows.
#guard dropToVerdict 0 .code "((x\n  sat))\n".toList == []

end Strata.SMT
end
