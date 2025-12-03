/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Laurel Parser using Lean's standard library Parser combinators.
This parser reflects the grammar defined in LaurelGrammar.lean
-/

import Std.Internal.Parsec.String
import Strata.Languages.Laurel.Laurel

namespace Laurel.Parser

open Std.Internal.Parsec
open Std.Internal.Parsec.String

abbrev Parser := Std.Internal.Parsec.String.Parser

/-
Helper parsers for whitespace and comments
-/

def lineComment : Parser Unit := do
  skipString "--"
  let _ <- many (satisfy fun c => c != '\n')
  let _ <- optional (pchar '\n')
  return ()

partial def blockCommentContent : Parser Unit := do
  let c <- satisfy (fun _ => true)
  if c == '-' then
    (attempt (skipChar '/' *> pure ())) <|> blockCommentContent
  else
    blockCommentContent

partial def blockComment : Parser Unit := do
  skipString "/-"
  blockCommentContent

def comment : Parser Unit := attempt blockComment <|> lineComment

def wsChar : Parser Unit := do
  let _ <- satisfy fun c => c.isWhitespace
  return ()

def ws : Parser Unit := do
  let _ <- many (wsChar <|> comment)
  return ()

/-
Token parsers that consume trailing whitespace
-/

def symbol (s : String) : Parser Unit := do
  skipString s
  ws

def keyword (s : String) : Parser Unit := do
  skipString s
  ws

def identifier : Parser String := do
  let first <- satisfy fun c => c.isAlpha || c == '_'
  let rest <- many (satisfy fun c => c.isAlphanum || c == '_')
  let id := String.mk (first :: rest.toList)
  -- Check that identifier is not a reserved keyword
  if id == "procedure" || id == "assert" || id == "assume" || id == "true" || id == "false" then
    fail s!"Reserved keyword used as identifier: {id}"
  ws
  return id

/-
Boolean literal parser
-/

def boolLiteral : Parser Bool := do
  (attempt (keyword "true" *> pure true)) <|> (keyword "false" *> pure false)

/-
StmtExpr parsers
-/

mutual

partial def stmtExpr : Parser StmtExpr := do
  literalBoolExpr <|> assertStmt <|> assumeStmt <|> blockStmt

partial def literalBoolExpr : Parser StmtExpr := do
  let b <- boolLiteral
  return .LiteralBool b

partial def assertStmt : Parser StmtExpr := do
  keyword "assert"
  let cond <- stmtExpr
  symbol ";"
  pure (.Assert cond #[])

partial def assumeStmt : Parser StmtExpr := do
  keyword "assume"
  let cond <- stmtExpr
  symbol ";"
  pure (.Assume cond #[])

partial def blockStmt : Parser StmtExpr := do
  symbol "{"
  let stmts <- many stmtExpr
  symbol "}"
  return .Block stmts.toList none

end

/-
Procedure parser
-/

def procedure : Parser Procedure := do
  keyword "procedure"
  let name <- identifier
  symbol "("
  symbol ")"
  let body <- blockStmt
  return {
    name := name
    inputs := []
    output := .TVoid
    precondition := .LiteralBool true
    decreases := .LiteralBool true
    deterministic := true
    reads := none
    modifies := .LiteralBool true
    body := .Transparent body
  }

/-
Program parser
-/

def program : Parser Program := do
  ws
  let procedures <- many procedure
  eof
  return {
    staticProcedures := procedures.toList
    staticFields := []
    types := []
  }

/-
Main parsing function
-/

def parseProgram (input : String) : Except String Program :=
  match program input.mkIterator with
  | ParseResult.success _ result => Except.ok result
  | ParseResult.error it err => Except.error s!"Parse error at position {it.pos}: {err}"

end Laurel.Parser