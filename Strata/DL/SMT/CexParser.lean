/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Std.Internal.Parsec.String

namespace Strata.SMT.CExParser
open Std (Format ToFormat format)

/--
Represents a key-value pair, representing the value of a variable (key) in a
counterexample.
-/
structure KeyValue where
  key: String
  value: String
deriving Repr

instance : ToFormat KeyValue where
  format kv := f!"({kv.key} {kv.value})"

/-- Represents a counterexample as a list of key-value pairs -/
structure CEx where
  pairs: List KeyValue
deriving Repr

def CEx.format (cex : CEx) : Format :=
  go cex.pairs
  where go pairs :=
  match pairs with
  | [] => f!""
  | p :: prest => f!"{p} {go prest}"

instance : ToFormat CEx where
  format := CEx.format

instance : ToFormat (Except Format CEx) where
  format c := match c with
    | .ok cex => f!"{cex}"
    | .error e => f!"ERROR: {e}"

open Std.Internal.Parsec
open Std.Internal.Parsec.String

abbrev Parser := Std.Internal.Parsec.String.Parser

def varToken : Parser String := do
  let chars ← many1 (satisfy (fun c =>
    !c.isWhitespace && c ≠ '(' && c ≠ ')'))
  return String.ofList chars.toList

def valToken : Parser String := do
  (attempt (do
    -- Handle parenthesized expression.
    let _open_paren ← pchar '('
    let content ← many (satisfy (fun c => c ≠ ')'))
    let _close_paren ← pchar ')'
    return s!"({String.ofList content.toList})")) <|>
    -- Handle regular token.
    varToken

/-- Parses a single key-value pair: (<string> <string>) -/
def keyValuePair : Parser KeyValue := do
  skipChar '('
  ws
  let key ← varToken
  ws
  let value ← valToken
  ws
  skipChar ')'
  ws
  return { key := key, value := value }

def parseCEx1 : Parser CEx := do
  -- Handle a list of pairs.
  (attempt (do
    ws
    skipChar '('
    ws
    let pairs ← many keyValuePair
    ws
    skipChar ')'
    return { pairs := pairs.toList })) <|>
  -- Handle empty string, possibly with some whitespace.
  (attempt (do
    ws
    return { pairs := [] }))

def parseCEx (cex : String) : Except Format CEx :=
  match parseCEx1 ⟨cex, cex.startValidPos⟩ with
  | Std.Internal.Parsec.ParseResult.success _ result => Except.ok result
  | Std.Internal.Parsec.ParseResult.error ⟨_, pos⟩ msg => Except.error s!"Parse error at {pos.offset}: {msg}"

end Strata.SMT.CExParser
