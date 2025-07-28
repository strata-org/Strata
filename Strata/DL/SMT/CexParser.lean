/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/



import Lean

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
  return String.mk chars.toList

def valToken : Parser String := do
  (attempt (do
    -- Handle parenthesized expression.
    let _open_paren ← pchar '('
    let content ← many (satisfy (fun c => c ≠ ')'))
    let _close_paren ← pchar ')'
    return s!"({String.mk content.toList})")) <|>
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
  match parseCEx1 (String.mkIterator cex) with
  | Std.Internal.Parsec.ParseResult.success _ result => Except.ok result
  | Std.Internal.Parsec.ParseResult.error pos msg => Except.error s!"Parse error at {pos}: {msg}"

/-- info: -/
#guard_msgs in
#eval format $ parseCEx ""

/-- info: (t1 -8) (t4 0) (t0 0) -/
#guard_msgs in
#eval format $ parseCEx "((t1 -8) (t4 0) (t0 0))"

/-- info: (t1 true) (t4 (+ blah blah)) (t0 (test x (foo y)) -/
#guard_msgs in
#eval format $ parseCEx "((t1 true)    (t4 (+ blah blah))
(t0 (test x (foo y))))"

/-- info: (t1 (- 8)) (t4 0) (t0 0) -/
#guard_msgs in
#eval format $ parseCEx "((t1 (- 8)) (t4 0) (t0 0))"

end Strata.SMT.CExParser
