/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Differential testing tool: reads (regex, string, mode) triples from stdin,
-- checks each against Strata's SMT backend, and prints results to stdout.
--
-- Input  (stdin):  one test per line, tab-separated: <regex>\t<string>\t<mode>
-- Output (stdout): one result per line, tab-separated: <regex>\t<string>\t<mode>\t<result>
--
-- <result> is one of:
--   match
--   noMatch
--   parseError:patternError
--   parseError:unimplemented
--   smtError:<detail>
--
-- Restriction: <regex> and <string> fields must not contain tab characters.

import Strata.Languages.Core.Verifier
import Strata.Languages.Python.Regex.ReToCore
import Strata.Languages.Core.DDMTransform.ASTtoCST

open Strata Strata.Python
open Core (VerifyOptions)

/-- Escape a string for embedding as a double-quoted Core string literal. -/
def escapeForCore (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '\\' => "\\\\"
    | '"'  => "\\\""
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | _    => toString c) ""

def parseMode (s : String) : Option MatchMode :=
  match s with
  | "match"     => some .match
  | "fullmatch" => some .fullmatch
  | "search"    => some .search
  | _           => none

inductive StrataResult where
  | match
  | noMatch
  | parseError (kind : String)  -- "patternError" or "unimplemented"
  | smtError   (msg  : String)

def StrataResult.toStr : StrataResult → String
  | .match           => "match"
  | .noMatch         => "noMatch"
  | .parseError kind => s!"parseError:{kind}"
  | .smtError   msg  => s!"smtError:{msg}"

/-- Build a Core program that asserts str.in.re(testStr, regexExpr). -/
def mkProgText (testStr : String) (regexStr : String) : String :=
  "program Core;\n" ++
  "procedure main() returns () {\n" ++
  s!"  assert [match_check]: (str.in.re(\"{escapeForCore testStr}\", {regexStr}));\n" ++
  "};"

/-- Check whether testStr matches pyRegex (in the given mode) via Strata's SMT backend. -/
def checkMatch (pyRegex testStr : String) (mode : MatchMode) : IO StrataResult := do
  let (regexExpr, parseErr) := pythonRegexToCore pyRegex mode
  match parseErr with
  | some (.patternError _ _ _)  => return .parseError "patternError"
  | some (.unimplemented _ _ _) => return .parseError "unimplemented"
  | none =>
    let regexStr := toString (Core.formatExprs [regexExpr])
    let progText := mkProgText testStr regexStr
    let inputCtx := Lean.Parser.mkInputContext progText "<diff_test>"
    let dctx := Elab.LoadedDialects.builtin
    let dctx := dctx.addDialect! Core
    let leanEnv ← Lean.mkEmptyEnvironment 0
    match Strata.Elab.elabProgram dctx leanEnv inputCtx with
    | .error errors =>
      let msgs ← errors.toList.mapM (·.toString)
      let errStr := String.intercalate "; " msgs
      return .smtError s!"elab: {errStr}"
    | .ok pgm =>
      let vcResults ← verify pgm inputCtx none .quiet
      match vcResults[0]? with
      | none    => return .smtError "no VCs generated"
      | some vc => return match vc.result with
        | .pass                    => .match
        | .fail                    => .noMatch
        | .unknown                 => .smtError "unknown"
        | .implementationError msg => .smtError s!"impl: {msg}"

def main : IO UInt32 := do
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  let mut line ← stdin.getLine
  while !line.isEmpty do
    let trimmed := line.dropRightWhile Char.isWhitespace
    if !trimmed.isEmpty then
      let parts := trimmed.splitOn "\t"
      let result ← match parts with
        | [regex, str, modeStr] => match parseMode modeStr with
          | none      => pure (StrataResult.smtError "unknown_mode")
          | some mode => checkMatch regex str mode
        | _ => pure (StrataResult.smtError "bad_input_format")
      match parts with
      | [regex, str, modeStr] =>
        stdout.putStrLn s!"{regex}\t{str}\t{modeStr}\t{result.toStr}"
      | _ =>
        stdout.putStrLn s!"<bad>\t<bad>\t<bad>\t{result.toStr}"
    line ← stdin.getLine
  return 0
