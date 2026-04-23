/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Differential testing tool: reads (regex, string, mode) triples from stdin,
-- checks each against Strata's SMT backend, and prints results to stdout.
--
-- Usage: DiffTestCore [--log-dir <path>]
--
-- Example: printf "a\ta\tfullmatch\n" | DiffTestCore
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
-- When --log-dir <path> is given, each generated .core.st program is written to
-- <path>/<n>_<mode>.core.st (1-indexed) with a header comment showing the
-- original regex and string, for inspection and debugging.
--
-- Restriction: <regex> and <string> fields must not contain tab characters.

import Strata.Languages.Core.Verifier
import Strata.Languages.Python.Regex.ReToCore

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

def modeToStr : MatchMode → String
  | .match     => "match"
  | .fullmatch => "fullmatch"
  | .search    => "search"

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
  "procedure main() {\n" ++
  s!"  assert [match_check]: (str.in.re(\"{escapeForCore testStr}\", {regexStr}));\n" ++
  "};"

/-- Check whether testStr matches pyRegex (in the given mode) via Strata's SMT backend.
    If logPath is some path, the generated Core program is written there before checking. -/
def checkMatch (pyRegex testStr : String) (mode : MatchMode)
    (logPath : Option String := none) : IO StrataResult := do
  let (regexExpr, parseErr) := pythonRegexToCore pyRegex mode
  match parseErr with
  | some (.patternError _ _ _)  => return .parseError "patternError"
  | some (.unimplemented _ _ _) => return .parseError "unimplemented"
  | none =>
    let regexStr := toString (Core.formatExprs [regexExpr])
    let progText := mkProgText testStr regexStr
    if let some path := logPath then
      try
        let header := s!"// regex:  {pyRegex}\n// string: {testStr}\n// mode:   {modeToStr mode}\n\n"
        IO.FS.writeFile path (header ++ progText ++ "\n")
      catch e =>
        IO.eprintln s!"[log] Failed to write {path}: {e}"
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
      | some vc =>
          if vc.isSuccess then return .match
          else if vc.isFailure then return .noMatch
          else return match vc.outcome with
            | .error msg => .smtError s!"impl: {msg}"
            | _ => .smtError "unknown"

def main (args : List String) : IO UInt32 := do
  let logDir : Option String ← match args with
    | ["--log-dir", path] => do
        try IO.FS.createDir path catch _ => pure ()
        pure (some path)
    | _ => pure none
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  let mut idx := 1
  let mut line ← stdin.getLine
  while !line.isEmpty do
    let trimmed := String.ofList (line.toList.reverse.dropWhile Char.isWhitespace).reverse
    if !trimmed.isEmpty then
      let parts := trimmed.splitOn "\t"
      let modeStr := (parts[2]?).getD "unknown"
      let logPath := logDir.map (fun dir => dir ++ s!"/{idx}_{modeStr}.core.st")
      let result ← match parts with
        | [regex, str, modeStr] => match parseMode modeStr with
          | none      => pure (StrataResult.smtError "unknown_mode")
          | some mode => checkMatch regex str mode logPath
        | _ => pure (StrataResult.smtError "bad_input_format")
      match parts with
      | [regex, str, modeStr] =>
        stdout.putStrLn s!"{regex}\t{str}\t{modeStr}\t{result.toStr}"
      | _ =>
        stdout.putStrLn s!"<bad>\t<bad>\t<bad>\t{result.toStr}"
      idx := idx + 1
    line ← stdin.getLine
  return 0
