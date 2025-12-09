/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Util.IO
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.LaurelToBoogieTranslator

open StrataTest.Util
open Strata

namespace Laurel

def vcResultToDiagnostic (headerOffset : Nat) (vcr : Boogie.VCResult) : Option Diagnostic := do
  -- Only create a diagnostic if the result is not .unsat (i.e., verification failed)
  match vcr.result with
  | .unsat => none  -- Verification succeeded, no diagnostic
  | result =>
    -- Extract file range from metadata
    let fileRangeElem ← vcr.obligation.metadata.findElem Imperative.MetaData.fileRange
    match fileRangeElem.value with
    | .fileRange range =>
      let message := match result with
        | .sat _ => "assertion does not hold"
        | .unknown => "assertion verification result is unknown"
        | .err msg => s!"verification error: {msg}"
        | _ => "verification failed"
      some {
        -- Subtract headerOffset to account for program header we added
        start := { line := range.start.line - headerOffset, column := range.start.column }
        ending := { line := range.ending.line - headerOffset, column := range.ending.column }
        message := message
      }
    | _ => none

def processLaurelFile (filePath : String) : IO (List Diagnostic) := do
  -- Read file content
  let bytes ← Strata.Util.readBinInputSource filePath
  let fileContent ← match String.fromUTF8? bytes with
    | some s => pure s
    | none => throw (IO.userError s!"File {filePath} contains non UTF-8 data")

  -- Create LoadedDialects with the Init and Laurel dialects
  let laurelDialect : Strata.Dialect := Laurel
  let dialects := Elab.LoadedDialects.ofDialects! #[initDialect, laurelDialect]
  let dialect : Strata.DialectName := "Laurel"

  -- Add program header to the content
  let contents := s!"program {dialect};\n\n" ++ fileContent

  -- Parse the file content as a Laurel program
  let leanEnv ← Lean.mkEmptyEnvironment 0
  let inputContext := Strata.Parser.stringInputContext filePath contents

  -- Parse using elabProgram which handles the program header
  let strataProgram ← match Strata.Elab.elabProgram dialects leanEnv inputContext with
    | .ok program => pure program
    | .error errors =>
      let errMsg ← errors.foldlM (init := "Parse errors:\n") fun msg e =>
        return s!"{msg}  {e.pos.line}:{e.pos.column}: {← e.data.toString}\n"
      throw (IO.userError errMsg)

  -- The parsed program has a single `program` operation wrapping the procedures
  -- We need to extract the actual procedure commands from within it
  let procedureCommands : Array Strata.Operation :=
    if strataProgram.commands.size == 1 &&
       strataProgram.commands[0]!.name == q`Laurel.program then
      -- Extract procedures from the program operation's first argument (Seq Procedure)
      match strataProgram.commands[0]!.args[0]! with
      | .seq _ procs => procs.filterMap fun arg =>
          match arg with
          | .op op => some op
          | _ => none
      | _ => strataProgram.commands
    else
      strataProgram.commands

  -- Create a new Strata.Program with just the procedures
  let procedureProgram : Strata.Program := {
    dialects := strataProgram.dialects
    dialect := strataProgram.dialect
    commands := procedureCommands
  }

  -- Convert to Laurel.Program using parseProgram from the Grammar module
  let (laurelProgram, transErrors) := Laurel.TransM.run inputContext (Laurel.parseProgram procedureProgram)
  if transErrors.size > 0 then
    throw (IO.userError s!"Translation errors: {transErrors}")

  -- Verify the program
  let vcResults ← Laurel.verify "z3" laurelProgram

  -- Convert VCResults to Diagnostics
  -- The header "program {dialect};\n\n" adds 2 lines, so subtract 2 from line numbers
  let headerOffset := 2
  let diagnostics := vcResults.filterMap (vcResultToDiagnostic headerOffset) |>.toList

  pure diagnostics

def testAssertFalse : IO Unit := do
  testFile processLaurelFile "Strata/Languages/Laurel/Examples/AssertFalse.lr.st"

#eval! testAssertFalse

end Laurel
