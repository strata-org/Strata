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

  let laurelDialect : Strata.Dialect := Laurel
  let (inputContext, strataProgram) ← Strata.Elab.parseDialectIntoConcreteAst filePath laurelDialect

  -- Convert to Laurel.Program using parseProgram (handles unwrapping the program operation)
  let (laurelProgram, transErrors) := Laurel.TransM.run inputContext (Laurel.parseProgram strataProgram)
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
