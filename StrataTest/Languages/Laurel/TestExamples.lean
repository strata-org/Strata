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
open Strata.Elab (parseStrataProgramFromDialect)

namespace Laurel

def processLaurelFile (filePath : String) : IO (Array Diagnostic) := do
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let (inputContext, strataProgram) ← parseStrataProgramFromDialect dialects Laurel.name filePath

  -- Convert to Laurel.Program using parseProgram (handles unwrapping the program operation)
  let (laurelProgram, transErrors) := Laurel.TransM.run inputContext (Laurel.parseProgram strataProgram)
  if transErrors.size > 0 then
    throw (IO.userError s!"Translation errors: {transErrors}")

  -- Verify the program
  let diagnostics ← Laurel.verifyToDiagnostics "z3" laurelProgram

  pure diagnostics

def testAssertFalse : IO Unit := do
  testFile processLaurelFile "StrataTest/Languages/Laurel/Examples/Fundamentals/1. AssertFalse.lr.st"

#guard_msgs(error, drop all) in
#eval! testAssertFalse

end Laurel
