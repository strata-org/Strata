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


def processLaurelFile (filePath : String) : IO (Array Diagnostic) := do

  let laurelDialect : Strata.Dialect := Laurel
  let (inputContext, strataProgram) ← Strata.Elab.parseStrataProgramFromDialect filePath laurelDialect

  -- Convert to Laurel.Program using parseProgram (handles unwrapping the program operation)
  let (laurelProgram, transErrors) := Laurel.TransM.run inputContext (Laurel.parseProgram strataProgram)
  if transErrors.size > 0 then
    throw (IO.userError s!"Translation errors: {transErrors}")

  -- Verify the program
  let diagnostics ← Laurel.verifyToDiagnostics "z3" laurelProgram

  pure diagnostics

def testAssertFalse : IO Unit := do
  testFile processLaurelFile "StrataTest/Languages/Laurel/Examples/Fundamentals/1. AssertFalse.lr.st"

#eval! testAssertFalse

end Laurel
