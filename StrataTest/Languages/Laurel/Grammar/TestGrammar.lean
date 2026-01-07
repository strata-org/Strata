/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Test the minimal Laurel grammar
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import StrataTest.DDM.TestGrammar
import Strata.DDM.BuiltinDialects.Init

open Strata
open StrataTest.DDM

namespace Laurel

def testAssertFalse : IO Unit := do
  let laurelDialect: Strata.Dialect := Laurel
  let filePath := "StrataTest/Languages/Laurel/Examples/Fundamentals/1. AssertFalse.lr.st"
  let result ← testGrammarFile laurelDialect filePath

  if !result.normalizedMatch then
    throw (IO.userError "Test failed: formatted output does not match input")

#guard_msgs in
#eval testAssertFalse
