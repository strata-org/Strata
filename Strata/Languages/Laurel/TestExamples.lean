/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import Strata.Languages.Laurel.LaurelToBoogieTranslator

open StrataTest.Util

namespace Laurel

def processLaurelFile (_ : String) : IO (List Diagnostic) := do
  pure []

def testAssertFalse : IO Unit := do
  testFile processLaurelFile "Strata/Languages/Laurel/Examples/AssertFalse.lr.st"

#eval! testAssertFalse

end Laurel
