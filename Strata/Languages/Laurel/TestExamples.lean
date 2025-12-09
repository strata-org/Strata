/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics

open StrataTest.Util

namespace Laurel

def testAssertFalse : IO Unit := do
  testFile "Strata/Languages/Laurel/Examples/Fundamentals/AssertFalse.lr.st"

#eval! testAssertFalse

end Laurel
