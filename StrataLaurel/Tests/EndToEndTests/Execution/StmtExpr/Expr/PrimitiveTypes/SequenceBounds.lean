/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! An index outside a sequence violates `seqSelect`'s precondition, which a run
reports on the statement and then carries on. The verifier reports the same
precondition as "could not be proved", which no concrete run produces, and the Core
interpreter does not reduce `Sequence` operations, so this block runs the Laurel
interpreter only. -/

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure outOfRange()
  entry
  opaque
{
  var s: Sequence<int> := seqEmpty();
  var x: int := seqSelect(s, 0)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
};
#end
