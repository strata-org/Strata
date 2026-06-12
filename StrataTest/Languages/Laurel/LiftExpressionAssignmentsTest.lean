/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the expression lifter correctly handles statement constructs
(heap-updating assignments) in non-last positions of block expressions,
by comparing the lifted Laurel against expected output.
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Laurel.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

private def parseLaurelAndLift (program : StrataDDM.Program) : IO Program := do
  let laurelProgram ← translateLaurel program
  let result := resolve laurelProgram
  pure (liftExpressionAssignments result.program result.model [])

private def printLifted (program : StrataDDM.Program) : IO Unit := do
  let lifted ← parseLaurelAndLift program
  for proc in lifted.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/--
info: procedure assertInBlockExpr()
  opaque
{
  var x: int := 0;
  assert $x_0 == 0;
  var $x_0: int := x;
  x := 1;
  var y: int := {
    x
  };
  assert y == 1
};
-/
#guard_msgs in
#eval! printLifted
#strata
program Laurel;
procedure assertInBlockExpr()
opaque {
  var x: int := 0;
  var y: int := { assert x == 0; x := 1; x };
  assert y == 1
};
#end

end Laurel
