/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the Laurel compilation pipeline produces the expected statistics
counters. Uses `translateWithLaurel` which returns `Statistics` as the fourth
tuple element.
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.LaurelCompilationPipeline
import Strata.Util.Statistics

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- Translate the program through the full Laurel pipeline and print stats. -/
private def printStats (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let (_, _, _, stats) ← translateWithLaurel {} laurelProgram
  IO.print stats.format

/-! ## Laurel Statistics: simple procedure -/

#guard_msgs in
#eval! printStats
#strata
program Laurel;
procedure test(x: int) returns (y: int)
  opaque
  ensures y == x
{
  y := x
};
#end

/-! ## Laurel Statistics: two procedures with holes -/

/--
info: [statistics] EliminateHoles.holesEliminated: 1
[statistics] InferHoleTypes.holesAnnotated: 1
-/
#guard_msgs in
#eval! printStats
#strata
program Laurel;
procedure p1(a: bool, b: bool) returns (r: bool)
  opaque
  ensures r == (a && b)
{
  r := a && b
};

procedure p2(x: int) returns (y: int)
  opaque
{
  y := x + <?>
};
#end

end Laurel
