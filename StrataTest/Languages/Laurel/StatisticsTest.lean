/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the Laurel compilation pipeline produces the expected statistics
counters. Uses `translateWithLaurel` which returns `Statistics` as the fourth
tuple element.
-/

import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.LaurelCompilationPipeline
import Strata.Util.Statistics

open Strata
open Strata.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-- Parse a Laurel source string and run it through the full Laurel pipeline,
    returning the merged statistics from all passes. -/
private def parseLaurelAndGetStats (input : String) : IO Statistics := do
  let inputCtx := Strata.Parser.stringInputContext "test" input
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let (_, _, _, stats) ← translateWithLaurel {} program
    return stats

/-! ## Laurel Statistics: simple procedure -/

#guard_msgs in
#eval! do
  let stats ← parseLaurelAndGetStats r"
procedure test(x: int) returns (y: int)
  ensures y == x
{
  y := x
};
"
  IO.print stats.format

/-! ## Laurel Statistics: two procedures with holes -/

/--
info: [statistics] EliminateHoles.holesEliminated: 1
[statistics] InferHoleTypes.holesAnnotated: 1
-/
#guard_msgs in
#eval! do
  let stats ← parseLaurelAndGetStats r"
procedure p1(a: bool, b: bool) returns (r: bool)
  ensures r == (a && b)
{
  r := a && b
};

procedure p2(x: int) returns (y: int)
{
  y := x + <?>
};
"
  IO.print stats.format

end Laurel
