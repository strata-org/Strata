/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
Tests that the `EliminateDoWhile` pass lowers a post-test `do … while` loop
to the pre-test form (see EliminateDoWhile.lean for the desugaring).
-/

meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
meta import Strata.Languages.Laurel.Grammar
meta import Strata.Languages.Laurel.EliminateDoWhile

meta section

open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-- Run the parser, then the `EliminateDoWhile` pass, so the printed output is
    the desugared pre-test form fed to the rest of the pipeline. -/
def parseEliminateDoWhile (input : String) : IO Program := do
  let inputCtx := StrataDDM.Parser.stringInputContext "test" input
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program => pure (eliminateDoWhile program)

/-- A single do-while; lowered form is in the `#guard_msgs` block below. -/
def basicProgram : String := r"
procedure basic()
  opaque
{
  var x: int := 0;
  do {
    x := x + 1
  } while(x < 3)
    invariant 0 <= x && x <= 2;
  assert x == 3
};
"

/--
info: procedure basic()
  opaque
{
  var x: int := 0;
  {
    while(true)
      invariant 0 <= x && x <= 2 {
      {
        x := x + 1
      };
      if !(x < 3)
        then exit $dowhile_exit_0
    }
  }$dowhile_exit_0;
  assert x == 3
};
-/
#guard_msgs in
#eval! do
  let program ← parseEliminateDoWhile basicProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-- Nested do-whiles get distinct fresh exit labels (`_0` inner, `_1` outer). -/
def nestedProgram : String := r"
procedure nested()
  opaque
{
  var x: int := 0;
  do {
    var y: int := 0;
    do {
      y := y + 1
    } while(y < 3)
      invariant 0 <= y;
    x := x + 1
  } while(x < 3)
    invariant 0 <= x;
  assert x == 3
};
"

/--
info: procedure nested()
  opaque
{
  var x: int := 0;
  {
    while(true)
      invariant 0 <= x {
      {
        var y: int := 0;
        {
          while(true)
            invariant 0 <= y {
            {
              y := y + 1
            };
            if !(y < 3)
              then exit $dowhile_exit_0
          }
        }$dowhile_exit_0;
        x := x + 1
      };
      if !(x < 3)
        then exit $dowhile_exit_1
    }
  }$dowhile_exit_1;
  assert x == 3
};
-/
#guard_msgs in
#eval! do
  let program ← parseEliminateDoWhile nestedProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

end Laurel
end Strata
end
