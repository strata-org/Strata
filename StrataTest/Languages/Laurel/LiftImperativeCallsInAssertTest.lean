/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the expression lifter correctly hoists imperative procedure calls
out of assert and assume conditions, while leaving assignments untouched
(so they are rejected downstream).
-/

import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.LaurelToCoreTranslator

open Strata
open Strata.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

private def parseLaurelAndLift (input : String) : IO Program := do
  let inputCtx := Strata.Parser.stringInputContext "test" input
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let result := resolve program
    let (program, model) := (result.program, result.model)
    pure (liftExpressionAssignments model program)

private def printLifted (input : String) : IO Unit := do
  let program ← parseLaurelAndLift input
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Imperative calls in assert are lifted -/

/--
info: procedure impure(): int
{ var x: int := 0; x := x + 1; x };
procedure test()
{ var $c_0: int; $c_0 := impure(); assert $c_0 == 1 };
-/
#guard_msgs in
#eval! printLifted r"
procedure impure(): int {
  var x: int := 0;
  x := x + 1;
  x
};
procedure test() {
  assert impure() == 1
};
"

/-! ## Assignments in assert are NOT lifted (rejected downstream) -/

/--
info: procedure test()
{ var x: int := 0; assert (x := 2) == 2 };
-/
#guard_msgs in
#eval! printLifted r"
procedure test() {
  var x: int := 0;
  assert (x := 2) == 2
};
"

/-! ## Imperative calls in assume are lifted -/

/--
info: procedure impure(): int
{ var x: int := 0; x := x + 1; x };
procedure test()
{ var $c_0: int; $c_0 := impure(); assume $c_0 == 1 };
-/
#guard_msgs in
#eval! printLifted r"
procedure impure(): int {
  var x: int := 0;
  x := x + 1;
  x
};
procedure test() {
  assume impure() == 1
};
"

end Laurel
