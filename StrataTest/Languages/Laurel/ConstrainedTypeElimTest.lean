/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the constrained type elimination pass correctly transforms
Laurel programs by comparing the output against expected results.
-/

import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.ConstrainedTypeElim
import Strata.Languages.Laurel.Resolution

open Strata
open Strata.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

def testProgram : String := r"
constrained nat = x: int where x >= 0 witness 0
procedure test(n: nat) returns (r: nat) {
  assert r >= 0;
  var y: nat := n;
  return y
};
"

def parseLaurelAndElim (input : String) : IO Program := do
  let inputCtx := Strata.Parser.stringInputContext "test" input
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let result := resolve program
    let (program, model) := (result.program, result.model)
    pure (constrainedTypeElim model program).1

/--
info: function nat$constraint(x: int): bool
{ x >= 0 };
procedure test(n: int)
  returns (r: int)
  requires nat$constraint(n)
  opaque
  ensures nat$constraint(r)
{ assert r >= 0; var y: int := n; assert nat$constraint(y); return y };
procedure $witness_nat()
{ var $witness: int := 0; assert nat$constraint($witness) };
-/
#guard_msgs in
#eval! do
  let program ← parseLaurelAndElim testProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

-- Scope management: constrained variable in if-branch must not leak into sibling block
def scopeProgram : String := r"
constrained pos = v: int where v > 0 witness 1
procedure test(b: bool) {
  if b then {
    var x: pos := 1
  };
  {
    var x: int := -5;
    x := -10
  }
};
"

/--
info: function pos$constraint(v: int): bool
{ v > 0 };
procedure test(b: bool)
{ if b then { var x: int := 1; assert pos$constraint(x) }; { var x: int := -5; x := -10 } };
procedure $witness_pos()
{ var $witness: int := 1; assert pos$constraint($witness) };
-/
#guard_msgs in
#eval! do
  let program ← parseLaurelAndElim scopeProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

-- Uninitialized constrained variable: havoc + assume constraint.
-- The variable has no known value, only the type constraint is assumed.
def uninitProgram : String := r"
constrained posint = x: int where x > 0 witness 1
procedure f() {
  var x: posint;
  assert x == 1
};
"

/--
info: function posint$constraint(x: int): bool
{ x > 0 };
procedure f()
{ var x: int; assume posint$constraint(x); assert x == 1 };
procedure $witness_posint()
{ var $witness: int := 1; assert posint$constraint($witness) };
-/
#guard_msgs in
#eval! do
  let program ← parseLaurelAndElim uninitProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

end Laurel
