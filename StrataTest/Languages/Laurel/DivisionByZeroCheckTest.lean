/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Laurel.DivisionByZeroCheck
import StrataTest.Util.TestDiagnostics

open Strata
open Strata.Elab (parseStrataProgramFromDialect)
open StrataTest.Util

namespace Strata.Laurel

/-! ## Helper -/

def parseLaurelAndInsertDivChecks (input : String) : IO Program := do
  let inputCtx := Strata.Parser.stringInputContext "test" input
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program => pure (insertDivisionByZeroChecks program)

/-! ## Unit test: transformation inserts the expected assertions -/

def divCheckUnitProgram : String := r"
procedure divTest(x: int, y: int) {
  var z: int := x / y;
}
"

/--
info: procedure divTest(x: int, y: int) returns ⏎
()
deterministic
{ assert y != 0; var z: int := x / y }
-/
#guard_msgs in
#eval! do
  let program ← parseLaurelAndInsertDivChecks divCheckUnitProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Unit test: mod also gets a check -/

def modCheckUnitProgram : String := r"
procedure modTest(x: int, y: int) {
  var z: int := x % y;
}
"

/--
info: procedure modTest(x: int, y: int) returns ⏎
()
deterministic
{ assert y != 0; var z: int := x % y }
-/
#guard_msgs in
#eval! do
  let program ← parseLaurelAndInsertDivChecks modCheckUnitProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Unit test: no division means no extra assertions -/

def noDivProgram : String := r"
procedure addTest(x: int, y: int) {
  var z: int := x + y;
}
"

/--
info: procedure addTest(x: int, y: int) returns ⏎
()
deterministic
{ var z: int := x + y }
-/
#guard_msgs in
#eval! do
  let program ← parseLaurelAndInsertDivChecks noDivProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Unit test: division inside if-then-else branch is not hoisted -/

def ifBranchDivProgram : String := r"
procedure ifBranchDiv(x: int, b: bool) {
  if (b) {
    var z: int := 10 / x;
  }
}
"

/--
info: procedure ifBranchDiv(x: int, b: bool) returns ⏎
()
deterministic
{ if b then { assert x != 0; var z: int := 10 / x } }
-/
#guard_msgs in
#eval! do
  let program ← parseLaurelAndInsertDivChecks ifBranchDivProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Unit test: division inside forall gets guarded with implication -/

def forallDivProgram : String := r"
procedure forallDiv(x: int) {
  assert forall(y: int) => x / y == x / y;
}
"

/--
info: procedure forallDiv(x: int) returns ⏎
()
deterministic
{ assert forall y: int => y != 0 && y != 0 ==> x / y == x / y }
-/
#guard_msgs in
#eval! do
  let program ← parseLaurelAndInsertDivChecks forallDivProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Unit test: functional procedure gets precondition instead of assert -/

def functionalDivProgram : String := r"
function pureDiv(x: int, y: int): int {
  x / y
}
"

/--
info: function pureDiv(x: int, y: int) returns ⏎
(result: int)
requires y != 0
deterministic
{ x / y }
-/
#guard_msgs in
#eval! do
  let program ← parseLaurelAndInsertDivChecks functionalDivProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## End-to-end test: safe division (no errors) and unsafe division (error) -/

def processLaurelWithDivChecks (input : Lean.Parser.InputContext) : IO (Array Diagnostic) := do
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name input
  let uri := Strata.Uri.file input.fileName
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok laurelProgram =>
    let transformed := insertDivisionByZeroChecks laurelProgram
    let files := Map.insert Map.empty uri input.fileMap
    Laurel.verifyToDiagnostics files transformed

def e2eProgram := r"
procedure safeDivision() {
  var x: int := 10;
  var y: int := 2;
  var z: int := x / y;
  assert z == 5;
}

procedure unsafeDivision(x: int) {
  var z: int := 10 / x;
//                   ^ error: assertion does not hold
}

function pureDiv(x: int, y: int): int {
  x / y
}

procedure callPureDivSafe() {
  var z: int := pureDiv(10, 2);
  assert z == 5;
}

procedure callPureDivUnsafe(x: int) {
  var z: int := pureDiv(10, x);
//              ^^^^^^^^^^^^^^ error: assertion does not hold
}
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "DivByZeroE2E" e2eProgram 168 processLaurelWithDivChecks

end Laurel
