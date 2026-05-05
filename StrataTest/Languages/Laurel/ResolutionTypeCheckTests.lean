/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the resolution pass detects type checking errors — e.g. using an int
where a bool is expected, or passing the wrong type to a procedure.
-/

import StrataTest.Util.TestDiagnostics
import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Resolution

open StrataTest.Util
open Strata
open Strata.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-- Run only parsing + resolution and return diagnostics (no SMT verification). -/
private def processResolution (input : Lean.Parser.InputContext) : IO (Array Diagnostic) := do
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name input
  let uri := Strata.Uri.file input.fileName
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let result := resolve program
    let files := Map.insert Map.empty uri input.fileMap
    return result.errors.toList.map (fun dm => dm.toDiagnostic files) |>.toArray

/-! ## Non-boolean condition in if-then-else -/

def ifCondNotBool := r"
function foo(x: int): int {
  if x then 1 else 0
//   ^ error: expected bool, but got 'int'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "IfCondNotBool" ifCondNotBool 39 processResolution

/-! ## Non-boolean condition in assert -/

def assertCondNotBool := r"
procedure baz() opaque {
  var x: int := 42;
  assert x
//       ^ error: expected bool, but got 'int'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "AssertCondNotBool" assertCondNotBool 49 processResolution

/-! ## Non-boolean condition in assume -/

def assumeCondNotBool := r"
procedure qux() opaque {
  var x: int := 42;
  assume x
//       ^ error: expected bool, but got 'int'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "AssumeCondNotBool" assumeCondNotBool 59 processResolution

/-! ## Non-boolean operand in logical and -/

def logicalAndNotBool := r"
function foo(x: int, y: bool): bool {
  x && y
//^^^^^^ error: expected bool, but got 'int'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "LogicalAndNotBool" logicalAndNotBool 69 processResolution

/-! ## Assignment type mismatch -/

def assignTypeMismatch := r"
procedure foo() opaque {
  var x: int := true
//^^^^^^^^^^^^^^^^^^ error: expected 'int', but got 'bool'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "AssignTypeMismatch" assignTypeMismatch 79 processResolution

/-! ## Function return type mismatch -/

def returnTypeMismatch := r"
function foo(): int {
//       ^^^ error: expected 'int', but got 'bool'
  true
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "ReturnTypeMismatch" returnTypeMismatch 89 processResolution

/-! ## Static call argument type mismatch -/

def callArgTypeMismatch := r"
function bar(x: int): int { x };
function foo(): int {
  bar(true)
//^^^^^^^^^ error: expected 'int', but got 'bool'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "CallArgTypeMismatch" callArgTypeMismatch 99 processResolution

/-! ## Non-boolean condition in while loop -/

def whileCondNotBool := r"
procedure wh() opaque {
  var x: int := 1;
  while (x) { }
//       ^ error: expected bool, but got 'int'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "WhileCondNotBool" whileCondNotBool 109 processResolution

/-! ## Non-numeric operand in comparison -/

def comparisonNotNumeric := r"
function cmp(x: string, y: int): bool {
  x < y
//^^^^^ error: expected a numeric type, but got 'string'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "ComparisonNotNumeric" comparisonNotNumeric 121 processResolution

end Laurel
