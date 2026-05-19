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

/-! ## Non-boolean conditions -/

def ifCondNotBool := r"
function foo(x: int): int {
  if x then 1 else 0
//   ^ error: expected 'bool', got 'int'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "IfCondNotBool" ifCondNotBool 44 processResolution

def assertCondNotBool := r"
procedure baz() opaque {
  var x: int := 42;
  assert x
//       ^ error: expected 'bool', got 'int'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "AssertCondNotBool" assertCondNotBool 54 processResolution

def assumeCondNotBool := r"
procedure qux() opaque {
  var x: int := 42;
  assume x
//       ^ error: expected 'bool', got 'int'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "AssumeCondNotBool" assumeCondNotBool 64 processResolution

def whileCondNotBool := r"
procedure wh() opaque {
  var x: int := 1;
  while (x) { }
//       ^ error: expected 'bool', got 'int'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "WhileCondNotBool" whileCondNotBool 74 processResolution

/-! ## Logical operator type checks -/

def logicalAndNotBool := r"
function foo(x: int, y: bool): bool {
  x && y
//^ error: expected 'bool', got 'int'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "LogicalAndNotBool" logicalAndNotBool 84 processResolution

/-! ## Numeric operator type checks -/

def comparisonNotNumeric := r"
function cmp(x: string, y: int): bool {
  x < y
//^ error: '<' expected a numeric type, got 'string'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "ComparisonNotNumeric" comparisonNotNumeric 94 processResolution

/-! ## Assignment type checks -/

def assignTypeMismatch := r"
procedure foo() opaque {
  var x: int := true
//^^^^^^^^^^^^^^^^^^ error: expected 'int', got 'bool'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "AssignTypeMismatch" assignTypeMismatch 104 processResolution

/-! ## Function return type checks -/

def returnTypeMismatch := r"
function foo(): int {
//       ^^^ error: expected 'int', got 'bool'
  true
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "ReturnTypeMismatch" returnTypeMismatch 114 processResolution

/-! ## Call argument type checks -/

def callArgTypeMismatch := r"
function bar(x: int): int { x };
function foo(): int {
  bar(true)
//    ^^^^ error: expected 'int', got 'bool'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "CallArgTypeMismatch" callArgTypeMismatch 124 processResolution

/-! ## Equality operator type checks -/

def equalityTypeMismatch := r"
function cmp(x: int, y: string): bool {
  x == y
//^^^^^^ error: Operands of '==' have incompatible types 'int' and 'string'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "EqualityTypeMismatch" equalityTypeMismatch 134 processResolution

/-! ## Multi-output procedures -/

def multiOutputInExpr := r"
procedure multi(x: int) returns (a: int, b: int) opaque;
procedure test() opaque {
  assert multi(1) == 1
//       ^^^^^^^^^^^^^ error: Operands of '==' have incompatible types '(int, int)' and 'int'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "MultiOutputInExpr" multiOutputInExpr 146 processResolution

def assignTargetCountMismatch := r"
procedure multi() returns (a: int, b: int) opaque;
procedure test() opaque {
  var x: int := multi()
//^^^^^^^^^^^^^^^^^^^^^ error: expected 'int', got '(int, int)'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "AssignTargetCountMismatch" assignTargetCountMismatch 156 processResolution

/-! ## UserDefined cross-type assignment

Assignments between unrelated composites are rejected: `isSubtype` walks
`extending` chains, so two composites with no common ancestor are not
subtypes of each other. -/

def userDefinedCrossType := r"
composite Dog { }
composite Cat { }
procedure test() opaque {
  var x: Dog := new Cat
//^^^^^^^^^^^^^^^^^^^^^ error: expected 'Dog', got 'Cat'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "UserDefinedCrossType" userDefinedCrossType 170 processResolution

/-! ## If-then-else branch join

When the two branches have different but subtype-related types, the construct
synthesizes their join (least upper bound) — not the then-branch arbitrarily.
So `if c then new Left else new Right`, with `Left, Right <: Top`, synthesizes
`Top` and an assignment to a `Left`-typed variable is rejected. -/

def ifBranchJoinToCommonAncestor := r"
composite Top { }
composite Left extends Top { }
composite Right extends Top { }
procedure test(c: bool) opaque {
  var x: Top := if c then new Left else new Right;
  var y: Left := if c then new Left else new Right
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: expected 'Left', got 'Top'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "IfBranchJoinToCommonAncestor" ifBranchJoinToCommonAncestor 198 processResolution

end Laurel
