/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
Tests that the resolution pass detects type checking errors — e.g. using an int
where a bool is expected, or passing the wrong type to a procedure.
-/

meta import all StrataTest.Util.TestDiagnostics
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
meta import Strata.Languages.Laurel.Grammar.LaurelGrammar
meta import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
meta import Strata.Languages.Laurel.Resolution

meta section

open StrataTest.Util
open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-- Run only parsing + resolution and return diagnostics (no SMT verification). -/
private def processResolution (input : Lean.Parser.InputContext) : IO (Array Diagnostic) := do
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
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
//              ^^^^ error: expected 'int', got 'bool'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "AssignTypeMismatch" assignTypeMismatch 104 processResolution

/-! ## Function return type checks -/

def returnTypeMismatch := r"
function foo(): int {
  true
//^^^^ error: expected 'int', got 'bool'
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
//^^^^^^ error: cannot compare 'int' with 'string' using '=='
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "EqualityTypeMismatch" equalityTypeMismatch 134 processResolution

/-! ## Multi-output procedures -/

def multiOutputInExpr := r"
procedure multi(x: int) returns (a: int, b: int) opaque;
procedure test() opaque {
  assert multi(1) == 1
//       ^^^^^^^^^^^^^ error: cannot compare '(int, int)' with 'int' using '=='
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "MultiOutputInExpr" multiOutputInExpr 146 processResolution

def assignTargetCountMismatch := r"
procedure multi() returns (a: int, b: int) opaque;
procedure test() opaque {
  var x: int := multi()
//              ^^^^^^^ error: expected 'int', got '(int, int)'
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
//              ^^^^^^^ error: expected 'Dog', got 'Cat'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "UserDefinedCrossType" userDefinedCrossType 170 processResolution

/-! ## Field type is read from the field, not a shadowing local

A field reference (`c#flag`) carries the field's `uniqueId`, but its bare
name can collide with a same-named local. `getVarType` must read the field's
declared type (`bool`) — not the shadowing local's type (`int`) — so the
assignment of an `int` to a `bool` field is still rejected. (Regression guard
for the scope-first lookup that previously returned the local's type and
silently dropped the mismatch.) -/

def fieldShadowedByLocal := r"
composite C {
  var flag: bool
}
procedure test() opaque {
  var c: C := new C;
  var flag: int := 0;
  c#flag := flag
//          ^^^^ error: expected 'bool', got 'int'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "FieldShadowedByLocal" fieldShadowedByLocal 184 processResolution

/-! ## `if`/`block` in synth-only operand position

An `if`/`then`/`else` (or non-empty block) used where operands are
synthesized — e.g. as an operand of `==`/`<`/`++` — now has a synth rule
(`Synth.ifThenElse` / `Synth.block`). Previously it hit the synth wildcard
and emitted a spurious "type cannot be synthesized" error. With both
branches consistent, the `if` synthesizes the branch type and resolves
cleanly (no diagnostics). -/

def ifInSynthPositionOk := r"
function foo(c: bool): bool {
  (if c then 1 else 2) == 3
};
"

#guard_msgs (drop info) in
#eval testInputWithOffset "IfInSynthPositionOk" ifInSynthPositionOk 198 processResolution

def blockInSynthPositionOk := r"
function foo(): bool {
  { 1 } == 1
};
"

#guard_msgs (drop info) in
#eval testInputWithOffset "BlockInSynthPositionOk" blockInSynthPositionOk 208 processResolution

/-! ## `if` with incompatible branch types (synth position)

When an `if` is synthesized and its two branches have mutually
inconsistent types, `Synth.ifThenElse` reports the mismatch at the `if`
and synthesizes `Unknown` to suppress cascading errors. -/

def ifBranchesIncompatible := r"
function foo(c: bool): bool {
  (if c then 1 else true) == 3
// ^^^^^^^^^^^^^^^^^^^^^ error: 'if' branches have incompatible types 'int' and 'bool'
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "IfBranchesIncompatible" ifBranchesIncompatible 218 processResolution

/-! ## Void procedure call in value position

A call to a `void` procedure (no `returns` clause) used where a value is
expected now synthesizes `TVoid` rather than the internal-only empty
`MultiValuedExpr []`. The diagnostic therefore reports the type as `'void'`
instead of the placeholder `'()'` that an empty tuple rendered as. (Regression
guard for `getCallInfo` mapping an empty output list to `TVoid`.) -/

def voidCallInValuePosition := r"
procedure act() opaque;
procedure test() opaque {
  assert act() == 1
//       ^^^^^^^^^^ error: cannot compare 'void' with 'int' using '=='
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "VoidCallInValuePosition" voidCallInValuePosition 234 processResolution

/-! ## Bitvectors are numeric

Bitvector operands (`bv n`) participate in arithmetic and comparison
operators just like the other numeric primitives. `isNumeric` therefore
accepts `TBv`, so a comparison of two bitvector parameters resolves
cleanly with no diagnostics. (Regression guard for `isNumeric` previously
rejecting `TBv` and emitting a spurious "expected a numeric type" error.) -/

def bitvectorComparisonOk := r"
function cmp(x: bv 32, y: bv 32): bool {
  x < y
};
"

#guard_msgs (drop info) in
#eval testInputWithOffset "BitvectorComparisonOk" bitvectorComparisonOk 250 processResolution

/-! ## An unresolved declared type collapses to `Unknown` (no cascade)

A variable declared with an undefined type name reports only the single
"is not defined" name-resolution error. `resolveHighType` collapses the
dangling `UserDefined` to `Unknown` once its name fails to resolve, so the
variable's later uses are not type-checked against a phantom type and no
cascade of follow-on mismatches (`0` vs the bad type, `x` vs `int`) is emitted.
(Regression guard: before the collapse-to-`Unknown` fix this program produced
three diagnostics — the name-resolution error plus the `0`-vs-`UndefinedType`
initializer mismatch and the `x`-vs-`int` use mismatch; it must now produce
exactly one.) -/

def unresolvedDeclaredTypeNoCascade := r"
procedure useUndef() opaque {
  var x: UndefinedType := 0;
//       ^^^^^^^^^^^^^ error: 'UndefinedType' is not defined
  var y: int := x + 2
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "UnresolvedDeclaredTypeNoCascade" unresolvedDeclaredTypeNoCascade 308 processResolution

end Laurel
