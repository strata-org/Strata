/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that file-scope global variables (`var g: int`) parse (Gap C) and that
bare references to them resolve to their `$static` field (Gap B). These are
resolution-only tests: they assert that reads/writes of a declared global do
*not* produce "Resolution failed", and that an undeclared bare name still does.
No lowering pass runs yet, so nothing hits `FilterPrelude`.
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.FilterPrelude

open StrataTest.Util
open Strata

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var someGlobal: int := 0
procedure reader() returns (r: int) opaque {
  return someGlobal + 1
};
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var someGlobal: int := 0
procedure writer() opaque {
  someGlobal := 3
};
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var counter: int := 0
var flag: bool := false
procedure touchBoth() opaque {
  counter := 5;
  flag := true
};
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
procedure reader() returns (r: int) opaque {
  return notAGlobal + 1
//       ^^^^^^^^^^ error: Resolution failed: 'notAGlobal' is not defined
};
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var g: int := 0
procedure shadows() returns (r: int) opaque {
  var g: int := 7;
  return g
};
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var g: int := 0
var g: int := 0
//  ^ error: Duplicate definition 'g' is already defined in this scope
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var g: int := 0
procedure keep()
  opaque
  ensures g == old(g)
//                 ^ error: file-scope globals are not yet supported inside `old(...)`
{
  g := g
};
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var g: int := 0
procedure readG() returns (r: int)
  opaque
  ensures r == g;
procedure keep()
  opaque
  ensures g == old(readG())
//                 ^^^^^^^ error: file-scope globals are not yet supported inside `old(...)`
{
  g := g
};
#end

#guard_msgs in
#eval do
  let prelude ← translateLaurel <|
    #strata
    program Laurel;
    composite Needed { var value: int }
    composite Unused { var value: int }
    #end
  let user ← translateLaurel <|
    #strata
    program Laurel;
    var global: Needed := new Needed
    #end
  match Strata.Laurel.filterPrelude prelude user with
  | .error message => throw (IO.userError message)
  | .ok filtered =>
      let names := filtered.types.map fun (type : Strata.Laurel.TypeDefinition) => type.name.text
      unless names == ["Needed"] do
        throw (IO.userError s!"unexpected retained types: {names}")

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var initialized: int := 5
procedure reader() returns (r: int) opaque {
  return initialized
};
#end

/-- error: Translation errors: file-scope global 'uninitialized' must declare an initializer: 'var uninitialized: <type> := <value>' -/
#guard_msgs in
#eval do
  let _ ← translateLaurel <|
    #strata
    program Laurel;
    var uninitialized: int
    #end
  pure ()

/-- info: resolution diagnostic: file-scope global 'bare' must declare an initializer: 'var bare: <type> := <value>' -/
#guard_msgs in
#eval do
  let program ← translateLaurel <|
    #strata
    program Laurel;
    procedure untouched() opaque {
    };
    #end
  let bare : Strata.Laurel.Field :=
    { name := Strata.Laurel.mkId "bare", isMutable := true,
      type := ⟨.TInt, default⟩ }
  let withBare := { program with staticFields := [bare] }
  for diagnostic in (Strata.Laurel.resolve (withBuiltins withBare)).errors do
    IO.println s!"resolution diagnostic: {diagnostic.message}"

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var typed: int := true
//                ^^^^ error: expected 'int', got 'bool'
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var first: int := 0
var second: int := first + 1
//                 ^^^^^ error: the initializer of file-scope global 'second' cannot depend on file-scope globals
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var first: int := 0
procedure readFirst() returns (r: int) {
  return first
};
var second: int := readFirst()
//                 ^^^^^^^^^^^ error: the initializer of file-scope global 'second' cannot depend on file-scope globals
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var effectful: int := { var tmp: int := 1; tmp }
//                      ^^^^^^^^^^^^^^^^^ error: the initializer of file-scope global 'effectful' must be effect-free
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
composite HeapCell {
  var value: int
}
procedure readCell(c: HeapCell) returns (r: int) {
  return c#value
};
var fromHeap: int := readCell(new HeapCell)
//                   ^^^^^^^^^^^^^^^^^^^^^^ error: the initializer of file-scope global 'fromHeap' must be effect-free
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var g: int := 0
procedure runMe()
  requires g == 0
//         ^ error: the contract of entry procedure 'runMe' cannot use file-scope globals: an entry procedure initializes its globals as locals inside its body, which contracts cannot see
  entry
  opaque
{
  g := 1
};
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var g: int := 0
procedure runMe()
  entry
  opaque
  ensures g == 1
//        ^ error: the contract of entry procedure 'runMe' cannot use file-scope globals: an entry procedure initializes its globals as locals inside its body, which contracts cannot see
{
  g := 1
};
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var g: int := 0
procedure runMe()
  entry
  opaque
{
  g := 1
};
procedure caller() opaque {
  runMe()
//^^^^^^^ error: entry procedure 'runMe' cannot be called here: it uses file-scope globals, which it initializes as locals rather than accepting as the hidden parameters this call would pass
};
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var g: int := 0
procedure runMe()
  entry
  opaque
{
  assert true
};
procedure caller() opaque {
  g := 1;
  runMe()
};
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
var count: nat := 0
procedure runMe()
//        ^^^^^ error: entry procedure 'runMe' cannot use constrained-typed global 'count': the global's type constraint is enforced through hidden-parameter contracts, which entry procedures do not receive
  entry
  opaque
{
  count := 1
};
#end


#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var $result: int := 0
//  ^^^^^^^ error: file-scope global name '$result' is reserved for compiler-generated variables
var $tmp0: int := 0
//  ^^^^^ error: file-scope global name '$tmp0' is reserved for compiler-generated variables
var $cp_0: int := 0
//  ^^^^^ error: file-scope global name '$cp_0' is reserved for compiler-generated variables
var $heap: int := 0
//  ^^^^^ error: file-scope global name '$heap' is reserved for compiler-generated variables
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
constrained captured = $static.g: int where $static.g >= 0 witness 0
//                     ^^^^^^^^^ error: name '$static.g' is reserved for compiler-generated variables
var g: nat := 0
procedure setG() { g := 1 };
procedure reader($static.g: int) returns (r: nat) {
//               ^^^^^^^^^ error: name '$static.g' is reserved for compiler-generated variables
  return g
};
procedure conditionalWriter(flag: bool) returns ($static.g: int) opaque {
//                                               ^^^^^^^^^ error: name '$static.g' is reserved for compiler-generated variables
  if flag then setG();
  $static.g := 0
};
#end


#guard_msgs (drop info) in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure pair() returns (x: int, y: int) opaque {
  g := 1;
  x := 2;
  y := 3
};
procedure caller() opaque {
  pair()
};
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var g: int := 0
procedure bump() returns (r: int) opaque {
  g := g + 1;
  return g
};
procedure caller()
  requires bump() > 0
//         ^^^^ error: calls to global-writing procedure 'bump' are not yet supported in contracts, loop conditions or annotations, quantifiers, or old expressions
  opaque
{
};
#end


#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var g: int := 0
procedure bump() returns (r: int) opaque {
  g := g + 1;
  return g
};
procedure caller() opaque {
  while (false)
    invariant bump() > 0 {
//            ^^^^ error: calls to global-writing procedure 'bump' are not yet supported in contracts, loop conditions or annotations, quantifiers, or old expressions
  }
};
#end


#guard_msgs (drop info) in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
composite GlobalPair {
  procedure pair(self: GlobalPair) returns (x: int, y: int) opaque {
    g := 1;
    x := 2;
    y := 3
  };
}
procedure caller(c: GlobalPair) opaque {
  c#pair()
};
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure writeBoth(x: int, v: int) returns (x: int, r: int) opaque {
  g := v;
  x := x + v;
  r := x
};
procedure caller() opaque {
  var x: int := 1;
  var r: int;
  assign x, r := writeBoth(x, 5)
//               ^^^^^^^^^ error: calls to global-writing procedure 'writeBoth' with explicit inout outputs are not yet supported
};
#end


#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var floor: int := 0
constrained AboveFloor = x: int where x >= floor witness 0
//                                         ^^^^^ error: file-scope globals are not yet supported in constrained type predicates or witnesses
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var g: int := 0
procedure setG(v: int) returns (r: int) opaque {
  g := v;
  return v
};
procedure readMutate(x: int, y: int) returns (x: int, r: int) opaque {
  x := x + g + y;
  r := x
};
procedure caller() opaque {
  var x: int := 1;
  var r: int;
  assign x, r := readMutate(x, setG(5))
//               ^^^^^^^^^^ error: mutating arguments to global-dependent procedure 'readMutate' with explicit inout outputs are not yet supported
};
#end


#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var g: int := 0
procedure readMutate(x: int, y: int) returns (x: int, r: int) opaque {
  x := x + g + y;
  r := x
};
procedure caller() opaque {
  var r: int;
  assign g, r := readMutate(g := 5, 0)
//               ^^^^^^^^^^ error: mutating arguments to global-dependent procedure 'readMutate' with explicit inout outputs are not yet supported
};
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: bool := false
constrained MutatesGlobal = x: bool where (g := true) witness false
//                                         ^^^^^^^^^ error: file-scope globals are not yet supported in constrained type predicates or witnesses
#end


#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure pair() returns (x: int, y: int) opaque {
  g := 1;
  x := 2;
  y := 3
};
procedure caller() opaque {
  var x: int;
  var y: int;
  assign x, y := pair()
//               ^^^^ error: calls to global-writing procedure 'pair' with more than one ordinary output are not yet supported
};
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure bumpInout(x: int) returns (x: int) opaque {
  x := x + 1
};
procedure caller() opaque {
  assign g := bumpInout(g)
//            ^^^^^^^^^ error: passing file-scope globals to explicit inout parameters of 'bumpInout' is not yet supported
};
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure bump() returns (r: int) opaque {
  g := g + 1;
  return g
};
procedure caller() opaque {
  assert forall(x: int) => bump() > x
//                         ^^^^ error: calls to global-writing procedure 'bump' are not yet supported in contracts, loop conditions or annotations, quantifiers, or old expressions
};
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure bump() returns (r: int) opaque {
  g := g + 1;
  return g
};
procedure caller() opaque
  ensures g == old(bump())
//                 ^^^^^^ error: file-scope globals are not yet supported inside `old(...)`
{
  g := g
};
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure bump() returns (r: int) opaque {
  g := g + 1;
  return g
};
procedure caller() opaque {
  while (false)
    invariant forall(x: int) => old(bump()) > x {
//                                  ^^^^^^ error: file-scope globals are not yet supported inside `old(...)`
  }
};
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: bool := false
procedure caller() opaque {
  assert forall(x: bool) => (g := x)
//                           ^^^^^^ error: global mutations are not yet supported in contracts, loop conditions or annotations, quantifiers, or old expressions
};
#end


#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure bumpInout(x: int) returns (x: int) opaque {
  x := x + 1
};
procedure caller() opaque {
  bumpInout({g})
//^^^^^^^^^ error: passing file-scope globals to explicit inout parameters of 'bumpInout' is not yet supported
};
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var $result: int := 0
//  ^^^^^^^ error: file-scope global name '$result' is reserved for compiler-generated variables
composite InitialErrorInstance {
  procedure untouched(self: InitialErrorInstance) opaque {
  };
}
#end


#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure readG() returns (r: int) {
  return g
};
constrained GlobalWitness = x: int where x >= 0 witness readG()
//                                                      ^^^^^^^ error: file-scope globals are not yet supported in constrained type predicates or witnesses
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure caller() opaque {
  assert forall(x: int) => g++ > x
//                         ^^^ error: global mutations are not yet supported in contracts, loop conditions or annotations, quantifiers, or old expressions
};
#end


#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure readMutate(x: int) returns (x: int) opaque {
  x := x + g
};
procedure caller() opaque {
  var x: int;
  assign x := readMutate(1)
//            ^^^^^^^^^^ error: explicit inout arguments to 'readMutate' must be variable references
};
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure pair(a: int) returns (x: int, y: int) opaque {
  x := g + a;
  y := a
};
procedure caller() opaque {
  var t: int := 0;
  var x: int;
  var y: int;
  assign x, y := {
    var t: int := 1;
    pair(t)
//  ^^^^ error: multi-output calls to global-dependent procedure 'pair' that require block-valued lowering are not yet supported
  }
};
#end


#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var g: int := 0
procedure globalPair(a: int) returns (x: int, y: int) opaque {
  x := g + a;
  y := a
};
procedure plainPair(a: int) returns (x: int, y: int) opaque {
  x := a;
  y := a + 1
};
procedure caller() opaque {
  var x: int;
  var y: int;
  assign x, y := {
    {
      globalPair(0);
      plainPair(1)
    }
  }
};
#end


#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure setG(v: int) returns (r: int) opaque {
  g := v;
  return v
};
procedure pair(a: int) returns (x: int, y: int) opaque {
  x := g + a;
  y := a
};
procedure caller() opaque {
  var x: int;
  var y: int;
  assign x, y := pair(setG(5))
//               ^^^^ error: multi-output calls to global-dependent procedure 'pair' that require block-valued lowering are not yet supported
};
#end


#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure setG(v: int)
  opaque
  ensures g == v
//        ^^^^^^ error: global references in postconditions of procedure 'setG' without an implementation are not yet supported
;
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure P(x: int): bool;
procedure trigger()
//        ^^^^^^^ error: global-writing 'invokeOn' procedure 'trigger' is not yet supported because its generated axiom cannot bind the hidden global output state
  invokeOn P(g)
  opaque
{
  g := g + 1
};
#end


#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure setG(v: int) returns (r: int) opaque {
  g := v;
  return v
};
procedure pair(a: int) returns (x: int, y: int) opaque {
  x := g + a;
  y := a
};
procedure caller(c: bool) opaque {
  var x: int;
  var y: int;
  assign x, y := if c then pair(setG(5)) else pair(0)
//                         ^^^^ error: multi-output calls to global-dependent procedure 'pair' that require block-valued lowering are not yet supported
};
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure setG(v: int) returns (r: int)
  opaque
  ensures r == r && g == v
//        ^^^^^^^^^^^^^^^^ error: global references in postconditions of procedure 'setG' without an implementation are not yet supported
;
#end


#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure tick() returns (r: bool) opaque {
  g := g + 1;
  return g < 3
};
procedure caller() opaque {
  while (tick()) {
//       ^^^^ error: calls to global-writing procedure 'tick' are not yet supported in contracts, loop conditions or annotations, quantifiers, or old expressions
  }
};
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure constrainGlobal() returns (r: int)
  opaque
  ensures r == r + g
//        ^^^^^^^^^^ error: global references in postconditions of procedure 'constrainGlobal' without an implementation are not yet supported
;
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
constrained Nat = x: int where x >= 0 witness 0
var Nat$constraint: int := 0
//  ^^^^^^^^^^^^^^ error: file-scope global name 'Nat$constraint' is reserved for compiler-generated variables
#end


#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure pair(a: int) returns (x: int, y: int) opaque {
  x := g + a;
  y := a
};
procedure caller() opaque {
  g := g;
  var x: int;
  var y: int;
  assign x, y := old(pair(1))
//                   ^^^^^^^ error: file-scope globals are not yet supported inside `old(...)`
};
#end


#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure pair() returns (x: int, y: int) opaque {
  x := g;
  y := g + 1
};
procedure caller() opaque {
  var a: int;
  var b: int;
  var x: int;
  var y: int;
  assign x, y := {
    assign a, b := pair()
//                 ^^^^ error: multi-output calls to global-dependent procedure 'pair' that require block-valued lowering are not yet supported
  }
};
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure bump() returns (r: bool) opaque {
  g := g + 1;
  return true
};
procedure assertCaller() opaque {
  assert bump()
//       ^^^^ error: calls to global-writing procedure 'bump' are not yet supported in contracts, loop conditions or annotations, quantifiers, or old expressions
};
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure bump() returns (r: bool) opaque {
  g := g + 1;
  return true
};
procedure assumeCaller() opaque {
  assume bump()
//       ^^^^ error: calls to global-writing procedure 'bump' are not yet supported in contracts, loop conditions or annotations, quantifiers, or old expressions
};
#end

#guard_msgs in
#eval testLaurel <|
#strata
program Laurel;
var g: int := 0
procedure bump() returns (r: bool) opaque {
  g := g + 1;
  return true
};
procedure trigger()
  invokeOn bump()
//         ^^^^ error: calls to global-writing procedure 'bump' are not yet supported in contracts, loop conditions or annotations, quantifiers, or old expressions
  opaque
{
};
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var g: int := 0
procedure runMe()
  entry
  opaque
{
  g += 1
};
procedure caller() opaque {
  runMe()
//^^^^^^^ error: entry procedure 'runMe' cannot be called here: it uses file-scope globals, which it initializes as locals rather than accepting as the hidden parameters this call would pass
};
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
composite $static {
//        ^^^^^^^ error: type name '$static' is reserved for file-scope global variables
  var g: bool
}
var g: int := 0
#end

#guard_msgs in
#eval testLaurelResolution <|
#strata
program Laurel;
var g: int := 0
procedure readMutate(x: int) returns (x: int)
  opaque
  ensures x == old(x) + g
{
  x := x + g
};
procedure caller() opaque {
  g := 3;
  var x: int := 1;
  readMutate(x)
//^^^^^^^^^^ error: bare calls to global-dependent procedure 'readMutate' with explicit inout outputs are not yet supported
};
#end
