/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
## A leading `$` is not available to a source program

The rule and its rationale are in `validateNoDollarNames`; this file pins the
declaration positions it covers, plus the `$result` carve-out and the fact that a
non-leading `$` stays legal.

These programs go through the *pipeline* (`testLaurelExecution`), which is where the
check runs. `testLaurelResolution` calls `Laurel.resolve` directly and so does not
reach it — a test-harness entry point only, not a production one. The leading-`$`
rejection for file-scope globals inside resolution is pinned in `GlobalVarTests.lean`.
-/

/-! ### Declaration positions -/

#guard_msgs in
#eval testLaurelExecution {} <|
#strata
program Laurel;
type $alias = int
//   ^^^^^^ error: type name '$alias' may not start with '$': that namespace is reserved for compiler-generated names
datatype Ctors { $Ctor() }
//               ^^^^^ error: constructor name '$Ctor' may not start with '$': that namespace is reserved for compiler-generated names
datatype Args { C($arg: int) }
//                ^^^^ error: constructor argument name '$arg' may not start with '$': that namespace is reserved for compiler-generated names
opaque $Handle
//     ^^^^^^^ error: type name '$Handle' may not start with '$': that namespace is reserved for compiler-generated names
opaque Box<$T>
//         ^^ error: type parameter name '$T' may not start with '$': that namespace is reserved for compiler-generated names
var $global: int := 0
//  ^^^^^^^ error: file-scope global name '$global' may not start with '$': that namespace is reserved for compiler-generated names
constrained Pos = $v: int where $v > 0 witness 1
//                ^^ error: value binding name '$v' may not start with '$': that namespace is reserved for compiler-generated names
composite Holder {
  var $field: int
//    ^^^^^^ error: field name '$field' may not start with '$': that namespace is reserved for compiler-generated names
}
procedure $proc() opaque {
//        ^^^^^ error: procedure name '$proc' may not start with '$': that namespace is reserved for compiler-generated names
};
procedure withParam($p: int) opaque {
//                  ^^ error: parameter name '$p' may not start with '$': that namespace is reserved for compiler-generated names
};
procedure withTypeParam<$T>(x: $T) opaque {
//                      ^^ error: type parameter name '$T' may not start with '$': that namespace is reserved for compiler-generated names
};
#end

/-! ### Binders inside a body -/

#guard_msgs in
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure localBinder() opaque {
  var $local: int := 0
//    ^^^^^^ error: variable name '$local' may not start with '$': that namespace is reserved for compiler-generated names
};
procedure quantBinder() opaque {
  assert forall($q: int) => $q == $q
//              ^^ error: bound variable name '$q' may not start with '$': that namespace is reserved for compiler-generated names
};
procedure catchBinder() opaque {
  try {
    assert true
  } catch $e {
//        ^^ error: catch binding name '$e' may not start with '$': that namespace is reserved for compiler-generated names
    assert true
  }
};
#end

/-! ### A coroutine's channel bindings

`yields (x: T)` / `resumes (y: U)` hang off `Procedure.contracts` rather than
`inputs`/`outputs`, but they are declarations all the same — in scope in the body
and in the `guarantees`/`relies` clauses — so they can shadow a generated name
exactly as a parameter can. -/

#guard_msgs in
#eval testLaurelExecution {} <|
#strata
program Laurel;
coroutine emit() yields ($x: int)
//                       ^^ error: yields binding name '$x' may not start with '$': that namespace is reserved for compiler-generated names
{
  $x := 1;
  yield
};
#end

#guard_msgs in
#eval testLaurelExecution {} <|
#strata
program Laurel;
coroutine take() resumes ($y: int)
//                        ^^ error: resumes binding name '$y' may not start with '$': that namespace is reserved for compiler-generated names
{
  yield
};
#end

/-! ### A `throws` binding -/

#guard_msgs in
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Err {}
procedure mayThrow() throws ($e: Err) opaque {
//                           ^^ error: throws binding name '$e' may not start with '$': that namespace is reserved for compiler-generated names
};
#end

/-! ### A block label -/

#guard_msgs in
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure labelled() opaque {
  { assert true } $lbl
//^^^^^^^^^^^^^^^^^^^^ error: block label name '$lbl' may not start with '$': that namespace is reserved for compiler-generated names
};
#end

/-! ### `$result` is legal as a procedure's sole output

The short `procedure f(…): T` form desugars to exactly one output named
`$result` (`resultOutputName`), so that spelling has to stay writable — both
implicitly and in the explicit `returns` form, which produces the identical
program. -/

#guard_msgs in
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure shortForm(x: int): int
  opaque
  ensures $result == x
{
  return x
};
procedure explicitResult(x: int) returns ($result: int)
  opaque
  ensures $result == x
{
  return x
};
procedure callThem() entry opaque {
  assert shortForm(3) == 3;
  assert explicitResult(4) == 4
};
#end

/-! ### …and only as the *sole* output

A second output means the name cannot have come from the return-form desugaring,
so the exemption does not apply. -/

#guard_msgs in
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure twoOutputs(x: int) returns (a: int, $result: int) opaque {
//                                            ^^^^^^^ error: output parameter name '$result' may not start with '$': that namespace is reserved for compiler-generated names
  a := x;
  $result := x
};
#end

/-! ### …and only under that exact spelling

The exemption is keyed on the name as well as on being the sole output, so a sole
output with any other `$` name is still rejected. -/

#guard_msgs in
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure soleOther(x: int) returns ($foo: int) opaque {
//                                   ^^^^ error: output parameter name '$foo' may not start with '$': that namespace is reserved for compiler-generated names
  $foo := x
};
#end

/-! ### An escaped spelling does not open the namespace

DDM's lexer accepts SMT-LIB pipe-delimited identifiers (`|any string|`) and Lean's
`«…»` escape. The check reads the AST, after unescaping, so neither spelling reaches
the reserved namespace. -/

#guard_msgs in
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure |$piped|() opaque {
//        ^^^^^^^^ error: procedure name '$piped' may not start with '$': that namespace is reserved for compiler-generated names
};
#end

#guard_msgs in
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure «$quoted»() opaque {
//        ^^^^^^^^^ error: procedure name '$quoted' may not start with '$': that namespace is reserved for compiler-generated names
};
#end

/-! ### A `$` that is not first is left alone

Only the leading character is reserved, and at every declaration position including
file scope. That is what lets the frontends namespace their generated Laurel as
`py$…` / `java?…` without an exemption. Whether a name of this shape later collides
with a generated one (`Box$a1$int`, `Nat$constraint`) is a separate concern. -/

#guard_msgs in
#eval testLaurelExecution {} <|
#strata
program Laurel;
type my$alias = int
datatype my$dt { My$Ctor(my$arg: int) }
var my$global: int := 0
composite my$Holder {
  var my$field: int
}
procedure my$proc<my$T>(my$p: my$T) opaque {
  var my$local: int := 0;
  assert forall(my$q: int) => my$q == my$q
};
procedure useThem()
  entry
  opaque
  modifies *
{
  var h: my$Holder := new my$Holder;
  h#my$field := 7;
  assert h#my$field == 7;
  var d: my$dt := My$Ctor(3);
  assert my$dt..my$arg(d) == 3
};
#end
