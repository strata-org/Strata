/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # An `if` in statement position does not join its branch types

A statement's value is never consumed, so `Check.statement` resolves an
`if/else` (and a block) in effect position by *checking* it against
`TVoid` (the statement-position marker) instead of synthesizing a type for
it; the arms of such an `if` are statements too. Arms that end in
assignments of different types are therefore fine wherever the `if` is a
statement: in non-last position, as the last statement of a nested block,
right before a loop's back edge, or as the last statement of a procedure
body. Only an `if` whose value is used (`Synth.ifThenElse`) still joins its
branches and rejects inconsistent ones. -/

-- Non-last statement of a procedure body.
#eval testLaurelResolution <|
#strata
program Laurel;
constrained int32 = x: int where -2147483648 <= x && x <= 2147483647 witness 0
procedure nonLastIf(k: int)
  opaque
{
  var go: bool := true;
  var steps: int32 := 0;
  if (k == 1) then { go := false } else { steps := steps + 1 };
  assert steps >= 0
};
#end

-- Last statement of a procedure body (the body is a statement too).
#eval testLaurelResolution <|
#strata
program Laurel;
constrained int32 = x: int where -2147483648 <= x && x <= 2147483647 witness 0
procedure lastIf(k: int)
  opaque
{
  var go: bool := true;
  var steps: int32 := 0;
  if (k == 1) then { go := false } else { steps := steps + 1 }
};
#end

-- Last statement of a non-last block (the shape a lowered `switch` takes):
-- the block is a statement, so its last statement is one as well.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure blockEndingInIf(k: int)
  opaque
{
  var go: bool := true;
  var n: int := 0;
  { var t: int := k; if (t == 1) then { go := false } else { n := n + 1 } };
  assert n >= 0
};
#end

-- Loop body ending in the `if`, followed by the back edge: the shape a front
-- end emits for `while (go) { if (..) {..} else {..} }` as a labelled block.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure ifBeforeBackEdge(k: int)
  opaque
{
  var go: bool := true;
  var steps: int := 0;
  {
    if (!go) then { exit L };
    if (k == 1) then { go := false } else { steps := steps + 1 };
    goto L
  } L
    invariant steps >= 0
};
#end

-- An `if` without `else` in non-last position, arm ending in an assignment.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure ifNoElse(k: int)
  opaque
{
  var steps: int := 0;
  if (k == 1) then { steps := steps + 1 };
  assert steps >= 0
};
#end

-- A body whose last statement is an `if` with value arms is a statement too:
-- the value of a body is never the procedure's result (outputs flow only
-- through `return` and named outputs), so the arms are discarded values, like
-- `5;`, and no type is joined.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure valueArmsInBody(c: bool): int {
  if c then 1 else true
};
procedure valueArmsAsStatement(c: bool)
  opaque
{
  if c then 1 else true;
  assert true
};
#end

-- Control: an `if` whose value is consumed still joins and rejects.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure valueIf(c: bool)
  opaque
{
  assert (if c then 1 else true) == 3
//        ^^^^^^^^^^^^^^^^^^^^^ error: 'if' branches have incompatible types 'int' and 'bool'
};
#end

-- Non-block arms of different types: calls, `++`/`--`, assignments, `return`.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure f() returns (r: int) opaque;
procedure g() returns (b: bool) opaque;
procedure bareArms(c: bool)
  opaque
{
  var x: int := 0;
  var b: bool := false;
  if c then f() else g();
  if c then x++ else x--;
  if c then x := 1 else b := true;
  if c then return else x := 1;
  if c then f() else g()
};
#end

-- A statement-position `if` is not a slot for inference: a generic call whose
-- type argument nothing determines still errors as the last statement of a
-- procedure body, of an arm, or as a bare arm.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure mk<V>() returns (r: V) opaque;
procedure trailingGeneric()
  opaque
{
  assert true;
  mk()
//^^^^ error: cannot infer type argument 'V' of 'mk': annotate the variable or output it is assigned to with a concrete type
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
procedure mk<V>() returns (r: V) opaque;
procedure genericInArm(c: bool)
  opaque
{
  if c then { mk() } else { assert true };
//            ^^^^ error: cannot infer type argument 'V' of 'mk': annotate the variable or output it is assigned to with a concrete type
  if c then mk() else assert true
//          ^^^^ error: cannot infer type argument 'V' of 'mk': annotate the variable or output it is assigned to with a concrete type
};
#end

-- An `if` in a slot with an expected type still pushes it into the arms.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure expectedIntoArms(c: bool)
  opaque
{
  var v: Set<int> := if c then setEmpty() else setEmpty();
  var w: Set<int> := if c then { setEmpty() } else { assert true; setEmpty() }
};
#end
