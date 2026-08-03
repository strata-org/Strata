/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the expression lifter (`liftExpressionAssignments`) correctly:
- handles statement constructs (heap-updating assignments) in non-last
  positions of block expressions, and
- hoists imperative procedure calls out of assert/assume conditions, while
  leaving assignments untouched (so they are rejected downstream),
by comparing the lifted Laurel against expected output.

The lifter takes a list of "root" names (procedures known to be impure /
multi-output) that drive which calls get hoisted; both `[]` and a populated
list are exercised below.
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.LaurelToCoreSchemaPass
import Strata.Languages.Laurel.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

private def parseLaurelAndLift (roots : List String) (program : StrataDDM.Program) : IO Program := do
  let laurelProgram ← translateLaurel program
  let result := resolve laurelProgram
  match liftExpressionAssignments result.program result.model roots with
  | .ok p => pure p
  | .error e => throw (IO.userError s!"Lift error: {e}")

private def printLifted (roots : List String) (program : StrataDDM.Program) : IO Unit := do
  let lifted ← parseLaurelAndLift roots program
  for proc in lifted.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Heap-updating assignments in non-last positions of a block expression -/

/--
info: procedure assertInBlockExpr()
  opaque
{
  var x: int := 0;
  assert x == 0;
  var $x_0: int := x;
  x := 1;
  var y: int := {
    x
  };
  assert y == 1
};
-/
#guard_msgs in
#eval! printLifted []
#strata
program Laurel;
procedure assertInBlockExpr()
opaque {
  var x: int := 0;
  var y: int := { assert x == 0; x := 1; x };
  assert y == 1
};
#end

/-! ## Imperative calls in assert are lifted -/

/--
info: procedure impure(): int
{
  var x: int := 0;
  x := x + 1;
  x
};
procedure test()
{
  var $cndtn_0: int := impure();
  assert $cndtn_0 == 1
};
-/
#guard_msgs in
#eval! printLifted ["impure", "multi_out"]
#strata
program Laurel;
procedure impure(): int {
  var x: int := 0;
  x := x + 1;
  x
};
procedure test() {
  assert impure() == 1
};
#end

/-! ## Assignments in assert are NOT lifted (rejected downstream) -/

/--
info: procedure test()
{
  var x: int := 0;
  var $x_0: int := x;
  x := 2;
  assert x == 2
};
-/
#guard_msgs in
#eval! printLifted ["impure", "multi_out"]
#strata
program Laurel;
procedure test() {
  var x: int := 0;
  assert (x := 2) == 2
};
#end

/-! ## Imperative calls in assume are lifted -/

/--
info: procedure impure(): int
{
  var x: int := 0;
  x := x + 1;
  x
};
procedure test()
{
  var $cndtn_0: int := impure();
  assume $cndtn_0 == 1
};
-/
#guard_msgs in
#eval! printLifted ["impure", "multi_out"]
#strata
program Laurel;
procedure impure(): int {
  var x: int := 0;
  x := x + 1;
  x
};
procedure test() {
  assume impure() == 1
};
#end

/-! ## Multi-output calls in expression position produce a single (broken) target.
    This is intentional — multi-output calls should not appear in expression position.
    Resolution should emit a diagnostic for this case. -/

/--
info: procedure multi_out(x: int)
  returns (r: int, extra: int)
{
  r := x + 1;
  extra := x + 2
};
procedure test()
{
  var $cndtn_0: BUG_MultiValuedExpr := multi_out(5);
  assert $cndtn_0 == 6
};
-/
#guard_msgs in
#eval! printLifted ["impure", "multi_out"]
#strata
program Laurel;
procedure multi_out(x: int) returns (r: int, extra: int) {
  r := x + 1;
  extra := x + 2
};
procedure test() {
  assert multi_out(5) == 6
};
#end

/-! ## Statement calls preserve earlier values across later assignments -/

/--
info: procedure writeHeap(c: int, value: int, heap: int)
  returns (heap: int, written: int)
  opaque;
procedure consume(c: int, before: int, written: int, heap: int)
  opaque;
procedure reproduce()
  opaque
{
  var heap: int := 2;
  var $heap_0: int := heap;
  assign heap, var written: int := writeHeap(0, 5, heap);
  consume(0, $heap_0, {
    written
  }, heap);
  consume(0, heap, 0, heap)
};
-/
#guard_msgs in
#eval printLifted ["writeHeap", "consume"]
#strata
program Laurel;
procedure writeHeap(c: int, value: int, heap: int)
  returns (heap: int, written: int)
  opaque;
procedure consume(c: int, before: int, written: int, heap: int)
  opaque;
procedure reproduce()
  opaque
{
  var heap: int := 2;
  consume(0, heap, {
    assign heap, var written: int := writeHeap(0, 5, heap);
    written
  }, heap);
  consume(0, heap, 0, heap)
};
#end

/-! ## Snapshots taken in a condition do not escape the statement

An assigning condition builds a before-snapshot the same way a call argument
does. That snapshot is only valid for occurrences *earlier in the same
statement*, so neither the statement after the `if`/`while` nor the guarded body
may read it — they must see the live variable. -/

/--
info: procedure consume(c: int, v: int)
  opaque;
procedure ifCondLeaksToNextStmt()
  opaque
{
  var x: int := 1;
  var $x_0: int := x;
  x := 5;
  if {
    x
  } > 0
    then {
      {
        
      }
    };
  consume(0, x)
};
-/
#guard_msgs in
#eval printLifted ["consume"]
#strata
program Laurel;
procedure consume(c: int, v: int)
  opaque;
procedure ifCondLeaksToNextStmt()
  opaque
{
  var x: int := 1;
  if { x := 5; x } > 0 then { };
  consume(0, x)
};
#end

/--
info: procedure consume(c: int, v: int)
  opaque;
procedure whileCondLeaksToNextStmt()
  opaque
{
  var x: int := 1;
  var $x_0: int := x;
  x := 5;
  while({
    x
  } > 0) {
    {
      
    }
  };
  consume(0, x)
};
-/
#guard_msgs in
#eval printLifted ["consume"]
#strata
program Laurel;
procedure consume(c: int, v: int)
  opaque;
procedure whileCondLeaksToNextStmt()
  opaque
{
  var x: int := 1;
  while ({ x := 5; x } > 0) { };
  consume(0, x)
};
#end

/--
info: procedure consume(c: int, v: int)
  opaque;
procedure ifCondLeaksIntoBranch()
  opaque
{
  var x: int := 1;
  var $x_0: int := x;
  x := 5;
  if {
    x
  } > 0
    then {
      {
        consume(0, x)
      }
    };
  consume(1, x)
};
-/
#guard_msgs in
#eval printLifted ["consume"]
#strata
program Laurel;
procedure consume(c: int, v: int)
  opaque;
procedure ifCondLeaksIntoBranch()
  opaque
{
  var x: int := 1;
  if { x := 5; x } > 0 then { consume(0, x) };
  consume(1, x)
};
#end

/--
info: procedure consume(c: int, v: int)
  opaque;
procedure whileCondLeaksIntoBody()
  opaque
{
  var x: int := 1;
  var $x_0: int := x;
  x := 5;
  while({
    x
  } > 0) {
    {
      consume(0, x)
    }
  };
  consume(1, x)
};
-/
#guard_msgs in
#eval printLifted ["consume"]
#strata
program Laurel;
procedure consume(c: int, v: int)
  opaque;
procedure whileCondLeaksIntoBody()
  opaque
{
  var x: int := 1;
  while ({ x := 5; x } > 0) { consume(0, x) };
  consume(1, x)
};
#end

/-! ## Regions evaluated after the condition also read live variables

A loop invariant is evaluated at the loop head, and an `if`-expression's branches
run after its condition, so neither may inherit a snapshot the condition took.
(The `while` goldens here and above also show a condition's assignment being
hoisted out of the loop, so it runs once rather than per iteration. That is a
separate pre-existing defect in the loop lowering; these programs are chosen so
it does not change their meaning.) -/

/--
info: procedure consume(c: int, v: int)
  opaque;
procedure invariantReadsLiveVar()
  opaque
{
  var x: int := 1;
  var $x_0: int := x;
  x := 5;
  while({
    x
  } > 0)
    invariant x >= 0 {
    {
      
    }
  };
  consume(0, x)
};
-/
#guard_msgs in
#eval printLifted ["consume"]
#strata
program Laurel;
procedure consume(c: int, v: int)
  opaque;
procedure invariantReadsLiveVar()
  opaque
{
  var x: int := 1;
  while ({ x := 5; x } > 0) invariant x >= 0 { };
  consume(0, x)
};
#end

/--
info: procedure consume(c: int, v: int)
  opaque;
procedure exprIfBranchesReadLiveVar()
  opaque
{
  var x: int := 1;
  var $x_0: int := x;
  x := 5;
  var z: int := if {
    x
  } > 0
    then x
    else x + 1;
  consume(0, z)
};
-/
#guard_msgs in
#eval printLifted ["consume"]
#strata
program Laurel;
procedure consume(c: int, v: int)
  opaque;
procedure exprIfBranchesReadLiveVar()
  opaque
{
  var x: int := 1;
  var z: int := (if { x := 5; x } > 0 then x else x + 1);
  consume(0, z)
};
#end

/-! ## An occurrence evaluated before the condition still gets the snapshot

The counterpart to the tests above: visiting the branches before the condition
must not stop the condition's substitution from reaching earlier arguments. -/

/--
info: procedure consume(c: int, v: int, w: int)
  opaque;
procedure earlierArgSeesSnapshot()
  opaque
{
  var x: int := 1;
  var $x_0: int := x;
  x := 5;
  consume(0, $x_0, if {
    x
  } > 0
    then 7
    else 8);
  consume(1, x, 0)
};
-/
#guard_msgs in
#eval printLifted ["consume"]
#strata
program Laurel;
procedure consume(c: int, v: int, w: int)
  opaque;
procedure earlierArgSeesSnapshot()
  opaque
{
  var x: int := 1;
  consume(0, x, (if { x := 5; x } > 0 then 7 else 8));
  consume(1, x, 0)
};
#end

end Laurel
