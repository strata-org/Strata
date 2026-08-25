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

/-- Lift a program that has deliberately **not** been resolved, so its
    declarations carry no `uniqueId`, and print the resulting error instead of
    throwing. The model still comes from `resolve` — only the program passed to
    the lifter is the unresolved one.

    This is the only way to reach the `Var (.Declare ..) has no uniqueId` throw:
    the lifter's precondition is that Resolution has run, so no surface program
    can trigger it. The throw exists to make a violated precondition loud rather
    than silently returning the expression unchanged, so the error path needs a
    test even though well-formed input can never take it. -/
private def printLiftErrorUnresolved (roots : List String) (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let model := (resolve laurelProgram).model
  match liftExpressionAssignments laurelProgram model roots with
  | .ok _ => IO.println "unexpectedly succeeded"
  | .error e => IO.println e

/-- As `printLiftErrorUnresolved`, but through `liftImperativeExpressionsPass`,
    to pin how the pass surfaces the error: an unchanged program plus a single
    `StrataBug` diagnostic. -/
private def printLiftPassDiagnosticsUnresolved (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let model := (resolve laurelProgram).model
  let uc : UnorderedCoreWithLaurelTypes :=
    { functions := [], coreProcedures := laurelProgram.staticProcedures
      datatypes := [], opaqueTypes := [], constants := [] }
  let (result, diags, _) := liftImperativeExpressionsPass.run {} uc model
  IO.println s!"procedures unchanged: {result.coreProcedures.length == uc.coreProcedures.length}"
  for d in diags do
    IO.println s!"{repr d.kind}: {d.message}"

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
#eval printLifted []
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
#eval printLifted ["impure", "multi_out"]
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
#eval printLifted ["impure", "multi_out"]
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
#eval printLifted ["impure", "multi_out"]
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
#eval printLifted ["impure", "multi_out"]
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

/-! ## Var declarations in blocks are lifted when their variable is read

    When a block contains a var declaration followed by asserts/assumes that
    reference the declared variable, the var declaration is lifted to statement
    level alongside the asserts/assumes. This keeps it in scope for the lifted
    statements. This is needed for quantifier proof procedures where the proof
    block introduces a havoced variable. -/

/--
info: procedure test()
{
  var x: int;
  assume x * x >= 0;
  assert {
    x * x >= 0
  }
};
-/
#guard_msgs in
#eval printLifted []
#strata
program Laurel;
procedure test() {
  assert { var x: int; assume x * x >= 0; x * x >= 0 }
};
#end

/-! ## Var declarations must not be spuriously lifted across procedures

    `liftedVarRefs` must not leak between procedures. If procedure A reads `x`,
    a `var x` inside a block expression in procedure B must NOT be lifted —
    it is a distinct variable that was never read by a lifted statement in B. -/

/--
info: procedure readsX()
{
  var x: int := 5;
  assert x == 5
};
procedure hasXInBlock()
{
  var y: int := {
    var x: int;
    x
  };
  assert y == 0
};
-/
#guard_msgs in
#eval printLifted []
#strata
program Laurel;
procedure readsX() {
  var x: int := 5;
  assert x == 5
};
procedure hasXInBlock() {
  var y: int := { var x: int; x };
  assert y == 0
};
#end

/-! ## A `Var (.Declare ..)` with no `uniqueId` is a loud error

    Hoisting a declaration requires identifying it, and the lifter identifies
    declarations by `uniqueId`. A `Declare` without one means Resolution did not
    run (or a pass produced a node it never saw), which the lifter reports rather
    than silently leaving the declaration where it is — a silent pass-through
    would strand the declaration below its uses and surface much later as a
    confusing "not defined" resolution failure.

    Reached here by handing the lifter an unresolved program, since a resolved
    one always has ids. -/

/--
info: Var (.Declare x) has no uniqueId
-/
#guard_msgs in
#eval printLiftErrorUnresolved []
#strata
program Laurel;
procedure test() {
  assert { var x: int; assume x * x >= 0; x * x >= 0 }
};
#end

/-! ### The pass reports it as a `StrataBug`, leaving the program untouched -/

/--
info: procedures unchanged: true
{ category := "error", impact := Strata.Pipeline.MessageImpact.internalError }: Internal error in LiftImperativeExpressions: Var (.Declare x) has no uniqueId
-/
#guard_msgs in
#eval printLiftPassDiagnosticsUnresolved
#strata
program Laurel;
procedure test() {
  assert { var x: int; assume x * x >= 0; x * x >= 0 }
};
#end

/-! ## Nothing is hoisted out of a quantifier

    A quantifier body is a spec position under a binder: hoisting out of it would
    both strand references to the bound variable outside its scope and collapse a
    per-instantiation evaluation into a single one before the quantifier. So the
    body is left untransformed — the declaration below stays inside the `forall`,
    where `x` is in scope, and `InlineLocalVariables` folds it away afterwards. -/

/--
info: procedure binderLocalNoProof()
  opaque
{
  assert forall(x: int) => {
    var t: int := x * x;
    t >= 0
  }
};
-/
#guard_msgs in
#eval printLifted []
#strata
program Laurel;
procedure binderLocalNoProof() opaque {
  assert forall(x: int) => { var t: int := x * x; t >= 0 }
};
#end

end Laurel
