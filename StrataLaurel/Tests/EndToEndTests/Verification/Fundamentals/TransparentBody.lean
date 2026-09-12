/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure transparentBody(): int
{
  assert true;
  return 3
};

procedure tranparentCaller(): int {
  return transparentBody()
};

procedure transparentCallerCaller() opaque {
  var x: int := tranparentCaller();
  assert x == 3
};

procedure letExpressionsInTransparent() returns (r: int) {
  var x: int := 0;
  var y: int := x + 1;
  var z: int := y + 1;
  return z
};

procedure callLetExpressionsInTransparent() opaque {
  var x: int := letExpressionsInTransparent();
  assert x == 2
};

procedure returnAtEnd(x: int) returns (r: int) {
  if x > 0 then {
    if x == 1 then {
      return 1
    } else {
      return 2
    }
  } else {
    return 3
  }
};

procedure elseWithCall(): int
{
  return if true then 3 else returnAtEnd(3)
};

procedure guardInFunction(x: int) returns (r: int)
{
  if x > 0 then {
    if x == 1 then {
      return 1
    } else {
      return 2
    }
  };

  return 3
};

procedure testFunctions()
  opaque
{
  assert returnAtEnd(1) == 1;
  assert returnAtEnd(1) == 2;
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  assert guardInFunction(1) == 1;
  assert guardInFunction(1) == 2
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure guards(a: int) returns (r: int)
{
  var b: int := a + 2;
  if b > 2 then {
      var c: int := b + 3;
      if c > 3 then {
          return c + 4
      };
      var d: int := c + 5;
      return d + 6
  };
  var e: int := b + 1;
  assert e <= 3;
  assert e < 3;
//^^^^^^^^^^^^ error: assertion does not hold
  return e
};

procedure dag(a: int) returns (r: int)
  opaque
{
  var b: int;

  if a > 0 then {
    b := 1
  };
  assert if a > 0 then { b == 1 } else { true };
  assert if a > 0 then { b == 2 } else { true };
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
  return b
};

// Valueless early return (issue #1353): a bare `return` parses to `.Return none`.
// Must verify cleanly — no value, used as an early exit.
procedure valuelessEarlyReturn(b: bool)
  opaque
{
  if b then {
    return
  };
  assert true
};

// Destructive updates to a local in a transparent body: the functional rewrite
// pass turns each update into a shadowing declaration in a nested scope, which
// `InlineLocalVariables` then inlines away.
procedure updateLocalOnce(a: int) returns (r: int)
{
  var x: int := a;
  x := x + 1;
  return x
};

procedure updateLocalTwice(a: int) returns (r: int)
{
  var x: int := a;
  x := x + 1;
  x := x * 2;
  return x
};

// The update reads the variable it assigns, so the shadowing declaration must
// see the *previous* binding for the value to be right.
procedure updateReadsItself(a: int) returns (r: int)
{
  var x: int := a * 2;
  x := x + a;
  return x
};

// Two independent locals, each destructively updated.
procedure updateTwoLocals(a: int) returns (r: int)
{
  var x: int := a;
  var y: int := a + 10;
  x := x + 1;
  y := y + 2;
  return x + y
};

// Early exits in a transparent body. `FunctionalRewrite` translates the
// statements after an if into the continuation of both its branches, so an
// `exit $return` inside a branch becomes that branch's value and the statements
// following the if become the other branch's. Statements after an if whose every
// path exits are unreachable, and are dropped.
procedure deadCodeAfterIfElse(x: int) returns (r: int)
{
  if x > 0 then { return 1 } else { return 2 };
  return 3
};

// One branch exits, the other falls through to the code after the if.
procedure guardEarly(x: int) returns (r: int)
{
  if x > 0 then {
    return 1
  };
  return 3
};

// Chained guards: each fall-through path carries the rest of the body.
procedure twoGuards(x: int) returns (r: int)
{
  if x > 10 then {
    return 1
  };
  if x > 5 then {
    return 2
  };
  return 3
};

// An early exit combined with a destructive update, so the exit's value is the
// innermost shadowing binding of `x` rather than the outer one.
procedure guardWithLocalUpdate(a: int) returns (r: int)
{
  var x: int := a;
  if a > 0 then {
    x := x + 1;
    return x
  };
  x := x - 1;
  return x
};

// A local declared without an initializer, then assigned: the declaration is bound
// to a hole and the assignment shadows it, so the hole is never read and the result
// is exactly the assigned value.
procedure uninitThenAssign(a: int) returns (r: int)
{
  var x: int;
  x := a + 1;
  return x
};

// Assigned in *every* branch of an if, so whichever path runs shadows the hole and
// the result is fully determined on both.
procedure assignedInBothBranches(b: bool) returns (r: int)
{
  var x: int;
  if b then {
    x := 1
  } else {
    x := 2
  };
  return x
};

// An assignment inside an unlabelled block shadows the hole just as it would at top
// level: the block's statements run in sequence right there.
procedure blockBinds() returns (r: int)
{
  var x: int;
  { x := 1 };
  return x
};

// A local that shadows an input parameter. Updating it is an ordinary destructive
// update of the *local*, not an assignment to the input, so it must be accepted.
// The input's value is irrelevant to the result, which is what pins that the
// shadowing binding is the one being read.
procedure shadowsInput(a: int) returns (r: int)
{
  var a: int := 100;
  a := a + 1;
  return a
};

// Eight chained guards. Each guard exits in its `then` branch, so only the `else`
// branch carries the continuation and the rewritten body grows linearly rather
// than exponentially — this is the shape real code uses, and it stays cheap.
procedure eightGuards(x: int) returns (r: int)
{
  if x > 8 then { return 1 };
  if x > 7 then { return 2 };
  if x > 6 then { return 3 };
  if x > 5 then { return 4 };
  if x > 4 then { return 5 };
  if x > 3 then { return 6 };
  if x > 2 then { return 7 };
  if x > 1 then { return 8 };
  return 9
};

// An exit to a user label. The labelled block binds its label to the translation
// of what follows it, so exiting skips the rest of the block and resumes after it.
procedure exitSkipsRest(x: int) returns (r: int)
{
  var y: int := 0;
  {
    if x > 0 then {
      y := 1;
      exit done
    };
    y := 2
  } done;
  return y
};

// An exit from a nested labelled block to the *outer* label, skipping both the
// rest of the inner block and the rest of the outer one.
procedure exitToOuterLabel(x: int) returns (r: int)
{
  var y: int := 0;
  {
    {
      if x > 0 then {
        y := 10;
        exit outer
      };
      y := 20
    } inner;
    y := y + 100
  } outer;
  return y
};

// Nested ifs where every path exits: the inner if is in tail position, so its
// continuation is unused and no code is duplicated.
procedure nestedIfAllExit(x: int) returns (r: int)
{
  if x > 0 then {
    if x > 10 then {
      return 1
    } else {
      return 2
    }
  } else {
    return 3
  }
};

// A guard nested inside a guard: `return 3` is the continuation of both the
// inner and the outer falling path, so it is reached from three places.
procedure nestedGuards(x: int, y: int) returns (r: int)
{
  if x > 0 then {
    if y > 0 then {
      return 1
    };
    return 2
  };
  return 3
};

// A nested if that falls through on the inside but not the outside, combined
// with a destructive update, so each path must see the right binding of `x`.
procedure nestedIfWithUpdate(a: int, b: int) returns (r: int)
{
  var x: int := a;
  if a > 0 then {
    x := x + 10;
    if b > 0 then {
      x := x + 100;
      return x
    };
    return x
  };
  return x
};

procedure testEarlyExits()
  opaque
{
  assert deadCodeAfterIfElse(5) == 1;
  assert deadCodeAfterIfElse(0 - 5) == 2;
  assert deadCodeAfterIfElse(5) == 3;
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  assert guardEarly(5) == 1;
  assert guardEarly(0 - 5) == 3;
  assert guardEarly(0 - 5) == 1;
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  assert twoGuards(20) == 1;
  assert twoGuards(7) == 2;
  assert twoGuards(1) == 3;
  assert twoGuards(7) == 3;
//^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  // Every guard's continuation must reach the right fall-through value. The
  // first guard whose condition holds wins: x=5 passes `x > 4` and returns 5,
  // x=2 passes `x > 1` and returns 8, and x=0 falls through every guard.
  assert eightGuards(100) == 1;
  assert eightGuards(5) == 5;
  assert eightGuards(2) == 8;
  assert eightGuards(0) == 9;
  assert eightGuards(5) == 4;
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  assert guardWithLocalUpdate(3) == 4;
  assert guardWithLocalUpdate(0 - 3) == 0 - 4;
  assert guardWithLocalUpdate(3) == 2
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure testExitToLabel()
  opaque
{
  // Exiting must skip `y := 2`; falling through must run it.
  assert exitSkipsRest(1) == 1;
  assert exitSkipsRest(0 - 1) == 2;
  assert exitSkipsRest(1) == 2;
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  // Exiting to `outer` must skip `y := y + 100`; falling out of `inner` must run it.
  assert exitToOuterLabel(1) == 10;
  assert exitToOuterLabel(0 - 1) == 120;
  assert exitToOuterLabel(1) == 110;
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
  assert exitToOuterLabel(0 - 1) == 20
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure testNestedIfs()
  opaque
{
  assert nestedIfAllExit(20) == 1;
  assert nestedIfAllExit(5) == 2;
  assert nestedIfAllExit(0 - 5) == 3;
  assert nestedIfAllExit(5) == 1;
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  assert nestedGuards(1, 1) == 1;
  assert nestedGuards(1, 0 - 1) == 2;
  assert nestedGuards(0 - 1, 1) == 3;
  assert nestedGuards(1, 0 - 1) == 3;
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  assert nestedIfWithUpdate(1, 1) == 111;
  assert nestedIfWithUpdate(1, 0 - 1) == 11;
  assert nestedIfWithUpdate(0 - 1, 1) == 0 - 1;
  assert nestedIfWithUpdate(1, 1) == 11
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure testUninitializedLocal()
  opaque
{
  assert uninitThenAssign(3) == 4;
  assert uninitThenAssign(3) == 5;
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  assert assignedInBothBranches(true) == 1;
  assert assignedInBothBranches(false) == 2;
  assert assignedInBothBranches(false) == 1;
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  assert blockBinds() == 1;
  assert blockBinds() == 2
//^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure testShadowsInput()
  opaque
{
  // The result comes from the local's initializer, so it is 101 whatever the
  // input is. If the input were read instead, these would differ.
  assert shadowsInput(0 - 1) == 101;
  assert shadowsInput(7) == 101;
  assert shadowsInput(7) == 8
//^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure testDestructiveUpdates()
  opaque
{
  assert updateLocalOnce(3) == 4;
  assert updateLocalOnce(3) == 5;
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  assert updateLocalTwice(3) == 8;
  assert updateLocalTwice(3) == 7;
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  assert updateReadsItself(3) == 9;
  assert updateTwoLocals(3) == 19
};
#end

-- An `exit` inside an assigned *block value*. The block-value arms translate the block
-- with its last element as the continuation, which would turn the `exit` into that
-- label's continuation as the assigned *value* and leave the statements after the
-- assignment to run anyway — so this body would evaluate to 1 + 100 where leaving the
-- labelled block before either assignment gives 1. An exit abandons the enclosing
-- statements, and a value's continuation is not the statement's continuation, so it is
-- reported rather than mistranslated.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure exitInBlockValue(c: bool) returns (r: int)
{
  r := 1;
  {
    r := { if c then { exit done }; 5 };
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: an `exit` or `return` inside an assigned block value is not YET supported in transparent bodies or contracts
    r := r + 100
  } done;
  return r
};
#end

-- A block value with no exit is unaffected, so the rejection above is not over-broad:
-- the block's statements are functionalized with its last element as the value.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure blockValueNoExit(a: int) returns (r: int)
{
  r := { var y: int := a; y := y + 1; y };
  return r
};

procedure testBlockValueNoExit()
  opaque
{
  assert blockValueNoExit(1) == 2
};
#end

-- Assigning to an input parameter is a destructive assignment that must still be
-- rejected: rewriting it into a shadowing declaration would silently accept the
-- program. `FunctionalRewrite` therefore reports it rather than rewriting it.
-- Kept in its own program because the error aborts verification of the rest.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure updateInputParameter(a: int) returns (r: int)
{
  a := a + 1;
//^^^^^^^^^^ error: destructive assignments are not supported in transparent bodies or contracts
  return a
};
#end

-- A local read while still unbound reads as an arbitrary-but-fixed value: the bare
-- declaration is bound to a deterministic hole. So the body is accepted, and nothing
-- concrete is provable about its value — but it *is* a function, so two calls with the
-- same arguments agree. That pins the hole as deterministic rather than nondeterministic.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure readBeforeAssign() returns (r: int)
{
  var x: int;
  return x
};

procedure testReadBeforeAssign()
  opaque
{
  assert readBeforeAssign() == readBeforeAssign();
  assert readBeforeAssign() == 0
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- A variable read inside its *own* first assignment reads the hole the declaration
-- was bound to, so `x := x + 1` is `hole + 1`: accepted, with no concrete value
-- provable, and equal to itself across calls.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure readInOwnAssign() returns (r: int)
{
  var x: int;
  x := x + 1;
  return x
};

procedure testReadInOwnAssign()
  opaque
{
  assert readInOwnAssign() == readInOwnAssign();
  assert readInOwnAssign() == 1
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Only *one* branch assigns, so the `b` path yields 1 and the other yields the hole.
-- The assigned path is fully provable; the unassigned one is not.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure onlyOneBranchAssigns(b: bool) returns (r: int)
{
  var x: int;
  if b then {
    x := 1
  };
  return x
};

procedure testOnlyOneBranchAssigns()
  opaque
{
  assert onlyOneBranchAssigns(true) == 1;
  assert onlyOneBranchAssigns(false) == 1
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- An `exit` before the assignment means that path never performs it, so that path reads
-- the hole. The bare `var x` shadows the input parameter of the same name, and the test
-- pins that the exit path reads the *hole* rather than that input: `== 77` is not
-- provable, while the `else` path still yields 2. Binding the declaration is what
-- guarantees that — an elided declaration would leave a free `x` resolving to the input.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure exitSkipsTheAssignment(x: int, c: bool) returns (r: int)
{
  var x: int;
  if c then { { if c then { exit skip }; x := 1 } skip }
  else { x := 2 };
  return x
};

procedure testExitSkipsTheAssignment()
  opaque
{
  assert exitSkipsTheAssignment(77, false) == 2;
  assert exitSkipsTheAssignment(77, true) == 77
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- The same shape with the labelled block as an `if` *branch* rather than a top-level
-- statement. The `exit blk` on the `e` path skips the `x := 1` inside that block, so that
-- path reads the hole and not the same-named input: `(true, true, 77) == 77` is not
-- provable, while the two paths that do assign yield 1 and 2. Branch position is what
-- this adds over `exitSkipsTheAssignment`; binding every declaration makes the two agree
-- without any analysis of where an exit can leave a labelled block.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure exitSkipsAssignmentInBranch(d: bool, e: bool, x: int) returns (r: int)
{
  var x: int;
  if d then { if e then { exit blk }; x := 1 } blk
       else { x := 2 };
  return x
};

procedure testExitSkipsAssignmentInBranch()
  opaque
{
  assert exitSkipsAssignmentInBranch(false, false, 77) == 2;
  assert exitSkipsAssignmentInBranch(true, false, 77) == 1;
  assert exitSkipsAssignmentInBranch(true, true, 77) == 77
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- A declaration in an inner scope that shadows an outer local of the same name. The
-- inner one dies at the end of its scope, so the trailing read must see the outer 0.
--
-- The rewrite extends a declaration's scope over the translation of the statements that
-- follow, and substitutes an if's continuation into both branches, so without renaming
-- the continuation's `x` would land inside the inner declaration's scope and read 1.
-- `alphaConvertLocals` gives each declaration a name unique to it, so neither can shadow
-- the other. Both the if-branch and the plain-block form are pinned, because the block
-- form has no branching at all — it is the flattening of the block that exposed it.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure innerDeclShadowsOuter(c: bool) returns (r: int)
{
  var x: int := 0;
  if c then {
    var x: int := 1
  };
  return x
};

procedure innerDeclShadowsOuterBlock() returns (r: int)
{
  var x: int := 0;
  {
    var x: int := 1
  };
  return x
};

procedure testInnerDeclShadowsOuter()
  opaque
{
  assert innerDeclShadowsOuter(true) == 0;
  assert innerDeclShadowsOuter(false) == 0;
  assert innerDeclShadowsOuterBlock() == 0;
  assert innerDeclShadowsOuter(true) == 1
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Shadowing in a body that carries a proof step. The `assert` is what makes this a
-- separate case from the two `innerDeclShadowsOuter*` cases above: it gives the procedure
-- a procedural twin, so `functionalize` runs over the body, and a block holding a single
-- statement keeps its wrapper so the inner `var x` stays in its own scope.
--
-- Core still rejects it, for the separate limitation `rewriteQuantifierBodiesM` documents:
-- Laurel's resolution accepts shadowing by giving the declarations distinct `uniqueId`s,
-- but Core keys its context on the name, and only the functional copy is alpha-converted
-- (`alphaConvertLocals`) — which is why the assert-free cases above verify. When Laurel
-- gains end-to-end shadowing support this becomes a clean `== 0` and the annotation goes.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure innerDeclShadowsOuterWithProofStep() returns (r: int)
{
  var x: int := 0;
  {
    var x: int := 1
//  ^^^^^^^^^^^^^^^ error: Variable x of type int already in context
  };
  assert 1 == 1;
  return x
};
#end

-- A transparent body whose statements are *all* proof steps, with a declared output whose
-- type is not `bool`. Functionalizing deletes the proof steps, which empties the body, and
-- an empty body is lowered to a hole of the declared type — so these verify. Substituting a
-- `bool` in place of a deleted step instead would reject them with "Impossible to unify int
-- with bool", which is what the pass used to do. Both `assert` and `assume` are covered
-- because the pass treats them as one case, and a non-`int` output is covered because the
-- old failure named the declared type, so `bool` alone would have passed either way.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure proofStepOnlyBody() returns (r: int)
{
  assert true
};

procedure proofStepOnlyBodyAssume() returns (r: int)
{
  assume true
};

procedure proofStepOnlyBodyString() returns (r: string)
{
  assert true
};
#end

-- An empty transparent body with a declared output. There are no proof steps to delete, so
-- this pins the other half: functionalizing must leave the empty block alone rather than
-- putting an expression there, since the pass that follows lowers it to a hole of the
-- declared type. A `Block` arm that rewrote an emptied block would reject this.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure emptyBodyWithOutput() returns (r: int)
{
};

procedure emptyBodyWithOutputString() returns (r: string)
{
};
#end

-- The converse, which the renaming must *not* break: an `x := 1` inside a branch is an
-- update of the outer `x`, not a new declaration, so it has to remain visible after the
-- if. Substituting the continuation under the shadowing declaration is what propagates
-- it, which is why the continuation is not bound outside the branch instead.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure updateInBranchFlowsOut(b: bool) returns (r: int)
{
  var x: int := 0;
  if b then {
    x := 1
  };
  return x
};

procedure testUpdateInBranchFlowsOut()
  opaque
{
  assert updateInBranchFlowsOut(true) == 1;
  assert updateInBranchFlowsOut(false) == 0;
  assert updateInBranchFlowsOut(true) == 0
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- A local that *shadows an input of the same name*, declared before an uninitialized
-- local. The hole's arguments are the enclosing function's inputs, and because the call is
-- hoisted above every user declaration they mean the inputs rather than the shadowing
-- local. So the value still varies with the real `a`: two calls with the *same* argument
-- agree, two with different arguments are not provably equal. Were the argument captured
-- by the local, the hole would be a constant and `f(1) == f(2)` would be provable.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure shadowingWithHole(a: int) returns (r: int)
{
  var a: int := 100;
  var b: int;
  return a + b
};

procedure testShadowingWithHole()
  opaque
{
  assert shadowingWithHole(1) == shadowingWithHole(1);
  assert shadowingWithHole(1) == shadowingWithHole(2)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- An uninitialized local in a *polymorphic* transparent body. The hole mirrors the
-- enclosing inputs, whose types mention the type variable, so the hole is polymorphic
-- too — and monomorphization runs long before this pass, so it could never be
-- instantiated. Reported here rather than left to surface from SMT encoding as an
-- unresolved type variable.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure polyHole<T>(x: T) returns (r: T)
//        ^^^^^^^^ error: a local without an initializer is not YET supported in a transparent body of a polymorphic procedure like 'polyHole'; give it an initializer
{
  var y: T;
  return y
};
#end

-- The converse: a polymorphic transparent body with every local initialized is
-- unaffected by that restriction and still verifies.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure polyId<T>(x: T) returns (r: T)
{
  return x
};

procedure testPolyId()
  opaque
{
  assert polyId(1) == polyId(1)
};
#end

-- A path that reaches the end of the body without assigning the *output*. The output is
-- an uninitialized variable like any other, so it is bound to a hole at the top of the
-- body: the `c` path yields 1 and the fall-through path yields the hole. After inlining
-- the body reads `if c then 1 else <hole>`.
--
-- The assigned path stays fully provable, the unassigned one is provably nothing in
-- particular, and both agree with the imperative twin, which havocs an unassigned output.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure fallThroughUnassigned(c: bool) returns (r: int)
{
  if c then {
    return 1
  }
};

procedure testFallThroughUnassigned()
  opaque
{
  assert fallThroughUnassigned(true) == 1;
  assert fallThroughUnassigned(false) == fallThroughUnassigned(false);
  assert fallThroughUnassigned(false) == 0
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- An assignment with no explicit `return`: the body falls off the end *after* assigning,
-- so the fall-through read finds the assignment's binding rather than the hole. This is
-- why the hole is bound outermost and the assignment shadows it, instead of the
-- fall-through continuation being the hole itself.
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure assignNoExit() returns (r: int)
{
  r := 7
};

procedure testAssignNoExit()
  opaque
{
  assert assignNoExit() == 7
};
#end
