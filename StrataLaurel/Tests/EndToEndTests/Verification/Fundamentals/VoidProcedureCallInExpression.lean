/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
## A procedure that returns nothing may be called from an expression context

`{ returnsNothing(x); e }` is a block expression whose value is `e`; the call is
there for its verification effect. That is how a *lemma* is invoked in Laurel: a
proof step needs a postcondition, only a procedure can carry one, and a procedure
whose whole purpose is the postcondition has nothing to return.

Two things have to hold for the idiom to be usable, and both are exercised below:

- the block lowers, wherever it appears — an ordinary body, a block expression, a
  transparent (function) body, a contract;
- the callee's postcondition is available to the statements that follow the call,
  and its precondition is still checked at it.

The postconditions here constrain an *input parameter* (`ensures x > 0`) rather
than the result of some function. That is deliberate: a call to a bodiless
`opaque` procedure yields a fresh symbolic output at every call site, so
`ensures f(x) > 0` would say nothing an `assert f(x) > 0` could use, and the test
would fail for a reason unrelated to what it is checking.
-/

/-! ### Statement position in an ordinary body

The baseline: the call is a statement, and the fact it establishes is available
afterwards. `withoutTheCall` is the control — the same assertion, unprovable when
nothing established it — so the test cannot pass by the assertion being provable
on its own. -/

#eval testLaurelVerification <|
#strata
program Laurel;

procedure knowsPositive(x: int)
  opaque
  ensures x > 0;

procedure callInBody(x: int)
  opaque
{
  knowsPositive(x);
  assert x > 0
};

procedure withoutTheCall(x: int)
  opaque
{
  assert x > 0
//^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### Expression position

The call is a non-final statement of a block expression, so the block's value is
the trailing `3`, and the postcondition is available afterwards. -/

#eval testLaurelVerification <|
#strata
program Laurel;

procedure knowsPositive(x: int)
  opaque
  ensures x > 0;

procedure callInBlockExpression(x: int)
  opaque
{
  var y: int := { knowsPositive(x); 3 };
  assert y == 3;
  assert x > 0
};
#end

/-! ### Transparent (function-like) body

A transparent body becomes a single pure expression, and `functionalize` deletes the
call on the way there, so what is left is the value. -/

#eval testLaurelVerification <|
#strata
program Laurel;

procedure knowsPositive(x: int)
  opaque
  ensures x > 0;

procedure transparentWithVoidCall(x: int): int
{
  knowsPositive(x);
  assert x > 0;
  return 3
};

// Control: the same assertion without the hint. Without it the block would only pin
// that the shape lowers, since the value 3 holds whether or not the hint contributes.
procedure transparentWithoutTheCall(x: int): int
{
  assert x > 0;
//^^^^^^^^^^^^ error: assertion does not hold
  return 3
};

procedure useTransparent(x: int)
  opaque
{
  assert transparentWithVoidCall(x) == 3
};
#end

/-! ### A call whose result is unused is simply dropped

Not only an output-less call: in the pure twin a call is a function application, and an
application whose value nobody binds contributes nothing — no effect to preserve, and its
obligations were raised on the imperative side. So a value-returning call in statement
position is dropped too, rather than reported.

`discardsTheResult` is that case, and it verifies: the body's value is the trailing `3`. -/

#eval testLaurelVerification <|
#strata
program Laurel;

procedure returnsSomething(x: int) returns (r: int)
  opaque;

procedure discardsTheResult(x: int): int
{
  returnsSomething(x);
  return 3
};

procedure useDiscardsTheResult(x: int)
  opaque
{
  assert discardsTheResult(x) == 3
};
#end

/-! Dropping a call must not drop a state change. It cannot: the state a callee writes is
threaded through its signature as a hidden inout (`HeapParameterization` declares the
`$heap` global, `GlobalParameterization` threads it and any written global), so by the time
`functionalize` runs the call is an assignment to that inout, not a `StaticCall`. A
transparent body cannot mutate an input — it has one result and no slot to thread the new
value out — so the call is rejected rather than dropped, and the diagnostic lands on it.

Both cases below use a *void* transparent body on purpose. Given a return type as well,
the threaded state makes two outputs and the diagnostic moves to the signature
("a transparent body with 2 output parameters is not supported"), which is a different
rule and would stop pinning this one. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var f: int }

procedure bump(c: C)
  opaque
  modifies c
{
  c#f := c#f + 1
};

procedure voidTransparentMutatesHeap(c: C)
{
  bump(c)
//^^^^^^^ error: a transparent body or contract cannot YET mutate any of its inputs, and this mutates '$heap'
};

procedure heapWriteInEnsures(c: C) returns (r: int)
  opaque
  ensures { bump(c); r == 0 }
//          ^^^^^^^ error: a transparent body or contract cannot YET mutate any of its inputs, and this mutates '$heap'
{ r := 0 };
#end

/-! A write to an ordinary file-scope global is caught by the same mechanism, even though
such a write is not recorded in `modifies` at all.

The write does not have to be direct: `setGIndirect` writes `g` only through `setG`, and a
transparent body calling it is rejected just the same, so the analysis is transitive. The
direct case alone would pass even if it were not. -/

#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0

procedure setG()
  opaque
{
  g := 7
};

procedure voidTransparentWritesGlobal()
{
  setG()
//^^^^^^ error: a transparent body or contract cannot YET mutate any of its inputs, and this mutates 'g'
};

procedure setGIndirect()
  opaque
{
  setG()
};

procedure voidTransparentIndirectWrite()
{
  setGIndirect()
//^^^^^^^^^^^^^^ error: a transparent body or contract cannot YET mutate any of its inputs, and this mutates 'g'
};
#end

/-! ### The callee's precondition is still checked

Erasing the call from the *pure* twin must not erase the obligation it carries:
`needsPositive` is called with an unconstrained `x`, and its `requires` is
reported at the call site even though the call sits inside a block expression. -/

#eval testLaurelVerification <|
#strata
program Laurel;

procedure needsPositive(x: int)
  requires x > 0
  opaque;

procedure unguardedCallInBlockExpression(x: int)
  opaque
{
  var y: int := { needsPositive(x); 3 };
//                ^^^^^^^^^^^^^^^^ error: precondition does not hold
  assert y == 3
};

procedure guardedCallInBlockExpression(x: int)
  opaque
{
  assume x > 0;
  var y: int := { needsPositive(x); 3 };
  assert y == 3
};
#end

/-! ### Inside a contract

This is the idiom the feature exists for. A contract expression is relocated into a
`$post_i` helper whose body is a statement context, so the same block shape lowers
there, and `ContractPass` instruments the call like any other — the callee's
precondition is checked and its postcondition assumed.

The hint acts on the obligations of the rest of the block, not on the condition itself,
so `assert x > 0` below is provable and a caller assuming this `ensures` still gets
exactly `r == 0`. -/

#eval testLaurelVerification <|
#strata
program Laurel;

procedure knowsPositive(x: int)
  opaque
  ensures x > 0;

procedure callInEnsures(x: int) returns (r: int)
  opaque
  ensures { knowsPositive(x); assert x > 0; r == 0 }
{
  r := 0
};

// Control: the same assertion without the hint is unprovable, so the case above does
// not pass by `x > 0` holding for some unrelated reason.
procedure ensuresWithoutTheHint(x: int) returns (r: int)
  opaque
  ensures { assert x > 0; r == 0 }
//          ^^^^^^^^^^^^ error: assertion does not hold
{
  r := 0
};

// The hint is not part of the condition: a caller assuming this `ensures` gets exactly
// `r == 0`, so `r` is pinned and nothing about `x` leaks in.
procedure callerSeesOnlyTheCondition(x: int)
  opaque
{
  var r: int := callInEnsures(x);
  assert r == 0
};
#end

/-! And the hint discharges a *following call's precondition* inside the contract — the
well-formedness use that motivates the idiom, rather than an explicit `assert`. -/

#eval testLaurelVerification <|
#strata
program Laurel;

procedure knowsPositive(x: int)
  opaque
  ensures x > 0;

procedure needsPositive(x: int) returns (r: int)
  requires x > 0
  opaque;

procedure hintDischargesPrecondition(x: int) returns (r: int)
  opaque
  ensures { knowsPositive(x); needsPositive(x) == needsPositive(x) }
{
  r := 0
};

// Control: without the hint, `needsPositive`'s precondition is open at both calls.
procedure withoutTheHint(x: int) returns (r: int)
  opaque
  ensures { needsPositive(x) == needsPositive(x) }
//          ^^^^^^^^^^^^^^^^ error: precondition does not hold
//                              ^^^^^^^^^^^^^^^^ error: precondition does not hold
{
  r := 0
};

// A `requires` is a separate path — its helper comes from `mkConditionProc`, which
// assumes the preceding clauses, not `mkPostConditionProc` — so it is covered too.
procedure hintInRequires(x: int) returns (r: int)
  requires { knowsPositive(x); needsPositive(x) == needsPositive(x) }
  opaque
{
  r := 0
};

procedure requiresWithoutTheHint(x: int) returns (r: int)
  requires { needsPositive(x) == needsPositive(x) }
//           ^^^^^^^^^^^^^^^^ error: precondition does not hold
//                               ^^^^^^^^^^^^^^^^ error: precondition does not hold
  opaque
{
  r := 0
};
#end

/-! ### A hint before a loop, and why one inside an invariant does nothing

A loop head is a position none of the cases above reach. An invariant is
re-checked on an arbitrary iteration, over havoc'd loop-carried variables, so a
fact has to survive from before the loop to hold there. It does: the hint is a
statement in the body, and what it establishes about `x` is untouched by the
loop.

`noHintBeforeLoop` is the control — the same invariant, unprovable when nothing
established it.

A hint inside the invariant instead does not help: `LoopInvariantWellFormedness`
re-emits each invariant as `assume I_i` in a branch sealed with `assume false`, so
nothing it assumes reaches the loop. The callee's obligation does survive, because
that comes from lowering the invariant's contents rather than from the hint —
`obligationCheckedInInvariant` pins it, and it is what makes the lost hint merely
incompleteness. -/

#eval testLaurelVerification <|
#strata
program Laurel;

procedure knowsPositive(x: int)
  opaque
  ensures x > 0;

procedure needsPositive(x: int)
  requires x > 0
  opaque;

procedure hintBeforeLoop(x: int)
  opaque
{
  knowsPositive(x);
  var i: int := 0;
  while (i < 3)
    invariant x > 0
  {
    i := i + 1
  }
};

procedure noHintBeforeLoop(x: int)
  opaque
{
  var i: int := 0;
  while (i < 3)
    invariant x > 0
//            ^^^^^ error: assertion does not hold
  {
    i := i + 1
  }
};

procedure hintInInvariant(x: int)
  opaque
{
  var i: int := 0;
  while (i < 3)
    invariant { knowsPositive(x); x > 0 }
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
  {
    i := i + 1
  }
};

procedure obligationCheckedInInvariant(x: int)
  opaque
{
  var i: int := 0;
  while (i < 3)
    invariant { needsPositive(x); i >= 0 }
//              ^^^^^^^^^^^^^^^^ error: precondition does not hold
  {
    i := i + 1
  }
};
#end
