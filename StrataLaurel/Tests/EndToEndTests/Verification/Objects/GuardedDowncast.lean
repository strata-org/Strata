/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Downcasting with `as`, and the obligation that makes it sound

`p as Child` lowers to a call to a synthesized `downcast$Child` helper — a pure function with
`p is Child` as its PRECONDITION. Being a function rather than a statement is what lets a
cast appear in a formula, which a statement-shaped lowering could not do. And `PrecondElim`
discharging that precondition is what makes the cast sound: without a proof that `p` really
is a `Child`, the downcast is unchecked.

So each case here has to discriminate on two axes at once, and it takes three programs to do
it. The value read through the cast must be real (not havoc), which the `_wrong` twin pins.
And the GUARD must actually do work, which the unguarded twin pins — remove the `is Child`
test and the same body has to fail, on the cast's own obligation rather than on the read.
A test with only the positive case would pass equally well against a cast that returned an
unconstrained reference, or against one with no precondition at all.
-/

/-! ## A guarded downcast, written through and read back

Inside the `is Child` branch the cast's precondition is discharged, so `c` is a genuine
`Child` and the write/read round-trip on its own field is an ordinary heap obligation. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Parent { var x: int }
composite Child extends Parent { var y: int }

procedure guardedDowncastWriteRead(p: Parent)
  opaque
  modifies p
{
  if (p is Child) then {
    var c: Child := p as Child;
    c#y := 9;
    assert c#y == 9
  } else { }
};
#end

-- SOUNDNESS twin on the VALUE axis: the read through the cast is constrained by the write,
-- so a wrong expected value must fail.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Parent { var x: int }
composite Child extends Parent { var y: int }

procedure guardedDowncastWrongValue(p: Parent)
  opaque
  modifies p
{
  if (p is Child) then {
    var c: Child := p as Child;
    c#y := 9;
    assert c#y == 8
//  ^^^^^^^^^^^^^^^ error: assertion could not be proved
  } else { }
};
#end

-- SOUNDNESS twin on the GUARD axis: the SAME body without the `is Child` test. An opaque
-- `Parent` is not provably a `Child`, so the cast's own precondition is what fails here —
-- which is how we know the guard above was doing work rather than decorating the branch.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Parent { var x: int }
composite Child extends Parent { var y: int }

procedure unguardedDowncast(p: Parent)
  opaque
  modifies p
{
  var c: Child := p as Child;
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
  c#y := 9;
  assert c#y == 9
};
#end

/-! ## A cast in a CONTRACT position

`(p as Child)#y` inside an `ensures` is the shape that needs `as` to be a function: a formula
has no room for a statement-shaped cast. The `p is Child` antecedent is what discharges the
helper's precondition as a well-definedness obligation — so the postcondition is only claimed
where the cast is legal. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Parent { var x: int }
composite Child extends Parent { var y: int }

procedure castInPostcondition(p: Parent) returns (r: int)
  opaque
  ensures (p is Child) ==> (r == (p as Child)#y)
{
  if (p is Child) then {
    var c: Child := p as Child;
    r := c#y
  } else {
    r := 0
  }
};
#end

-- SOUNDNESS twin: the contract cast is a real obligation, so an off-by-one postcondition has
-- to fail rather than being vacuously true wherever the cast is well defined.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Parent { var x: int }
composite Child extends Parent { var y: int }

procedure castInPostconditionWrong(p: Parent) returns (r: int)
  opaque
  ensures (p is Child) ==> (r == (p as Child)#y + 1)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
{
  if (p is Child) then {
    var c: Child := p as Child;
    r := c#y
  } else {
    r := 0
  }
};
#end

/-! ## Generics × casts

The target is a generic INSTANTIATION, so the guard and the cast both have to be lowered
against the monomorph's tag (`Box$a1$int`) rather than the generic name. This is the
intersection of the two features; either one alone is covered elsewhere. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite BaseD<T> { var tag: T }
composite BoxD<T> extends BaseD<T> { var val: T }

procedure guardedDowncastToInstantiation(base: BaseD<int>)
  opaque
  modifies base
{
  if (base is BoxD<int>) then {
    var b: BoxD<int> := base as BoxD<int>;
    b#val := 9;
    assert b#val == 9
  } else { }
};
#end

/-! ## A HEAP-NEUTRAL procedure

The cases above all declare `modifies p`, so the cast is lowered alongside a heap inout. A
procedure that reads through the cast without writing anything has no heap output at all, and
the cast still has to be lowered and its obligation still has to be discharged. That is a
distinct path through the lowering — a `modifies`-driven implementation would have nothing to
hang the cast on here.

The unguarded twin is what shows the lowering ran: if `as` had quietly become a no-op in the
heap-neutral case, the cast's precondition would never be emitted and nothing would fail. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Parent { var x: int }
composite Child extends Parent { var y: int }

procedure heapNeutralGuardedDowncast(p: Parent) returns (r: int)
  opaque
  ensures true
{
  if (p is Child) then {
    var c: Child := p as Child;
    r := c#y
  } else {
    r := 0
  }
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Parent { var x: int }
composite Child extends Parent { var y: int }

procedure heapNeutralUnguardedDowncast(p: Parent) returns (r: int)
  opaque
  ensures true
{
  var c: Child := p as Child;
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
  r := c#y
};
#end
