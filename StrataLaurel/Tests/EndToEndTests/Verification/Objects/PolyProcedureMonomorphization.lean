/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # A polymorphic procedure that touches a GENERIC COMPOSITE is monomorphized, not freshened

Laurel handles polymorphic procedures two different ways, and which one applies is decided by
what the procedure touches rather than by how it is declared:

* a procedure whose `T` is only ever a VALUE rides per-call-site type-variable freshening in
  `CallElim` — that path is covered in `Execution/Procedures/PolyProcedure.lean`;
* a procedure that materializes a GENERIC COMPOSITE at `T` is CLONED per call-site
  instantiation, because Core has no representation for a generic composite. Freshening it
  would leave `Box<T>` un-lowered and the clone's field write would reach Core as a
  `strata-bug`.

The partition is the thing that can go wrong, in both directions. Over-capturing sends
value-`T` procedures down the cloning path unnecessarily (the counter-case is in the
freshening file); under-capturing misses a procedure and produces an internal error. And the
trigger is not just the signature — a procedure with a value-`T` signature that allocates a
`Box<T>` in its BODY has to be captured too, which is what the body-scan case below pins.

Cloning brings its own obligations, each with a case here: the clone's fields must be
re-resolved independently (or two instantiations cross-link and one's write is visible through
the other), the clone's contract must be substituted and still checked, and the discovery has
to be a FIXPOINT — cloning `outer$int` reveals a now-concrete `inner(b: Box<int>)` call that
needs cloning in turn.

Verification-only throughout: every case is heap-allocating.
-/

/-! ## Reading the boxed field off the clone

Passing a `Box<int>` is not enough on its own — it can succeed for reasons unrelated to
monomorphization. Reading `b#val` through the clone is what requires the clone's field to
exist and be typed at the instantiation. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure unbox<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };

procedure readsClonedField()
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 7;
  var got: int := unbox(bx);
  assert got == 7
};

// Two instantiations: each clone reads ITS OWN monomorph's field. Clearing the clone's field
// ids is what keeps them apart; without it the two bodies cross-link.
procedure readsClonedFieldTwoInstantiations()
  opaque
  modifies *
{
  var bi: Box<int> := new Box<int>;
  bi#val := 7;
  var gi: int := unbox(bi);
  var bb: Box<bool> := new Box<bool>;
  bb#val := true;
  var gb: bool := unbox(bb);
  assert gi == 7 && gb == true
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure unbox<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };

procedure readsClonedFieldFalse()
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 7;
  var got: int := unbox(bx);
  assert got == 8
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- The BOOL half of the two-instantiation case falsified: the `int` instantiation passing must
-- not mask the `bool` one.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure unbox<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };

procedure readsClonedFieldTwoInstantiationsFalse()
  opaque
  modifies *
{
  var bi: Box<int> := new Box<int>;
  bi#val := 7;
  var gi: int := unbox(bi);
  var bb: Box<bool> := new Box<bool>;
  bb#val := true;
  var gb: bool := unbox(bb);
  assert gi == 7 && gb == false
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## The clone's CONTRACT is substituted and still checked

Both halves of the contract, since they fail at different places: a false `ensures` fails in
the clone's own body VC, and a violated `requires` fails at the call site. The precondition
case produces two failures — the gating one, and the caller's own assertion, which is no
longer provable once the bad call leaves `got` unconstrained. Both are pinned so a change that
collapsed them into one would be visible. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure pk<T>(b: Box<T>) returns (r: int)
  opaque
  ensures r == 0
//        ^^^^^^ error: postcondition does not hold
{ r := 1 };

procedure falsePostconditionOnClone()
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  var g: int := pk(bx);
  assert 1 == 1
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure get7<T>(b: Box<T>) returns (r: T) requires b#val == 7 opaque ensures r == b#val { r := b#val };

procedure violatedPreconditionOnClone()
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 5;
  var got: int := get7(bx);
//^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
  assert got == 7
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A CONCRETE generic-composite parameter

`take(b: Box<int>)` is not polymorphic at all, but its parameter type is a monomorph — so the
argument has to be passed to a clone that was emitted for a type the caller named. The
`ensures r == b#val` makes the passing observable rather than merely well typed. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure take(b: Box<int>) returns (r: int) opaque ensures r == b#val { r := b#val };

procedure concreteMonomorphParameter()
  opaque
  modifies *
{
  var x: Box<int> := new Box;
  x#val := 7;
  var got: int := take(x);
  assert got == 7
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure take(b: Box<int>) returns (r: int) opaque ensures r == b#val { r := b#val };

procedure concreteMonomorphParameterFalse()
  opaque
  modifies *
{
  var x: Box<int> := new Box;
  x#val := 7;
  var got: int := take(x);
  assert got == 8
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A bare declaration inside the clone

`var t: Box<T>;` with no initializer parses to `.Var (.Declare …)`, a different node from the
`.Assign [.Declare …] e` the initialized form takes. Substitution has to reach both arms — a
missing one leaves `Box<T>` in the clone and crashes at Core. Nothing about the program's
meaning depends on `t`; the point is that it translates at all. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure mk<T>(x: T) returns (r: int) opaque ensures r == 0 { var t: Box<T>; r := 0 };

procedure bareGenericDeclarationInClone()
  opaque
{
  var z: int := mk(7);
  assert 1 == 1
};
#end

/-! ## The BODY-SCAN trigger

`mkl<T>(x: T) returns (r: T)` has a purely value-`T` signature, so the signature alone says
"freshen". But its body allocates a `Box<T>`, which freshening cannot lower — so the decision
has to be made after scanning the body. Without that scan the case fails as an internal error
rather than a wrong answer. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure mkl<T>(x: T) returns (r: T) opaque ensures r == x { var t: Box<T> := new Box<T>; t#val := x; r := t#val };

procedure bodyLocalGenericComposite()
  opaque
{
  var got: int := mkl(7);
  assert got == 7
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure mkl<T>(x: T) returns (r: T) opaque ensures r == x { var t: Box<T> := new Box<T>; t#val := x; r := t#val };

procedure bodyLocalGenericCompositeFalse()
  opaque
{
  var got: int := mkl(7);
  assert got == 8
//^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! ## Discovery is a FIXPOINT, and it reaches CONTRACT positions

`outer<T>` calls `inner<T>` passing its generic-composite parameter. Cloning `outer$int` is
what makes the `inner(b: Box<int>)` call concrete, so `inner$int` can only be discovered on a
second pass — a single collection pass renames the call without ever emitting its target and
leaves a dangling reference.

The `invokeOn` case is the same requirement in a different position: the only call to `g` is
in a CONTRACT, so a collector that walked bodies alone would rename `g` to `g$a1$int` while
never cloning it. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure inner<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };
procedure outer<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := inner(b) };

procedure twoHopChain()
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 7;
  var got: int := outer(bx);
  assert got == 7
};

// Both hops at two instantiations, discovered independently.
procedure twoHopChainTwoInstantiations()
  opaque
  modifies *
{
  var bi: Box<int> := new Box<int>;
  bi#val := 7;
  var gi: int := outer(bi);
  var bb: Box<bool> := new Box<bool>;
  bb#val := true;
  var gb: bool := outer(bb);
  assert gi == 7 && gb == true
};
#end

-- SOUNDNESS twin: the inner clone's contract is threaded through both hops, so a wrong value
-- end-to-end must fail. This also covers the indirect-only callee: `inner` is never called
-- directly, so it gets no separate witness clone (see `PolyProcedureWitness.lean`) and its
-- correctness here comes entirely from the chain.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure inner<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := b#val };
procedure outer<T>(b: Box<T>) returns (r: T) opaque ensures r == b#val { r := inner(b) };

procedure twoHopChainFalse()
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 7;
  var got: int := outer(bx);
  assert got == 99
//^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- The only call to `g` is in an `invokeOn` clause.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure g<T>(b: Box<T>) opaque { assert 1 == 1 };
procedure h(x: Box<int>)
  invokeOn g(x)
  opaque
{ assert 1 == 1 };
#end
