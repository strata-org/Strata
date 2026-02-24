/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-! # Function Preconditions Tests -/

namespace Strata

-- Simple function with a precondition
def divPgm :=
#strata
program Core;

function safeDiv(x : int, y : int) : int
  requires y != 0;
{ x / y }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: safeDiv_body_calls_Int.SafeDiv_0
Property: assert
Assumptions:
precond_safeDiv_0: !($__y1 == 0)
Obligation:
!($__y1 == 0)

---
info: Obligation: safeDiv_body_calls_Int.SafeDiv_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify divPgm

-- Function with multiple preconditions
def multiPrecondPgm :=
#strata
program Core;

function safeSub(x : int, y : int) : int
  requires x >= 0;
  requires y >= 0;
  requires x >= y;
{ x - y }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:

---
info:
-/
#guard_msgs in
#eval verify multiPrecondPgm

-- Datatype destructor with precondition
def listHeadPgm :=
#strata
program Core;

datatype List { Nil(), Cons(head : int, tail : List) };

// Wrapper function with explicit precondition for safe access
inline function safeHead(x : List) : int
  requires List..isCons(x);
{ List..head(x) }

procedure testHead() returns ()
{
  var x : int;
  havoc x;
  assume (x == 1);
  var z : int := safeHead(Cons(x, Nil));
  assert (z == 1);
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: init_calls_safeHead_0
Property: assert
Assumptions:
assume_0: $__x1 == 1
Obligation:
true

Label: assert_0
Property: assert
Assumptions:
assume_0: $__x1 == 1
Obligation:
$__x1 == 1

---
info:
Obligation: init_calls_safeHead_0
Property: assert
Result: ✅ pass

Obligation: assert_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify listHeadPgm

-- Option type with precondition
def optionGetPgm :=
#strata
program Core;

datatype Option { None(), Some(value : int) };

function get(x : Option) : int
  requires Option..isSome(x);
{ Option..value(x) }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:

---
info:
-/
#guard_msgs in
#eval verify optionGetPgm

-- Multiple preconditions where second depends on first (WF check)
def dependentPrecondPgm :=
#strata
program Core;

function foo(x : int, y : int) : int
  requires y > 0;
  requires (x / y) > 0;
{ x / y }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: foo_precond_calls_Int.SafeDiv_0
Property: assert
Assumptions:
precond_foo_0: $__y1 > 0
Obligation:
!($__y1 == 0)

Label: foo_body_calls_Int.SafeDiv_0
Property: assert
Assumptions:
precond_foo_0: $__y1 > 0
precond_foo_1: $__x0 / $__y1 > 0
Obligation:
!($__y1 == 0)

---
info: Obligation: foo_precond_calls_Int.SafeDiv_0
Property: assert
Result: ✅ pass

Obligation: foo_body_calls_Int.SafeDiv_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify dependentPrecondPgm

-- Function body calls another function with preconditions (Phase 3 test)
-- Expression: safeDiv(safeDiv(x, y), z)
-- This should generate WF obligations for both calls to safeDiv
def funcCallsFuncPgm :=
#strata
program Core;

function doubleDiv(x : int, y : int, z : int) : int
  requires y != 0;
  requires z != 0;
{ (x / y) / z }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: doubleDiv_body_calls_Int.SafeDiv_0
Property: assert
Assumptions:
precond_doubleDiv_0: !($__y1 == 0)
precond_doubleDiv_1: !($__z2 == 0)
Obligation:
!($__z2 == 0)

Label: doubleDiv_body_calls_Int.SafeDiv_1
Property: assert
Assumptions:
precond_doubleDiv_0: !($__y1 == 0)
precond_doubleDiv_1: !($__z2 == 0)
Obligation:
!($__y1 == 0)

---
info:
Obligation: doubleDiv_body_calls_Int.SafeDiv_0
Property: assert
Result: ✅ pass

Obligation: doubleDiv_body_calls_Int.SafeDiv_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify funcCallsFuncPgm

-- Function body calls another function but precondition does NOT hold (should fail)
-- Expression: safeDiv(x, 0) - calling with literal 0
def funcCallsFuncFailPgm :=
#strata
program Core;

function badDiv(x : int) : int
{ x / 0 }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: badDiv_body_calls_Int.SafeDiv_0
Property: assert
Obligation:
false



Result: Obligation: badDiv_body_calls_Int.SafeDiv_0
Property: assert
Result: ❌ fail


[DEBUG] Evaluated program:
procedure |badDiv$$wf| (x : int) returns ()
{
  assert [badDiv_body_calls_Int.SafeDiv_0]: false;
  };
function badDiv (x : int) : int {
  x / 0
}

---
info:
Obligation: badDiv_body_calls_Int.SafeDiv_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify funcCallsFuncFailPgm

-- Call to function with precondition - unconditionally true
def callUnconditionalPgm :=
#strata
program Core;

procedure test() returns ()
{
  var z : int := 10 / 2;
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: init_calls_Int.SafeDiv_0
Property: assert
Obligation:
true

---
info: Obligation: init_calls_Int.SafeDiv_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify callUnconditionalPgm

-- Call to function with precondition - depends on path condition (if)
def callWithIfPgm :=
#strata
program Core;

procedure test(a : int) returns ()
{
  var z : int;
  if (a > 0) {
    z := 10 / a;
  } else {
  }
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: set_z_calls_Int.SafeDiv_0
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Gt a #0)>: $__a0 > 0
Obligation:
!($__a0 == 0)

---
info: Obligation: set_z_calls_Int.SafeDiv_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify callWithIfPgm

-- Call to function with precondition - depends on path condition (assume)
def callWithAssumePgm :=
#strata
program Core;

function safeDiv(x : int, y : int) : int
  requires y != 0;
{ x / y }

procedure test(a : int) returns ()
{
  assume a != 0;
  var z : int := safeDiv(10, a);
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: safeDiv_body_calls_Int.SafeDiv_0
Property: assert
Assumptions:
precond_safeDiv_0: !($__y1 == 0)
Obligation:
!($__y1 == 0)

Label: init_calls_safeDiv_0
Property: assert
Assumptions:
assume_0: !($__a2 == 0)
Obligation:
!($__a2 == 0)

---
info: Obligation: safeDiv_body_calls_Int.SafeDiv_0
Property: assert
Result: ✅ pass

Obligation: init_calls_safeDiv_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify callWithAssumePgm

-- Function call inside a quantifier with implication
-- Expression: forall x : int :: x > 0 ==> safeDiv(y, x) > 0
-- The precondition y != 0 should be found inside the quantifier body
def funcInQuantifierPgm :=
#strata
program Core;

function safeDiv(x : int, y : int) : int
  requires y != 0;
{ x / y }

function allPositiveDiv(y : int) : bool
  requires y >= 0;
{ forall x : int :: x > 0 ==> safeDiv(y, x) > 0 }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: safeDiv_body_calls_Int.SafeDiv_0
Property: assert
Assumptions:
precond_safeDiv_0: !($__y1 == 0)
Obligation:
!($__y1 == 0)

Label: allPositiveDiv_body_calls_safeDiv_0
Property: assert
Assumptions:
precond_allPositiveDiv_0: $__y2 >= 0
Obligation:
forall __q0 : int :: __q0 > 0 ==> !(__q0 == 0)

---
info: Obligation: safeDiv_body_calls_Int.SafeDiv_0
Property: assert
Result: ✅ pass

Obligation: allPositiveDiv_body_calls_safeDiv_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify funcInQuantifierPgm

-- Inline function declaration (funcDecl) with precondition
def funcDeclPgm :=
#strata
program Core;

procedure test() returns ()
{
  var x : int := 5;
  function addPositive(y : int) : int
    requires y > 0;
    { x + y }
  var z : int := addPositive(3);
  assert (z == 8);
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: init_calls_addPositive_0
Property: assert
Obligation:
true

Label: assert_0
Property: assert
Obligation:
addPositive(3) == 8

---
info:
Obligation: init_calls_addPositive_0
Property: assert
Result: ✅ pass

Obligation: assert_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify funcDeclPgm

-- Precondition in loop guard
def loopGuardPrecondPgm :=
#strata
program Core;

procedure test(n : int) returns ()
spec {
  requires n != 0;
}
{
  var i : int := 0;
  while (i / n < 10)
    invariant i >= 0
  {
    i := i + 1;
  }
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: loop_guard_calls_Int.SafeDiv_0
Property: assert
Assumptions:
test_requires_0: !($__n0 == 0)
Obligation:
!($__n0 == 0)

Label: entry_invariant_0
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt (~Int.SafeDiv i n) #10)>: 0 / $__n0 < 10
test_requires_0: !($__n0 == 0)
Obligation:
true

Label: arbitrary_iter_maintain_invariant_0
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt (~Int.SafeDiv i n) #10)>: 0 / $__n0 < 10
assume_guard_0: $__i1 / $__n0 < 10
assume_invariant_0: $__i1 >= 0
test_requires_0: !($__n0 == 0)
Obligation:
$__i1 + 1 >= 0

---
info:
Obligation: loop_guard_calls_Int.SafeDiv_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify loopGuardPrecondPgm

end Strata
