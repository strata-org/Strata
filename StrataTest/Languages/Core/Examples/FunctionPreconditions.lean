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
Property: division by zero check
Assumptions:
precond_safeDiv_0: !(y@1 == 0)
Obligation:
!(y@1 == 0)

---
info:
Obligation: safeDiv_body_calls_Int.SafeDiv_0
Property: division by zero check
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

procedure testHead()
{
  var x : int;
  havoc x;
  assume (x == 1);
  var z : int := List..head(Cons(x, Nil));
  assert (z == 1);
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: init_calls_List..head_0
Property: assert
Assumptions:
assume_0: x@1 == 1
Obligation:
true

Label: assert_0
Property: assert
Assumptions:
assume_0: x@1 == 1
Obligation:
x@1 == 1

---
info:
Obligation: init_calls_List..head_0
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
{ Option..value!(x) }

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
Property: division by zero check
Assumptions:
precond_foo_0: y@1 > 0
Obligation:
!(y@1 == 0)

Label: foo_body_calls_Int.SafeDiv_0
Property: division by zero check
Assumptions:
precond_foo_0: y@1 > 0
precond_foo_1: x@1 / y@1 > 0
Obligation:
!(y@1 == 0)

---
info:
Obligation: foo_precond_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: foo_body_calls_Int.SafeDiv_0
Property: division by zero check
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
Property: division by zero check
Assumptions:
precond_doubleDiv_0: !(y@1 == 0)
precond_doubleDiv_1: !(z@1 == 0)
Obligation:
!(y@1 == 0)

Label: doubleDiv_body_calls_Int.SafeDiv_1
Property: division by zero check
Assumptions:
precond_doubleDiv_0: !(y@1 == 0)
precond_doubleDiv_1: !(z@1 == 0)
Obligation:
!(z@1 == 0)

---
info:
Obligation: doubleDiv_body_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: doubleDiv_body_calls_Int.SafeDiv_1
Property: division by zero check
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
Property: division by zero check
Obligation:
false

---
info:
Obligation: badDiv_body_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❌ fail
-/
#guard_msgs in
#eval verify funcCallsFuncFailPgm

-- Call to function with precondition - unconditionally true
def callUnconditionalPgm :=
#strata
program Core;

procedure test()
{
  var z : int := 10 / 2;
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: init_calls_Int.SafeDiv_0
Property: division by zero check
Obligation:
true

---
info: Obligation: init_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass
-/
#guard_msgs in
#eval verify callUnconditionalPgm

-- Call to function with precondition - depends on path condition (if)
def callWithIfPgm :=
#strata
program Core;

procedure test(a : int)
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
Property: division by zero check
Assumptions:
<label_ite_cond_true: a > 0>: a@1 > 0
Obligation:
!(a@1 == 0)

---
info:
Obligation: set_z_calls_Int.SafeDiv_0
Property: division by zero check
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

procedure test(a : int)
{
  assume a != 0;
  var z : int := safeDiv(10, a);
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: safeDiv_body_calls_Int.SafeDiv_0
Property: division by zero check
Assumptions:
precond_safeDiv_0: !(y@1 == 0)
Obligation:
!(y@1 == 0)

Label: init_calls_safeDiv_0
Property: assert
Assumptions:
assume_0: !(a@1 == 0)
Obligation:
!(a@1 == 0)

---
info:
Obligation: safeDiv_body_calls_Int.SafeDiv_0
Property: division by zero check
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
Property: division by zero check
Assumptions:
precond_safeDiv_0: !(y@1 == 0)
Obligation:
!(y@1 == 0)

Label: allPositiveDiv_body_calls_safeDiv_0
Property: assert
Assumptions:
precond_allPositiveDiv_0: y@2 >= 0
Obligation:
forall __q0 : int :: __q0 > 0 ==> !(__q0 == 0)

---
info:
Obligation: safeDiv_body_calls_Int.SafeDiv_0
Property: division by zero check
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

procedure test()
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

procedure test(n : int)
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
Property: division by zero check
Assumptions:
test_requires_0: !(n@1 == 0)
Obligation:
!(n@1 == 0)

Label: entry_invariant_0_0
Property: assert
Assumptions:
test_requires_0: !(n@1 == 0)
Obligation:
true

Label: loop_guard_end_calls_Int.SafeDiv_0
Property: division by zero check
Assumptions:
<label_ite_cond_true: i / n < 10>: 0 / n@1 < 10
assume_guard_0: i@1 / n@1 < 10
assume_invariant_0_0: i@1 >= 0
test_requires_0: !(n@1 == 0)
Obligation:
!(n@1 == 0)

Label: arbitrary_iter_maintain_invariant_0_0
Property: assert
Assumptions:
<label_ite_cond_true: i / n < 10>: 0 / n@1 < 10
assume_guard_0: i@1 / n@1 < 10
assume_invariant_0_0: i@1 >= 0
test_requires_0: !(n@1 == 0)
Obligation:
i@1 + 1 >= 0

---
info:
Obligation: loop_guard_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: loop_guard_end_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify loopGuardPrecondPgm

end Strata
