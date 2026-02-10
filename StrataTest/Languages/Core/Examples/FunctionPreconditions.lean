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
{ x div y }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: safeDiv_calls_Int.Div_0
Property: assert
Assumptions:
(precond_safeDiv, (~Bool.Not (y == #0)))
Proof Obligation:
(~Bool.Not (y == #0))

---
info: Obligation: safeDiv_calls_Int.Div_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" divPgm

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
#eval verify "cvc5" multiPrecondPgm

-- Datatype destructor with precondition
def listHeadPgm :=
#strata
program Core;

datatype List { Nil(), Cons(head : int, tail : List) };

procedure testHead() returns ()
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
(assume_0, ($__x0 == #1))

Proof Obligation:
#true

Label: assert_0
Property: assert
Assumptions:
(assume_0, ($__x0 == #1))

Proof Obligation:
($__x0 == #1)

---
info: Obligation: init_calls_List..head_0
Property: assert
Result: ✅ pass

Obligation: assert_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" listHeadPgm

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
Label: get_calls_Option..value_0
Property: assert
Assumptions:
(precond_get, (~Option..isSome x))
Proof Obligation:
(~Option..isSome x)

---
info: Obligation: get_calls_Option..value_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" optionGetPgm

-- Multiple preconditions where second depends on first (WF check)
def dependentPrecondPgm :=
#strata
program Core;

function foo(x : int, y : int) : int
  requires y > 0;
  requires (x div y) > 0;
{ x div y }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: foo_calls_Int.Div_0
Property: assert
Assumptions:
(precond_foo, ((~Int.Gt y) #0))
Proof Obligation:
(~Bool.Not (y == #0))

Label: foo_calls_Int.Div_1
Property: assert
Assumptions:
(precond_foo, ((~Int.Gt y) #0))
(precond_foo, ((~Int.Gt ((~Int.Div x) y)) #0))
Proof Obligation:
(~Bool.Not (y == #0))

---
info: Obligation: foo_calls_Int.Div_0
Property: assert
Result: ✅ pass

Obligation: foo_calls_Int.Div_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" dependentPrecondPgm

-- Function body calls another function with preconditions (Phase 3 test)
-- Expression: safeDiv(safeDiv(x, y), z)
-- This should generate WF obligations for both calls to safeDiv
def funcCallsFuncPgm :=
#strata
program Core;

function doubleDiv(x : int, y : int, z : int) : int
  requires y != 0;
  requires z != 0;
{ (x div y) div z }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: doubleDiv_calls_Int.Div_0
Property: assert
Assumptions:
(precond_doubleDiv, (~Bool.Not (y == #0)))
(precond_doubleDiv, (~Bool.Not (z == #0)))
Proof Obligation:
(~Bool.Not (z == #0))

Label: doubleDiv_calls_Int.Div_1
Property: assert
Assumptions:
(precond_doubleDiv, (~Bool.Not (y == #0)))
(precond_doubleDiv, (~Bool.Not (z == #0)))
Proof Obligation:
(~Bool.Not (y == #0))

---
info:
Obligation: doubleDiv_calls_Int.Div_0
Property: assert
Result: ✅ pass

Obligation: doubleDiv_calls_Int.Div_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" funcCallsFuncPgm

-- Function body calls another function but precondition does NOT hold (should fail)
-- Expression: safeDiv(x, 0) - calling with literal 0
def funcCallsFuncFailPgm :=
#strata
program Core;

function badDiv(x : int) : int
{ x div 0 }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: badDiv_calls_Int.Div_0
Property: assert
Assumptions:

Proof Obligation:
(~Bool.Not (#0 == #0))



Result: Obligation: badDiv_calls_Int.Div_0
Property: assert
Result: ❌ fail


Evaluated program:
func badDiv :  ((x : int)) → int :=
  ((((~Int.Div : (arrow int (arrow int int))) (x : int)) #0))
---
info:
Obligation: badDiv_calls_Int.Div_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify "cvc5" funcCallsFuncFailPgm

-- Call to function with precondition - unconditionally true
def callUnconditionalPgm :=
#strata
program Core;

procedure test() returns ()
{
  var z : int := 10 div 2;
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: init_calls_Int.Div_0
Property: assert
Assumptions:


Proof Obligation:
#true

---
info: Obligation: init_calls_Int.Div_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" callUnconditionalPgm

-- Call to function with precondition - depends on path condition (if)
def callWithIfPgm :=
#strata
program Core;

procedure test(a : int) returns ()
{
  var z : int;
  if (a > 0) {
    z := 10 div a;
  } else {
  }
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: set_z_calls_Int.Div_0
Property: assert
Assumptions:
(<label_ite_cond_true: ((~Int.Gt a) #0)>, ((~Int.Gt $__a0) #0))


Proof Obligation:
(~Bool.Not ($__a0 == #0))

---
info: Obligation: set_z_calls_Int.Div_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" callWithIfPgm

-- Call to function with precondition - depends on path condition (assume)
def callWithAssumePgm :=
#strata
program Core;

function safeDiv(x : int, y : int) : int
  requires y != 0;
{ x div y }

procedure test(a : int) returns ()
{
  assume a != 0;
  var z : int := safeDiv(10, a);
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: safeDiv_calls_Int.Div_0
Property: assert
Assumptions:
(precond_safeDiv, (~Bool.Not (y == #0)))
Proof Obligation:
(~Bool.Not (y == #0))

Label: init_calls_safeDiv_0
Property: assert
Assumptions:
(assume_0, (~Bool.Not ($__a0 == #0)))

Proof Obligation:
(~Bool.Not ($__a0 == #0))

---
info: Obligation: safeDiv_calls_Int.Div_0
Property: assert
Result: ✅ pass

Obligation: init_calls_safeDiv_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" callWithAssumePgm

-- Function call inside a quantifier with implication
-- Expression: forall x : int :: x > 0 ==> safeDiv(y, x) > 0
-- The precondition y != 0 should be found inside the quantifier body
def funcInQuantifierPgm :=
#strata
program Core;

function safeDiv(x : int, y : int) : int
  requires y != 0;
{ x div y }

function allPositiveDiv(y : int) : bool
  requires y >= 0;
{ forall x : int :: x > 0 ==> safeDiv(y, x) > 0 }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: safeDiv_calls_Int.Div_0
Property: assert
Assumptions:
(precond_safeDiv, (~Bool.Not (y == #0)))
Proof Obligation:
(~Bool.Not (y == #0))

Label: allPositiveDiv_calls_safeDiv_0
Property: assert
Assumptions:
(precond_allPositiveDiv, ((~Int.Ge y) #0))
Proof Obligation:
(∀ ((~Bool.Implies ((~Int.Gt %0) #0)) (~Bool.Not (%0 == #0))))

---
info: Obligation: safeDiv_calls_Int.Div_0
Property: assert
Result: ✅ pass

Obligation: allPositiveDiv_calls_safeDiv_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" funcInQuantifierPgm

end Strata
