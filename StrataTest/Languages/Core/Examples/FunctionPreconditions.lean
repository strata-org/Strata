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

---
info:
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

function safeHead(xs : List) : int
  requires List..isCons(xs);
{ List..head(xs) }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:

---
info:
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

---
info:
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

---
info:
-/
#guard_msgs in
#eval verify "cvc5" dependentPrecondPgm

-- Function body calls another function with preconditions (Phase 3 test)
-- Expression: safeDiv(safeDiv(x, y), z)
-- This should generate WF obligations for both calls to safeDiv
def funcCallsFuncPgm :=
#strata
program Core;

function safeDiv(x : int, y : int) : int
  requires y != 0;
{ x div y }

function doubleSafeDiv(x : int, y : int, z : int) : int
  requires y != 0;
  requires z != 0;
{ safeDiv(safeDiv(x, y), z) }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: doubleSafeDiv_calls_safeDiv_0
Property: assert
Assumptions:
(precond_doubleSafeDiv, (~Bool.Not (y == #0)))
(precond_doubleSafeDiv, (~Bool.Not (z == #0)))
Proof Obligation:
(~Bool.Not (z == #0))

Label: doubleSafeDiv_calls_safeDiv_1
Property: assert
Assumptions:
(precond_doubleSafeDiv, (~Bool.Not (y == #0)))
(precond_doubleSafeDiv, (~Bool.Not (z == #0)))
Proof Obligation:
(~Bool.Not (y == #0))

---
info:
Obligation: doubleSafeDiv_calls_safeDiv_0
Property: assert
Result: ✅ pass

Obligation: doubleSafeDiv_calls_safeDiv_1
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

function safeDiv(x : int, y : int) : int
  requires y != 0;
{ x div y }

function badDiv(x : int) : int
{ safeDiv(x, 0) }

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: badDiv_calls_safeDiv_0
Property: assert
Assumptions:

Proof Obligation:
(~Bool.Not (#0 == #0))



Result: Obligation: badDiv_calls_safeDiv_0
Property: assert
Result: ❌ fail


Evaluated program:
func safeDiv :  ((x : int) (y : int)) → int
  requires ((~Bool.Not : (arrow bool bool)) ((y : int) == #0)) :=
  ((((~Int.Div : (arrow int (arrow int int))) (x : int)) (y : int)))
func badDiv :  ((x : int)) → int :=
  ((((~safeDiv : (arrow int (arrow int int))) (x : int)) #0))
---
info:
Obligation: badDiv_calls_safeDiv_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify "cvc5" funcCallsFuncFailPgm

-- Call to function with precondition - unconditionally true
def callUnconditionalPgm :=
#strata
program Core;

function safeDiv(x : int, y : int) : int
  requires y != 0;
{ x div y }

procedure test() returns ()
{
  var z : int := safeDiv(10, 2);
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: init_calls_safeDiv_0
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not (#2 == #0))

---
info: Obligation: init_calls_safeDiv_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" callUnconditionalPgm

-- Call to function with precondition - depends on path condition (if)
def callWithIfPgm :=
#strata
program Core;

function safeDiv(x : int, y : int) : int
  requires y != 0;
{ x div y }

procedure test(a : int) returns ()
{
  var z : int;
  if (a > 0) {
    z := safeDiv(10, a);
  } else {
  }
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: set_z_calls_safeDiv_0
Property: assert
Assumptions:
(<label_ite_cond_true: ((~Int.Gt a) #0)>, ((~Int.Gt $__a0) #0))


Proof Obligation:
(~Bool.Not ($__a0 == #0))

---
info: Obligation: set_z_calls_safeDiv_0
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
Label: init_calls_safeDiv_0
Property: assert
Assumptions:
(assume_0, (~Bool.Not ($__a0 == #0)))

Proof Obligation:
(~Bool.Not ($__a0 == #0))

---
info: Obligation: init_calls_safeDiv_0
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
Label: allPositiveDiv_calls_safeDiv_0
Property: assert
Assumptions:
(precond_allPositiveDiv, ((~Int.Ge y) #0))
Proof Obligation:
(∀ ((~Bool.Implies ((~Int.Gt %0) #0)) (~Bool.Not (%0 == #0))))

---
info:
Obligation: allPositiveDiv_calls_safeDiv_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" funcInQuantifierPgm

end Strata
