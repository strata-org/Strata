/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.Languages.Boogie.Verifier

namespace Boogie

---------------------------------------------------------------------

section TriggerErrorHandlingTests
open Std (ToFormat Format format)

-- Test 1: Unbound variable in trigger should produce error
def unboundVariableTriggerEnv : Environment :=
#strata
open Boogie;

function f(x : int): int;

axiom [unbound_var_trigger]: forall x : int :: { f(z) } f(x) > 0;
#end

/--
This test should FAIL with an error about unbound variable 'z' in trigger.
Currently it may pass parsing but should fail during trigger validation when implemented.
Expected error: "Unbound variable 'z' in trigger pattern"
-/
/--
error: [Strata.Boogie] Type checking failed.

error: Undefined identifier z
-/
#guard_msgs in
#eval verify "~/Documents/solvers/cvc5" unboundVariableTriggerEnv

-- Test 2: Empty trigger should produce error or be handled gracefully
def emptyTriggerEnv : Environment :=
#strata
open Boogie;

function f(x : int): int;

-- Note: This may not parse correctly with current grammar, but if it does, should be handled
axiom [empty_trigger]: forall x : int :: { } f(x) > 0;
#end

/--
This test should either fail to parse or produce an appropriate error.
Expected: Parse error or "Empty trigger pattern not allowed"
-/
/--
error: [Strata.Boogie] Type checking failed.

error: <input>:6:44: expected expression
-/
#guard_msgs in
#eval verify "~/Documents/solvers/cvc5" emptyTriggerEnv

-- Test 3: Trigger with invalid expression should produce error
def invalidExpressionTriggerEnv : Environment :=
#strata
open Boogie;

function f(x : int): int;

-- Using an undefined function in trigger
axiom [invalid_expr_trigger]: forall x : int :: { undefined_func(x) } f(x) > 0;
#end

/--
This test should FAIL with an error about undefined function in trigger.
Expected error: "Undefined function 'undefined_func' in trigger pattern"
-/
/--
error: [Strata.Boogie] Type checking failed.

error: Undefined identifier undefined_func
-/
#guard_msgs in
#eval verify "~/Documents/solvers/cvc5" invalidExpressionTriggerEnv

-- Test 4: Nested quantifier with incomplete coverage should produce warning
def incompleteCoverageEnv : Environment :=
#strata
open Boogie;

function p(y : int): int;

axiom [incomplete_coverage]: forall x : int :: (forall y : int :: { p(y) } p(y) > x);
#end

/--
This test should pass verification but produce a warning about incomplete variable coverage.
The trigger { p(y) } only covers variable y but not x in the outer quantifier.
Expected warning: "Trigger pattern does not cover all variables: missing coverage for 'x'"
-/
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: incomplete_coverage
Assumptions:
Proof Obligation:
(∀ (∀ ((~Int.Gt (~p %0)) %1)))

Wrote problem to vcs/incomplete_coverage.smt2.
---
info:
Obligation: incomplete_coverage
Result: verified
-/
#guard_msgs in
#eval verify "~/Documents/solvers/cvc5" incompleteCoverageEnv

-- Test 5: Complex trigger expression should work correctly
def complexTriggerEnv : Environment :=
#strata
open Boogie;

function f(x : int): int;
function g(x : int, y : int): int;

axiom [complex_trigger]: forall x : int, y : int :: { f(x + y) } { g(f(x), y) } f(x + y) == g(f(x), y);
#end

/--
This test should pass when triggers are implemented.
It tests complex expressions in triggers including function composition.
Expected: Should generate appropriate SMT2 with complex trigger patterns
-/
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: complex_trigger
Assumptions:
Proof Obligation:
(∀ (∀ (((~Int.Add (~f ((~Int.Add %1) %0))) %0) == ((~g (~f %1)) %0))))

Wrote problem to vcs/complex_trigger.smt2.
---
info:
Obligation: complex_trigger
Result: verified
-/
#guard_msgs in
#eval verify "~/Documents/solvers/cvc5" complexTriggerEnv

-- Test 6: Trigger with boolean expression (edge case)
def booleanTriggerEnv : Environment :=
#strata
open Boogie;

function p(x : int): bool;

axiom [boolean_trigger]: forall x : int :: { p(x) } p(x) ==> x > 0;
#end

/--
This test should pass when triggers are implemented.
It tests triggers with boolean-valued expressions.
Expected: Should generate appropriate SMT2 with boolean trigger pattern
-/
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: boolean_trigger
Assumptions:
Proof Obligation:
(∀ ((~Bool.Implies (~p %0)) ((~Int.Gt %0) #0)))

Wrote problem to vcs/boolean_trigger.smt2.
---
info:
Obligation: boolean_trigger
Result: verified
-/
#guard_msgs in
#eval verify "~/Documents/solvers/cvc5" booleanTriggerEnv

end TriggerErrorHandlingTests

---------------------------------------------------------------------

end Boogie
