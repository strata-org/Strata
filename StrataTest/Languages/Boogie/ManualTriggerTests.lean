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

section ManualTriggerTests
open Std (ToFormat Format format)
open Lambda.LTy.Syntax Lambda.LExpr.Syntax Boogie.Syntax

-- Test 1: Basic trigger translation that currently fails
def basicTriggerEnv : Environment :=
#strata
open Boogie;

function f(x : int): int;

axiom [basic_trigger]: forall x : int :: { f(x) } f(x) > 0;

procedure TestBasicTrigger(x : int) returns (r : int)
spec {
  ensures r > 0;
}
{
  r := f(x);
};
#end

/--
This test should pass when triggers are implemented.
Currently it will pass verification but the SMT2 output will NOT contain :pattern attributes.
The generated SMT2 should contain: (forall ((x Int)) (! (> (f x) 0) :pattern ((f x))))
But currently generates: (forall ((x Int)) (> (f x) 0))
-/
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: basic_trigger
Assumptions:
Proof Obligation:
(∀ ((~Int.Gt (~f %0)) #0))

Label: TestBasicTrigger_ensures_0
Assumptions:
(basic_trigger, (∀ ((~Int.Gt (~f %0)) #0)))
Proof Obligation:
((~Int.Gt (~f $__x0)) #0)

Wrote problem to vcs/basic_trigger.smt2.
Wrote problem to vcs/TestBasicTrigger_ensures_0.smt2.
---
info:
Obligation: basic_trigger
Result: verified

Obligation: TestBasicTrigger_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "~/Documents/solvers/cvc5" basicTriggerEnv

-- Test 2: Multiple trigger patterns
def multipleTriggerEnv : Environment :=
#strata
open Boogie;

function f(x : int): int;
function g(x : int, y : int): int;

axiom [multi_trigger]: forall x : int, y : int :: { f(x) } { g(x, y) } f(x) + g(x, y) > 0;

procedure TestMultipleTriggers(x : int, y : int) returns (r : int)
spec {
  ensures r > 0;
}
{
  r := f(x) + g(x, y);
};
#end

/--
This test should pass when triggers are implemented.
The generated SMT2 should contain multiple :pattern attributes:
(forall ((x Int) (y Int)) (! (> (+ (f x) (g x y)) 0) :pattern ((f x)) :pattern ((g x y))))
But currently generates: (forall ((x Int) (y Int)) (> (+ (f x) (g x y)) 0))
-/
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: multi_trigger
Assumptions:
Proof Obligation:
(∀ (∀ ((~Int.Gt ((~Int.Add (~f %1)) ((~g %1) %0))) #0)))

Label: TestMultipleTriggers_ensures_0
Assumptions:
(multi_trigger, (∀ (∀ ((~Int.Gt ((~Int.Add (~f %1)) ((~g %1) %0))) #0))))
Proof Obligation:
((~Int.Gt ((~Int.Add (~f $__x0)) ((~g $__x0) $__y1))) #0)

Wrote problem to vcs/multi_trigger.smt2.
Wrote problem to vcs/TestMultipleTriggers_ensures_0.smt2.
---
info:
Obligation: multi_trigger
Result: verified

Obligation: TestMultipleTriggers_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "~/Documents/solvers/cvc5" multipleTriggerEnv

-- Test 3: Multi-term trigger pattern
def multiTermTriggerEnv : Environment :=
#strata
open Boogie;

function f(x : int): int;
function g(x : int): int;

axiom [multi_term_trigger]: forall x : int :: { f(x), g(x) } f(x) == g(x);

procedure TestMultiTermTrigger(x : int) returns (r : bool)
spec {
  ensures r == true;
}
{
  r := (f(x) == g(x));
};
#end

/--
This test should pass when triggers are implemented.
The generated SMT2 should contain a multi-term pattern:
(forall ((x Int)) (! (= (f x) (g x)) :pattern ((f x) (g x))))
But currently generates: (forall ((x Int)) (= (f x) (g x)))
-/
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: multi_term_trigger
Assumptions:
Proof Obligation:
(∀ (((~f %0) == (~g %0))))

Label: TestMultiTermTrigger_ensures_0
Assumptions:
(multi_term_trigger, (∀ (((~f %0) == (~g %0)))))
Proof Obligation:
((((~f $__x0) == (~g $__x0)) == #true))

Wrote problem to vcs/multi_term_trigger.smt2.
Wrote problem to vcs/TestMultiTermTrigger_ensures_0.smt2.
---
info:
Obligation: multi_term_trigger
Result: verified

Obligation: TestMultiTermTrigger_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "~/Documents/solvers/cvc5" multiTermTriggerEnv

-- Test 4: Nested quantifier flattening test - should flatten
def nestedQuantifierFlattenEnv : Environment :=
#strata
open Boogie;

function h(x : int, y : int): int;

axiom [nested_flatten]: forall x : int :: (forall y : int :: { h(x, y) } h(x, y) > x + y);

procedure TestNestedFlattening(x : int, y : int) returns (r : int)
spec {
  ensures r > x + y;
}
{
  r := h(x, y);
};
#end

/--
This test should pass when triggers are implemented with flattening.
Since the inner trigger { h(x, y) } covers both variables x and y, the nested quantifiers should be flattened.
The generated SMT2 should contain:
(forall ((x Int) (y Int)) (! (> (h x y) (+ x y)) :pattern ((h x y))))
But currently generates nested quantifiers without triggers:
(forall ((x Int)) (forall ((y Int)) (> (h x y) (+ x y))))
-/
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: nested_flatten
Assumptions:
Proof Obligation:
(∀ (∀ ((~Int.Gt ((~h %1) %0)) ((~Int.Add %1) %0))))

Label: TestNestedFlattening_ensures_0
Assumptions:
(nested_flatten, (∀ (∀ ((~Int.Gt ((~h %1) %0)) ((~Int.Add %1) %0)))))
Proof Obligation:
((~Int.Gt ((~h $__x0) $__y1)) ((~Int.Add $__x0) $__y1))

Wrote problem to vcs/nested_flatten.smt2.
Wrote problem to vcs/TestNestedFlattening_ensures_0.smt2.
---
info:
Obligation: nested_flatten
Result: verified

Obligation: TestNestedFlattening_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "~/Documents/solvers/cvc5" nestedQuantifierFlattenEnv

-- Test 5: Nested quantifier that should NOT flatten (incomplete coverage)
def nestedQuantifierNoFlattenEnv : Environment :=
#strata
open Boogie;

function p(y : int): int;

axiom [nested_no_flatten]: forall x : int :: (forall y : int :: { p(y) } p(y) > x);

procedure TestNestedNoFlattening(x : int, y : int) returns (r : int)
spec {
  ensures r > x;
}
{
  r := p(y);
};
#end

/--
This test should pass when triggers are implemented but should NOT flatten.
Since the inner trigger { p(y) } only covers variable y but not x, the nested structure should be preserved.
The generated SMT2 should contain:
(forall ((x Int)) (forall ((y Int)) (! (> (p y) x) :pattern ((p y)))))
And should generate a warning about incomplete variable coverage.
But currently generates: (forall ((x Int)) (forall ((y Int)) (> (p y) x)))
-/
#guard_msgs in
#eval verify "~/Documents/solvers/cvc5" nestedQuantifierNoFlattenEnv

end ManualTriggerTests

---------------------------------------------------------------------

end Boogie
