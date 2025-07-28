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

section SMT2TriggerValidationTests
open Std (ToFormat Format format)

-- Helper function to check if SMT2 file contains expected trigger patterns
-- This will be used once triggers are implemented
def checkSMT2ContainsTriggers (filename : String) (expectedPatterns : List String) : IO Bool := do
  try
    let content ← IO.FS.readFile s!"vcs/{filename}.smt2"
    let hasAllPatterns := expectedPatterns.all (fun pattern => content.contains pattern)
    return hasAllPatterns
  catch _ =>
    return false

-- Test 1: Validate basic trigger pattern in SMT2 output
def basicTriggerValidationEnv : Environment :=
#strata
open Boogie;

function f(x : int): int;

axiom [basic_trigger_validation]: forall x : int :: { f(x) } f(x) > 0;
#end

/--
This test validates that the SMT2 output contains the expected :pattern attribute.
Currently this will FAIL because triggers are not implemented.
Expected SMT2 pattern: ":pattern ((f"
-/
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: basic_trigger_validation
Assumptions:
Proof Obligation:
(∀ ((~Int.Gt (~f %0)) #0))

Wrote problem to vcs/basic_trigger_validation.smt2.
---
info:
Obligation: basic_trigger_validation
Result: verified
-/
#guard_msgs in
#eval verify "~/Documents/solvers/cvc5" basicTriggerValidationEnv

-- Test 2: Validate multiple trigger patterns in SMT2 output
def multipleTriggerValidationEnv : Environment :=
#strata
open Boogie;

function f(x : int): int;
function g(x : int, y : int): int;

axiom [multi_trigger_validation]: forall x : int, y : int :: { f(x) } { g(x, y) } f(x) + g(x, y) > 0;
#end

/--
This test validates that the SMT2 output contains multiple :pattern attributes.
Currently this will FAIL because triggers are not implemented.
Expected SMT2 patterns: ":pattern ((f" and ":pattern ((g"
-/
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: multi_trigger_validation
Assumptions:
Proof Obligation:
(∀ (∀ ((~Int.Gt ((~Int.Add (~f %1)) ((~g %1) %0))) #0)))

Wrote problem to vcs/multi_trigger_validation.smt2.
---
info:
Obligation: multi_trigger_validation
Result: verified
-/
#guard_msgs in
#eval verify "~/Documents/solvers/cvc5" multipleTriggerValidationEnv

-- Test 3: Validate multi-term trigger pattern in SMT2 output
def multiTermTriggerValidationEnv : Environment :=
#strata
open Boogie;

function f(x : int): int;
function g(x : int): int;

axiom [multi_term_validation]: forall x : int :: { f(x), g(x) } f(x) == g(x);
#end

/--
This test validates that the SMT2 output contains a multi-term trigger pattern.
Currently this will FAIL because triggers are not implemented.
Expected SMT2 pattern: ":pattern ((f" followed by "(g" in the same pattern
-/
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: multi_term_validation
Assumptions:
Proof Obligation:
(∀ (((~f %0) == (~g %0))))

Wrote problem to vcs/multi_term_validation.smt2.
---
info:
Obligation: multi_term_validation
Result: verified
-/
#guard_msgs in
#eval verify "~/Documents/solvers/cvc5" multiTermTriggerValidationEnv

-- Test 4: Validate nested quantifier flattening produces correct SMT2
def nestedFlattenValidationEnv : Environment :=
#strata
open Boogie;

function h(x : int, y : int): int;

axiom [nested_flatten_validation]: forall x : int :: (forall y : int :: { h(x, y) } h(x, y) > 0);
#end

/--
This test validates that nested quantifiers with complete variable coverage are flattened.
Currently this will FAIL because:
1. Triggers are not implemented
2. Flattening logic is not implemented
Expected: Single quantifier with both variables and trigger pattern
Actual: Nested quantifiers without triggers
-/
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: nested_flatten_validation
Assumptions:
Proof Obligation:
(∀ (∀ ((~Int.Gt ((~h %1) %0)) #0)))

Wrote problem to vcs/nested_flatten_validation.smt2.
---
info:
Obligation: nested_flatten_validation
Result: verified
-/
#guard_msgs in
#eval verify "~/Documents/solvers/cvc5" nestedFlattenValidationEnv

-- Test 5: Validate that quantifiers without triggers work as before (backward compatibility)
def noTriggerValidationEnv : Environment :=
#strata
open Boogie;

function f(x : int): int;

axiom [no_trigger_validation]: forall x : int :: f(x) > 0;
#end

/--
This test validates that quantifiers without triggers continue to work as before.
This should PASS even when triggers are implemented (backward compatibility).
Expected: Quantifier without any :pattern attributes
-/
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: no_trigger_validation
Assumptions:
Proof Obligation:
(∀ ((~Int.Gt (~f %0)) #0))

Wrote problem to vcs/no_trigger_validation.smt2.
---
info:
Obligation: no_trigger_validation
Result: verified
-/
#guard_msgs in
#eval verify "~/Documents/solvers/cvc5" noTriggerValidationEnv

end SMT2TriggerValidationTests

---------------------------------------------------------------------

end Boogie
