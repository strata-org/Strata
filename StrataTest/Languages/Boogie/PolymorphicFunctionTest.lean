/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

/-!
# Polymorphic Function Integration Tests

Tests polymorphic function declarations in Boogie using the DDM syntax.
Verifies:
- Parsing of polymorphic function declarations with type parameters
- Type checking succeeds with type inference for polymorphic function calls
- Multiple type parameters work correctly
- Arrow types with type parameters work correctly
- Multiple instantiations of the same polymorphic function in a single term
-/

namespace Strata.PolymorphicFunctionTest

---------------------------------------------------------------------
-- Test 4.2: Single Type Parameter Function in Expressions
---------------------------------------------------------------------

/--
Test: Declare `function identity<a>(x : a) : a` and use it with concrete type.
Verifies type inference correctly instantiates `a` to `int`.
-/
def singleTypeParamPgm : Program :=
#strata
program Boogie;

// Polymorphic identity function with single type parameter
function identity<a>(x : a) : a;

procedure TestIdentity() returns ()
spec {
  ensures true;
}
{
  var x : int;
  var y : int;

  // Use identity with int - type parameter 'a' should be inferred as 'int'
  x := 42;
  y := identity(x);

  // Assert the identity function returns its input
  assert [identity_preserves]: y == x;

  // Direct call with literal
  assert [identity_literal]: identity(100) == 100;
};
#end

def singleTypeParamBoogie := TransM.run Inhabited.default (translateProgram singleTypeParamPgm)

/-- info: true -/
#guard_msgs in
#eval singleTypeParamBoogie.snd.isEmpty

/-- info: ok: func identity : ∀[a]. ((x : a)) → a;
(procedure TestIdentity :  () → ())
modifies: []
preconditions: 
postconditions: (TestIdentity_ensures_0, #true)
body: init (x : int) := (init_x_0 : int)
init (y : int) := (init_y_1 : int)
x := #42
y := ((~identity : (arrow int int)) (x : int))
assert [identity_preserves] ((y : int) == (x : int))
assert [identity_literal] (((~identity : (arrow int int)) #100) == #100) -/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet singleTypeParamBoogie.fst

---------------------------------------------------------------------
-- Test 4.2 (continued): Single Type Parameter with Bool
---------------------------------------------------------------------

/--
Test: Use identity function with bool type.
Verifies type inference works for different concrete types.
-/
def singleTypeParamBoolPgm : Program :=
#strata
program Boogie;

function identity<a>(x : a) : a;

procedure TestIdentityBool() returns ()
spec {
  ensures true;
}
{
  var b : bool;
  var c : bool;

  // Use identity with bool - type parameter 'a' should be inferred as 'bool'
  b := true;
  c := identity(b);

  assert [identity_bool]: c == b;
  assert [identity_true]: identity(true) == true;
  assert [identity_false]: identity(false) == false;
};
#end

def singleTypeParamBoolBoogie := TransM.run Inhabited.default (translateProgram singleTypeParamBoolPgm)

/-- info: true -/
#guard_msgs in
#eval singleTypeParamBoolBoogie.snd.isEmpty

/-- info: ok: func identity : ∀[a]. ((x : a)) → a;
(procedure TestIdentityBool :  () → ())
modifies: []
preconditions: 
postconditions: (TestIdentityBool_ensures_0, #true)
body: init (b : bool) := (init_b_0 : bool)
init (c : bool) := (init_c_1 : bool)
b := #true
c := ((~identity : (arrow bool bool)) (b : bool))
assert [identity_bool] ((c : bool) == (b : bool))
assert [identity_true] (((~identity : (arrow bool bool)) #true) == #true)
assert [identity_false] (((~identity : (arrow bool bool)) #false) == #false) -/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet singleTypeParamBoolBoogie.fst

---------------------------------------------------------------------
-- Test 4.3: Multiple Type Parameter Function in Expressions
---------------------------------------------------------------------

/--
Test: Declare functions with multiple type parameters and use with concrete types.
-/
def multiTypeParamPgm : Program :=
#strata
program Boogie;

// Function that takes two type parameters and returns the first argument
function first<a, b>(x : a, y : b) : a;

// Function that takes two type parameters and returns the second argument
function second<a, b>(x : a, y : b) : b;

procedure TestMultiTypeParam() returns ()
spec {
  ensures true;
}
{
  var i : int;
  var b : bool;
  var r1 : int;
  var r2 : bool;

  i := 42;
  b := true;

  // Use first with (int, bool) - should return int
  r1 := first(i, b);
  assert [first_returns_int]: r1 == i;

  // Use second with (int, bool) - should return bool
  r2 := second(i, b);
  assert [second_returns_bool]: r2 == b;

  // Direct calls with literals
  assert [first_literal]: first(100, false) == 100;
  assert [second_literal]: second(100, false) == false;
};
#end

def multiTypeParamBoogie := TransM.run Inhabited.default (translateProgram multiTypeParamPgm)

/-- info: true -/
#guard_msgs in
#eval multiTypeParamBoogie.snd.isEmpty

/-- info: ok: func first : ∀[a, b]. ((x : a) (y : b)) → a;
func second : ∀[a, b]. ((x : a) (y : b)) → b;
(procedure TestMultiTypeParam :  () → ())
modifies: []
preconditions: 
postconditions: (TestMultiTypeParam_ensures_0, #true)
body: init (i : int) := (init_i_0 : int)
init (b : bool) := (init_b_1 : bool)
init (r1 : int) := (init_r1_2 : int)
init (r2 : bool) := (init_r2_3 : bool)
i := #42
b := #true
r1 := (((~first : (arrow int (arrow bool int))) (i : int)) (b : bool))
assert [first_returns_int] ((r1 : int) == (i : int))
r2 := (((~second : (arrow int (arrow bool bool))) (i : int)) (b : bool))
assert [second_returns_bool] ((r2 : bool) == (b : bool))
assert [first_literal] ((((~first : (arrow int (arrow bool int))) #100) #false) == #100)
assert [second_literal] ((((~second : (arrow int (arrow bool bool))) #100) #false) == #false) -/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet multiTypeParamBoogie.fst

---------------------------------------------------------------------
-- Test 4.3 (continued): Multiple Type Parameters with Same Type
---------------------------------------------------------------------

/--
Test: Use multi-param function where both type parameters are the same.
-/
def multiTypeParamSameTypePgm : Program :=
#strata
program Boogie;

function first<a, b>(x : a, y : b) : a;
function second<a, b>(x : a, y : b) : b;

procedure TestMultiTypeParamSameType() returns ()
spec {
  ensures true;
}
{
  var x : int;
  var y : int;
  var r1 : int;
  var r2 : int;

  x := 10;
  y := 20;

  // Both type parameters instantiated to int
  r1 := first(x, y);
  r2 := second(x, y);

  assert [first_same_type]: r1 == x;
  assert [second_same_type]: r2 == y;
};
#end

def multiTypeParamSameTypeBoogie := TransM.run Inhabited.default (translateProgram multiTypeParamSameTypePgm)

/-- info: true -/
#guard_msgs in
#eval multiTypeParamSameTypeBoogie.snd.isEmpty

/-- info: ok: func first : ∀[a, b]. ((x : a) (y : b)) → a;
func second : ∀[a, b]. ((x : a) (y : b)) → b;
(procedure TestMultiTypeParamSameType :  () → ())
modifies: []
preconditions: 
postconditions: (TestMultiTypeParamSameType_ensures_0, #true)
body: init (x : int) := (init_x_0 : int)
init (y : int) := (init_y_1 : int)
init (r1 : int) := (init_r1_2 : int)
init (r2 : int) := (init_r2_3 : int)
x := #10
y := #20
r1 := (((~first : (arrow int (arrow int int))) (x : int)) (y : int))
r2 := (((~second : (arrow int (arrow int int))) (x : int)) (y : int))
assert [first_same_type] ((r1 : int) == (x : int))
assert [second_same_type] ((r2 : int) == (y : int)) -/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet multiTypeParamSameTypeBoogie.fst

---------------------------------------------------------------------
-- Test 4.4: Polymorphic Function with Arrow Types
---------------------------------------------------------------------

/--
Test: Declare `function apply<a, b>(f : a -> b, x : a) : b`.
Uses a higher-order polymorphic function with arrow types.
-/
def arrowTypePgm : Program :=
#strata
program Boogie;

// Higher-order polymorphic function
function apply<a, b>(f : a -> b, x : a) : b;

// A concrete function to use with apply
function inc(x : int) : int;
axiom forall x : int :: inc(x) == x + 1;

// Another concrete function
function isPositive(x : int) : bool;
axiom forall x : int :: isPositive(x) == (x > 0);

procedure TestApply() returns ()
spec {
  ensures true;
}
{
  var x : int;
  var y : int;
  var b : bool;

  x := 5;

  // Apply inc to x - type params: a=int, b=int
  y := apply(inc, x);
  assert [apply_inc]: y == 6;

  // Apply isPositive to x - type params: a=int, b=bool
  b := apply(isPositive, x);
  assert [apply_isPositive]: b == true;
};
#end

def arrowTypeBoogie := TransM.run Inhabited.default (translateProgram arrowTypePgm)

/-- info: true -/
#guard_msgs in
#eval arrowTypeBoogie.snd.isEmpty

/-- info: ok: func apply : ∀[a, b]. ((f : (arrow a b)) (x : a)) → b;
func inc :  ((x : int)) → int;
axiom axiom_0: (∀ (((~inc : (arrow int int)) %0) == (((~Int.Add : (arrow int (arrow int int))) %0) #1)));
func isPositive :  ((x : int)) → bool;
axiom axiom_1: (∀ (((~isPositive : (arrow int bool)) %0) == (((~Int.Gt : (arrow int (arrow int bool))) %0) #0)));
(procedure TestApply :  () → ())
modifies: []
preconditions: 
postconditions: (TestApply_ensures_0, #true)
body: init (x : int) := (init_x_0 : int)
init (y : int) := (init_y_1 : int)
init (b : bool) := (init_b_2 : bool)
x := #5
y := (((~apply : (arrow (arrow int int) (arrow int int))) (~inc : (arrow int int))) (x : int))
assert [apply_inc] ((y : int) == #6)
b := (((~apply : (arrow (arrow int bool) (arrow int bool))) (~isPositive : (arrow int bool))) (x : int))
assert [apply_isPositive] ((b : bool) == #true) -/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet arrowTypeBoogie.fst

---------------------------------------------------------------------
-- Test 4.4 (continued): Compose with Arrow Types
---------------------------------------------------------------------

/--
Test: Function composition with three type parameters.
-/
def composePgm : Program :=
#strata
program Boogie;

// Function composition: (b -> c) -> (a -> b) -> a -> c
function compose<a, b, c>(g : b -> c, f : a -> b, x : a) : c;

function double(x : int) : int;
axiom forall x : int :: double(x) == x * 2;

function isEven(x : int) : bool;
axiom forall x : int :: isEven(x) == (x mod 2 == 0);

procedure TestCompose() returns ()
spec {
  ensures true;
}
{
  var x : int;
  var b : bool;

  x := 3;

  // compose(isEven, double, x) should check if double(x) is even
  // double(3) = 6, isEven(6) = true
  b := compose(isEven, double, x);
  assert [compose_result]: b == true;
};
#end

def composeBoogie := TransM.run Inhabited.default (translateProgram composePgm)

/-- info: true -/
#guard_msgs in
#eval composeBoogie.snd.isEmpty

/-- info: ok: func compose : ∀[a, b, c]. ((g : (arrow b c)) (f : (arrow a b)) (x : a)) → c;
func double :  ((x : int)) → int;
axiom axiom_0: (∀ (((~double : (arrow int int)) %0) == (((~Int.Mul : (arrow int (arrow int int))) %0) #2)));
func isEven :  ((x : int)) → bool;
axiom axiom_1: (∀ (((~isEven : (arrow int bool)) %0) == ((((~Int.Mod : (arrow int (arrow int int))) %0) #2) == #0)));
(procedure TestCompose :  () → ())
modifies: []
preconditions: 
postconditions: (TestCompose_ensures_0, #true)
body: init (x : int) := (init_x_0 : int)
init (b : bool) := (init_b_1 : bool)
x := #3
b := ((((~compose : (arrow (arrow int bool) (arrow (arrow int int) (arrow int bool)))) (~isEven : (arrow int bool))) (~double : (arrow int int))) (x : int))
assert [compose_result] ((b : bool) == #true) -/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet composeBoogie.fst

---------------------------------------------------------------------
-- Test 4.5: Multiple Instantiations in a Single Term
---------------------------------------------------------------------

/--
Test: Multiple instantiations of the same polymorphic function in one expression.
Both `identity` calls instantiate `a` to `int` in one term.
-/
def multipleInstantiationsSameTypePgm : Program :=
#strata
program Boogie;

function identity<a>(x : a) : a;

// Polymorphic equality function
function eq<a>(x : a, y : a) : bool;
axiom forall x : int, y : int :: eq(x, y) == (x == y);
axiom forall x : bool, y : bool :: eq(x, y) == (x == y);

procedure TestMultipleInstantiations() returns ()
spec {
  ensures true;
}
{
  var b : bool;

  // eq(identity(42), identity(100)) - both identity calls use a=int
  b := eq(identity(42), identity(100));
  assert [eq_different_ints]: b == false;

  // eq(identity(42), identity(42)) - same value
  b := eq(identity(42), identity(42));
  assert [eq_same_ints]: b == true;
};
#end

def multipleInstantiationsSameTypeBoogie := TransM.run Inhabited.default (translateProgram multipleInstantiationsSameTypePgm)

/-- info: true -/
#guard_msgs in
#eval multipleInstantiationsSameTypeBoogie.snd.isEmpty

/-- info: ok: func identity : ∀[a]. ((x : a)) → a;
func eq : ∀[a]. ((x : a) (y : a)) → bool;
axiom axiom_0: (∀ (∀ ((((~eq : (arrow int (arrow int bool))) %1) %0) == (%1 == %0))));
axiom axiom_1: (∀ (∀ ((((~eq : (arrow bool (arrow bool bool))) %1) %0) == (%1 == %0))));
(procedure TestMultipleInstantiations :  () → ())
modifies: []
preconditions: 
postconditions: (TestMultipleInstantiations_ensures_0, #true)
body: init (b : bool) := (init_b_0 : bool)
b := (((~eq : (arrow int (arrow int bool))) ((~identity : (arrow int int)) #42)) ((~identity : (arrow int int)) #100))
assert [eq_different_ints] ((b : bool) == #false)
b := (((~eq : (arrow int (arrow int bool))) ((~identity : (arrow int int)) #42)) ((~identity : (arrow int int)) #42))
assert [eq_same_ints] ((b : bool) == #true)-/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet multipleInstantiationsSameTypeBoogie.fst

---------------------------------------------------------------------
-- Test 4.5 (continued): Multiple Instantiations with Different Types
---------------------------------------------------------------------

/--
Test: Multiple instantiations of the same polymorphic function with different types
in the same expression.
-/
def multipleInstantiationsDifferentTypesPgm : Program :=
#strata
program Boogie;

function identity<a>(x : a) : a;
function first<a, b>(x : a, y : b) : a;
function second<a, b>(x : a, y : b) : b;

procedure TestMultipleInstantiationsDifferentTypes() returns ()
spec {
  ensures true;
}
{
  var i : int;
  var b : bool;

  // first(identity(42), identity(true))
  // - outer first: a=int, b=bool
  // - first identity: a=int
  // - second identity: a=bool
  i := first(identity(42), identity(true));
  assert [first_mixed]: i == 42;

  // second(identity(42), identity(true))
  b := second(identity(42), identity(true));
  assert [second_mixed]: b == true;
};
#end

def multipleInstantiationsDifferentTypesBoogie := TransM.run Inhabited.default (translateProgram multipleInstantiationsDifferentTypesPgm)

/-- info: true -/
#guard_msgs in
#eval multipleInstantiationsDifferentTypesBoogie.snd.isEmpty

/-- info: ok: func identity : ∀[a]. ((x : a)) → a;
func first : ∀[a, b]. ((x : a) (y : b)) → a;
func second : ∀[a, b]. ((x : a) (y : b)) → b;
(procedure TestMultipleInstantiationsDifferentTypes :  () → ())
modifies: []
preconditions: 
postconditions: (TestMultipleInstantiationsDifferentTypes_ensures_0, #true)
body: init (i : int) := (init_i_0 : int)
init (b : bool) := (init_b_1 : bool)
i := (((~first : (arrow int (arrow bool int))) ((~identity : (arrow int int)) #42)) ((~identity : (arrow bool bool)) #true))
assert [first_mixed] ((i : int) == #42)
b := (((~second : (arrow int (arrow bool bool))) ((~identity : (arrow int int)) #42)) ((~identity : (arrow bool bool)) #true))
assert [second_mixed] ((b : bool) == #true)-/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet multipleInstantiationsDifferentTypesBoogie.fst

---------------------------------------------------------------------
-- Test 4.5 (continued): Nested Polymorphic Calls
---------------------------------------------------------------------

/--
Test: Nested polymorphic function calls.
-/
def nestedPolymorphicPgm : Program :=
#strata
program Boogie;

function identity<a>(x : a) : a;

procedure TestNestedPolymorphic() returns ()
spec {
  ensures true;
}
{
  var x : int;
  var b : bool;

  // identity(identity(identity(42))) - nested calls all with a=int
  x := identity(identity(identity(42)));
  assert [nested_int]: x == 42;

  // identity(identity(true)) - nested calls with a=bool
  b := identity(identity(true));
  assert [nested_bool]: b == true;
};
#end

def nestedPolymorphicBoogie := TransM.run Inhabited.default (translateProgram nestedPolymorphicPgm)

/-- info: true -/
#guard_msgs in
#eval nestedPolymorphicBoogie.snd.isEmpty

/-- info: ok: func identity : ∀[a]. ((x : a)) → a;
(procedure TestNestedPolymorphic :  () → ())
modifies: []
preconditions: 
postconditions: (TestNestedPolymorphic_ensures_0, #true)
body: init (x : int) := (init_x_0 : int)
init (b : bool) := (init_b_1 : bool)
x := ((~identity : (arrow int int)) ((~identity : (arrow int int)) ((~identity : (arrow int int)) #42)))
assert [nested_int] ((x : int) == #42)
b := ((~identity : (arrow bool bool)) ((~identity : (arrow bool bool)) #true))
assert [nested_bool] ((b : bool) == #true)-/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet nestedPolymorphicBoogie.fst

end Strata.PolymorphicFunctionTest
