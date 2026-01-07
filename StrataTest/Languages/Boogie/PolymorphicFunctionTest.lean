/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

/-!
# Polymorphic Function Integration Tests

Tests polymorphic function declarations in Boogie syntax. Verifies:
- Parsing of polymorphic function declarations with type parameters
- Type checking succeeds with correct type parameter instantiation
- Type inference correctly instantiates type parameters from value arguments
- Multiple type parameters work correctly
- Arrow types with type parameters work correctly
- Multiple instantiations in a single term work correctly
- Type unification errors are properly reported

Requirements: 1.1, 1.2, 1.3, 1.4, 5.3, 7.1, 7.4
-/

namespace Strata.PolymorphicFunctionTest

---------------------------------------------------------------------
-- Test 1: Single Type Parameter Function Declaration
---------------------------------------------------------------------

/-- Test that a polymorphic function with a single type parameter can be declared -/
def singleTypeParamDeclPgm : Program :=
#strata
program Boogie;

// Declare a polymorphic identity function
function identity<a>(x : a) : a;

#end

/--
info: ok: func identity : ∀[$__ty0]. ((x : $__ty0)) → $__ty0;
-/
#guard_msgs in
#eval Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram singleTypeParamDeclPgm)).fst

---------------------------------------------------------------------
-- Test 2: Single Type Parameter Function Used in Expression with Int
---------------------------------------------------------------------

/-- Test that a polymorphic function can be called with concrete int type -/
def singleTypeParamIntPgm : Program :=
#strata
program Boogie;

function identity<a>(x : a) : a;

procedure TestIdentityInt() returns ()
spec {
  ensures true;
}
{
  var x : int;
  var y : int;
  x := 42;
  // Call identity with int - type parameter 'a' should be inferred as 'int'
  y := identity(x);
};
#end

/-- info: ok: func identity : ∀[$__ty0]. ((x : $__ty0)) → $__ty0;
(procedure TestIdentityInt :  () → ())
modifies: []
preconditions: 
postconditions: (TestIdentityInt_ensures_0, #true)
body: init (x : int) := (init_x_0 : int)
init (y : int) := (init_y_1 : int)
x := #42
y := ((~identity : (arrow int int)) (x : int))-/
#guard_msgs in
#eval (Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram singleTypeParamIntPgm)).fst)

---------------------------------------------------------------------
-- Test 3: Single Type Parameter Function Used with Bool
---------------------------------------------------------------------

/-- Test that type parameter can be instantiated to bool -/
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
  b := true;
  // Call identity with bool - type parameter 'a' should be inferred as 'bool'
  c := identity(b);
};
#end

/-- info: ok: func identity : ∀[$__ty0]. ((x : $__ty0)) → $__ty0;
(procedure TestIdentityBool :  () → ())
modifies: []
preconditions: 
postconditions: (TestIdentityBool_ensures_0, #true)
body: init (b : bool) := (init_b_0 : bool)
init (c : bool) := (init_c_1 : bool)
b := #true
c := ((~identity : (arrow bool bool)) (b : bool))-/
#guard_msgs in 
#eval (Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram singleTypeParamBoolPgm)).fst)

---------------------------------------------------------------------
-- Test 4: Multiple Type Parameter Function Declaration
---------------------------------------------------------------------

/-- Test that a polymorphic function with multiple type parameters can be declared -/
def multiTypeParamDeclPgm : Program :=
#strata
program Boogie;

// Declare a polymorphic function with two type parameters
function makePair<a, b>(x : a, y : b) : Map a b;

#end

/-- info: ok: func makePair : ∀[$__ty0, $__ty1]. ((x : $__ty0) (y : $__ty1)) → (Map $__ty0 $__ty1);-/
#guard_msgs in
#eval (Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram multiTypeParamDeclPgm)).fst)

---------------------------------------------------------------------
-- Test 5: Multiple Type Parameter Function Used in Expression
---------------------------------------------------------------------

/-- Test that a polymorphic function with multiple type parameters can be called -/
def multiTypeParamUsePgm : Program :=
#strata
program Boogie;

function makePair<a, b>(x : a, y : b) : Map a b;

procedure TestMakePair() returns ()
spec {
  ensures true;
}
{
  var m : Map int bool;
  // Call makePair with int and bool - type parameters should be inferred
  m := makePair(42, true);
};
#end

/-- info: ok: func makePair : ∀[$__ty0, $__ty1]. ((x : $__ty0) (y : $__ty1)) → (Map $__ty0 $__ty1);
(procedure TestMakePair :  () → ())
modifies: []
preconditions: 
postconditions: (TestMakePair_ensures_0, #true)
body: init (m : (Map int bool)) := (init_m_0 : (Map int bool))
m := (((~makePair : (arrow int (arrow bool (Map int bool)))) #42) #true)-/
#guard_msgs in
#eval (Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram multiTypeParamUsePgm)).fst)

---------------------------------------------------------------------
-- Test 6: Polymorphic Function with Arrow Types
---------------------------------------------------------------------

/-- Test that a polymorphic function with arrow types can be declared -/
def arrowTypeParamDeclPgm : Program :=
#strata
program Boogie;

// Declare a polymorphic apply function with arrow type parameter
function apply<a, b>(f : a -> b, x : a) : b;

#end

/-- info: ok: func apply : ∀[$__ty0, $__ty1]. ((f : (arrow $__ty0 $__ty1)) (x : $__ty0)) → $__ty1;-/
#guard_msgs in
#eval (Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram arrowTypeParamDeclPgm)).fst)

---------------------------------------------------------------------
-- Test 7: Polymorphic Function with Arrow Types Used in Expression
---------------------------------------------------------------------

/-- Test that a polymorphic function with arrow types can be called -/
def arrowTypeParamUsePgm : Program :=
#strata
program Boogie;

function apply<a, b>(f : a -> b, x : a) : b;
function intToBool(x : int) : bool;

procedure TestApply() returns ()
spec {
  ensures true;
}
{
  var result : bool;
  // Call apply with a concrete function - type parameters should be inferred
  result := apply(intToBool, 42);
};
#end

/-- info: ok: func apply : ∀[$__ty0, $__ty1]. ((f : (arrow $__ty0 $__ty1)) (x : $__ty0)) → $__ty1;
func intToBool :  ((x : int)) → bool;
(procedure TestApply :  () → ())
modifies: []
preconditions: 
postconditions: (TestApply_ensures_0, #true)
body: init (result : bool) := (init_result_0 : bool)
result := (((~apply : (arrow (arrow int bool) (arrow int bool))) (~intToBool : (arrow int bool))) #42)-/
#guard_msgs in
#eval (Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram arrowTypeParamUsePgm)).fst)

---------------------------------------------------------------------
-- Test 8: Multiple Instantiations in a Single Term
---------------------------------------------------------------------

/-- Test that a polymorphic function can be instantiated multiple times in a single term -/
def multiInstantiationPgm : Program :=
#strata
program Boogie;

function identity<a>(x : a) : a;
function eq<a>(x : a, y : a) : bool;

procedure TestMultiInstantiation() returns ()
spec {
  ensures true;
}
{
  var result : bool;
  // Both identity calls instantiate 'a' to 'int' in one term
  result := eq(identity(42), identity(100));
};
#end

/-- info: ok: func identity : ∀[$__ty0]. ((x : $__ty0)) → $__ty0;
func eq : ∀[$__ty1]. ((x : $__ty1) (y : $__ty1)) → bool;
(procedure TestMultiInstantiation :  () → ())
modifies: []
preconditions: 
postconditions: (TestMultiInstantiation_ensures_0, #true)
body: init (result : bool) := (init_result_0 : bool)
result := (((~eq : (arrow int (arrow int bool))) ((~identity : (arrow int int)) #42)) ((~identity : (arrow int int)) #100))-/
#guard_msgs in
#eval (Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram multiInstantiationPgm)).fst)

---------------------------------------------------------------------
-- Test 9: Different Instantiations in a Single Term
---------------------------------------------------------------------

/-- Test that a polymorphic function can be instantiated to different types in a single term -/
def differentInstantiationsPgm : Program :=
#strata
program Boogie;

function identity<a>(x : a) : a;
function makePair<a, b>(x : a, y : b) : Map a b;

procedure TestDifferentInstantiations() returns ()
spec {
  ensures true;
}
{
  var m : Map int bool;
  // identity is instantiated to both int and bool within the same expression
  m := makePair(identity(42), identity(true));
};
#end

/-- info: ok: func identity : ∀[$__ty0]. ((x : $__ty0)) → $__ty0;
func makePair : ∀[$__ty1, $__ty2]. ((x : $__ty1) (y : $__ty2)) → (Map $__ty1 $__ty2);
(procedure TestDifferentInstantiations :  () → ())
modifies: []
preconditions: 
postconditions: (TestDifferentInstantiations_ensures_0, #true)
body: init (m : (Map int bool)) := (init_m_0 : (Map int bool))
m := (((~makePair : (arrow int (arrow bool (Map int bool)))) ((~identity : (arrow int int)) #42)) ((~identity : (arrow bool bool)) #true))-/
#guard_msgs in
#eval (Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram differentInstantiationsPgm)).fst)

---------------------------------------------------------------------
-- Test 10: Negative Test - Type Unification Failure (eq with different types)
---------------------------------------------------------------------

/-- Test that type checking fails when eq is called with incompatible types -/
def eqTypeMismatchPgm : Program :=
#strata
program Boogie;

function eq<a>(x : a, y : a) : bool;

procedure TestEqTypeMismatch() returns ()
spec {
  ensures true;
}
{
  var result : bool;
  // This should fail: eq<a>(x : a, y : a) requires both args to have same type
  // but 42 is int and true is bool
  result := eq(42, true);
};
#end

/-- info: error: Cannot unify differently named type constructors int and bool!-/
#guard_msgs in
#eval (Boogie.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram eqTypeMismatchPgm)).fst)

end Strata.PolymorphicFunctionTest
