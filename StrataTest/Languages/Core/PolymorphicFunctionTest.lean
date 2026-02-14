/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Polymorphic Function Integration Tests

Tests polymorphic function declarations in Core syntax, including parsing,
typechecking, and type inference.
-/

namespace Strata.PolymorphicFunctionTest

---------------------------------------------------------------------
-- Test 1: Single Type Parameter Function Declaration
---------------------------------------------------------------------

def singleTypeParamDeclPgm : Program :=
#strata
program Core;

function identity<a>(x : a) : a;

#end

/--
info: ok: func identity : ∀[$__ty0]. ((x : $__ty0)) → $__ty0;
-/
#guard_msgs in
#eval Core.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram singleTypeParamDeclPgm)).fst

---------------------------------------------------------------------
-- Test 2: Single Type Parameter Function Concrete Instantiation
---------------------------------------------------------------------

def singleTypeParamIntPgm : Program :=
#strata
program Core;

function identity<a>(x : a) : a;

procedure TestIdentityInt() returns ()
spec {
  ensures true;
}
{
  var x : int;
  var y : int;
  x := 42;
  y := identity(x);
};
#end

/--
info: ok: func identity : ∀[$__ty0]. ((x : $__ty0)) → $__ty0;
procedure TestIdentityInt :  () → ()
  modifies: []
  preconditions: ⏎
  postconditions: (TestIdentityInt_ensures_0, #true)
{
  {
    init (x : int) := (init_x_0 : int)
    init (y : int) := (init_y_1 : int)
    x := #42
    y := ((~identity : (arrow int int)) (x : int))
  }
}
-/
#guard_msgs in
#eval (Core.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram singleTypeParamIntPgm)).fst)

---------------------------------------------------------------------
-- Test 3: Multiple Type Parameter Function Used in Expression
---------------------------------------------------------------------

def multiTypeParamUsePgm : Program :=
#strata
program Core;

function makePair<a, b>(x : a, y : b) : Map a b;

procedure TestMakePair() returns ()
spec {
  ensures true;
}
{
  var m : Map int bool;
  m := makePair(42, true);
};
#end

/--
info: ok: func makePair : ∀[$__ty0, $__ty1]. ((x : $__ty0) (y : $__ty1)) → (Map $__ty0 $__ty1);
procedure TestMakePair :  () → ()
  modifies: []
  preconditions: ⏎
  postconditions: (TestMakePair_ensures_0, #true)
{
  {
    init (m : (Map int bool)) := (init_m_0 : (Map int bool))
    m := ((~makePair : (arrow int (arrow bool (Map int bool)))) #42 #true)
  }
}
-/
#guard_msgs in
#eval (Core.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram multiTypeParamUsePgm)).fst)

---------------------------------------------------------------------
-- Test 4: Polymorphic Function with Arrow Types Used in Expression
---------------------------------------------------------------------

def arrowTypeParamUsePgm : Program :=
#strata
program Core;

function apply<a, b>(f : a -> b, x : a) : b;
function intToBool(x : int) : bool;

procedure TestApply() returns ()
spec {
  ensures true;
}
{
  var result : bool;
  result := apply(intToBool, 42);
};
#end

/--
info: ok: func apply : ∀[$__ty0, $__ty1]. ((f : (arrow $__ty0 $__ty1)) (x : $__ty0)) → $__ty1;
func intToBool :  ((x : int)) → bool;
procedure TestApply :  () → ()
  modifies: []
  preconditions: ⏎
  postconditions: (TestApply_ensures_0, #true)
{
  {
    init (result : bool) := (init_result_0 : bool)
    result := ((~apply : (arrow (arrow int bool) (arrow int bool))) (~intToBool : (arrow int bool)) #42)
  }
}
-/
#guard_msgs in
#eval (Core.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram arrowTypeParamUsePgm)).fst)

---------------------------------------------------------------------
-- Test 5: Different Instantiations in a Single Term
---------------------------------------------------------------------

def differentInstantiationsPgm : Program :=
#strata
program Core;

function identity<a>(x : a) : a;
function makePair<a, b>(x : a, y : b) : Map a b;

procedure TestDifferentInstantiations() returns ()
spec {
  ensures true;
}
{
  var m : Map int bool;
  m := makePair(identity(42), identity(true));
};
#end

/--
info: ok: func identity : ∀[$__ty0]. ((x : $__ty0)) → $__ty0;
func makePair : ∀[$__ty1, $__ty2]. ((x : $__ty1) (y : $__ty2)) → (Map $__ty1 $__ty2);
procedure TestDifferentInstantiations :  () → ()
  modifies: []
  preconditions: ⏎
  postconditions: (TestDifferentInstantiations_ensures_0, #true)
{
  {
    init (m : (Map int bool)) := (init_m_0 : (Map int bool))
    m := ((~makePair : (arrow int (arrow bool (Map int bool))))
     ((~identity : (arrow int int)) #42)
     ((~identity : (arrow bool bool)) #true))
  }
}
-/
#guard_msgs in
#eval (Core.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram differentInstantiationsPgm)).fst)

---------------------------------------------------------------------
-- Test 6: Negative Test - Type Unification Failure (eq with different types)
---------------------------------------------------------------------

def eqTypeMismatchPgm : Program :=
#strata
program Core;

function eq<a>(x : a, y : a) : bool;

procedure TestEqTypeMismatch() returns ()
spec {
  ensures true;
}
{
  var result : bool;
  result := eq(42, true);
};
#end

/--
info: error: (5305-5328) Impossible to unify (arrow int bool) with (arrow bool $__ty6).
First mismatch: int with bool.
-/
#guard_msgs in
#eval (Core.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram eqTypeMismatchPgm)).fst)

end Strata.PolymorphicFunctionTest
