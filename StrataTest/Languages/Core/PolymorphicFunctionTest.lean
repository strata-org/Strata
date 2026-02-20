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

/-- info: ok: function identity<|$__ty0|> (x : $__ty0) : $__ty0; -/
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
info: ok: function identity<|$__ty0|> (x : $__ty0) : $__ty0;
procedure TestIdentityInt () returns ()
spec {
  ensures [TestIdentityInt_ensures_0]: true;
  } {
  var x : int;
  var y : int;
  x := 42;
  y := identity(x);
  };
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
info: ok: function makePair<|$__ty0|, |$__ty1|> (x : $__ty0, y : $__ty1) : Map $__ty0 $__ty1;
procedure TestMakePair () returns ()
spec {
  ensures [TestMakePair_ensures_0]: true;
  } {
  var m : (Map int bool);
  m := makePair(42, true);
  };
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
info: ok: function apply<|$__ty0|, |$__ty1|> (f : $__ty0 -> $__ty1, x : $__ty0) : $__ty1;
function intToBool (x : int) : bool;
procedure TestApply () returns ()
spec {
  ensures [TestApply_ensures_0]: true;
  } {
  var result : bool;
  result := apply(intToBool, 42);
  };
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
info: ok: function identity<|$__ty0|> (x : $__ty0) : $__ty0;
function makePair<|$__ty1|, |$__ty2|> (x : $__ty1, y : $__ty2) : Map $__ty1 $__ty2;
procedure TestDifferentInstantiations () returns ()
spec {
  ensures [TestDifferentInstantiations_ensures_0]: true;
  } {
  var m : (Map int bool);
  m := makePair(identity(42), identity(true));
  };
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
info: error: (4714-4737) Impossible to unify (arrow int bool) with (arrow bool $__ty5).
First mismatch: int with bool.
-/
#guard_msgs in
#eval (Core.typeCheck Options.quiet (TransM.run Inhabited.default (translateProgram eqTypeMismatchPgm)).fst)

end Strata.PolymorphicFunctionTest
