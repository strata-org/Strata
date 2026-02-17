/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DDM.Integration.Lean

/-!
# Tests for @[declareTVar] annotation

Tests that type variables declared via `@[declareTVar]` are properly
brought into scope via `@[scope]`.
-/

#dialect
dialect TestDeclareTVar;

type bool;
type int;
type Map (k : Type, v : Type);

fn trueExpr : bool => "true";
fn intLit (n : Num) : int => n;

category TypeVar;
@[declareTVar(name)]
op type_var (name : Ident) : TypeVar => name;

category TypeArgs;
@[scope(args)]
op type_args (args : CommaSepBy TypeVar) : TypeArgs => "<" args ">";

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] name ":" tp;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

@[declareFn(name, b, r)]
op command_fndecl (name : Ident,
                   typeArgs : Option TypeArgs,
                   @[scope(typeArgs)] b : Bindings,
                   @[scope(typeArgs)] r : Type) : Command =>
  "function " name typeArgs b " : " r ";\n";

#end

---------------------------------------------------------------------
-- Test 1: Single type parameter
---------------------------------------------------------------------

def singleTypeParamPgm :=
#strata
program TestDeclareTVar;
function identity<a>(x : a) : a;
#end

/--
info: program TestDeclareTVar;
function identity<a>(x:tvar!a) : tvar!a;
-/
#guard_msgs in
#eval IO.println singleTypeParamPgm

---------------------------------------------------------------------
-- Test 2: No type parameters
---------------------------------------------------------------------

def noTypeParamPgm :=
#strata
program TestDeclareTVar;
function constInt(x : int) : int;
#end

/--
info: program TestDeclareTVar;
function constInt(x:int) : int;
-/
#guard_msgs in
#eval IO.println noTypeParamPgm

---------------------------------------------------------------------
-- Test 3: Multiple type parameters used in Map
---------------------------------------------------------------------

def typeParamInMapPgm :=
#strata
program TestDeclareTVar;
function lookup<k, v>(m : Map k v, key : k) : v;
#end

/--
info: program TestDeclareTVar;
function lookup<k, v>(m:(Map tvar!v tvar!k), key:tvar!k) : tvar!v;
-/
#guard_msgs in
#eval IO.println typeParamInMapPgm
