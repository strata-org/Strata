/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean

-- Declare dialect for testing declareFn
#dialect
dialect TestDeclareFn;

type bool;
type int;
fn trueExpr : bool => "true";
fn intLit (n : Num) : int => n;

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] name ":" tp;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

@[declareFn(name, b, r)]
op command_fndecl (name : Ident, b : Bindings, r : Type) : Command => "function " name b " : " r ";\n";
op command_assert (b : bool) : Command => "assert " b ";\n";
#end

def testDeclareFnPgm :=
#strata
program TestDeclareFn;
function f(b : bool, i : int) : bool;
assert f(true, 2);
#end

/--
info: program TestDeclareFn;
function f(b:bool, i:int) : bool;
assert f(true, 2);
-/
#guard_msgs in
#eval IO.println testDeclareFnPgm

#dialect
dialect TestDeclareType;

@[declareType(name, none)]
op command_typedecl (name : Ident) : Command => "type " name ";\n";

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] name ":" tp;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

@[declareType(name, some args)]
op command_typefn (name : Ident, args : Option Bindings) : Command => "type_fn " name args ";\n";

@[aliasType(name, some args, rhs)]
op typealias (name : Ident, args : Option Bindings, @[scope(args)] rhs : Type) : Command => "type_alias " name args "=" rhs ";\n";

@[declare(name, tp)]
op var (name : Ident, tp : Type) : Command => "var " name " : " tp ";\n";

op checkType (tp : Type) : Command => "check_type " tp ";\n";

op checkVar (tp : Type, v : tp) : Command => "check " v " : " tp ";\n";

#end

def testDeclareTypePgm :=
#strata
program TestDeclareType;
type Int;
type_fn Nat;
type_fn Array (name : Type);
type_fn Array2 (a : Type, b : Type);
type_alias F (name : Type) = Array name;

var a : Array Int;

check_type Nat;
check_type Int;
check_type (Array Int);
check_type F Int;

check a : F Int;
#end

/--
info: program TestDeclareType;
type Int;
type_fn Nat;
type_fn Array(name:Type);
type_fn Array2(a:Type, b:Type);
type_alias F(name:Type)=Array name;
var a : Array Int;
check_type Nat;
check_type Int;
check_type Array Int;
check_type F Int;
check a : F Int;
-/
#guard_msgs in
#eval IO.println testDeclareTypePgm
