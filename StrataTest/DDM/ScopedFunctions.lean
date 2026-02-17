/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DDM.Integration.Lean

/-!
# Tests for Scoped Function Declarations in DDM

Tests that function declarations within blocks are properly scoped
using the `@[declareFn]` annotation combined with `@[scope]`.

This tests the DDM scoping mechanism independently of the Strata Core language.
-/

#dialect
dialect TestScopedFn;

type bool;
type int;

fn trueExpr : bool => "true";
fn falseExpr : bool => "false";
fn intLit (n : Num) : int => n;
fn add (a : int, b : int) : int => @[prec(25), leftassoc] a "+" b;

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] name ":" tp;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

category VarDecl;
@[declare(name, tp)]
op varDecl (name : Ident, tp : Type) : VarDecl => name ":" tp;

category Statement;
category Block;

op var_statement (v : VarDecl) : Statement => "var " v ";\n";

@[declare(name, tp)]
op init_statement (name : Ident, tp : Type, e : tp) : Statement =>
  "var " name " : " tp " := " e ";\n";

op assign_statement (tp : Type, v : Ident, e : tp) : Statement =>
  v " := " e ";\n";

op assert_statement (e : bool) : Statement => "assert " e ";\n";

@[declareFn(name, b, r)]
op funcDecl_statement (name : Ident,
                       b : Bindings,
                       r : Type,
                       @[scope(b)] body : r) : Statement =>
  "function " name b " : " r " { " body " }";

@[scope(stmts)]
op block (stmts : Seq Statement) : Block => "{\n" indent(2, stmts) "}\n";

op command_block (b : Block) : Command => b;

#end

---------------------------------------------------------------------
-- Test 1: Function declaration in block, called in subsequent statement
---------------------------------------------------------------------

def funcInBlockPgm :=
#strata
program TestScopedFn;
{
  function double(x : int) : int { x + x }
  var result : int := double(5);
  assert true;
}
#end

/--
info: program TestScopedFn;
{
  function double(x:int) : int { x+x }var result : int := double(5);
  assert true;
}
-/
#guard_msgs in
#eval IO.println funcInBlockPgm

---------------------------------------------------------------------
-- Test 2: Multiple function declarations in sequence
---------------------------------------------------------------------

def multipleFuncsPgm :=
#strata
program TestScopedFn;
{
  function inc(x : int) : int { x + 1 }
  function dec(x : int) : int { x + 0 }
  var a : int := inc(5);
  var b : int := dec(a);
  assert true;
}
#end

/--
info: program TestScopedFn;
{
  function inc(x:int) : int { x+1 }function dec(x:int) : int { x+0 }var a : int := inc(5);
  var b : int := dec(a);
  assert true;
}
-/
#guard_msgs in
#eval IO.println multipleFuncsPgm

---------------------------------------------------------------------
-- Test 3: Function with multiple parameters
---------------------------------------------------------------------

def multiParamFuncPgm :=
#strata
program TestScopedFn;
{
  function sum(a : int, b : int) : int { a + b }
  var result : int := sum(3, 4);
  assert true;
}
#end

/--
info: program TestScopedFn;
{
  function sum(a:int, b:int) : int { a+b }var result : int := sum(3, 4);
  assert true;
}
-/
#guard_msgs in
#eval IO.println multiParamFuncPgm

---------------------------------------------------------------------
-- Test 4: Nested function calls
---------------------------------------------------------------------

def nestedCallsPgm :=
#strata
program TestScopedFn;
{
  function double(x : int) : int { x + x }
  function quadruple(x : int) : int { double(double(x)) }
  var result : int := quadruple(2);
  assert true;
}
#end

/--
info: program TestScopedFn;
{
  function double(x:int) : int { x+x }function quadruple(x:int) : int { double(double(x)) }var result : int := quadruple(2);
  assert true;
}
-/
#guard_msgs in
#eval IO.println nestedCallsPgm

---------------------------------------------------------------------
