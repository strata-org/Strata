/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate

-- Tests for Core.Program → CST Conversion
-- This file tests one-direction conversion: AST → CST using the old
-- translator to obtain the AST.

namespace Strata.Test

open Strata.CoreDDM
open Strata
open Core

def ASTtoCST (program : Strata.Program) := do
  -- Use old translator to get AST
  let (ast, errs) := TransM.run Inhabited.default (translateProgram program)
  if !errs.isEmpty then
    IO.println f!"CST to AST Error: {errs}"
  IO.println f!"{Core.formatProgram ast}"

-------------------------------------------------------------------------------

private def testTypes : Program :=
#strata
program Core;

// Basic type declarations
type T0;

// Type aliases with built-in types
type Byte := bv8;
type IntMap := Map int int;

// Polymorphic types
type T1 (x : Type);
type MyMap (a : Type, b : Type);
type Foo (a : Type, b : Type) := Map b a;

// Polymorphic Datatypes
datatype List (a : Type)
  { Nil(),
    Cons(head: a, tail: List a) };

type IntList := List int;

datatype Tree (a : Type) {
    Leaf(val: a),
    Node(left: Tree a, right: Tree a) };
#end

/--
info: type T0;
type Byte := bv8;
type IntMap := Map int int;
type T1 (a0 : Type);
type MyMap (a0 : Type, a1 : Type);
type Foo (a : Type, b : Type) := Map b a;
datatype List (a : Type) {(
  (Nil())),
  (Cons(head : a, tail : (List a)))
};
type IntList := List int;
datatype Tree (a : Type) {(
  (Leaf(val : a))),
  (Node(left : (Tree a), right : (Tree a)))
};
-/
#guard_msgs in
#eval ASTtoCST testTypes

-------------------------------------------------------------------------------

private def testFnAxs : Program :=
#strata
program Core;

// 0-ary function
const fooConst : int;
axiom [fooConst_value]: fooConst == 5;

// 1-ary function
function f1(x: int): int;
axiom [f1_ax1]: (forall x : int :: {f1(x)} f1(x) > x);
axiom [f1_ax2_no_trigger]: (forall x : int :: f1(x) > x);

// 2-ary function
function f2(x : int, y : bool): bool;
axiom [f2_ax]: (forall x : int, y : bool ::
                  {f2(x, true), f2(x, false)}
                  f2(x, true) == true);

// 3-ary function
function f3(x : int, y : bool, z : regex): bool;
axiom [f3_ax]: (forall x : int, y : bool, z : regex ::
                  { f3(x, y, z), f2(x, y) }
                  f3(x, y, z) == f2(x, y));

// Polymorphic function.
function f4<T1, T2>(x : T1) : Map T1 T2;
axiom [foo_ax]: (forall x : int :: (f4(x))[1] == true);

// Function with defined body
function f5<T1, T2>(x : T1, y : T2) : T1 {
  x
}
#end

/--
info: function fooConst () : int;
axiom [fooConst_value]: fooConst == 5;
function f1 (x : int) : int;
axiom [f1_ax1]: forall x0 : int ::  { f1(x0) }
  f1(x0) > x0;
axiom [f1_ax2_no_trigger]: forall x0 : int :: f1(x0) > x0;
function f2 (x : int, y : bool) : bool;
axiom [f2_ax]: forall x0 : int :: forall x1 : bool ::  { f2(x0, true), f2(x0, false) }
  f2(x0, true) == true;
function f3 (x : int, y : bool, z : regex) : bool;
axiom [f3_ax]: forall x0 : int :: forall x1 : bool :: forall x2 : regex ::  { f3(x0, x1, x2), f2(x0, x1) }
  f3(x0, x1, x2) == f2(x0, x1);
function f4<T1, T2> (x : T1) : Map T1 T2;
axiom [foo_ax]: forall x0 : int :: (f4(x0))[1] == true;
function f5<T1, T2> (x : T1, y : T2) : T1 {
  x
}
-/
#guard_msgs in
#eval ASTtoCST testFnAxs

-------------------------------------------------------------------------------

def testProcedures : Program :=
#strata
program Core;

datatype IntList () { Nil(), Cons(head: int, tail: IntList) };

procedure Test1(x : bool) returns (y : bool)
{
  y := x;
};

function intId(x : int): int;
var g : bool;

procedure Test2(x : bool) returns (y : bool)
spec {
  ensures (y == x);
  ensures (x == y);
  ensures (g == g);
  ensures (g == old(g));
  ensures [List_head_test]: (IntList..isNil(Nil()));
} {
  var b0 : bool;
  y := x || x;
  call b0 := Test1(5);
  var b1 : bool;
  call b1 := Test1(6);
};

function boolId(x : bool): bool;
#end

/--
info: datatype IntList {(
  (Nil())),
  (Cons(head : int, tail : IntList))
};
procedure Test1 (x : bool) returns (y : bool)
{
  y := x;
  };
function intId (x : int) : int;
var g : bool;
procedure Test2 (x : bool) returns (y : bool)
spec {
  ensures [Test2_ensures_0]: y == x;
  ensures [Test2_ensures_1]: x == y;
  ensures [Test2_ensures_2]: g == g;
  ensures [Test2_ensures_3]: g == old(g);
  ensures [List_head_test]: IntList..isNil(Nil);
  } {
  var b0 : bool;
  y := x || x;
  call b0 := Test1(5);
  var b1 : bool;
  call b1 := Test1(6);
  };
function boolId (x : bool) : bool;
-/
#guard_msgs in
#eval ASTtoCST testProcedures

-------------------------------------------------------------------------------

private def testPolyProc : Program :=
#strata
program Core;

datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };

procedure Extract<a>(xs : List a) returns (h : a)
spec { requires List..isCons(xs); } {
};
#end


/--
info: datatype List (a : Type) {(
  (Nil())),
  (Cons(head : a, tail : (List a)))
};
procedure Extract<a> (xs : (List a)) returns (h : (a))
spec {
  requires [Extract_requires_0]: List..isCons(xs);
  } {
  };
-/
#guard_msgs in
#eval ASTtoCST testPolyProc

-------------------------------------------------------------------------------

private def polyFns :=
#strata
program Core;

function identity<a>(x : a) : a;
function makePair<a, b>(x : a, y : b) : Map a b;

procedure TestDifferentInstantiations() returns ()
{
  var m : Map int bool;
  m := makePair(identity(42), identity(true));
};
#end

/--
info: function identity<a> (x : a) : a;
function makePair<a, b> (x : a, y : b) : Map a b;
procedure TestDifferentInstantiations () returns ()
{
  var m : (Map int bool);
  m := makePair(identity(42), identity(true));
  };
-/
#guard_msgs in
#eval ASTtoCST polyFns

-------------------------------------------------------------------------------

private def bitvecPgm :=
#strata
program Core;

procedure P(x: bv8, y: bv8, z: bv8) returns () {
  assert [add_comm]: x + y == y + x;
  assert [xor_cancel]: x ^ x == bv{8}(0);
  assert [div_shift]: x div bv{8}(2) == x >> bv{8}(1);
  assert [mul_shift]: x * bv{8}(2) == x << bv{8}(1);
  assert [demorgan]: ~(x & y) == ~x | ~y;
  assert [mod_and]: x mod bv{8}(2) == x & bv{8}(1);
  assert [bad_shift]: x >> y == x << y;
  var xy : bv16 := bvconcat{8}{8}(x, y);
  var xy2 : bv32 := bvconcat{16}{16}(xy, xy);
  var xy4 : bv64 := bvconcat{32}{32}(xy2, xy2);
};
#end

/--
info: procedure P (x : bv8, y : bv8, z : bv8) returns ()
{
  assert [add_comm]: x + y == y + x;
  assert [xor_cancel]: x ^ x == bv{8}(0);
  assert [div_shift]: x div bv{8}(2) == x >> bv{8}(1);
  assert [mul_shift]: x * bv{8}(2) == x << bv{8}(1);
  assert [demorgan]: ~(x & y) == ~x | ~y;
  assert [mod_and]: x mod bv{8}(2) == x & bv{8}(1);
  assert [bad_shift]: x >> y == x << y;
  var xy : bv16 := bvconcat{8}{8}(x, y);
  var xy2 : bv32 := bvconcat{16}{16}(xy, xy);
  var xy4 : bv64 := bvconcat{32}{32}(xy2, xy2);
  };
-/
#guard_msgs in
#eval ASTtoCST bitvecPgm

-------------------------------------------------------------------------------

private def polyRoseTreeHavocPgm : Program :=
#strata
program Core;

forward type RoseTree (a : Type);
forward type Forest (a : Type);
mutual
  datatype Forest (a : Type) { FNil(), FCons(head: RoseTree a, tail: Forest a) };
  datatype RoseTree (a : Type) { Node(val: a, children: Forest a) };
end;

procedure TestPolyRoseTreeHavoc() returns ()
spec {
  ensures true;
}
{
  var t : RoseTree int;
  var f : Forest int;
  havoc t;
  havoc f;
  assume t == Node(42, FNil());
  assume f == FCons(t, FNil());
  assert [valIs42]: RoseTree..val(t) == 42;
  assert [headIsT]: Forest..head(f) == t;
  assert [headVal]: RoseTree..val(Forest..head(f)) == 42;
};
#end

/--
info: forward type RoseTree (a : Type);
forward type Forest (a : Type);
mutual
   datatype Forest (a : Type) {(
    (FNil())),
    (FCons(head : (RoseTree a), tail : (Forest a)))
  };
   datatype RoseTree (a : Type) {
    (Node(val : a, children : (Forest a)))
  };
  end;
procedure TestPolyRoseTreeHavoc () returns ()
spec {
  ensures [TestPolyRoseTreeHavoc_ensures_0]: true;
  } {
  var t : (RoseTree int);
  var f : (Forest int);
  havoc t;
  havoc f;
  assume [assume_0]: t == Node(42, FNil);
  assume [assume_1]: f == FCons(t, FNil);
  assert [valIs42]: RoseTree..val(t) == 42;
  assert [headIsT]: Forest..head(f) == t;
  assert [headVal]: RoseTree..val(Forest..head(f)) == 42;
  };
-/
#guard_msgs in
#eval ASTtoCST polyRoseTreeHavocPgm

-------------------------------------------------------------------------------

private def funcDeclStmtPgm : Program :=
#strata
program Core;

procedure testFuncDecl(c: int) returns () {
  function double(x : int) : int { x + x + c}
  var y : int := 5;
  var result : int := double(y);
  assert result == 12;
};

#end

-- BROKEN!
#guard_msgs (drop all) in
#eval ASTtoCST funcDeclStmtPgm
-- AST to CST Error:
-- Unsupported construct in funcDeclToStatement: funcDecl without body not supported in statements:
-- Context: Global scope:
-- Scope 1:
--   boundVars: [c]
-- Scope 2:

-------------------------------------------------------------------------------

end Strata.Test
