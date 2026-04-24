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
info: program Core;

type T0;
type Byte := bv8;
type IntMap := Map int int;
type T1 (x : Type);
type MyMap (a : Type, b : Type);
type Foo (a : Type, b : Type) := Map b a;
datatype List (a : Type) {
  Nil(),
  Cons(head : a, tail : List a)
};
type IntList := List int;
datatype Tree (a : Type) {
  Leaf(val : a),
  Node(left : Tree a, right : Tree a)
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
info: program Core;

function fooConst () : int;
axiom [fooConst_value]: fooConst == 5;
function f1 (x : int) : int;
axiom [f1_ax1]: forall __q0 : int ::  { f1(__q0) }
  f1(__q0) > __q0;
axiom [f1_ax2_no_trigger]: forall __q0 : int :: f1(__q0) > __q0;
function f2 (x : int, y : bool) : bool;
axiom [f2_ax]: forall __q0 : int :: forall __q1 : bool ::  { f2(__q0, true), f2(__q0, false) }
  f2(__q0, true) == true;
function f3 (x : int, y : bool, z : regex) : bool;
axiom [f3_ax]: forall __q0 : int :: forall __q1 : bool :: forall __q2 : regex ::  { f3(__q0, __q1, __q2), f2(__q0, __q1) }
  f3(__q0, __q1, __q2) == f2(__q0, __q1);
function f4<T1, T2> (x : T1) : Map T1 T2;
axiom [foo_ax]: forall __q0 : int :: (f4(__q0))[1] == true;
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

procedure Test1(x : bool, out y : bool)
{
  y := x;
};

function intId(x : int): int;

procedure Test2(x : bool, g : bool, out y : bool)
spec {
  ensures (y == x);
  ensures (x == y);
  ensures (g == g);
  ensures (g == old g);
  ensures [List_head_test]: (IntList..isNil(Nil()));
} {
  var b0 : bool;
  y := x || x;
  call Test1(5, out b0);
  var b1 : bool;
  call Test1(6, out b1);
};

function boolId(x : bool): bool;
#end

/--
info: program Core;

datatype IntList {
  Nil(),
  Cons(head : int, tail : IntList)
};
procedure Test1 (x : bool, out y : bool)
{
  y := x;
};
function intId (x : int) : int;
procedure Test2 (x : bool, g : bool, out y : bool)
spec {
  ensures [Test2_ensures_0]: y == x;
  ensures [Test2_ensures_1]: x == y;
  ensures [Test2_ensures_2]: g == g;
  ensures [Test2_ensures_3]: g == old g;
  ensures [List_head_test]: IntList..isNil(Nil);
  } {
  var b0 : bool;
  y := x || x;
  call Test1(5, out b0);
  var b1 : bool;
  call Test1(6, out b1);
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

procedure Extract<a>(xs : List a, out h : a)
spec { requires List..isCons(xs); } {
};
#end


/--
info: program Core;

datatype List (a : Type) {
  Nil(),
  Cons(head : a, tail : List a)
};
procedure Extract<a> (xs : List a, out h : a)
spec {
  requires [Extract_requires_0]: List..isCons(xs);
  } {
  ⏎
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

procedure TestDifferentInstantiations()
{
  var m : Map int bool;
  m := makePair(identity(42), identity(true));
};
#end

/--
info: program Core;

function identity<a> (x : a) : a;
function makePair<a, b> (x : a, y : b) : Map a b;
procedure TestDifferentInstantiations ()
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

procedure P(x: bv8, y: bv8, z: bv8) {
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
info: program Core;

procedure P (x : bv8, y : bv8, z : bv8)
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

  datatype Forest (a : Type) { FNil(), FCons(head: RoseTree a, tail: Forest a) }
  datatype RoseTree (a : Type) { Node(val: a, children: Forest a) };

procedure TestPolyRoseTreeHavoc()
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
info: program Core;

datatype Forest (a : Type) {
  FNil(),
  FCons(head : RoseTree a, tail : Forest a)
}
datatype RoseTree (a : Type) {
  Node(val : a, children : Forest a)
};
procedure TestPolyRoseTreeHavoc ()
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

procedure testFuncDecl(c: int) {
  function double(x : int) : int { x + x + c }
  var y : int := 5;
  var result : int := double(y);
  assert result == 12;
};

#end

/--
info: program Core;

procedure testFuncDecl (c : int)
{
  function double (x : int) : int { x + x + c }
  var y : int := 5;
  var result : int := double(y);
  assert [assert_0]: result == 12;
};
-/
#guard_msgs in
#eval ASTtoCST funcDeclStmtPgm

-------------------------------------------------------------------------------

private def findMaxPgm : Program :=
#strata
program Core;

procedure find_max(nums: Map bv64 bv32, nums_len: bv64, out ret: bv32)
spec {
  requires ((nums_len > bv{64}(0)));
  ensures (forall x0: bv64 :: (((bv{64}(0) <= x0) && (x0 < nums_len)) ==> (ret >=s (nums[x0]))));
  ensures (exists x0: bv64 :: (((bv{64}(0) <= x0) && (x0 < nums_len)) && (ret == (nums[x0]))));
}
{
  var max : bv32;
  var i : bv64;
  max := (nums[bv{64}(0)]);
  i := bv{64}(1);
  while ((i < nums_len))
    invariant (nums_len > bv{64}(0))
    invariant (bv{64}(0) <= i)
    invariant (i <= nums_len)
    invariant (forall x0: bv64 :: (((bv{64}(0) <= x0) && (x0 < i)) ==> (max >=s (nums[x0]))))
    invariant (exists x0: bv64 :: (((bv{64}(0) <= x0) && (x0 < i)) && (max == (nums[x0]))))
  {
    if (((nums[i]) >s max)) {
      max := (nums[i]);
    } else {
    }
    i := (i + bv{64}(1));
  }
  ret := max;
};
#end

/--
info: program Core;

procedure find_max (nums : Map bv64 bv32, nums_len : bv64, out ret : bv32)
spec {
  requires [find_max_requires_0]: nums_len > bv{64}(0);
  ensures [find_max_ensures_1]: forall __q0 : bv64 :: bv{64}(0) <= __q0 && __q0 < nums_len ==> ret >=s nums[__q0];
  ensures [find_max_ensures_2]: exists __q0 : bv64 :: bv{64}(0) <= __q0 && __q0 < nums_len && ret == nums[__q0];
  } {
  var max : bv32;
  var i : bv64;
  max := nums[bv{64}(0)];
  i := bv{64}(1);
  while (i < nums_len)
  invariant nums_len > bv{64}(0)
  invariant bv{64}(0) <= i
  invariant i <= nums_len
  invariant forall __q0 : bv64 :: bv{64}(0) <= __q0 && __q0 < i ==> max >=s nums[__q0]
  invariant exists __q0 : bv64 :: bv{64}(0) <= __q0 && __q0 < i && max == nums[__q0]
  {
    if (nums[i] >s max) {
      max := nums[i];
    }
    i := i + bv{64}(1);
  }
  ret := max;
};
-/
#guard_msgs in
#eval ASTtoCST findMaxPgm

-------------------------------------------------------------------------------

private def recFuncPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};

#end

/-- info: program Core;

datatype IntList {
  Nil(),
  Cons(hd : int, tl : IntList)
};
rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};
-/
#guard_msgs in
#eval ASTtoCST recFuncPgm

-------------------------------------------------------------------------------

private def mutualRecFuncPgm : Program :=
#strata
program Core;

datatype RoseTree { Leaf(val: int), Node(children: RoseList) }
datatype RoseList { RNil(), RCons(hd: RoseTree, tl: RoseList) };

rec function treeSize (@[cases] t : RoseTree) : int
{
  if RoseTree..isLeaf(t) then 1 else listSize(RoseTree..children(t))
}
function listSize (@[cases] xs : RoseList) : int
{
  if RoseList..isRNil(xs) then 0 else treeSize(RoseList..hd(xs)) + listSize(RoseList..tl(xs))
};

#end

/-- info: program Core;

datatype RoseTree {
  Leaf(val : int),
  Node(children : RoseList)
}
datatype RoseList {
  RNil(),
  RCons(hd : RoseTree, tl : RoseList)
};
rec function treeSize (@[cases] t : RoseTree) : int
{
  if RoseTree..isLeaf(t) then 1 else listSize(RoseTree..children(t))
}
function listSize (@[cases] xs : RoseList) : int
{
  if RoseList..isRNil(xs) then 0 else treeSize(RoseList..hd(xs)) + listSize(RoseList..tl(xs))
};
-/
#guard_msgs in
#eval ASTtoCST mutualRecFuncPgm

-------------------------------------------------------------------------------

private def nondetCondPgm : Program :=
#strata
program Core;

procedure TestNondetIf()
{
  var x : int := 0;
  if * {
    x := 1;
  } else {
    x := 2;
  }
  assert [x_pos]: x >= 0;
};

procedure TestNondetWhile()
{
  var x : int := 0;
  while *
    invariant x >= 0
  {
    x := x + 1;
  }
  assert [x_pos]: x >= 0;
};
#end

/--
info: program Core;

procedure TestNondetIf ()
{
  var x : int := 0;
  if * {
    x := 1;
  } else {
    x := 2;
  }
  assert [x_pos]: x >= 0;
};
procedure TestNondetWhile ()
{
  var x : int := 0;
  while *
  invariant x >= 0
  {
    x := x + 1;
  }
  assert [x_pos]: x >= 0;
};
-/
#guard_msgs in
#eval ASTtoCST nondetCondPgm

-------------------------------------------------------------------------------
-- Test: call statements with out and inout args (roundtrip formatting)
-------------------------------------------------------------------------------

private def callArgKindsPgm : Program :=
#strata
program Core;

procedure Callee(x : int, inout y : int, out z : int)
spec {
  ensures z == x + y;
  ensures y == old y + 1;
} {
  z := x + y;
  y := y + 1;
};

procedure UnitCallee(a : int) {
  assert a > 0;
};

procedure Caller(inout g : int, out result : int) {
  var tmp : int := 0;
  call Callee(42, inout g, out tmp);
  call Callee(tmp, inout g, out result);
  call UnitCallee(result);
};
#end

/--
info: program Core;

procedure Callee (x : int, inout y : int, out z : int)
spec {
  ensures [Callee_ensures_0]: z == x + y;
  ensures [Callee_ensures_1]: y == old y + 1;
  } {
  z := x + y;
  y := y + 1;
};
procedure UnitCallee (a : int)
{
  assert [assert_0]: a > 0;
};
procedure Caller (inout g : int, out result : int)
{
  var tmp : int := 0;
  call Callee(42, inout g, out tmp);
  call Callee(tmp, inout g, out result);
  call UnitCallee(result);
};
-/
#guard_msgs in
#eval ASTtoCST callArgKindsPgm

-------------------------------------------------------------------------------

-- Lambda formatting tests: construct Core.Program values with lambda
-- expressions and verify the DDM formatter output.

open Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax

private def formatCore (p : Core.Program) : IO Unit :=
  IO.println f!"{Core.formatProgram p}"

private def lambdaIdentityPgm : Core.Program := { decls := [
  .func { name := "intID", typeArgs := [], inputs := [],
          output := .arrow .int .int,
          body := some (.abs () "" (.some .int) (.bvar () 0)) } .empty
]}

/--
info: program Core;

function intID () : int -> int {
  lambda __q0 : int :: __q0
}
-/
#guard_msgs in
#eval formatCore lambdaIdentityPgm

private def lambdaNestedPgm : Core.Program := { decls := [
  .func { name := "constFn", typeArgs := [], inputs := [],
          output := .arrow .int (.arrow .int .int),
          body := some (.abs () "" (.some .int)
            (.abs () "" (.some .int) (.bvar () 1))) } .empty
]}

/--
info: program Core;

function constFn () : int -> int -> int {
  lambda __q0 : int :: lambda __q1 : int :: __q0
}
-/
#guard_msgs in
#eval formatCore lambdaNestedPgm

private def lambdaNamedPgm : Core.Program := { decls := [
  .func { name := "namedLam", typeArgs := [], inputs := [],
          output := .arrow .int .int,
          body := some (.abs () "x" (.some .int) (.bvar () 0)) } .empty
]}

/--
info: program Core;

function namedLam () : int -> int {
  lambda x : int :: x
}
-/
#guard_msgs in
#eval formatCore lambdaNamedPgm

-- Lambda applied to an argument (expression application)
private def lambdaAppliedPgm : Core.Program := { decls := [
  .func { name := "test", typeArgs := [], inputs := [],
          output := .int,
          body := some (.app () (.abs () "x" (.some .int) (.bvar () 0)) (.intConst () 5)) } .empty
]}

/--
info: program Core;

function test () : int {
  (lambda x : int :: x)(5)
}
-/
#guard_msgs in
#eval formatCore lambdaAppliedPgm

-- Multi-binding lambda (curried): lambda x : int :: lambda y : int :: x + y
private def lambdaMultiBindPgm : Core.Program := { decls := [
  .func { name := "add", typeArgs := [], inputs := [],
          output := .arrow .int (.arrow .int .int),
          body := some (.abs () "x" (.some .int)
            (.abs () "y" (.some .int)
              (.app () (.app () Core.intAddOp (.bvar () 1)) (.bvar () 0)))) } .empty
]}

/--
info: program Core;

function add () : int -> int -> int {
  lambda x : int :: lambda y : int :: x + y
}
-/
#guard_msgs in
#eval formatCore lambdaMultiBindPgm

-- Higher-order lambda: lambda that takes a function argument
private def lambdaHigherOrderPgm : Core.Program := { decls := [
  .func { name := "applyFn", typeArgs := [], inputs := [],
          output := .arrow (.arrow .int .int) (.arrow .int .int),
          body := some (.abs () "f" (.some (.arrow .int .int))
            (.abs () "x" (.some .int)
              (.app () (.bvar () 1) (.bvar () 0)))) } .empty
]}

/-- info: program Core;

function applyFn () : int -> int -> int -> int {
  lambda f : int -> int :: lambda x : int :: f(x)
}-/
#guard_msgs in
#eval formatCore lambdaHigherOrderPgm

end Strata.Test
