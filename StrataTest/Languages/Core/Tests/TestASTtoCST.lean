/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.DDMTransform.ASTtoCST
meta import Strata.Languages.Core.DDMTransform.Translate
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)

-- Tests for Core.Program → CST Conversion
-- This file tests one-direction conversion: AST → CST using the old
-- translator to obtain the AST.

namespace Strata.Test

open Strata.CoreDDM
open Strata
open Core

def ASTtoCST (program : StrataDDM.Program) := do
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
type Byte := bv W8;
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
type Byte := bv W8;
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
axiom [f1_ax1]: (forall x : int :: {f1(x)} int.gt(f1(x), x));
axiom [f1_ax2_no_trigger]: (forall x : int :: int.gt(f1(x), x));

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
axiom [f1_ax1]: forall x : int ::  { f1(x) }
  int.gt(f1(x), x);
axiom [f1_ax2_no_trigger]: forall x : int :: int.gt(f1(x), x);
function f2 (x : int, y : bool) : bool;
axiom [f2_ax]: forall x : int :: forall y : bool ::  { f2(x, true), f2(x, false) }
  f2(x, true) == true;
function f3 (x : int, y : bool, z : regex) : bool;
axiom [f3_ax]: forall x : int :: forall y : bool :: forall z : regex ::  { f3(x, y, z), f2(x, y) }
  f3(x, y, z) == f2(x, y);
function f4<T1, T2> (x : T1) : Map T1 T2;
axiom [foo_ax]: forall x : int :: (f4(x))[1] == true;
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

/-- A type parameter whose name begins with `s` parses correctly: the signed
comparison operators are the word-like tokens `slt`/`sle`/`sgt`/`sge`, so no
operator token shadows the `<` that opens a type-parameter list, and `f<s>`
tokenizes as a type-parameter list containing `s`. -/
private def typeParamStartingWithS :=
#strata
program Core;

function f<s>(x : s) : s;
function g<s, t>(x : s, y : t) : Map s t;
#end

/--
info: program Core;

function f<s> (x : s) : s;
function g<s, t> (x : s, y : t) : Map s t;
-/
#guard_msgs in
#eval ASTtoCST typeParamStartingWithS

-------------------------------------------------------------------------------

/-- Regression test: the word-like operators `slt`/`sle`/`sgt`/`sge`/`ashr`
respect identifier boundaries. Identifiers that merely *begin with* those
spellings (but are not exactly the keyword) are ordinary identifiers, not the
operator. Exact spellings `slt`/`sle`/`sgt`/`sge`/`ashr` are reserved
keywords and are not usable as identifiers, same as `div`/`mod`/etc. -/
private def operatorNamePrefixIdentifiers :=
#strata
program Core;

function h<slte>(x : slte) : slte;
function k<sltx, sgey>(x : sltx, y : sgey) : Map sltx sgey;
function m<ashrx>(x : ashrx) : ashrx;
#end

/--
info: program Core;

function h<slte> (x : slte) : slte;
function k<sltx, sgey> (x : sltx, y : sgey) : Map sltx sgey;
function m<ashrx> (x : ashrx) : ashrx;
-/
#guard_msgs in
#eval ASTtoCST operatorNamePrefixIdentifiers

-------------------------------------------------------------------------------

/-- An operator written tight against a following identifier tokenizes as two
separate tokens, so the identifier keeps its leading letter: `>>step` parses as
`>>` then `step`, and `/table`/`%total` parse as `/`/`%` then the identifier.
The printer reinserts the surrounding spaces. -/
private def operatorAdjacentIdentifiers :=
#strata
program Core;

procedure P(x: bv W8, step: bv W8, a: int, table: int, total: int, safe: int) {
  var r1 : bv W8 := bv8.uShr(x, step);
  var r2 : int := int.safeDiv(a, table);
  var r3 : int := int.safeMod(a, total);
  var r4 : int := int.add(safe, 1);
};
#end

/--
info: program Core;

procedure P (x : bv W8, step : bv W8, a : int, table : int, total : int, safe : int)
{
  var r1 : bv W8 := bv8.uShr(x, step);
  var r2 : int := int.safeDiv(a, table);
  var r3 : int := int.safeMod(a, total);
  var r4 : int := int.add(safe, 1);
};
-/
#guard_msgs in
#eval ASTtoCST operatorAdjacentIdentifiers

-------------------------------------------------------------------------------

private def bitvecPgm :=
#strata
program Core;

procedure P(x: bv W8, y: bv W8, z: bv W8) {
  assert [add_comm]: bv8.add(x, y) == bv8.add(y, x);
  assert [xor_cancel]: bv8.xor(x, x) == bv{8}(0);
  assert [div_shift]: bv8.uDiv(x, bv{8}(2)) == bv8.uShr(x, bv{8}(1));
  assert [mul_shift]: bv8.mul(x, bv{8}(2)) == bv8.shl(x, bv{8}(1));
  assert [demorgan]: bv8.not(bv8.and(x, y)) == bv8.or(bv8.not(x), bv8.not(y));
  assert [mod_and]: bv8.uMod(x, bv{8}(2)) == bv8.and(x, bv{8}(1));
  assert [bad_shift]: bv8.uShr(x, y) == bv8.shl(x, y);
  assert [arith_shift]: bv8.sShr(x, y) == bv8.uShr(x, y);
  assert [signed_lt]: bv8.sLt(x, y);
  assert [signed_le]: bv8.sLe(x, y);
  var xy : bv W16 := bvconcat{8}{8}(x, y);
  var xy2 : bv W32 := bvconcat{16}{16}(xy, xy);
  var xy4 : bv W64 := bvconcat{32}{32}(xy2, xy2);
};
#end

/--
info: program Core;

procedure P (x : bv W8, y : bv W8, z : bv W8)
{
  assert [add_comm]: bv8.add(x, y) == bv8.add(y, x);
  assert [xor_cancel]: bv8.xor(x, x) == bv{8}(0);
  assert [div_shift]: bv8.uDiv(x, bv{8}(2)) == bv8.uShr(x, bv{8}(1));
  assert [mul_shift]: bv8.mul(x, bv{8}(2)) == bv8.shl(x, bv{8}(1));
  assert [demorgan]: bv8.not(bv8.and(x, y)) == bv8.or(bv8.not(x), bv8.not(y));
  assert [mod_and]: bv8.uMod(x, bv{8}(2)) == bv8.and(x, bv{8}(1));
  assert [bad_shift]: bv8.uShr(x, y) == bv8.shl(x, y);
  assert [arith_shift]: bv8.sShr(x, y) == bv8.uShr(x, y);
  assert [signed_lt]: bv8.sLt(x, y);
  assert [signed_le]: bv8.sLe(x, y);
  var xy : bv W16 := bvconcat{8}{8}(x, y);
  var xy2 : bv W32 := bvconcat{16}{16}(xy, xy);
  var xy4 : bv W64 := bvconcat{32}{32}(xy2, xy2);
};
-/
#guard_msgs in
#eval ASTtoCST bitvecPgm

-------------------------------------------------------------------------------

/-- Round-trip coverage for the integer division/modulo family. The truncating
safe operators use call syntax `Int.SafeDivT(a, b)`/`Int.SafeModT(a, b)`,
mirroring their non-safe siblings `Int.DivT`/`Int.ModT`. -/
private def intDivModPgm :=
#strata
program Core;

procedure Q(a: int, b: int) {
  assert [euclid_div]: int.div(a, b) == int.div(a, b);
  assert [euclid_mod]: int.mod(a, b) == int.mod(a, b);
  assert [safe_div]: int.safeDiv(a, b) == int.safeDiv(a, b);
  assert [safe_mod]: int.safeMod(a, b) == int.safeMod(a, b);
  assert [trunc_div]: int.divT(a, b) == int.divT(a, b);
  assert [trunc_mod]: int.modT(a, b) == int.modT(a, b);
  assert [safe_trunc_div]: int.safeDivT(a, b) == int.safeDivT(a, b);
  assert [safe_trunc_mod]: int.safeModT(a, b) == int.safeModT(a, b);
};
#end

/--
info: program Core;

procedure Q (a : int, b : int)
{
  assert [euclid_div]: int.div(a, b) == int.div(a, b);
  assert [euclid_mod]: int.mod(a, b) == int.mod(a, b);
  assert [safe_div]: int.safeDiv(a, b) == int.safeDiv(a, b);
  assert [safe_mod]: int.safeMod(a, b) == int.safeMod(a, b);
  assert [trunc_div]: int.divT(a, b) == int.divT(a, b);
  assert [trunc_mod]: int.modT(a, b) == int.modT(a, b);
  assert [safe_trunc_div]: int.safeDivT(a, b) == int.safeDivT(a, b);
  assert [safe_trunc_mod]: int.safeModT(a, b) == int.safeModT(a, b);
};
-/
#guard_msgs in
#eval ASTtoCST intDivModPgm

-------------------------------------------------------------------------------

/-- Round-trip coverage for the overflow-checked ("safe") bitvector family.
Every safe operator uses `Bv.`-namespaced call syntax, matching the sibling
overflow predicates (`Bv.SAddOverflow(a, b)` etc.) that guard them. -/
private def safeBvPgm :=
#strata
program Core;

procedure R(x: bv W8, y: bv W8) {
  assert [s_add]: bv8.safeAdd(x, y) == bv8.safeAdd(x, y);
  assert [s_sub]: bv8.safeSub(x, y) == bv8.safeSub(x, y);
  assert [s_mul]: bv8.safeMul(x, y) == bv8.safeMul(x, y);
  assert [s_neg]: bv8.safeNeg(x) == bv8.safeNeg(x);
  assert [s_sdiv]: bv8.safeSDiv(x, y) == bv8.safeSDiv(x, y);
  assert [s_smod]: bv8.safeSMod(x, y) == bv8.safeSMod(x, y);
};
#end

/--
info: program Core;

procedure R (x : bv W8, y : bv W8)
{
  assert [s_add]: bv8.safeAdd(x, y) == bv8.safeAdd(x, y);
  assert [s_sub]: bv8.safeSub(x, y) == bv8.safeSub(x, y);
  assert [s_mul]: bv8.safeMul(x, y) == bv8.safeMul(x, y);
  assert [s_neg]: bv8.safeNeg(x) == bv8.safeNeg(x);
  assert [s_sdiv]: bv8.safeSDiv(x, y) == bv8.safeSDiv(x, y);
  assert [s_smod]: bv8.safeSMod(x, y) == bv8.safeSMod(x, y);
};
-/
#guard_msgs in
#eval ASTtoCST safeBvPgm

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
  function double(x : int) : int { int.add(int.add(x, x), c) }
  var y : int := 5;
  var result : int := double(y);
  assert result == 12;
};

#end

/--
info: program Core;

procedure testFuncDecl (c : int)
{
  function double (x : int) : int { int.add(int.add(x, x), c) }
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

procedure find_max(nums: Map (bv W64) (bv W32), nums_len: bv W64, out ret: bv W32)
spec {
  requires ((bv64.uGt(nums_len, bv{64}(0))));
  ensures (forall x0: bv W64 :: (((bv64.uLe(bv{64}(0), x0)) && (bv64.uLt(x0, nums_len))) ==> (bv32.sGe(ret, (nums[x0])))));
  ensures (exists x0: bv W64 :: (((bv64.uLe(bv{64}(0), x0)) && (bv64.uLt(x0, nums_len))) && (ret == (nums[x0]))));
}
{
  var max : bv W32;
  var i : bv W64;
  max := (nums[bv{64}(0)]);
  i := bv{64}(1);
  while ((bv64.uLt(i, nums_len)))
    invariant (bv64.uGt(nums_len, bv{64}(0)))
    invariant (bv64.uLe(bv{64}(0), i))
    invariant (bv64.uLe(i, nums_len))
    invariant (forall x0: bv W64 :: (((bv64.uLe(bv{64}(0), x0)) && (bv64.uLt(x0, i))) ==> (bv32.sGe(max, (nums[x0])))))
    invariant (exists x0: bv W64 :: (((bv64.uLe(bv{64}(0), x0)) && (bv64.uLt(x0, i))) && (max == (nums[x0]))))
  {
    if ((bv32.sGt((nums[i]), max))) {
      max := (nums[i]);
    } else {
    }
    i := (bv64.add(i, bv{64}(1)));
  }
  ret := max;
};
#end

/--
info: program Core;

procedure find_max (nums : Map (bv W64) (bv W32), nums_len : bv W64, out ret : bv W32)
spec {
  requires [find_max_requires_0]: bv64.uGt(nums_len, bv{64}(0));
  ensures [find_max_ensures_1]: forall x0 : (bv W64) :: bv64.uLe(bv{64}(0), x0) && bv64.uLt(x0, nums_len) ==> bv32.sGe(ret, nums[x0]);
  ensures [find_max_ensures_2]: exists x0 : (bv W64) :: bv64.uLe(bv{64}(0), x0) && bv64.uLt(x0, nums_len) && ret == nums[x0];
  } {
  var max : (bv W32);
  var i : (bv W64);
  max := nums[bv{64}(0)];
  i := bv{64}(1);
  while (bv64.uLt(i, nums_len))
  invariant bv64.uGt(nums_len, bv{64}(0))
  invariant bv64.uLe(bv{64}(0), i)
  invariant bv64.uLe(i, nums_len)
  invariant forall x0 : (bv W64) :: bv64.uLe(bv{64}(0), x0) && bv64.uLt(x0, i) ==> bv32.sGe(max, nums[x0])
  invariant exists x0 : (bv W64) :: bv64.uLe(bv{64}(0), x0) && bv64.uLt(x0, i) && max == nums[x0]
  {
    if (bv32.sGt(nums[i], max)) {
      max := nums[i];
    }
    i := bv64.add(i, bv{64}(1));
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
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
};

#end

/-- info: program Core;

datatype IntList {
  Nil(),
  Cons(hd : int, tl : IntList)
};
rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
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
  if RoseList..isRNil(xs) then 0 else int.add(treeSize(RoseList..hd(xs)), listSize(RoseList..tl(xs)))
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
  if RoseList..isRNil(xs) then 0 else int.add(treeSize(RoseList..hd(xs)), listSize(RoseList..tl(xs)))
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
  assert [x_pos]: int.ge(x, 0);
};

procedure TestNondetWhile()
{
  var x : int := 0;
  while *
    invariant int.ge(x, 0)
  {
    x := int.add(x, 1);
  }
  assert [x_pos]: int.ge(x, 0);
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
  assert [x_pos]: int.ge(x, 0);
};
procedure TestNondetWhile ()
{
  var x : int := 0;
  while *
  invariant int.ge(x, 0)
  {
    x := int.add(x, 1);
  }
  assert [x_pos]: int.ge(x, 0);
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
  ensures z == int.add(x, y);
  ensures y == int.add(old y, 1);
} {
  z := int.add(x, y);
  y := int.add(y, 1);
};

procedure UnitCallee(a : int) {
  assert int.gt(a, 0);
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
  ensures [Callee_ensures_0]: z == int.add(x, y);
  ensures [Callee_ensures_1]: y == int.add(old y, 1);
  } {
  z := int.add(x, y);
  y := int.add(y, 1);
};
procedure UnitCallee (a : int)
{
  assert [assert_0]: int.gt(a, 0);
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
  fun __q0 : int => __q0
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
  fun __q0 : int => fun __q1 : int => __q0
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
  fun x : int => x
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
  (fun x : int => x)(5)
}
-/
#guard_msgs in
#eval formatCore lambdaAppliedPgm

-- Multi-binding lambda (curried): fun x : int => fun y : int => x + y
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
  fun x : int => fun y : int => int.add(x, y)
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

function applyFn () : (int -> int) -> int -> int {
  fun f : (int -> int) => fun x : int => f(x)
}-/
#guard_msgs in
#eval formatCore lambdaHigherOrderPgm

-------------------------------------------------------------------------------

private def strPrefixSuffixPgm : Program :=
#strata
program Core;

procedure TestPrefixSuffix(s1 : string, s2 : string)
spec {
  requires str.prefixof(s1, s2);
  ensures str.suffixof(s1, s2) || str.prefixof(s1, s2);
}
{
  assert [prefix_holds]: str.prefixof(s1, s2);
  assert [either]: str.suffixof(s1, s2) || str.prefixof(s1, s2);
};
#end

/--
info: program Core;

procedure TestPrefixSuffix (s1 : string, s2 : string)
spec {
  requires [TestPrefixSuffix_requires_0]: str.prefixof(s1, s2);
  ensures [TestPrefixSuffix_ensures_1]: str.suffixof(s1, s2) || str.prefixof(s1, s2);
  } {
  assert [prefix_holds]: str.prefixof(s1, s2);
  assert [either]: str.suffixof(s1, s2) || str.prefixof(s1, s2);
};
-/
#guard_msgs in
#eval ASTtoCST strPrefixSuffixPgm

-------------------------------------------------------------------------------
-- Real literals with no terminating decimal representation are printed as the
-- exact rational literal `frac{n, d}`.
-------------------------------------------------------------------------------

-- Wrap a real expression as the body of `function f () : real { … }` and print.
private def showReal (e : Core.Expression.Expr) : IO Unit :=
  formatCore { decls := [
    .func { name := "f", typeArgs := [], inputs := [], output := .real,
            body := some e } .empty ] }

/--
info: program Core;

function f () : real {
  frac{1, 3}
}
-/
#guard_msgs in
#eval showReal (.realConst () (1/3 : Rat))

/--
info: program Core;

function f () : real {
  frac{1, 7}
}
-/
#guard_msgs in
#eval showReal (.realConst () (1/7 : Rat))

/--
info: program Core;

function f () : real {
  real.neg(frac{2, 3})
}
-/
#guard_msgs in
#eval showReal (.realConst () (-2/3 : Rat))

-- A `Rat` keeps its sign in the numerator, so the denominator is never
-- negative. Writing the sign on the denominator (`1 / (-3)`) normalizes to
-- `num = -1, den = 3`.
/--
info: program Core;

function f () : real {
  real.neg(frac{1, 3})
}
-/
#guard_msgs in
#eval showReal (.realConst () (1 / (-3) : Rat))

-- Terminating decimals are unaffected: they still print as decimals.
/--
info: program Core;

function f () : real {
  0.5
}
-/
#guard_msgs in
#eval showReal (.realConst () (1/2 : Rat))

-------------------------------------------------------------------------------
-- Round-trip: `frac{n, d}` written in surface syntax parses back to the exact
-- rational.
-------------------------------------------------------------------------------

private def fracRoundtripPgm : Program :=
#strata
program Core;

function oneThird () : real { frac{1, 3} }
function negTwoThirds () : real { real.neg(frac{2, 3}) }
#end

/--
info: program Core;

function oneThird () : real {
  frac{1, 3}
}
function negTwoThirds () : real {
  real.neg(frac{2, 3})
}
-/
#guard_msgs in
#eval ASTtoCST fracRoundtripPgm

-- A non-normalized fraction like `frac{2, 6}` parses to the reduced rational
-- `1/3` (Lean `Rat` normalizes), so it re-prints in reduced form.
private def fracReducePgm : Program :=
#strata
program Core;

function f () : real { frac{2, 6} }
#end

/--
info: program Core;

function f () : real {
  frac{1, 3}
}
-/
#guard_msgs in
#eval ASTtoCST fracReducePgm

-- The formatter only emits `frac{...}` on the
-- `Decimal.fromRat = none` (non-terminating) path.
private def fracTerminatingPgm : Program :=
#strata
program Core;

function f () : real { frac{1, 2} }
#end

/--
info: program Core;

function f () : real {
  0.5
}
-/
#guard_msgs in
#eval ASTtoCST fracTerminatingPgm

-------------------------------------------------------------------------------
-- A zero denominator has no rational value. The translator records an error
-- (without panicking) and falls back to a benign `realConst 0`; `ASTtoCST`
-- prints the collected error alongside the program.
-------------------------------------------------------------------------------

private def fracZeroDenomPgm : Program :=
#strata
program Core;

function f () : real { frac{1, 0} }
#end

-- Note: the error is caught at CST->AST time (during translateProgram.)
/--
info: CST to AST Error: #[fracLit: denominator must be non-zero]
program Core;

function f () : real {
  0.0
}
-/
#guard_msgs in
#eval ASTtoCST fracZeroDenomPgm

-- Note: we don't need a zero-denominator check for reals in the Core formatter:
-- a Lean `Rat` cannot hold a zero denominator (`den_nz : den ≠ 0` is a field of
-- the structure), so `mkRat _ 0` (and thus `(1/0 : Rat)`) is just `0` at
-- construction.
/-- info: 0 -/
#guard_msgs in
#eval (1 / 0 : Rat)

/--
info: program Core;

function f () : real {
  0.0
}
-/
#guard_msgs in
#eval showReal (.realConst () (1/0 : Rat))

-------------------------------------------------------------------------------
-- The `frac{...}` literal uses `frac{` as its leading token (like `bv{N}`), so
-- bare `frac` remains a valid identifier: a user may declare and call a
-- function named `frac` with no collision against the literal syntax.
-------------------------------------------------------------------------------

private def fracIdentifierPgm : Program :=
#strata
program Core;

function frac (x : int, y : int) : bool { true }

function g () : bool { frac(1, 2) }
#end

/--
info: program Core;

function frac (x : int, y : int) : bool {
  true
}
function g () : bool {
  frac(1, 2)
}
-/
#guard_msgs in
#eval ASTtoCST fracIdentifierPgm

-------------------------------------------------------------------------------
-- Constants built directly as AST nodes with `Core.Decl.const`, which is what
-- tools that produce Core declarations without going through the concrete
-- syntax use. A constant is a nullary function, so it prints as one.
-------------------------------------------------------------------------------

private def constAstPgm : Core.Program := { decls := [
  Core.Decl.const "opaque" .int,
  Core.Decl.const "five" .int (value := some (.intConst () 5)),
  Core.Decl.const "seven" .int
    (value := some (.app () (.app () Core.intAddOp (.fvar () "five" none)) (.intConst () 2)))
    (attr := #[.inline])
]}

/--
info: program Core;

function opaque () : int;
function five () : int {
  5
}
inline function seven () : int {
  int.add(five, 2)
}
-/
#guard_msgs in
#eval formatCore constAstPgm

end Strata.Test

end
