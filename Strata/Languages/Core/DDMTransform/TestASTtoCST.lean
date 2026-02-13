/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.DDMTransform.Parse

/-!
# Tests for Core.Program → CST Conversion

This file tests one-direction conversion: AST → CST using the old
translator to obtain the AST.
-/

namespace Strata.Test

open Strata.CoreDDM
open Strata
open Core

def ASTtoCST (program : Strata.Program) := do
  -- Use old translator to get AST
  let (ast, errs) := TransM.run Inhabited.default (translateProgram program)
  if !errs.isEmpty then
    IO.println f!"CST to AST Error: {errs}"
  -- Convert AST → CST
  match (programToCST (M := SourceRange) ast program.globalContext).run
        ToCSTContext.empty with
  | .error errs =>
    IO.println "AST to CST Error:"
    for err in errs do
      match err with
      | .unsupportedConstruct fn desc ctx _md =>
        IO.println s!"Unsupported construct in {fn}: {desc}\nContext: {ctx}"
  | .ok (cmds, _finalCtx) =>
    -- Format with original global context
    let ctx := FormatContext.ofDialects program.dialects
      program.globalContext {}
    let state : FormatState := {
      openDialects := program.dialects.toList.foldl (init := {})
        fun a (d : Dialect) => a.insert d.name
    }
    -- Display commands using mformat
    IO.println "Rendered Program:\n"
    for cmd in cmds do
      IO.print ((mformat (ArgF.op cmd.toAst) ctx state).format)

-------------------------------------------------------------------------------

def test1 : Program :=
#strata
program Core;

type T0;
type T1 (x : Type);

type Byte := bv8;
type IntMap := Map int int;

type MyMap (a : Type, b : Type);
type Foo (a : Type, b : Type) := Map b a;

datatype List () { Nil(), Cons(head: int, tail: List) };

datatype Tree () { Leaf(val: int), Node(left: Tree, right: Tree) };

const fooConst : int;
function id(x : int, y : int) : int { y }
function foo<T1, T2>(x : T1) : Map T1 T2;

axiom [fooConst_value]: fooConst == 5;

function f1(x: int): int;
axiom [f1_ax]: (forall x : int :: f1(x) > x);

function f2(x : int, y : bool): bool;
axiom [f2_ax]: (forall x : int, y : bool :: f2(x, true) == true);

function f3(x : int, y : bool, z : regex): bool;
axiom [f3_ax]: (forall x : int, y : bool, z : regex :: f3(x, y, z) == f2(x, y));

var g : bool;

procedure Test1(x : bool) returns (y : bool)
{
  y := x;
};

procedure Test2(x : bool) returns (y : bool)
spec {
  ensures (y == x);
  ensures (x == y);
  ensures (g == g);
  ensures (g == old(g));
  ensures [test_foo]: (fooConst == 5);
  ensures [List_head_test]: (List..isNil(Nil()));
  ensures [test_id]: (id(4,3) == 4);
} {
  y := x || x;
};
#end

/--
info: Rendered Program:

type T0;
type T1 (a0 : Type);
type Byte := bv8;
type IntMap := Map int int;
type MyMap (a0 : Type, a1 : Type);
type Foo (a : Type, b : Type) := Map b a;
datatype List {(Nil()),(Cons(head : int, tail : List))};
datatype Tree {(Leaf(val : int)),(Node(left : Tree, right : Tree))};
function fooConst () : int;
function id (x : int, y : int) : int {
y
}
function foo<T1, T2> (x : T1) : Map T1 T2;
axiom [fooConst_value]: fooConst==5;
function f1 (x : int) : int;
axiom [f1_ax]: forall x0 : int :: f1(x0)>x0;
function f2 (x : int, y : bool) : bool;
axiom [f2_ax]: forall x0 : int :: forall x1 : bool :: f2(x0, true)==true;
function f3 (x : int, y : bool, z : regex) : bool;
axiom [f3_ax]: forall x0 : int :: forall x1 : bool :: forall x2 : regex :: f3(x0, x1, x2)==f2(x0, x1);
var g : bool;
procedure Test1 (x : bool) returns (y : bool)
 {
(y) := x;
  }
;
procedure Test2 (x : bool) returns (y : bool)
spec{
  ensures [Test2_ensures_0]: y==x;
    ensures [Test2_ensures_1]: x==y;
    ensures [Test2_ensures_2]: g==g;
    ensures [Test2_ensures_3]: g==old(g);
    ensures [test_foo]: fooConst==5;
    ensures [List_head_test]: List..isNil(Nil);
    ensures [test_id]: id(4, 3)==4;
    } {
(y) := x||x;
  }
;
-/
#guard_msgs in
#eval ASTtoCST test1

def test2 :=
#strata
program Core;

datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };
procedure Extract<a>(xs : List a) returns (h : a)
spec { requires List..isCons(xs); } {
};
#end


#guard_msgs in
#eval ASTtoCST test2

end Strata.Test
