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

def testProgram : Program :=
#strata
program Core;
type T0;
type T1 (x : Type);
type Byte := bv8;
type IntMap := Map int int;
type MyMap (a : Type, b : Type);
type Foo (a : Type, b : Type) := Map b a;
const fooConst : int;
function id(x : int, y : int) : int { y }
function foo<T1, T2>(x : T1) : Map T1 T2;

// axiom [fooConst_value]: fooConst == 5;

// function f(x: int): int;
// axiom [f1]: (f(5) > 5);

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
  // ensures (g == old(g));
}
{
  y := x;
};

#end

--- #print CoreDDM.Expr

/--
info: Rendered Program:

type T0;
type T1 (a0 : Type);
type Byte := bv8;
type IntMap := Map int int;
type MyMap (a0 : Type, a1 : Type);
type Foo (a : Type, b : Type) := Map b a;
function fooConst () : int;
function id (x : int, y : int) : int {
y
}
function foo<T1, T2> (x : T1) : Map T1 T2;
var g:bool;
procedure Test1 (x : bool) returns (y : bool)
 {
(y) := x;
  }
;
procedure Test2 (x : bool) returns (y : bool)
spec{
  ensures [Test2_ensures_0]:y==x;
    ensures [Test2_ensures_1]:x==y;
    ensures [Test2_ensures_2]:g==g;
    } {
(y) := x;
  }
;
-/
#guard_msgs in
#eval do
  -- Use old translator to get AST
  let (ast, errs) := TransM.run Inhabited.default (translateProgram testProgram)
  if !errs.isEmpty then
    IO.println f!"CST to AST Error: {errs}"

  -- Convert AST → CST
  match (programToCST (M := SourceRange) ast).run ToCSTContext.empty with
  | .error errs =>
    IO.println "AST to CST Error:"
    for err in errs do
      match err with
      | .unsupportedConstruct fn desc ctx _md =>
        IO.println s!"Unsupported construct in {fn}: {desc}\nContext: {ctx}"
  | .ok (cmds, _finalCtx) =>
    -- Format with original global context
    let ctx := FormatContext.ofDialects testProgram.dialects
      testProgram.globalContext {}
    let state : FormatState := {
      openDialects := testProgram.dialects.toList.foldl (init := {})
        fun a (d : Dialect) => a.insert d.name
    }

    -- Display commands using mformat
    IO.println "Rendered Program:\n"
    for cmd in cmds do
      IO.print ((mformat (ArgF.op cmd.toAst) ctx state).format)

end Strata.Test
