/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.ProcedureType
meta import Strata.Languages.Core
import Strata.Languages.Core.Factory
import StrataDDM.Integration.Lean.HashCommands
meta import StrataTest.Languages.Core.Tests.TestUtil
meta import StrataTest.Transform.CallFixtures

meta section

namespace Core

---------------------------------------------------------------------

section Tests
open Std (ToFormat Format format)
open Procedure Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Core.TestUtil (anyFunction callTyArgs cfgProc coreVerdict declNondet identityDecl listDecl
  mkProc translate tyArgsOfResult verdictOf)

/--
info: ok: (procedure P (x : int, out y : int)
 spec {
   requires [|0_lt_x|]: int.lt(0, x);
   ensures [ret_y_lt_0]: int.lt(y, 0);
   } {
   y := int.sub(0, x);
 };
 ,
 context:
 types:   
 aliases: [] state: tyGen: 0 tyPrefix: $__ty exprGen: 0 exprPrefix: $__var subst: )
-/
#guard_msgs in
#eval do let ans ← Procedure.typeCheck { LContext.default with functions := Core.Factory }
                             TEnv.default
                             Program.init
                             { header := {name := "P",
                                          typeArgs := [],
                                          inputs := [("x", mty[int])],
                                          outputs := [("y", mty[int])] },
                               spec := { preconditions := [("0_lt_x", ⟨eb[((~Int.Lt #0) x)], .Default, #[]⟩)],
                                         postconditions := [("ret_y_lt_0", ⟨eb[((~Int.Lt y) #0)], .Default, #[]⟩)] },
                               body := .structured [
                                 Statement.set "y" eb[((~Int.Sub #0) x)] .empty
                               ] false
                             }
                            .empty
         return format ans

/-! ## Rigid procedure type parameters and their scope -/

-- A postcondition may quantify over the procedure's rigid parameter type.
open Strata in
private def constAllPgm :=
#strata
program Core;
procedure ConstAll<a>(x : a, out r : a)
spec {
  ensures (forall y : a :: y == x);
}
{
  r := x;
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure ConstAll<a> (x : a, out r : a)
spec {
  ensures [ConstAll_ensures_0]: forall y : a :: y == x;
} {
  r := x;
};
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate constAllPgm))

/-- `Test` calls `Foo` with a Boolean output variable. -/
private def callFooAtBool : Decl :=
  mkProc "Test" [] [] []
    [Statement.init "y" (.forAll [] .bool) (.det eb[#true]) .empty,
     Statement.call "Foo" none [.outArg "y"] .empty]

private def xAndTrue : Expression.Expr := eb[((~Bool.And x) #true)]

private def nilExpr : Expression.Expr := .op Core.coreLoc "Nil" none

-- Assigning `0` to `x : a` would refine the rigid parameter `a` to `int`.
private def rigidOutputAssignmentRefinementPgm : Program := { decls :=
  [mkProc "Foo" ["a"] [] [("x", .ftvar "a")]
     [Statement.set "x" eb[#0] .empty],
   callFooAtBool] }

/--
info: error: Procedure 'Foo': Rigid type variable 'a' was refined to 'int'
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default rigidOutputAssignmentRefinementPgm)

-- Passing `x : a` as an `int` output would refine the rigid `a`.
private def rigidCallOutputRefinementPgm : Program := { decls :=
  [mkProc "Bar" [] [] [("r", .int)] [Statement.set "r" eb[#0] .empty],
   mkProc "Foo" ["a"] [] [("x", .ftvar "a")]
     [Statement.call "Bar" none [.outArg "x"] .empty],
   callFooAtBool] }

/--
info: error: Procedure 'Foo': Rigid type variable 'a' was refined to 'int'
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default rigidCallOutputRefinementPgm)

-- Using `x : a` as a Boolean guard would refine the rigid `a`.
private def rigidConditionalGuardRefinementPgm : Program := { decls :=
  [mkProc "Foo" ["a"] [("x", .ftvar "a")] []
    [.ite (.det xAndTrue) [] [] .empty]] }

/--
info: error: Procedure 'Foo': Rigid type variable 'a' was refined to 'bool'
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default rigidConditionalGuardRefinementPgm)

-- Using `x : a` as a loop guard would refine the rigid `a`.
private def rigidLoopGuardRefinementPgm : Program := { decls :=
  [mkProc "Foo" ["a"] [("x", .ftvar "a")] []
    [.loop (.det xAndTrue) none [] [] .empty]] }

/--
info: error: Procedure 'Foo': Rigid type variable 'a' was refined to 'bool'
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default rigidLoopGuardRefinementPgm)

-- Assigning `Nil()` to `x : a` would refine the rigid `a` to `List _`.
private def rigidUnsolvedListRefinementPgm : Program := { decls :=
  [listDecl,
   mkProc "Foo" ["a"] [] [("x", .ftvar "a")]
     [Statement.set "x" nilExpr .empty]] }

/--
info: error: Procedure 'Foo': Rigid type variable 'a' was refined to '(List _)'
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default rigidUnsolvedListRefinementPgm)

-- Passing `x : a` as a `List c` call output would refine the rigid `a` to `List _`.
private def rigidCallUnsolvedListRefinementPgm : Program := { decls :=
  [listDecl,
   mkProc "Mk" ["c"] [] [("r", .tcons "List" [.ftvar "c"])]
     [Statement.set "r" nilExpr .empty],
   mkProc "Foo" ["a"] [] [("x", .ftvar "a")]
     [Statement.call "Mk" none [.outArg "x"] .empty]] }

/--
info: error: Procedure 'Foo': Rigid type variable 'a' was refined to '(List _)'
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default rigidCallUnsolvedListRefinementPgm)

-- A call instantiates `T` once, so an `int` input with a `bool` output is rejected.
private def inconsistentCallInstantiationPgm : Program := { decls :=
  [identityDecl,
   mkProc "Bad" [] [] [("result", .bool)]
     [Statement.init "n" (.forAll [] .int) (.det eb[#42]) .empty,
      Statement.init "b" (.forAll [] .bool) (.det eb[#true]) .empty,
      Statement.call "Identity" none [.inArg eb[n], .outArg "b"] .empty,
      Statement.set "result" eb[b] .empty]] }

/--
info: error: Procedure 'Bad': [call Identity]: argument types [int] and return types [bool] are incompatible with signature ([T]) → ([T])
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default inconsistentCallInstantiationPgm)

-- An argument whose type nothing constrains is shown as `_`, not by its generated name.
private def openArgumentCallPgm : Program := { decls :=
  [.func anyFunction .empty,
   mkProc "F" [] [("x", .int)] [("y", .int)] [Statement.set "y" eb[x] .empty],
   mkProc "Bad" [] [] [("b", .bool)]
     [Statement.call "F" none [.inArg (.op Core.coreLoc "any" none), .outArg "b"] .empty]] }

/--
info: error: Procedure 'Bad': [call F]: argument types [_] and return types [bool] are incompatible with signature ([int]) → ([int])
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default openArgumentCallPgm)

/-! ## Stored call type arguments -/

/-- The type arguments stored on each call of `pgm` after type checking, in program order. -/
private def checkedTyArgs (pgm : Program) : List (Option (List String)) :=
  tyArgsOfResult (Core.typeCheck .default pgm)

-- `Caller` calls `Identity<T>` with an `int`, so the checked call stores `int` for `T`.
private def tyArgsStoredPgm : Program := { decls :=
  [identityDecl,
   mkProc "Caller" [] [] [("m", .int)]
     [Statement.init "n" (.forAll [] .int) (.det eb[#42]) .empty,
      Statement.call "Identity" none [.inArg eb[n], .outArg "m"] .empty]] }

/-- info: [none] -/
#guard_msgs in
#eval callTyArgs tyArgsStoredPgm

/--
info: [Strata.Core] Type checking succeeded.

---
info: [some ["int"]]
-/
#guard_msgs in
#eval checkedTyArgs tyArgsStoredPgm

-- The checker computes the type arguments itself and ignores a value the call already carries.
private def tyArgsBogusPgm : Program := { decls :=
  [identityDecl,
   mkProc "Caller" [] [] [("m", .int)]
     [Statement.init "n" (.forAll [] .int) (.det eb[#42]) .empty,
      Statement.call "Identity" (some [.forAll [] .bool]) [.inArg eb[n], .outArg "m"]
        .empty]] }

/-- info: [some ["bool"]] -/
#guard_msgs in
#eval callTyArgs tyArgsBogusPgm

/--
info: [Strata.Core] Type checking succeeded.

---
info: [some ["int"]]
-/
#guard_msgs in
#eval checkedTyArgs tyArgsBogusPgm

-- `Wrap<U>` calls `Identity<T>` with its own type parameter `U`, so the call stores `U`.
private def tyArgsRigidPgm : Program := { decls :=
  [identityDecl,
   mkProc "Wrap" ["U"] [("a", .ftvar "U")] [("b", .ftvar "U")]
     [Statement.call "Identity" none [.inArg eb[a], .outArg "b"] .empty]] }

/--
info: [Strata.Core] Type checking succeeded.

---
info: [some ["U"]]
-/
#guard_msgs in
#eval checkedTyArgs tyArgsRigidPgm

-- `Pair<A, B>` and `Swap<A, B>` list their type parameters in the same order but use them in
-- opposite orders in the formals, so each call stores `[int, bool]`, in parameter order.
private def tyArgsTwoParamPgm : Program := { decls :=
  [mkProc "Pair" ["A", "B"] [("x", .ftvar "A"), ("y", .ftvar "B")] [("r", .ftvar "A")]
     [Statement.set "r" eb[x] .empty],
   mkProc "Swap" ["A", "B"] [("x", .ftvar "B"), ("y", .ftvar "A")] [("r", .ftvar "A")]
     [Statement.set "r" eb[y] .empty],
   mkProc "Caller" [] [] [("m", .int)]
     [Statement.init "n" (.forAll [] .int) (.det eb[#42]) .empty,
      Statement.init "b" (.forAll [] .bool) (.det eb[#true]) .empty,
      Statement.call "Pair" none [.inArg eb[n], .inArg eb[b], .outArg "m"] .empty,
      Statement.call "Swap" none [.inArg eb[b], .inArg eb[n], .outArg "m"] .empty]] }

/--
info: [Strata.Core] Type checking succeeded.

---
info: [some ["int", "bool"], some ["int", "bool"]]
-/
#guard_msgs in
#eval checkedTyArgs tyArgsTwoParamPgm

-- A call to a callee without type parameters stores the empty list.
private def tyArgsMonomorphicPgm : Program := { decls :=
  [mkProc "Inc" [] [("x", .int)] [("y", .int)] [Statement.set "y" eb[x] .empty],
   mkProc "Caller" [] [] [("m", .int)]
     [Statement.init "n" (.forAll [] .int) (.det eb[#42]) .empty,
      Statement.call "Inc" none [.inArg eb[n], .outArg "m"] .empty]] }

/--
info: [Strata.Core] Type checking succeeded.

---
info: [some []]
-/
#guard_msgs in
#eval checkedTyArgs tyArgsMonomorphicPgm

-- Calls inside a block, both branches of a conditional and a loop body each store their own
-- type arguments.
private def tyArgsNestedPgm : Program := { decls :=
  [identityDecl,
   mkProc "Caller" [] [] [("m", .int), ("c", .bool)]
     [Statement.init "n" (.forAll [] .int) (.det eb[#42]) .empty,
      Statement.init "b" (.forAll [] .bool) (.det eb[#true]) .empty,
      .block "blk" [Statement.call "Identity" none [.inArg eb[n], .outArg "m"] .empty] .empty,
      .ite (.det eb[b])
        [Statement.call "Identity" none [.inArg eb[b], .outArg "c"] .empty]
        [Statement.call "Identity" none [.inArg eb[n], .outArg "m"] .empty] .empty,
      .loop (.det eb[b]) none []
        [Statement.call "Identity" none [.inArg eb[b], .outArg "c"] .empty] .empty]] }

/--
info: [Strata.Core] Type checking succeeded.

---
info: [some ["int"], some ["bool"], some ["int"], some ["bool"]]
-/
#guard_msgs in
#eval checkedTyArgs tyArgsNestedPgm

-- Calls in two blocks of a control-flow graph body each store their own type arguments.
private def tyArgsCfgPgm : Program := { decls :=
  [identityDecl,
   cfgProc "Caller" [] [("m", .int), ("c", .bool)]
     [("entry",
       { cmds :=
           [.cmd (.init "n" (.forAll [] .int) (.det eb[#42]) .empty),
            .cmd (.init "b" (.forAll [] .bool) (.det eb[#true]) .empty),
            .call "Identity" none [.inArg eb[n], .outArg "m"] .empty],
         transfer := .goto "next" .empty }),
      ("next",
       { cmds := [.call "Identity" none [.inArg eb[b], .outArg "c"] .empty],
         transfer := .finish .empty })]] }

/--
info: [Strata.Core] Type checking succeeded.

---
info: [some ["int"], some ["bool"]]
-/
#guard_msgs in
#eval checkedTyArgs tyArgsCfgPgm

-- `q<a>()` has no arguments, so the call does not determine `a`. The checker stores a generated
-- type variable for it, which is not a type parameter of the caller, so it rejects the program.
/--
info: REJECTED: Procedure 'Caller': the call to 'q' does not determine one of its type
parameters
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (Core.CallFixtures.qProg Core.CallFixtures.qReflDecl)

/-! ## Distinct call results -/

-- A call may not pass the same variable for more than one of its results.
private def threeOutputs : Decl :=
  mkProc "three" [] [] [("x", .int), ("y", .int), ("z", .int)]
    [Statement.set "x" eb[#1] .empty, Statement.set "y" eb[#2] .empty,
     Statement.set "z" eb[#3] .empty]

private def repeatedOutCallPgm : Program := { decls :=
  [threeOutputs,
   mkProc "Caller" [] [] []
     [Statement.init "x" (.forAll [] .int) (.det eb[#0]) .empty,
      Statement.call "three" none [.outArg "x", .outArg "x", .outArg "x"] .empty]] }

/--
info: error: Procedure 'Caller': [call three(out x, out x, out x);]: Ill-formed call: the call to three passes the variable x for more than one out parameter; the results of a call must be distinct variables
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default repeatedOutCallPgm)

-- An in-out argument and an output of the same call may not be the same variable.
private def repeatedInoutOutCallPgm : Program := { decls :=
  [mkProc "P" [] [("a", .int)] [("a", .int), ("b", .int)]
     [Statement.set "a" eb[#1] .empty, Statement.set "b" eb[#0] .empty],
   mkProc "Caller" [] [] []
     [Statement.init "g" (.forAll [] .int) (.det eb[#0]) .empty,
      Statement.call "P" none [.inoutArg "g", .outArg "g"] .empty]] }

/--
info: error: Procedure 'Caller': [call P(inout g, out g);]: Ill-formed call: the call to P passes the inout argument g for more than one inout or out parameter; an inout argument must not alias another result of the call
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default repeatedInoutOutCallPgm)

-- Distinct variables for the results of a call are accepted.
open Strata in
private def distinctOutCallPgm :=
#strata
program Core;
procedure three(out x : int, out y : int, out z : int)
{
  x := 1;
  y := 2;
  z := 3;
};
procedure Caller()
{
  var x : int := 0;
  var y : int := 0;
  var z : int := 0;
  call three(out x, out y, out z);
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure three (out x : int, out y : int, out z : int)
{
  x := 1;
  y := 2;
  z := 3;
};
procedure Caller ()
{
  var x : int := 0;
  var y : int := 0;
  var z : int := 0;
  call three(out x, out y, out z);
};
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate distinctOutCallPgm))

/-! ## No position in a procedure may refine its rigid type parameters -/

-- A precondition may not refine the rigid `a`.
private def preRefinePgm : Program := { decls :=
  [mkProc "PreRefine" ["a"] [("x", .ftvar "a")] [] (pre := [eb[x == #5]])] }

/--
info: error: Procedure 'PreRefine', condition 'PreRefine_requires_0': Rigid type variable 'a' was refined to 'int'
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default preRefinePgm)

-- A postcondition may not refine the rigid `a`.
private def postRefinePgm : Program := { decls :=
  [mkProc "PostRefine" ["a"] [] [("r", .ftvar "a")] (post := [eb[r == #5]])] }

/--
info: error: Procedure 'PostRefine', condition 'PostRefine_ensures_0': Rigid type variable 'a' was refined to 'int'
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default postRefinePgm)

-- A loop invariant may not refine the rigid `a`.
private def invRefinePgm : Program := { decls :=
  [mkProc "InvRefine" ["a"] [("x", .ftvar "a")] []
    [.loop (.det eb[#true]) none [("inv", eb[x == #5])] [] .empty]] }

/--
info: error: Procedure 'InvRefine': Rigid type variable 'a' was refined to 'int'
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default invRefinePgm)

-- Initializing `y : a` with an integer would refine the rigid `a`.
private def localConcretizePgm : Program := { decls :=
  [mkProc "LocalConc" ["a"] [("x", .ftvar "a")] []
    [Statement.init "y" (.forAll [] (.ftvar "a")) (.det eb[#5]) .empty]] }

/--
info: error: Procedure 'LocalConc': Rigid type variable 'a' was refined to 'int'
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default localConcretizePgm)

-- Using `x : a` in a loop measure's integer addition would refine the rigid `a`.
private def loopMeasureRefinePgm : Program := { decls :=
  [mkProc "DecRefine" ["a"] [("x", .ftvar "a")] []
    [.loop (.det eb[#true]) (some eb[((~Int.Add x) #0)]) [] [] .empty]] }

/--
info: error: Procedure 'DecRefine': Rigid type variable 'a' was refined to 'int'
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default loopMeasureRefinePgm)

-- Assigning `y : b` to `z : a` would identify two distinct rigid parameters.
private def procUnifyParamsPgm : Program := { decls :=
  [mkProc "UnifyParams" ["a", "b"] [("x", .ftvar "a"), ("y", .ftvar "b")]
    [("z", .ftvar "a")] [Statement.set "z" eb[y] .empty]] }

/--
info: error: Procedure 'UnifyParams': Rigid type variable 'a' was refined to 'b'
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default procUnifyParamsPgm)

-- A type parameter used only by a postcondition binder keeps its declared name.
open Strata in
private def postOnlyTyVarPgm :=
#strata
program Core;
procedure PostOnly<a>()
spec {
  ensures (forall q : a :: true);
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure PostOnly<a> ()
spec {
  ensures [PostOnly_ensures_0]: forall q : a :: true;
  } ;
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate postOnlyTyVarPgm))

-- An assertion may not refine the rigid `a` to `bool`.
private def assertRefinePgm : Program := { decls :=
  [mkProc "AssertRefine" ["a"] [("x", .ftvar "a")] []
    [Statement.assert "assert_0" xAndTrue .empty]] }

/--
info: error: Procedure 'AssertRefine': Rigid type variable 'a' was refined to 'bool'
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default assertRefinePgm)

-- Callee type parameters are independent of equally named caller parameters.

-- A precondition calling `g` at `int` does not constrain the procedure's `a`.
open Strata in
private def preCoincidentPgm :=
#strata
program Core;
function g<a>(x : a) : int;
procedure PreCallCoincident<a>(y : a)
spec {
  requires (g(42) == 0);
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function g<a> (x : a) : int;
procedure PreCallCoincident<a> (y : a)
spec {
  requires [PreCallCoincident_requires_0]: g(42) == 0;
  } ;
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate preCoincidentPgm))

-- Renaming the callee's type parameter preserves acceptance.
open Strata in
private def preRenamedPgm :=
#strata
program Core;
function g<b>(x : b) : int;
procedure PreCallRenamed<a>(y : a)
spec {
  requires (g(42) == 0);
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function g<b> (x : b) : int;
procedure PreCallRenamed<a> (y : a)
spec {
  requires [PreCallRenamed_requires_0]: g(42) == 0;
  } ;
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate preRenamedPgm))

-- A body assertion may call a function with an equally named type parameter.
open Strata in
private def bodyCoincidentPgm :=
#strata
program Core;
function g<a>(x : a) : int;
procedure BodyCallCoincident<a>(y : a)
{
  assert (g(42) == 0);
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function g<a> (x : a) : int;
procedure BodyCallCoincident<a> (y : a)
{
  assert [assert_0]: g(42) == 0;
};
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate bodyCoincidentPgm))

-- A postcondition may call `g` at `int`.
open Strata in
private def postCoincidentPgm :=
#strata
program Core;
function g<a>(x : a) : int;
procedure PostCallCoincident<a>(y : a)
spec {
  ensures (g(42) == 0);
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function g<a> (x : a) : int;
procedure PostCallCoincident<a> (y : a)
spec {
  ensures [PostCallCoincident_ensures_0]: g(42) == 0;
  } ;
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate postCoincidentPgm))

-- A loop invariant may call `g` at `int`.
open Strata in
private def invCoincidentPgm :=
#strata
program Core;
function g<a>(x : a) : int;
procedure InvCallCoincident<a>(y : a)
{
  while (true)
    invariant (g(42) == 0)
  {
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function g<a> (x : a) : int;
procedure InvCallCoincident<a> (y : a)
{
  while (true)
  invariant g(42) == 0
  {

  }
};
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate invCoincidentPgm))

-- Equally named type parameters of two separate functions remain independent.
open Strata in
private def funcBodyCoincidentPgm :=
#strata
program Core;
function g<a>(x : a) : int;
function f<a>(y : a) : int {
  g(42)
}
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function g<a> (x : a) : int;
function f<a> (y : a) : int {
  g(42)
}
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate funcBodyCoincidentPgm))

-- A procedure parameter may be passed to a function with an equally named type parameter.
open Strata in
private def preCallAtParamPgm :=
#strata
program Core;
function g<a>(x : a) : int;
procedure PreCallAtParam<a>(y : a)
spec {
  requires (g(y) == 0);
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function g<a> (x : a) : int;
procedure PreCallAtParam<a> (y : a)
spec {
  requires [PreCallAtParam_requires_0]: g(y) == 0;
  } ;
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate preCallAtParamPgm))

-- `g(y) : a` may be assigned to `z : a` though `g` and the procedure both bind `a`.
open Strata in
private def assignCallCoincidentPgm :=
#strata
program Core;
function g<a>(x : a) : a;
procedure AssignCallCoincident<a>(y : a, out z : a)
{
  z := g(y);
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function g<a> (x : a) : a;
procedure AssignCallCoincident<a> (y : a, out z : a)
{
  z := g(y);
};
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate assignCallCoincidentPgm))

/-- `function g<b>(x : b) : b;`. -/
private def polyIdG : Decl :=
  .func { name := "g", typeArgs := ["b"], inputs := [("x", .ftvar "b")],
          output := .ftvar "b" } .empty

private def gOfYEq5 : Expression.Expr := eb[(~g y) == #5]

-- Comparing `g(y) : a` with an integer would refine the procedure's rigid `a`.
private def preRefineThroughCallPgm : Program := { decls :=
  [polyIdG,
   mkProc "PreRefineThroughCall" ["a"] [("y", .ftvar "a")] []
     (pre := [gOfYEq5])] }

/--
info: error: Procedure 'PreRefineThroughCall', condition 'PreRefineThroughCall_requires_0': Rigid type variable 'a' was refined to 'int'
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default preRefineThroughCallPgm)

-- Comparing `g(y) : a` with an integer in a body assertion would refine the rigid `a`.
private def bodyRefineThroughCallPgm : Program := { decls :=
  [polyIdG,
   mkProc "BodyRefineThroughCall" ["a"] [("y", .ftvar "a")] []
     [Statement.assert "assert_0" gOfYEq5 .empty]] }

/--
info: error: Procedure 'BodyRefineThroughCall': Rigid type variable 'a' was refined to 'int'
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default bodyRefineThroughCallPgm)

-- Assigning a callee's `int` result to `z : a` would refine the rigid `a`.
private def assignRefineThroughCallPgm : Program := { decls :=
  [.func { name := "g", typeArgs := ["b"], inputs := [("x", .ftvar "b")],
           output := .int } .empty,
   mkProc "AssignRefineThroughCall" ["a"] [("y", .ftvar "a")]
     [("z", .ftvar "a")] [Statement.set "z" eb[(~g y)] .empty]] }

/--
info: error: Procedure 'AssignRefineThroughCall': Rigid type variable 'a' was refined to 'int'
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default assignRefineThroughCallPgm)

-- A measure that is a formal of a type-variable type is rejected.
open Strata in
private def typeVarMeasurePgm :=
#strata
program Core;
rec function r<a>(x : a) : int
  decreases x
{
  r(x)
};
#end

/--
info: error: recursive function 'r': decreases expression must have type int or be a parameter of a datatype type, got 'a'
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate typeVarMeasurePgm))

-- A recursive function may call itself at its declared rigid parameter type.
open Strata in
private def monoRecIntMeasurePgm :=
#strata
program Core;
rec function r<a>(x : a, n : int) : int
  decreases n
{
  r(x, n)
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

rec function r<a> (x : a, n : int) : int
decreases n
  {
  r(x, n)
};
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate monoRecIntMeasurePgm))

-- A recursive call at `int` is accepted (polymorphic recursion); the measure `x : a` is not an
-- `int` or a datatype parameter, which is rejected.
/-- `rec function r<a>(x : a) : int decreases x { r(42) }`, with the
    self-call annotated `a → int`. -/
private def polyRecFunc : Function :=
  { name := ⟨"r", ()⟩, typeArgs := ["a"], isRecursive := true,
    inputs := [(⟨"x", ()⟩, .ftvar "a")], output := .int,
    measure := some (.fvar Core.coreLoc ⟨"x", ()⟩ (some (.ftvar "a"))),
    body := some (.app Core.coreLoc (.op Core.coreLoc ⟨"r", ()⟩ (some (.arrow (.ftvar "a") .int)))
      (.intConst Core.coreLoc 42)),
    attr := #[.inlineIfAllValues] }

/--
info: REJECTED: recursive function 'r': decreases expression must have type int or be a parameter of a datatype type, got 'a'
-/
#guard_msgs in
#eval coreVerdict { decls := [.recFuncBlock [polyRecFunc] .empty] }

-- A top-level function and a top-level procedure may not share a name.
open Strata in
private def sameNameCallPgm :=
#strata
program Core;
function h<a>(x : a) : int;
procedure h<a>(y : a)
{
  assert (h(42) == 0);
};
#end

/--
info: error: Error in procedure h: a declaration of this name already exists.
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate sameNameCallPgm))

-- A body-local `function` may name the enclosing rigid `a`; its stored type keeps `a`.
open Strata in
private def localFuncAtRigidPgm :=
#strata
program Core;
procedure NestedCaptureConsistent<a>(x : a, out z : a)
{
  function g(y : a) : a { y }
  z := g(x);
};
#end

/--
info: [Strata.Core] Type checking succeeded.
 
---
info: ok: program Core;
 
procedure NestedCaptureConsistent<a> (x : a, out z : a)
{
  var g : a -> a := fun y : a => y;
  z := g(x);
};
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate localFuncAtRigidPgm))

-- Using a local function's result of rigid type `a` at `int` would refine `a`.
open Strata in
private def localFuncResultAtIntPgm :=
#strata
program Core;
procedure CaptureGen<a>(x : a)
{
  function g() : a { x }
  var i : int := g();
};
#end

/--
info: REJECTED: Procedure 'CaptureGen': Rigid type variable 'a' was refined to 'int'
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate localFuncResultAtIntPgm)

-- A local function declared to return the rigid `a` may not have an `int` body.
open Strata in
private def localFuncIntBodyPgm :=
#strata
program Core;
procedure CaptureFix<a>(x : a)
{
  function g() : a { 5 }
};
#end

/--
info: REJECTED: Procedure 'CaptureFix': Rigid type variable 'a' was refined to 'int'
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate localFuncIntBodyPgm)

-- A local function declared to return `int` may not have a body of rigid type `t`.
open Strata in
private def captureIntResultPgm :=
#strata
program Core;
procedure CaptureIntResult<t>(y : t)
{
  function f() : int { y }
};
#end

/--
info: REJECTED: Procedure 'CaptureIntResult': Rigid type variable 't' was refined to 'int'
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict (translate captureIntResultPgm)

-- A procedure parameter may share its name with a constant, which it shadows.
open Strata in
private def procParamCollidesPgm :=
#strata
program Core;

const y : int;
procedure P(y : int) {
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function y () : int;
procedure P (y : int)
{
  
};
-/
#guard_msgs in
#eval
  Std.format (Core.typeCheck .default (translate procParamCollidesPgm))

-- A procedure with a repeated type parameter is rejected.
private def procDupTypeArgsPgm : Program :=
  { decls := [
      .proc { header := { name := "P", typeArgs := ["a", "a"], inputs := [], outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [] false } .empty
  ]}

/--
info: error: Procedure 'P': duplicate type arguments [a, a]
-/
#guard_msgs in
#eval Std.format (Core.typeCheck .default procDupTypeArgsPgm)

-- A repeated type parameter with a reserved prefix is reported as written.
private def procDupReservedTypeArgsPgm : Program :=
  { decls := [
      .proc { header := { name := "P", typeArgs := ["$__ty0", "$__ty0"], inputs := [],
                          outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [] false } .empty
  ]}

/--
info: error: Procedure 'P': duplicate type arguments [$__ty0, $__ty0]
-/
#guard_msgs in
#eval Std.format (Core.typeCheck .default procDupReservedTypeArgsPgm)

-- A procedure type parameter with the generated-variable prefix `$__ty` is renamed, so the
-- procedure is accepted.
private def procReservedTypeArgPgm : Program :=
  { decls := [
      .proc { header := { name := "P", typeArgs := ["$__ty0"],
                          inputs := [("x", .ftvar "$__ty0")], outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [] false } .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure P<a> (x : a)
{
  
};
-/
#guard_msgs in
#eval Std.format (Core.typeCheck .default procReservedTypeArgPgm)

-- A procedure type parameter with the precondition-instance prefix `$__precond_` is renamed,
-- so the procedure is accepted.
private def procPrecondTypeArgPgm : Program :=
  { decls := [
      .proc { header := { name := "P", typeArgs := ["$__precond_b"],
                          inputs := [("x", .ftvar "$__precond_b")], outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [] false } .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure P<a> (x : a)
{
  
};
-/
#guard_msgs in
#eval Std.format (Core.typeCheck .default procPrecondTypeArgPgm)

-- A procedure with two inputs of the same name is rejected.
private def procDupInputsPgm : Program :=
  { decls := [
      .proc { header := { name := "P", typeArgs := [],
                          inputs := [("x", .int), ("x", .int)], outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [] false } .empty
  ]}

/--
info: error: Procedure 'P': duplicate input parameter names [x, x]
-/
#guard_msgs in
#eval Std.format (Core.typeCheck .default procDupInputsPgm)

-- A procedure with two outputs of the same name is rejected.
private def procDupOutputsPgm : Program :=
  { decls := [
      .proc { header := { name := "P", typeArgs := [],
                          inputs := [], outputs := [("y", .int), ("y", .int)] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [] false } .empty
  ]}

/--
info: error: Procedure 'P': duplicate output parameter names [y, y]
-/
#guard_msgs in
#eval Std.format (Core.typeCheck .default procDupOutputsPgm)

-- An output named `old g` beside the in-out `g` is rejected.
private def procOldOutputPgm : Program :=
  { decls := [
      .proc { header := { name := "P", typeArgs := [], inputs := [("g", .int)],
                          outputs := [("g", .int), ("old g", .bool)] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [] false } .empty
  ]}

/--
info: error: [P] Parameter old g: a name starting with "old " denotes the initial value of an in-out parameter!
-/
#guard_msgs in
#eval Std.format (Core.typeCheck .default procOldOutputPgm)

-- An input named `old g` beside the in-out `g` is rejected.
private def procOldInputPgm : Program :=
  { decls := [
      .proc { header := { name := "P", typeArgs := [],
                          inputs := [("g", .int), ("old g", .bool)], outputs := [("g", .int)] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [] false } .empty
  ]}

/--
info: error: [P] Parameter old g: a name starting with "old " denotes the initial value of an in-out parameter!
-/
#guard_msgs in
#eval Std.format (Core.typeCheck .default procOldInputPgm)

-- A procedure name with the generated-variable prefix `$__ty` is accepted.
private def procReservedNamePgm : Program :=
  { decls := [
      .proc { header := { name := "$__tyP", typeArgs := [], inputs := [], outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [] false } .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure $__tyP ()
{
  
};
-/
#guard_msgs in
#eval Std.format (Core.typeCheck .default procReservedNamePgm)

-- A procedure parameter with the generated-variable prefix `$__ty` is accepted.
private def procReservedParamPgm : Program :=
  { decls := [
      .proc { header := { name := "P", typeArgs := [], inputs := [("$__ty0", .int)],
                          outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [] false } .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure P ($__ty0 : int)
{
  
};
-/
#guard_msgs in
#eval Std.format (Core.typeCheck .default procReservedParamPgm)

-- A procedure body assigning an input, which is neither an output nor a local, is rejected.
private def procModifiesInputPgm : Program :=
  { decls := [
      .proc { header := { name := "P", typeArgs := [], inputs := [("x", .int)], outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [Statement.set "x" (LExpr.intConst Core.coreLoc 1) .empty] false }
                  .empty
  ]}

/--
info: error: Procedure 'P': variable 'x' is modified but is not an output parameter or a local
variable
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default procModifiesInputPgm)

-- A local variable may share its name with a constant, which it shadows.
private def localVarCollidesPgm : Program :=
  { decls := [
      Decl.const ⟨"c", ()⟩ .int,
      .proc { header := { name := "P", typeArgs := [], inputs := [], outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [
                Statement.init "c" (.forAll [] .int) .nondet .empty
              ] false } .empty
  ]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function c () : int;
procedure P ()
{
  var c : int;
};
-/
#guard_msgs in
#eval Std.format (Core.typeCheck .default localVarCollidesPgm)

-- A precondition naming an undeclared variable `z` is rejected.
private def preUnknownVarProg : Program :=
  { decls := [
      .proc { header := { name := "PreUnknownVar", typeArgs := [],
                          inputs := [("x", mty[int])], outputs := [] },
              spec := { preconditions := [("pre_unknown", ⟨eb[z], .Default, #[]⟩)],
                        postconditions := [] },
              body := .structured [] false } .empty
  ]}

/--
info: error: Procedure 'PreUnknownVar', condition 'pre_unknown': [z] No free variables are allowed here!
Free Variables: [z]
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default preUnknownVarProg)

-- A precondition whose free variable has the generated binder name `$__var0` is rejected.
private def preBinderCapturesFvarProg : Program :=
  let generatedBinderName : CoreIdent := ⟨"$__var0", ()⟩
  let cond : Expression.Expr :=
    .quant Core.coreLoc .all "q" (some .int) (LExpr.noTrigger Core.coreLoc)
      (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.fvar Core.coreLoc generatedBinderName none))
  { decls := [
      .proc { header := { name := "PreBinderCapture", typeArgs := [],
                          inputs := [("x", mty[int])], outputs := [] },
              spec := { preconditions := [("pre_capture", ⟨cond, .Default, #[]⟩)],
                        postconditions := [] },
              body := .structured [] false } .empty
  ]}

/--
info: error: Procedure 'PreBinderCapture', condition 'pre_capture': [forall q : int :: q == $__var0] No free variables are allowed here!
Free Variables: [$__var0]
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default preBinderCapturesFvarProg)

-- A precondition may refer to the procedure's input parameters.
open Strata in
private def preOverInputsPgm :=
#strata
program Core;
procedure PreOverInputs(x : int, y : int)
spec {
  requires (x == y);
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure PreOverInputs (x : int, y : int)
spec {
  requires [PreOverInputs_requires_0]: x == y;
  } ;
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate preOverInputsPgm))

-- A postcondition may refer to an output parameter.
open Strata in
private def postOverOutputPgm :=
#strata
program Core;
procedure PostOverOutput(x : int, out r : int)
spec {
  ensures (r == x);
}
{
  r := x;
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure PostOverOutput (x : int, out r : int)
spec {
  ensures [PostOverOutput_ensures_0]: r == x;
} {
  r := x;
};
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate postOverOutputPgm))

-- A precondition may bind its own quantified variable.
open Strata in
private def preQuantifierBinderPgm :=
#strata
program Core;
procedure PreQuantifierBinder(x : int)
spec {
  requires (forall q : int :: q == x);
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure PreQuantifierBinder (x : int)
spec {
  requires [PreQuantifierBinder_requires_0]: forall q : int :: q == x;
  } ;
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate preQuantifierBinderPgm))

/-! ## Condition annotations

A condition's type may be fixed by `bool`; annotation type variables must be type parameters. -/

section ConditionAnnotations
open Imperative
open Core.TestUtil (Env0 programVerdict)

/-! ### A condition whose type only the expected type fixes

Function and procedure preconditions `anybool()` are accepted. -/

private def expectedFixesPgm : StrataDDM.Program :=
#strata
program Core;

function anybool<a>() : a;

function pf(n : int) : int
  requires (anybool());
{
  n
}

procedure pp ()
spec {
  requires (anybool());
};
#end

/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (translate expectedFixesPgm)

/-! ### A chain of polymorphic identities linked to one type variable

Wrapping `anybool()` in polymorphic identities is accepted. -/

private def chainPgm : StrataDDM.Program :=
#strata
program Core;

function anybool<a>() : a;
function idb<a>(x : a) : a;

function pf(n : int) : int
  requires (idb(idb(anybool())));
{
  n
}

procedure pp ()
spec {
  requires (idb(idb(anybool())));
};
#end

/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (translate chainPgm)

/-! ### Postconditions

A postcondition `anybool()` is accepted. -/

private def postPgm : StrataDDM.Program :=
#strata
program Core;

function anybool<a>() : a;

procedure pp ()
spec {
  ensures (anybool());
};
#end

/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (translate postPgm)

/-! ### Binder annotation type variables must be procedure type parameters

Any other type variable is rejected; a type parameter is stored as written. -/

/-- Check a procedure with the given conditions and show the stored procedure, or the error. -/
private def storedConditions (typeArgs : List TyIdentifier) (inputs : @LMonoTySignature Unit)
    (pre post : List Expression.Expr) : Std.Format :=
  let label (n : Nat) := s!"c{n}"
  let proc : Procedure :=
    { header := { name := ⟨"pp", ()⟩, typeArgs, inputs, outputs := [] }
      spec := { preconditions := pre.zipIdx.map fun (e, n) => (label n, { expr := e })
                postconditions :=
                  post.zipIdx.map fun (e, n) => (label (pre.length + n), { expr := e }) }
      body := .structured [] false }
  match Core.Program.typeCheck initTyContext Env0 { decls := [.proc proc .empty] } with
  | .ok (p', _) => Std.format p'
  | .error e => f!"REJECTED: {e.message}"

/-- The condition `forall x : ty :: x == x`. -/
private def reflCond (ty : LMonoTy) : Expression.Expr :=
  LExpr.all Core.coreLoc "x" (some ty)
      (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0))

/--
info: REJECTED: Procedure 'pp', condition 'c0': type variable `b` is not in scope
-/
#guard_msgs in
#eval storedConditions [] [] [reflCond (.ftvar "b")] [reflCond (.ftvar "b")]

-- An annotation naming a procedure type parameter is stored as written.
/--
info: program Core;

procedure pp<b> ()
spec {
  requires [c0]: forall x : b :: x == x;
  } {
  
};
-/
#guard_msgs in
#eval storedConditions ["b"] [] [reflCond (.ftvar "b")] []

-- An undeclared `c` is rejected even though the quantifier body would fix it to `int`.
/--
info: REJECTED: Procedure 'pp', condition 'c0': type variable `c` is not in scope
-/
#guard_msgs in
#eval storedConditions []
  [] [LExpr.all Core.coreLoc "x" (some (.ftvar "c"))
      (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.intConst Core.coreLoc 1))] []

-- Neither `b` nor `c` is a type parameter; the first one met is reported.
/--
info: REJECTED: Procedure 'pp', condition 'c0': type variable `b` is not in scope
-/
#guard_msgs in
#eval storedConditions [] []
  [LExpr.all Core.coreLoc "x" (some (.ftvar "b"))
    (LExpr.all Core.coreLoc "y" (some (.ftvar "c"))
      (.eq Core.coreLoc (.bvar Core.coreLoc 1) (.bvar Core.coreLoc 0)))] []

end ConditionAnnotations

-- A local function body may read a procedure parameter of rigid type `a`.
open Strata in
private def nestedReadsOuterPgm :=
#strata
program Core;
procedure Outer<a>(p : a)
{
  function loc (y : int) : int { if p == p then y else y }
  assert [ok]: loc(1) == loc(1);
};
#end

/--
info: [Strata.Core] Type checking succeeded.
 
---
info: ok: program Core;
 
procedure Outer<a> (p : a)
{
  var loc : int -> int := fun y : int => (if p == p then y else y);
  assert [ok]: loc(1) == loc(1);
};
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate nestedReadsOuterPgm))

-- A binder annotation in a local function body may name the procedure's type parameter.
open Strata in
private def nestedBinderNamesOuterPgm :=
#strata
program Core;
procedure Outer<a>(p : a)
{
  function loc (y : int) : int { if (forall z : a :: z == z) then y else y }
};
#end

/--
info: [Strata.Core] Type checking succeeded.
 
---
info: ok: program Core;
 
procedure Outer<a> (p : a)
{
  var loc : int -> int := fun y : int => (if forall z : a :: z == z then y else y);
};
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate nestedBinderNamesOuterPgm))

-- An op annotation's type variables belong to the op: inside `pp<a>`, `idf` annotated `a → a`,
-- `c → c` or not at all may be used at `bool`, in a precondition and in a body assertion.
open Core.TestUtil (idfDecl idfTrueEq printIdfVerdicts) in
/--
info: ACCEPTED
ACCEPTED
ACCEPTED
-/
#guard_msgs in
#eval printIdfVerdicts fun ann => { decls := [idfDecl,
  .proc { header := { name := "pp", typeArgs := ["a"], inputs := [("x", .ftvar "a")],
                      outputs := [] }
          spec := { preconditions := [("c0", { expr := idfTrueEq ann })],
                    postconditions := [] }
          body := .structured [] false } .empty] }

open Core.TestUtil (idfDecl idfTrueEq printIdfVerdicts) in
/--
info: ACCEPTED
ACCEPTED
ACCEPTED
-/
#guard_msgs in
#eval printIdfVerdicts fun ann => { decls := [idfDecl,
  .proc { header := { name := "pp", typeArgs := ["a"], inputs := [("x", .ftvar "a")],
                      outputs := [] }
          spec := { preconditions := [], postconditions := [] }
          body := .structured [Statement.assert "t" (idfTrueEq ann) .empty] false } .empty] }

/-! ## Ambient rigid type variables

Rigid type variables of the calling context stay rigid in a procedure without type parameters. -/

private def ambientRigidC : Core.Expression.TyContext :=
  { LContext.default with
      functions := Core.Factory,
      knownTypes := Core.KnownTypes,
      rigidTypeVars := ["a"] }

private def ambientRigidProc (initTy : LMonoTy) : Procedure :=
  { header := { name := "ambientRigid", typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [
      .cmd (.cmd (.init "x" (.forAll [] initTy) (.det (.intConst Core.coreLoc 0)) #[]))
    ] false }

-- An ambient rigid `a` cannot be inferred as `int` from the initializer.
/-- info: REJECTED: Procedure 'ambientRigid': an ambient rigid type variable was refined -/
#guard_msgs in
#eval verdictOf (Procedure.typeCheck ambientRigidC TEnv.default Program.init
  (ambientRigidProc (.ftvar "a")) .empty)

-- A declaration at type `int` is accepted under the same ambient rigid context.
/-- info: ACCEPTED -/
#guard_msgs in
#eval verdictOf (Procedure.typeCheck ambientRigidC TEnv.default Program.init
  (ambientRigidProc .int) .empty)

-- A precondition may not name the ambient rigid `a` in a binder annotation: only the
-- procedure's own type parameters are in scope.
/-- info: REJECTED: Procedure 'ambientRigid', condition 'p': type variable `a` is not in scope -/
#guard_msgs in
#eval verdictOf (Procedure.typeCheck ambientRigidC TEnv.default Program.init
  { ambientRigidProc .int with
    spec := { preconditions := [("p", ⟨LExpr.all Core.coreLoc "x" (some (.ftvar "a"))
                (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.intConst Core.coreLoc 0)), .Default,
                    #[]⟩)],
              postconditions := [] } } .empty)

-- Operator annotations are not scoped: a precondition may use `idf` annotated `a → a`, `c → c`
-- or not at all at `bool`, whatever the ambient rigid variables.
open Core.TestUtil (idfDecl idfTrueEq printIdfVerdicts) in
/--
info: ACCEPTED
ACCEPTED
ACCEPTED
-/
#guard_msgs in
#eval printIdfVerdicts (C := ambientRigidC) fun ann => { decls := [idfDecl,
  .proc { ambientRigidProc .int with
    spec := { preconditions := [("p", ⟨idfTrueEq ann, .Default, #[]⟩)],
              postconditions := [] } } .empty] }

/-! ## Reserved type names in called procedure signatures

A procedure signature naming the unregistered type `$__rigid_caller_a` is rejected at its
declaration. The rigid types of procedure `caller` avoid that name, so a call passing its type
parameter does not match it. -/

private def reservedSignatureCallee : Procedure :=
  { header :=
      { name := "reservedCallee", typeArgs := [],
        inputs := [("x", .tcons "$__rigid_caller_a" [])], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [] false }

private def reservedSignatureProgram : Program :=
  { decls := [.proc reservedSignatureCallee .empty] }

private def callerOfReservedSignature : Procedure :=
  { header :=
      { name := "caller", typeArgs := ["a"],
        inputs := [("x", .ftvar "a")], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [
      Statement.call "reservedCallee" none
        [.inArg (LExpr.fvar Core.coreLoc "x" none)] .empty
    ] false }

-- The caller checked alone against a program declaring the callee is rejected at the call: the
-- callee's signature names the unregistered type `$__rigid_caller_a`, which the caller's rigid
-- type for `a` is not.
/-- info: REJECTED: Procedure 'caller': Type $__rigid_caller_a is not an instance of a previously registered type! -/
#guard_msgs in
#eval Core.TestUtil.firstLineOf
  (verdictOf (Procedure.typeCheck initTyContext TEnv.default reservedSignatureProgram
    callerOfReservedSignature .empty))

-- The program declaring the callee and the caller is rejected at the callee.
/--
info: REJECTED: Procedure 'reservedCallee': signature type $__rigid_caller_a is not a registered type
-/
#guard_msgs in
#eval verdictOf (Program.typeCheck initTyContext TEnv.default
  { decls := [.proc reservedSignatureCallee .empty, .proc callerOfReservedSignature .empty] })

-- With the caller declared first, the program is rejected at the call in the caller.
/-- info: REJECTED: Procedure 'caller': Type $__rigid_caller_a is not an instance of a previously registered type! -/
#guard_msgs in
#eval Core.TestUtil.firstLineOf (verdictOf (Program.typeCheck initTyContext TEnv.default
  { decls := [.proc callerOfReservedSignature .empty, .proc reservedSignatureCallee .empty] }))

-- The rigid type of `caller` avoids the output types of other procedures.
/-- info: [("a", "$__rigid_caller_a_1")] -/
#guard_msgs in
#eval
  let P : Program := { decls := [.proc { reservedSignatureCallee with
      header := { reservedSignatureCallee.header with
        inputs := [],
        outputs := [("r", .tcons "$__rigid_caller_a" [])] } } .empty] }
  Procedure.rigidNames (scopeTyNameThunk initTyContext TEnv.default)
    (procSigTyNameThunk P) initTyContext callerOfReservedSignature
    fun _ => procTyNames callerOfReservedSignature (procAnnotTys callerOfReservedSignature)

/-! ## Rigid type names in conditions and control-flow graph bodies

Unregistered type names in conditions and control-flow graph expressions are rejected. A
control-flow graph body is otherwise type checked like a structured body. -/

section AnnotationHygiene
open Imperative
open Core.TestUtil (rigidA firstLineOf procedureVerdict xId)

private def xAtRigid : Expression.Expr := .fvar Core.coreLoc xId (some rigidA)

private def rigidEq : Expression.Expr := .eq Core.coreLoc xAtRigid xAtRigid

private def baseProcedure : Procedure :=
  { header := {
      name := ⟨"p", ()⟩,
      typeArgs := ["a"],
      inputs := [(xId, .ftvar "a")],
      outputs := []
    },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [] false }

private def postconditionAnnotated : Procedure :=
  { baseProcedure with
    spec := {
      preconditions := [],
      postconditions := [("ens", ⟨rigidEq, .Default, #[]⟩)]
    } }

private def cfgCommandAnnotated : Procedure :=
  { baseProcedure with
    body := .cfg {
      entry := "entry",
      blocks := [("entry", {
        cmds := [.cmd (.assert "a" rigidEq .empty)],
        transfer := .finish .empty
      })]
    } false }

private def cfgGuardAnnotated : Procedure :=
  { baseProcedure with
    body := .cfg {
      entry := "entry",
      blocks := [("entry", {
        cmds := [],
        transfer := .condGoto rigidEq "entry" "entry" .empty
      })]
    } false }

private def cfgIllTypedControl : Procedure :=
  { baseProcedure with
    body := .cfg {
      entry := "entry",
      blocks := [("entry", {
        cmds := [.cmd (.assert "not_bool" (LExpr.intConst Core.coreLoc 1) .empty)],
        transfer := .finish .empty
      })]
    } false }

-- A postcondition annotation naming a type with the rigid prefix is rejected.
/--
info: REJECTED: Procedure 'p', condition 'ens': Type $__rigid_a is not an instance of a previously registered type!
-/
#guard_msgs in
#eval firstLineOf <| procedureVerdict postconditionAnnotated

-- A control-flow graph command annotation naming a type with the rigid prefix is rejected.
/-- info: REJECTED: Procedure 'p': Type $__rigid_a is not an instance of a previously registered type! -/
#guard_msgs in
#eval firstLineOf <| procedureVerdict cfgCommandAnnotated

-- A control-flow graph guard annotation naming a type with the rigid prefix is rejected.
/-- info: REJECTED: Procedure 'p': Type $__rigid_a is not an instance of a previously registered type! -/
#guard_msgs in
#eval firstLineOf <| procedureVerdict cfgGuardAnnotated

-- A control-flow graph body is type checked: asserting an integer is rejected.
/-- info: REJECTED: Procedure 'p': Assertion not_bool expected to be of type boolean, but inferred type is int. -/
#guard_msgs in
#eval firstLineOf <| procedureVerdict cfgIllTypedControl

end AnnotationHygiene

/-! ## Unbound type variables in locals and call type arguments -/

section UnboundTyVars

/-- `p() { var y : 'b := * }`: no type parameter `b`, and nothing solves it. -/
private def unboundLocalPgm : Program := { decls :=
  [mkProc "p" [] [] [] [declNondet "y" (.ftvar "b")]] }

/--
info: REJECTED: Procedure 'p': local 'y' is declared at type variable 'b',
which is not a type parameter of the procedure
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict unboundLocalPgm

/-- `p() { var y : 'b := *; var z : 'c := * }`: two written variables, both unsolved. The error
    names both. -/
private def twoUnboundLocalsPgm : Program := { decls :=
  [mkProc "p" [] [] [] [declNondet "y" (.ftvar "b"), declNondet "z" (.ftvar "c")]] }

/--
info: REJECTED: Procedure 'p': local 'y' is declared at type variable 'b', which is not a type
parameter of the procedure; local 'z' is declared at type variable 'c', which is not a type
parameter of the procedure
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict twoUnboundLocalsPgm

/-- `Caller() { var y : 'b := *; call q() }`: a written unbound variable and a call that leaves
    `q`'s type parameter undetermined. The error reports both. -/
private def unboundLocalAndCallPgm : Program := { decls :=
  [Core.CallFixtures.qReflDecl,
   mkProc "Caller" [] [] []
     [declNondet "y" (.ftvar "b"), Statement.call "q" none [] .empty]] }

/--
info: REJECTED: Procedure 'Caller': local 'y' is declared at type variable 'b', which is not a type
parameter of the procedure; the call to 'q' does not determine one of its type parameters
-/
#guard_msgs (whitespace := lax) in
#eval coreVerdict unboundLocalAndCallPgm

/-- `Caller() { var x : 'b := *; call q(x) }` with `q<a>(x : a)`: the call determines `a`, but at
    the written variable `b`, which is not a type parameter of `Caller`. -/
private def callAtUnboundWrittenPgm : Program := { decls :=
  [Core.CallFixtures.qArgDecl,
   mkProc "Caller" [] [] []
     [declNondet "x" (.ftvar "b"),
      Statement.call "q" none [.inArg (.fvar Core.coreLoc ⟨"x", ()⟩ none)] .empty]] }

/--
info: REJECTED: Procedure 'Caller': local 'x' is declared at type variable 'b', which is not a type
parameter of the procedure; the call to 'q' is instantiated at type variable 'b', which is not a
type parameter of the procedure
-/
#guard_msgs in
#eval coreVerdict callAtUnboundWrittenPgm

/-- `p() { var x : 'b := *; var y : int := x }`: the written `b` is solved to `int`. -/
private def solvedLocalPgm : Program := { decls :=
  [mkProc "p" [] [] []
    [declNondet "x" (.ftvar "b"),
     Statement.init "y" (.forAll [] .int) (.det (.fvar Core.coreLoc ⟨"x", ()⟩ none)) .empty]] }

/-- info: ACCEPTED -/
#guard_msgs in
#eval coreVerdict solvedLocalPgm

/-- `p<a>() { var y : a := * }`: the local mentions only the procedure's own type parameter. -/
private def polymorphicLocalPgm : Program := { decls :=
  [mkProc "p" ["a"] [] [] [declNondet "y" (.ftvar "a")]] }

/-- info: ACCEPTED -/
#guard_msgs in
#eval coreVerdict polymorphicLocalPgm

-- An unsolved type variable on an operator annotation, not on a local, stays accepted.
open Strata in
private def opAnnotPgm :=
#strata
program Core;
function n<a>() : a;
procedure P()
{
  assert (n() == n());
};
#end

/-- info: ACCEPTED -/
#guard_msgs in
#eval coreVerdict (translate opAnnotPgm)

end UnboundTyVars

---------------------------------------------------------------------
end Tests
end Core

end
