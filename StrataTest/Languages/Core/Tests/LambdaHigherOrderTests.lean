/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.Verifier

/-! # Lambda, Higher-Order Function, and Function Type Tests

Tests for lambda expressions, higher-order functions, and function types in Core.
Covers parsing, type checking, verification, SMT encoding error messages,
and interactions with polymorphism, recursive functions, and datatypes.
-/

open Core
open Strata

def translate (t : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

/-! ## Lambda expression parsing and formatting -/

def lambdaIdentityPgm :=
#strata
program Core;

function intID() : int -> int {
  fun x : int => x
}
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function intID () : int -> int {
  fun x : int => x
}
-/
#guard_msgs in
#eval (Std.format ((Core.typeCheck .default (translate lambdaIdentityPgm).stripMetaData)))

def lambdaNestedPgm :=
#strata
program Core;

function constFn() : int -> int -> int {
  fun x : int => fun y : int => x
}
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function constFn () : int -> int -> int {
  fun x : int => fun y : int => x
}
-/
#guard_msgs in
#eval (Std.format ((Core.typeCheck .default (translate lambdaNestedPgm).stripMetaData)))

/-! ## Lambda used as a function body, applied via higher-order function -/

def lambdaApplyPgm :=
#strata
program Core;

inline function apply(f : int -> int, x : int) : int
{
  f(x)
}

procedure TestLambdaApply(out result : int)
spec {
  ensures result == 6;
}
{
  result := apply(fun x : int => x + 1, 5);
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function apply (f : int -> int, x : int) : int {
  f(x)
}
procedure TestLambdaApply (out result : int)
spec {
  ensures [TestLambdaApply_ensures_0]: result == 6;
  } {
  result := apply(fun x : int => x + 1, 5);
};
-/
#guard_msgs in
#eval (Std.format ((Core.typeCheck .default (translate lambdaApplyPgm).stripMetaData)))

/--
info:
Obligation: TestLambdaApply_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify lambdaApplyPgm (options := .quiet)

/-! ## Lambda used as a function body, no "inline" (fails) -/

def lambdaApplyNoInlinePgm :=
#strata
program Core;

function apply(f : int -> int, x : int) : int
{
  f(x)
}

procedure TestLambdaApply(out result : int)
spec {
  ensures result == 6;
}
{
  result := apply(fun x : int => x + 1, 5);
};
#end

/--
info:
Obligation: TestLambdaApply_ensures_0
Property: assert
Result: 🚨 Implementation Error! SMT Encoding Error! Cannot encode function 'apply' to SMT: it has function-typed parameter(s) [f]. Higher-order functions cannot be encoded to SMT. Consider marking the function as `inline`.
-/
#guard_msgs in
#eval verify lambdaApplyNoInlinePgm (options := .quiet)

/-! ## Lambda in function body (no higher-order inputs) -/

def lambdaInBodyPgm :=
#strata
program Core;

function mkFn(i: int) : int
{
  (fun x : int => x + 1)(i)
}

procedure Test(out result : int)
spec {
  ensures result == 2;
}
{
  result := (mkFn())(1);
};
#end

/-- info:
Obligation: Test_ensures_0
Property: assert
Result: 🚨 Implementation Error! SMT Encoding Error! Cannot encode function 'mkFn' to SMT: its body contains a lambda expression. Lambda abstractions cannot be encoded to SMT. Consider marking the function as `inline`.-/
#guard_msgs in
#eval verify lambdaInBodyPgm (options := .quiet)

/-! ## Recursive function with function-typed input -/

def recHigherOrderPgm :=
#strata
program Core;

datatype MyNat { Zero(), Succ(pred: MyNat) };

rec function applyN(@[cases] n : MyNat, f : int -> int, x : int) : int
{
  if MyNat..isZero(n) then x else applyN(MyNat..pred(n), f, f(x))
};

procedure Test(out result : int)
spec {
  ensures result == 3;
}
{
  result := applyN(Succ(Succ(Succ(Zero()))), fun x : int => x + 1, 0);
};
#end

/-- info:
Obligation: applyN_terminates_0
Property: assert
Result: ✅ pass

Obligation: applyN_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify recHigherOrderPgm (options := .quiet)

/-! ## Recursive function with lambda in body -/

def recLambdaInBodyPgm :=
#strata
program Core;

datatype MyNat { Zero(), Succ(pred: MyNat) };

rec function foo(@[cases] n : MyNat) : int -> int
{
  if MyNat..isZero(n) then fun x : int => x
  else fun x : int => x + 1
};

procedure Test(out result : int)
spec {
  ensures result == 5;
}
{
  result := (foo(Zero()))(5);
};
#end

/-- info:
Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify recLambdaInBodyPgm (options := .quiet)

/-! ## Lambda directly in a procedure assert -/

def lambdaInAssertPgm :=
#strata
program Core;

procedure Test(out result : bool)
spec {
  ensures result == true;
}
{
  var y : int -> int := fun x : int => x + 1;

  result := (y == fun x : int => 1 + x);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: 🚨 Implementation Error! SMT Encoding Error! Cannot encode lambda expression to SMT. Lambda abstractions must be eliminated (e.g., by beta-reduction) before SMT encoding.
Lambda: fun x : int => x + 1-/
#guard_msgs in
#eval verify lambdaInAssertPgm (options := .quiet)

-- If it can be simplified by partial evaluation, it is OK
def lambdaInAssertPgm2 :=
#strata
program Core;

procedure Test(out result : bool)
spec {
  ensures result == true;
}
{
  var y : int -> int := fun x : int => x + 1;

  result := (y == fun z : int => z + 1);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify lambdaInAssertPgm2 (options := .quiet)

/-! ## Polymorphic functions with lambdas -/

-- Polymorphic apply: lambda passed in a polymorphic position
def polyApplyPgm :=
#strata
program Core;

inline function apply<T>(f : T -> T, x : T) : T
{
  f(x)
}

procedure Test(out result : int)
spec {
  ensures result == 6;
}
{
  result := apply(fun x : int => x + 1, 5);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify polyApplyPgm (options := .quiet)

-- Polymorphic compose: two lambdas chained through polymorphic positions
def polyComposePgm :=
#strata
program Core;

inline function compose<A, B, C>(f : B -> C, g : A -> B, x : A) : C
{
  f(g(x))
}

procedure Test(out result : bool)
spec {
  ensures result == true;
}
{
  result := compose(fun x : int => x >= 0, fun x : int => x + 1, -1);
};

procedure Test1(out result : bool)
spec {
  ensures result == false;
}
{
  result := compose(fun x : int => x > 0, fun x : int => x + 1, -1);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass

Obligation: Test1_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify polyComposePgm (options := .quiet)

-- Polymorphic lambda: lambda whose parameter has a type variable type
def polyLambdaPgm :=
#strata
program Core;

inline function mkIdentity<T>() : T -> T
{
  fun x : T => x
}

inline function apply<T>(f : T -> T, x : T) : T
{
  f(x)
}

procedure Test(out r1 : int, out r2 : bool)
spec {
  ensures r1 == 5 && r2 == true;
}
{
  r1 := apply(mkIdentity(), 5);
  r2 := apply(mkIdentity(), true);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify polyLambdaPgm (options := .quiet)

-- Polymorphic identity lambda
def polyIdentityLambdaPgm :=
#strata
program Core;

inline function apply<T>(f : T -> T, x : T) : T
{
  f(x)
}

procedure Test(out r1 : int, out r2 : bool)
spec {
  ensures r1 == 5 && r2 == true;
}
{
  r1 := apply(fun x : int => x + 1, 4);
  r2 := apply(fun b : bool => !b, false);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify polyIdentityLambdaPgm (options := .quiet)

-- Polymorphic datatype + monomorphic recursive function + polymorphic function + polymorphic lambda
def polyRecLambdaPgm :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

rec function intListLen(@[cases] xs : MyList int) : int
{
  if MyList..isNil(xs) then 0 else 1 + intListLen(MyList..tl(xs))
};

inline function apply<T>(f : T -> T, x : T) : T
{
  f(x)
}

procedure Test(out result : int)
spec {
  ensures result == 5;
}
{
  result := apply(fun n : int => n + 2, intListLen(Cons(1, Cons(2, Cons(3, Nil())))));
};
#end

/-- info: Obligation: intListLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: intListLen_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify polyRecLambdaPgm (options := .quiet)

/-! ## Multi-binding lambda -/

-- Tests that translateLambda handles foldr nesting with correct bvar indices
def multiBindingLambdaPgm :=
#strata
program Core;

inline function apply2(f : int -> int -> int, x : int, y : int) : int
{
  (f(x))(y)
}

procedure Test(out result : int)
spec {
  ensures result == 7;
}
{
  result := apply2(fun x : int, y : int => x + y, 3, 4);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify multiBindingLambdaPgm (options := .quiet)

/-! ## Expression application -/

-- (lambda)(arg) applied directly, reduced by partial evaluation
def exprApplyPgm :=
#strata
program Core;

procedure Test(out result : int)
spec {
  ensures result == 6;
}
{
  result := (fun x : int => x + 1)(5);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify exprApplyPgm (options := .quiet)


-- Expression application with polymorphic selector (requires apply_expr type inference)
def polyDatatypeFnInstExprAppPgm :=
#strata
program Core;

datatype Box (a : Type) { MkBox(val: a) };

procedure Test(out result : int)
spec {
  ensures result == 6;
}
{
  result := (Box..val(MkBox(fun x : int => x + 1)))(5);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify polyDatatypeFnInstExprAppPgm (options := .quiet)


/-! ## Lambda in a spec -/

def lambdaInSpecPgm :=
#strata
program Core;

inline function apply(f : int -> int, x : int) : int
{
  f(x)
}

procedure Test(out result : int)
spec {
  ensures (fun x : int => x * 2)(result) == 10;
}
{
  result := 5;
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify lambdaInSpecPgm (options := .quiet)

/-! ## Currying: lambda returning lambda, applied step by step -/

def curryPgm :=
#strata
program Core;

procedure Test(out result : int)
spec {
  ensures result == 7;
}
{
  result := ((fun x : int => fun y : int => x + y)(3))(4);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify curryPgm (options := .quiet)

/-! ## Lambda in a conditional -/

def lambdaInCondPgm :=
#strata
program Core;

inline function apply(f : int -> int, x : int) : int
{
  f(x)
}

procedure Test(out r1 : int, out r2 : int)
spec {
  ensures r1 == 5 && r2 == 6;
}
{
  r1 := apply(if true then fun x : int => x else fun x : int => x + 1, 5);
  r2 := apply(if false then fun x : int => x else fun x : int => x + 1, 5);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify lambdaInCondPgm (options := .quiet)

/-! ## Higher-order lambda: lambda that takes a function argument -/

def higherOrderLambdaPgm :=
#strata
program Core;

procedure Test(out result : int)
spec {
  ensures result == 6;
}
{
  // (λ f . λ x. f x) (λ y. y + 1) 5
  result := ((fun f : int -> int, x : int => (f)(x))(fun y : int => y + 1))(5);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify higherOrderLambdaPgm (options := .quiet)

/-! ## Datatype with function-typed field + lambda -/

-- A datatype whose constructor takes a function argument, instantiated with a lambda
def datatypeFnFieldLambdaPgm :=
#strata
program Core;

datatype Transformer { MkTransformer(f: int -> int, base: int) };

inline function applyTransformer(t : Transformer) : int
{
  (Transformer..f(t))(Transformer..base(t))
}

procedure Test(out result : int)
spec {
  ensures result == 6;
}
{
  result := applyTransformer(MkTransformer(fun x : int => x + 1, 5));
};
#end

/-- error: Cannot encode datatype 'Transformer' to SMT: constructor 'MkTransformer' has function-typed field 'f' of type '(arrow int int)'. Function types cannot be represented in SMT-LIB datatypes.-/
#guard_msgs in
#eval verify datatypeFnFieldLambdaPgm (options := .quiet)

-- A similar test with symbolic values
def datatypeFnFieldSymbolicPgm :=
#strata
program Core;

datatype Transformer { MkTransformer(f: int -> int, base: int) };

inline function applyTransformer(t : Transformer) : int
{
  (Transformer..f(t))(Transformer..base(t))
}

function add1 (x: int) : int {
  x + 1
}

procedure Test(z : int, out result : int)
spec {
  ensures result == z + 1;

}
{
  var x: Transformer;
  assume (Transformer..f(x) == add1);
  assume (Transformer..base(x) == z);
  result := applyTransformer(x);
};
#end

/-- error: Cannot encode datatype 'Transformer' to SMT: constructor 'MkTransformer' has function-typed field 'f' of type '(arrow int int)'. Function types cannot be represented in SMT-LIB datatypes.-/
#guard_msgs in
#eval verify datatypeFnFieldSymbolicPgm (options := .quiet)

/-! ## Polymorphic datatype instantiated with function type -/

-- Box<T> instantiated with int -> int, holding a lambda. Solved by partial evaluation.
def polyDatatypeFnInstPgm :=
#strata
program Core;

datatype Box (a : Type) { MkBox(val: a) };

inline function apply(f : int -> int, x : int) : int
{
  f(x)
}

procedure Test(out result : int)
spec {
  ensures result == 6;
}
{
  result := apply(Box..val(MkBox(fun x : int => x + 1)), 5);
};
#end

/-- info: Obligation: set_result_calls_Box..val_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify polyDatatypeFnInstPgm (options := .quiet)
