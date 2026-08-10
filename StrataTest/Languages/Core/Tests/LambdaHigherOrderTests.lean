/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.Transform.BetaReduce

meta section

/-! # Lambda, Higher-Order Function, and Function Type Tests

Tests for lambda expressions, higher-order functions, and function types in Core.
Covers parsing, type checking, verification, SMT encoding error messages,
and interactions with polymorphism, recursive functions, and datatypes.
-/

open Core
open Strata

def translate (t : StrataDDM.Program) : Core.Program :=
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
  result := apply(fun x : int => int.add(x, 1), 5);
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

inline function apply (f : int -> int, x : int) : int {
  f(x)
}
procedure TestLambdaApply (out result : int)
spec {
  ensures [TestLambdaApply_ensures_0]: result == 6;
  } {
  result := apply(fun x : int => int.add(x, 1), 5);
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
#eval Strata.Core.verify lambdaApplyPgm (options := .quiet)

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
  result := apply(fun x : int => int.add(x, 1), 5);
};
#end

/--
info:
Obligation: TestLambdaApply_ensures_0
Property: assert
Result: 🚨 SMT Encoding Error! Cannot encode function 'apply' to SMT: it has function-typed parameter(s) [f]. Higher-order functions cannot be encoded to SMT. Consider marking the function as `inline`.
-/
#guard_msgs in
#eval Strata.Core.verify lambdaApplyNoInlinePgm (options := .quiet)

/-! ## Lambda in function body (no higher-order inputs) -/

def lambdaInBodyPgm :=
#strata
program Core;

function mkFn(i: int) : int
{
  (fun x : int => int.add(x, 1))(i)
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
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify lambdaInBodyPgm (options := .quiet)

/-! ## Nested lambda redex whose inner body references the OUTER bound var.
    The SMT encoder's `betaReduceRedexes` reduces the redexes innermost-first;
    since each redex it contracts is applied to an already-closed argument, the
    locally-closed `betaReduce` fast path (= `subst`) applies at every step, and
    the body encodes without residual abstractions. -/

def nestedRedexPgm :=
#strata
program Core;

function nestedRedex(i : int) : int
{
  (fun b : int => (fun x : int => int.add(x, b))(i))(i)
}

procedure TestNested(out result : int)
spec {
  ensures result == 4;
}
{
  result := nestedRedex(2);
};
#end

/-- info:
Obligation: TestNested_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify nestedRedexPgm (options := .quiet)

def deep3RedexPgm :=
#strata
program Core;

function deep3(i : int) : int
{
  (fun a : int => (fun b : int => (fun c : int => int.add(int.add(a, b), c))(i))(i))(i)
}

procedure TestDeep3(out result : int)
spec {
  ensures result == 6;
}
{
  result := deep3(2);
};
#end

/-- info:
Obligation: TestDeep3_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify deep3RedexPgm (options := .quiet)

/-! ## Redex whose argument references an enclosing binder, with the redex
    variable used under a further inner binder — exercises `betaReduce`'s
    argument lifting (`liftBVars`) when a redex is contracted at nonzero
    binder depth during encoder-side reduction. -/

def liftArgRedexPgm :=
#strata
program Core;

function liftArg(i : int) : int
{
  (fun a : int => (fun x : int => (fun y : int => int.add(x, y))(1))(int.add(a, 10)))(i)
}

procedure TestLiftArg(out result : int)
spec {
  ensures result == 13;
}
{
  result := liftArg(2);
};
#end

/-- info:
Obligation: TestLiftArg_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify liftArgRedexPgm (options := .quiet)

/-! ## Constant-lambda redex through the SMT encoder (erasing reducer).
    `(fun ignored : int => 42)(i)` is a constant lambda: `bvarUsed 0 body`
    is false, so the SMT encoder's erasing `betaReduceRedexes` drops the (dead)
    argument and encodes `constLam` as the constant `42`, with no residual
    abstraction to reject. This exercises the erasing branch of
    `betaReduceRedexesFuel` reached via the encoder (the termination checker
    uses the non-erasing variant), pinning the concrete verified result. -/

def constLamPgm :=
#strata
program Core;

function constLam(i : int) : int
{
  (fun ignored : int => 42)(i)
}

procedure TestConstLam(out result : int)
spec {
  ensures result == 42;
}
{
  result := constLam(7);
};
#end

/-- info:
Obligation: TestConstLam_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify constLamPgm (options := .quiet)

/-! ## Duplicating redex: fuel must account for bound-variable multiplicity.
    `(fun x : int => int.add(int.add(x, x), x))(int.add(i, 1))` references its bound variable three
    times, so β-reduction duplicates the (compound) argument and the reduced
    term is larger than the input. A `sizeOf`-only fuel budget could be exhausted
    before reduction completes, leaving a residual `.abs` the SMT encoder would
    reject; the multiplicity-scaled budget suffices for this (single-level)
    duplication shape — full reduction is not guaranteed in general. -/

def dupRedexPgm :=
#strata
program Core;

function dupRedex(i : int) : int
{
  (fun x : int => int.add(int.add(x, x), x))(int.add(i, 1))
}

procedure TestDupRedex(out result : int)
spec {
  ensures result == 6;
}
{
  result := dupRedex(1);
};
#end

/-- info:
Obligation: TestDupRedex_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify dupRedexPgm (options := .quiet)

/-! ## Redex under a binder: the phase reduces inside quantifier bodies.
    The redex `(fun y : int => y + y)(x)` sits under the `forall x` binder, so
    contracting it must decrement/lift de Bruijn indices relative to the
    enclosing binder (`betaReduce`, not plain `subst`). Symbolic evaluation
    does not evaluate under binders, so only the `betaReduce` phase can
    contract it; without reduction the encoder would reject the `.app` of an
    abstraction inside the quantifier body. -/

def underBinderPgm :=
#strata
program Core;

function underBinder() : bool
{
  forall x : int :: (fun y : int => int.add(y, y))(x) == int.add(x, x)
}

procedure TestUnderBinder()
spec {
  ensures underBinder();
}
{
};
#end

/-- info:
Obligation: TestUnderBinder_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify underBinderPgm (options := .quiet)

-- Pin the reduced shape: after the phase, the quantifier body is redex-free.
/-- info: reduced body: forall x : int :: int.add(x, x) == int.add(x, x) -/
#guard_msgs in
#eval show Std.Format from
  match (Core.BetaReduce.betaReduceProgram (translate underBinderPgm)).decls with
  | [.func f _, _] =>
    match f.body with
    | some b => f!"reduced body: {b}"
    | none => f!"NO BODY"
  | _ => f!"UNEXPECTED shape"

/-! ## `have`-binding: Core's surface syntax for a let-alias redex.
    `have c : T = v in body` is sugar for `(fun c : T => body)(v)`; the phase
    contracts it like any other redex, so the encoder sees `haveAlias` as a
    first-order body. -/

def haveAliasPgm :=
#strata
program Core;

function haveAlias(i : int) : int
{
  have c : int = int.add(i, 1) in int.add(c, c)
}

procedure TestHaveAlias(out result : int)
spec {
  ensures result == 6;
}
{
  result := haveAlias(2);
};
#end

/-- info:
Obligation: TestHaveAlias_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify haveAliasPgm (options := .quiet)

/-! ## Redex inside a locally-declared function (`funcDecl` statement).
    `betaReduceProgram` recurses into `funcDecl` bodies — unlike
    `Imperative.Stmt.mapExpr`, which treats `funcDecl` as a leaf. The factory
    registers local-function bodies verbatim (`collectFuncDecls` in
    `Verifier.lean`), so a residual redex there would reach the encoder
    whenever the partial evaluator does not inline the call. The shape pin
    below is the discriminating check: without the `funcDecl` recursion the
    body stays `(fun c : int => c + c)(x + x)`. -/

def nestedFuncDeclPgm :=
#strata
program Core;

procedure TestNestedFuncDecl(out result : int)
spec {
  ensures result == 8;
}
{
  function quad(x : int) : int { have c : int = int.add(x, x) in int.add(c, c) }
  result := quad(2);
};
#end

/-- info:
Obligation: TestNestedFuncDecl_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify nestedFuncDeclPgm (options := .quiet)

-- Pin the reduced shape of the nested function body after the phase.
/-- info: reduced nested body: int.add(int.add(x, x), int.add(x, x)) -/
#guard_msgs in
#eval show Std.Format from
  match (Core.BetaReduce.betaReduceProgram (translate nestedFuncDeclPgm)).decls with
  | [.proc proc _] =>
    match proc.body with
    | .structured (Imperative.Stmt.funcDecl decl _ :: _) =>
      match decl.body with
      | some b => f!"reduced nested body: {b}"
      | none => f!"NO BODY"
    | _ => f!"UNEXPECTED body shape"
  | _ => f!"UNEXPECTED decl shape"

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
  result := applyN(Succ(Succ(Succ(Zero()))), fun x : int => int.add(x, 1), 0);
};
#end

/-- info:
Obligation: applyN_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: applyN_terminates_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Core.verify recHigherOrderPgm (options := .quiet)

/-! ## Recursive function with lambda in body -/

def recLambdaInBodyPgm :=
#strata
program Core;

datatype MyNat { Zero(), Succ(pred: MyNat) };

rec function foo(@[cases] n : MyNat) : int -> int
{
  if MyNat..isZero(n) then fun x : int => x
  else fun x : int => int.add(x, 1)
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
#eval Strata.Core.verify recLambdaInBodyPgm (options := .quiet)

/-! ## Lambda directly in a procedure assert -/

def lambdaInAssertPgm :=
#strata
program Core;

procedure Test(out result : bool)
spec {
  ensures result == true;
}
{
  var y : int -> int := fun x : int => int.add(x, 1);

  result := (y == fun x : int => int.add(1, x));
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: 🚨 SMT Encoding Error! Cannot encode lambda expression to SMT. Lambda abstractions must be eliminated (e.g., by beta-reduction) before SMT encoding.
Lambda: fun x : int => int.add(x, 1)-/
#guard_msgs in
#eval Strata.Core.verify lambdaInAssertPgm (options := .quiet)

-- If it can be simplified by partial evaluation, it is OK
def lambdaInAssertPgm2 :=
#strata
program Core;

procedure Test(out result : bool)
spec {
  ensures result == true;
}
{
  var y : int -> int := fun x : int => int.add(x, 1);

  result := (y == fun z : int => int.add(z, 1));
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Core.verify lambdaInAssertPgm2 (options := .quiet)

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
  result := apply(fun x : int => int.add(x, 1), 5);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Core.verify polyApplyPgm (options := .quiet)

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
  result := compose(fun x : int => int.ge(x, 0), fun x : int => int.add(x, 1), int.neg(1));
};

procedure Test1(out result : bool)
spec {
  ensures result == false;
}
{
  result := compose(fun x : int => int.gt(x, 0), fun x : int => int.add(x, 1), int.neg(1));
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass

Obligation: Test1_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Core.verify polyComposePgm (options := .quiet)

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
#eval Strata.Core.verify polyLambdaPgm (options := .quiet)

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
  r1 := apply(fun x : int => int.add(x, 1), 4);
  r2 := apply(fun b : bool => !b, false);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Core.verify polyIdentityLambdaPgm (options := .quiet)

-- Polymorphic datatype + monomorphic recursive function + polymorphic function + polymorphic lambda
def polyRecLambdaPgm :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

rec function intListLen(@[cases] xs : MyList int) : int
{
  if MyList..isNil(xs) then 0 else int.add(1, intListLen(MyList..tl(xs)))
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
  result := apply(fun n : int => int.add(n, 2), intListLen(Cons(1, Cons(2, Cons(3, Nil())))));
};
#end

/-- info: Obligation: intListLen_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass

Obligation: intListLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Core.verify polyRecLambdaPgm (options := .quiet)

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
  result := apply2(fun x : int, y : int => int.add(x, y), 3, 4);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Core.verify multiBindingLambdaPgm (options := .quiet)

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
  result := (fun x : int => int.add(x, 1))(5);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Core.verify exprApplyPgm (options := .quiet)


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
  result := (Box..val(MkBox(fun x : int => int.add(x, 1))))(5);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Core.verify polyDatatypeFnInstExprAppPgm (options := .quiet)


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
  ensures (fun x : int => int.mul(x, 2))(result) == 10;
}
{
  result := 5;
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Core.verify lambdaInSpecPgm (options := .quiet)

/-! ## Currying: lambda returning lambda, applied step by step -/

def curryPgm :=
#strata
program Core;

procedure Test(out result : int)
spec {
  ensures result == 7;
}
{
  result := ((fun x : int => fun y : int => int.add(x, y))(3))(4);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Core.verify curryPgm (options := .quiet)

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
  r1 := apply(if true then fun x : int => x else fun x : int => int.add(x, 1), 5);
  r2 := apply(if false then fun x : int => x else fun x : int => int.add(x, 1), 5);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Core.verify lambdaInCondPgm (options := .quiet)

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
  result := ((fun f : int -> int, x : int => (f)(x))(fun y : int => int.add(y, 1)))(5);
};
#end

/-- info: Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Core.verify higherOrderLambdaPgm (options := .quiet)

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
  result := applyTransformer(MkTransformer(fun x : int => int.add(x, 1), 5));
};
#end

/-- error: Cannot encode datatype 'Transformer' to SMT: constructor 'MkTransformer' has function-typed field 'f' of type '(arrow int int)'. Function types cannot be represented in SMT-LIB datatypes.-/
#guard_msgs in
#eval Strata.Core.verify datatypeFnFieldLambdaPgm (options := .quiet)

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
  int.add(x, 1)
}

procedure Test(z : int, out result : int)
spec {
  ensures result == int.add(z, 1);

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
#eval Strata.Core.verify datatypeFnFieldSymbolicPgm (options := .quiet)

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
  result := apply(Box..val(MkBox(fun x : int => int.add(x, 1))), 5);
};
#end

/-- info: Obligation: set_result_calls_Box..val_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Core.verify polyDatatypeFnInstPgm (options := .quiet)

end
