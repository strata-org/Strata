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
meta import Strata.Transform.LambdaLift

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
Result: ✅ pass
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

/--
info:
Obligation: applyN_terminates_0
Property: assert
Result: ✅ pass

Obligation: applyN_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
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

/--
info:
Obligation: Test_ensures_0
Property: assert
Result: ✅ pass-/
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

/--
info:
Obligation: intListLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: intListLen_body_calls_MyList..tl_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
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

-- A datatype whose constructor takes a function argument, instantiated with a lambda.
-- The constructor and both projections are applied to literals, so partial evaluation
-- discharges the obligation and `Transformer` never reaches the SMT encoder. Contrast
-- the symbolic program below, where the datatype is encoded to SMT with its
-- function-typed field as an array.
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

/--
info:
Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
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

/--
info:
Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify datatypeFnFieldSymbolicPgm (options := .quiet)

-- The same program with a wrong postcondition is not proved. The solver answers
-- unknown rather than giving a counterexample, because of the quantified axiom
-- that makes the array value of `add1` agree with `add1`.
def datatypeFnFieldSymbolicWrongPgm :=
#strata
program Core;

datatype Transformer { MkTransformer(f: int -> int, base: int) };

function add1 (x: int) : int {
  int.add(x, 1)
}

procedure Test(z : int, out result : int)
spec {
  ensures result == int.add(z, 2);
}
{
  var x: Transformer;
  assume (Transformer..f(x) == add1);
  assume (Transformer..base(x) == z);
  result := (Transformer..f(x))(Transformer..base(x));
};
#end

/--
info:
Obligation: Test_ensures_0
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Strata.Core.verify datatypeFnFieldSymbolicWrongPgm (options := .quiet)

/-! ## Datatype with a curried function-typed field, applied symbolically -/

-- `Op..f(o)(x)(y)` selects the field and applies the stored function to two
-- arguments in turn. Two values whose fields are equal functions are equal, since
-- function values are extensional.
def datatypeCurriedFnFieldPgm :=
#strata
program Core;

datatype Op { MkOp(f: int -> int -> int) };

function sub(x: int, y: int) : int {
  int.sub(x, y)
}

procedure Test(o1 : Op, o2 : Op, a : int, b : int)
spec {
  requires Op..f(o1) == sub;
  requires forall x : int, y : int :: ((Op..f(o2))(x))(y) == int.sub(x, y);
}
{
  assert [apply]: ((Op..f(o1))(a))(b) == int.sub(a, b);
  assert [ext]: o1 == o2;
};
#end

/--
info:
Obligation: apply
Property: assert
Result: ✅ pass

Obligation: ext
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify datatypeCurriedFnFieldPgm (options := .quiet)

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

/--
info:
Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify polyDatatypeFnInstPgm (options := .quiet)

/-! ## Substitution metadata stays bounded (direct related locations only)

Each `mergeMetadataForSubst` keeps only the direct non-primary locations of the
step, not the locations those in turn relate, so chained substitutions do not
grow `relatedLocs`. The transitive merge grew it linearly with depth. -/

private def parsedLoc (name : String) : ExprSourceLoc :=
  { uri := some (.file name), range := SourceRange.none }

/-- The running metadata of a substitution chain: each step merges the previous
step (as the lambda) with a fresh argument and replaced-variable location. -/
private def substChain : Nat → ExprSourceLoc
  | 0 => parsedLoc "base"
  | n + 1 =>
    Lambda.LExpr.mergeMetadataForSubst (TBase := CoreLParams) (substChain n)
      (parsedLoc s!"arg{n}") (parsedLoc s!"var{n}")

-- A two-step chain keeps exactly this step's two direct locations: the fresh
-- argument and the previous step's own location.
#guard (substChain 2).relatedLocs.length = 2 &&
  (substChain 2).relatedLocs.contains (some (Uri.file "arg1"), SourceRange.none) &&
  (substChain 2).relatedLocs.contains (some (Uri.file "var0"), SourceRange.none)

-- A deep chain stays bounded at two related locations.
#guard (substChain 100).relatedLocs.length ≤ 2

/-! ## A record of functions: the shape of a trait witness -/

-- A trait whose implementations supply a predicate and an extension of a
-- postcondition, as a front end for Rust traits lowers them. The witness of one
-- implementation is defined by an axiom, so partial evaluation cannot reduce
-- its fields and the datatype, its curried field and the lifted lambdas all
-- reach the solver. `wrong` is not proved, and since its obligation mentions
-- lifted functions, the solver's model is reported as unknown rather than as a
-- counterexample.
def traitWitnessPgm :=
#strata
program Core;

datatype TrSpec { MkTrSpec(specFn: int -> bool, ensFn: int -> int -> bool) };

function impl0() : TrSpec;

axiom [impl0_def]: impl0() == MkTrSpec(fun s : int => s == 0, fun s : int => fun u : int => int.lt(u, 10));

procedure Generic(w : TrSpec, s : int, u : int)
spec {
  requires ((TrSpec..ensFn(w))(s))(u);
}
{
  assert [holds]: ((TrSpec..ensFn(w))(s))(u);
};

procedure Concrete(s : int, u : int)
spec {
  requires ((TrSpec..ensFn(impl0()))(s))(u);
}
{
  assert [lt10]: int.lt(u, 10);
  assert [specAt0]: (TrSpec..specFn(impl0()))(0);
  assert [wrong]: int.lt(u, 5);
};
#end

/--
info:
Obligation: holds
Property: assert
Result: ✅ pass

Obligation: lt10
Property: assert
Result: ✅ pass

Obligation: specAt0
Property: assert
Result: ✅ pass

Obligation: wrong
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Strata.Core.verify traitWitnessPgm (options := .quiet)

/-! ## Lambdas capturing a quantified variable, compared by extensionality -/

-- Each lambda captures the quantified `y` and lifts to a function of `y`. The
-- two lambdas of `same` are the same up to the name of their bound variable and
-- lift to the same function. Those of `ext` are different lambdas equal at every
-- argument, so they are equal by extensionality. Those of `differs` are not
-- equal, and the solver's model is reported as unknown since the obligation
-- mentions lifted functions.
def capturingLambdaPgm :=
#strata
program Core;

function g(f : int -> int) : int;

procedure Test()
{
  assert [same]: forall y : int :: g(fun x : int => int.add(x, y)) == g(fun z : int => int.add(z, y));
  assert [ext]: forall y : int :: (fun x : int => int.add(x, y)) == (fun x : int => int.add(y, x));
  assert [differs]: forall y : int :: (fun x : int => int.add(x, y)) == (fun x : int => x);
};
#end

/--
info:
Obligation: same
Property: assert
Result: ✅ pass

Obligation: ext
Property: assert
Result: ✅ pass

Obligation: differs
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Strata.Core.verify capturingLambdaPgm (options := .quiet)

/-! ## Partial application is a closure -/

-- `sub(1)` applies a two-argument function to one argument, which is the
-- closure `fun y : int => sub(1, y)`.
def partialApplicationPgm :=
#strata
program Core;

function sub(x : int, y : int) : int { int.sub(x, y) }

function g(f : int -> int) : int;

procedure Test()
{
  assert [eta]: g(sub(1)) == g(fun y : int => int.sub(1, y));
};
#end

/--
info:
Obligation: eta
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify partialApplicationPgm (options := .quiet)

/-! ## A function with a precondition as a value -/

-- Outside its precondition a function returns an unspecified value that
-- depends only on its arguments, so the value `pos` is the function itself:
-- applying it checks nothing and agrees with `pos` at every argument, while
-- the direct call `pos(0)` still raises its precondition.
def precondFnValuePgm :=
#strata
program Core;

function pos(x : int) : int
  requires int.gt(x, 0);
{ x }

function apply(f : int -> int, x : int) : int
{ f(x) }

procedure Test()
{
  assert [atFive]: apply(pos, 5) == 5;
  assert [unchecked]: apply(pos, 0) == pos(0);
};
#end

/--
info:

Obligation assert_unchecked_calls_pos_0: failed!

Result obtained during evaluation.
---
info:
Obligation: atFive
Property: assert
Result: ✅ pass

Obligation: assert_unchecked_calls_pos_0
Property: assert
Result: ❌ fail

Obligation: unchecked
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify precondFnValuePgm (options := .quiet)

/-! ## Recursion through the result of a function type -/

-- A tree whose children are indexed by an integer recurses through an array,
-- which cvc5 rejects as a nested-recursive datatype.
def treeThroughFunctionPgm :=
#strata
program Core;

datatype Tree { Leaf(), Node(kids: int -> Tree) };

procedure Test(t : Tree)
{
  assert [node]: Tree..isNode(t) || Tree..isLeaf(t);
};
#end

/-- error: Cannot encode datatype 'Tree' to SMT: constructor 'Node' has field 'kids' of type '(arrow int Tree)', which recurses through a function type. -/
#guard_msgs in
#eval Strata.Core.verify treeThroughFunctionPgm (options := .quiet)

-- A datatype in the argument of a function type recurses through it as well. The type
-- checker already refuses it as a non-strictly positive occurrence, before the encoder's
-- own check, which covers it too.
def treeThroughArgumentPgm :=
#strata
program Core;

datatype Tree { Leaf(), Node(f: Tree -> int) };

procedure Test(t : Tree)
{
  assert [node]: Tree..isNode(t) || Tree..isLeaf(t);
};
#end

/--
error: ❌ Type checking error.
Error in constructor Node: Non-strictly positive occurrence of Tree in type (arrow Tree int)
-/
#guard_msgs in
#eval Strata.Core.verify treeThroughArgumentPgm (options := .quiet)

/-! ## A precondition under a lambda -/

-- A call under a lambda raises its precondition for every value of the bound
-- variable, so `pos(x)` fails at `x == 0`, once for each lambda.
def precondUnderLambdaPgm :=
#strata
program Core;

function pos(x : int) : int
  requires int.gt(x, 0);
{ x }

function g(f : int -> int) : int;

procedure Test()
{
  assert [usesPos]: g(fun x : int => pos(x)) == g(fun x : int => pos(x));
};
#end

/--
info:
Obligation: assert_usesPos_calls_pos_0
Property: assert
Result: ❌ fail

Obligation: assert_usesPos_calls_pos_1
Property: assert
Result: ❌ fail

Obligation: usesPos
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify precondUnderLambdaPgm (options := .quiet)

-- A built-in operator with a precondition under a lambda keeps its obligation
-- after lifting: dividing by a captured variable that can be 0 fails where it is
-- 0 and passes where it is not.
def divUnderLambdaPgm :=
#strata
program Core;

function g(f : int -> int) : int;

procedure MayBeZero(y : int)
{
  assert [divMayFail]: g(fun x : int => int.safeDiv(x, y)) == g(fun x : int => int.safeDiv(x, y));
};

procedure NonZero(y : int)
spec {
  requires int.gt(y, 0);
}
{
  assert [divSafe]: g(fun x : int => int.safeDiv(x, y)) == g(fun x : int => int.safeDiv(x, y));
};
#end

/--
info:
Obligation: assert_divMayFail_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❌ fail

Obligation: assert_divMayFail_calls_Int.SafeDiv_1
Property: division by zero check
Result: ❌ fail

Obligation: divMayFail
Property: assert
Result: ✅ pass

Obligation: assert_divSafe_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: assert_divSafe_calls_Int.SafeDiv_1
Property: division by zero check
Result: ✅ pass

Obligation: divSafe
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify divUnderLambdaPgm (options := .quiet)

-- The checks of a call under a lambda read the lambda's own bound variable, never a
-- variable outside it with the same name: here the outer `x` is 1, but the inner one
-- is any integer, so the division check fails.
def shadowedPrecondPgm :=
#strata
program Core;

function g(f : int -> int) : int;

procedure P(x : int)
spec {
  requires x == 1;
}
{
  assert [shadowed]: g(fun x : int => int.safeDiv(1, x)) == g(fun x : int => int.safeDiv(1, x));
};
#end

/--
info:
Obligation: assert_shadowed_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❌ fail

Obligation: assert_shadowed_calls_Int.SafeDiv_1
Property: division by zero check
Result: ❌ fail

Obligation: shadowed
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify shadowedPrecondPgm (options := .quiet)

/-! ## Obligations whose models may be spurious -/

-- The solver's arrays may be only some of the functions, so a model of an
-- obligation that quantifies over a type containing a function type need not
-- be a counterexample. `lambdaLift` marks the procedures with such obligations:
-- those quantifying over a function type, over a datatype with a function-typed
-- field, or applying a function whose axioms do, and those of a program with an
-- axiom that does. A function counts when it reaches such axioms through the
-- body of another function it applies, as `Indirect` does through `viaLambda`,
-- and when its own body quantifies, as `allFnsAt0` does for `ViaBody`. A
-- function type behind a type synonym or under a type constructor counts too,
-- as in `QuantAlias` and `QuantMap`.
-- A lifted lambda whose captures are first-order does not mark its procedure,
-- since its axiom fixes it at every capture.
def spuriousModelsPgm :=
#strata
program Core;

datatype Box { MkBox(f: int -> int) };

function c() : int;

procedure QuantFn()
{
  assume [allFns]: forall g : int -> int :: g(0) == c() || g(0) != c();
  assert [q1]: c() == 1;
};

procedure QuantBox()
{
  assume [allBoxes]: forall b : Box :: (Box..f(b))(0) == c() || (Box..f(b))(0) != c();
  assert [q2]: c() == 1;
};

procedure CapturesFn(h : int -> int)
{
  assert [q3]: (fun x : int => h(x)) == (fun x : int => x);
};

procedure FirstOrder(y : int)
{
  assert [q4]: (fun x : int => int.add(x, y)) == (fun x : int => x);
};

function g(f : int -> int) : int;

function viaLambda(h : int -> int) : int { g(fun x : int => h(x)) }

procedure Indirect(h : int -> int)
{
  assert [q5]: viaLambda(h) == c();
};

function allFnsAt0() : bool { forall g : int -> int :: g(0) == c() || g(0) != c() }

procedure ViaBody()
{
  assert [q6]: allFnsAt0();
};

type IntFn := int -> int;

procedure QuantAlias()
{
  assume [allAliased]: forall g : IntFn :: g(0) == c() || g(0) != c();
  assert [q7]: c() == 1;
};

procedure QuantMap()
{
  assume [allMaps]: forall m : Map int (int -> int) :: m == m || c() == 0;
  assert [q8]: c() == 1;
};
#end

/-- Translates and type-checks `pgm`, then runs `lambdaLift` on it. -/
private def liftedProgram (pgm : StrataDDM.Program) : IO _root_.Core.Program := do
  let p := (TransM.run Inhabited.default (translateProgram pgm)).fst
  let .ok p := _root_.Core.typeCheck .quiet p | throw (IO.userError "type checking failed")
  let (r, _) := (_root_.Core.LambdaLift.run p).run _root_.Core.Transform.CoreTransformState.emp
  let .ok (_, p') := r | throw (IO.userError "lambdaLift failed")
  return p'

/-- The procedures of `p` whose body holds a spurious-models marker. -/
private def markedProcNames (p : _root_.Core.Program) : List String :=
  p.decls.filterMap fun
    | .proc q _ =>
      let isMarker : _root_.Core.Statement → Bool
        | .cmd (.cmd (.assume l _ _)) => l == _root_.Core.spuriousModelsLabel
        | _ => false
      if !Imperative.Block.allSubstmts (fun s => !isMarker s) q.body.statements then
        some q.header.name.name else none
    | _ => none

/-- info: [QuantFn, QuantBox, CapturesFn, Indirect, ViaBody, QuantAlias, QuantMap] -/
#guard_msgs in
#eval show IO Unit from do
  let p' ← liftedProgram spuriousModelsPgm
  IO.println (markedProcNames p')

/-- Verify `pgm` with the default pipeline and print each obligation's label and verdict. -/
private def printVerdicts (pgm : StrataDDM.Program) (useArrayTheory : Bool := false) :
    IO Unit := do
  match ← (Strata.Core.verifyProgram (translate pgm)
      { _root_.Core.VerifyOptions.quiet with useArrayTheory }).toBaseIO with
  | .ok rs => for r in rs.toList do IO.println s!"{r.obligation.label} {r.formatOutcome}"
  | .error e => IO.println s!"error: {e}"

-- A program axiom is a path condition of every obligation declared after it. One that
-- applies a function whose body quantifies over a function type marks every procedure
-- declared after it, including one that never mentions it (`Unrelated`), and none
-- declared before it (`Before`), which keeps its counterexample.
def spuriousAxiomAppliesPgm :=
#strata
program Core;

function allZero() : bool { forall g : int -> int :: g(0) == 0 || g(0) != 0 }

procedure Before(y : int)
{
  assert [before]: y == 0;
};

axiom [usesAllZero]: allZero();

procedure Unrelated(y : int)
{
  assert [plain]: y == 0;
};
#end

/-- info: [Unrelated] -/
#guard_msgs in
#eval show IO Unit from do
  let p' ← liftedProgram spuriousAxiomAppliesPgm
  IO.println (markedProcNames p')

/--
info: before ❌ fail
plain ❓ unknown
-/
#guard_msgs in
#eval printVerdicts spuriousAxiomAppliesPgm

-- A lemma is an obligation of its own, so one quantifying over a function type
-- carries the marker in its metadata, which its obligation alone keeps. A procedure next
-- to it keeps its counterexample, even one whose assertion has the lemma's label.
def spuriousLemmaPgm :=
#strata
program Core;

function c() : int;

lemma [allFns]: forall g : int -> int :: g(0) == c() || g(0) != c();

procedure Unrelated(y : int)
{
  assert [plain]: y == 0;
  assert [allFns]: y == 1;
};
#end

/-- info: [allFns] -/
#guard_msgs in
#eval show IO Unit from do
  let p' ← liftedProgram spuriousLemmaPgm
  IO.println (p'.decls.filterMap fun
    | .lemma l md => if (md.findElem _root_.Core.spuriousModelsField).isSome then
        some (toString l.name) else none
    | _ => none)

-- The default pipeline turns the lemma into an obligation unit before `lambdaLift`, which
-- marks it with an assumption like any procedure; a pipeline that keeps lemmas, as
-- `cfn-strata` does, marks it through its metadata. Either way the procedure's assertion
-- named `allFns` keeps its counterexample.
/--
info: allFns ✅ pass
plain ❌ fail
allFns ❌ fail
-/
#guard_msgs in
#eval printVerdicts spuriousLemmaPgm

-- A lemma that does not quantify over a function type is marked too when an
-- axiom declared before it does, since that axiom is one of its path conditions; a lemma
-- declared before the axiom is not.
def spuriousAxiomLemmaPgm :=
#strata
program Core;

function c() : int;

lemma [before]: c() == c();

axiom [allFns]: forall g : int -> int :: g(0) == c() || g(0) != c();

lemma [plain]: c() == c();
#end

/-- info: [plain] -/
#guard_msgs in
#eval show IO Unit from do
  let p' ← liftedProgram spuriousAxiomLemmaPgm
  IO.println (p'.decls.filterMap fun
    | .lemma l md => if (md.findElem _root_.Core.spuriousModelsField).isSome then
        some (toString l.name) else none
    | _ => none)

-- The marking decides the verdict. The solver finds a model of each assertion
-- being false. `lambdaLift`'s model validation turns it into unknown for an
-- obligation that quantifies over a function type, directly (`marked`), through
-- a function it calls (`viaCall`), or through a loop invariant, which loop
-- elimination turns into an assumption before `lambdaLift` runs (`afterLoop`);
-- after a quantifier over `int` (`unmarked`) the model stands as a
-- counterexample, in the same program. `lambdaLift` runs last, so no phase can
-- drop its markers before the obligations are read. A lifted lambda capturing a
-- function marks its procedure too (`CapturesFn` in `spuriousModelsPgm`); its
-- verdict cannot show it, since the solver answers unknown on its axiom.
def spuriousVerdictPgm :=
#strata
program Core;

function c() : int;

function allFnsAt0() : bool { forall g : int -> int :: g(0) == c() || g(0) != c() }

procedure MarkedQuant()
{
  assume [allFns]: forall g : int -> int :: g(0) == c() || g(0) != c();
  assert [marked]: c() == 1;
};

procedure UnmarkedQuant()
{
  assume [allInts]: forall i : int :: i == c() || i != c();
  assert [unmarked]: c() == 1;
};

procedure ViaCall()
{
  assert [viaCall]: allFnsAt0() && c() == 1;
};

procedure LoopInv(n : int, out i : int)
{
  i := 0;
  while (int.lt(i, n))
    invariant forall g : int -> int :: g(0) == c() || g(0) != c()
  {
    i := int.add(i, 1);
  }
  assert [afterLoop]: c() == 1;
};
#end

/-- For each assertion of `pgm`, the solver's answer to its validity query and what
    `lambdaLift`'s model validation makes of it: `sat` passes through, and becomes
    `unknown` when the obligation is marked. -/
private def lambdaLiftVerdicts (pgm : StrataDDM.Program) : IO Unit := do
  let kind : Imperative.SMT.Result Core.Expression.Ident → String
    | .sat _ => "sat" | .unsat => "unsat" | .unknown _ => "unknown" | .err _ => "error"
  match ← (Strata.Core.verifyProgram (translate pgm) _root_.Core.VerifyOptions.quiet).toBaseIO with
  | .error e => IO.println s!"error: {e}"
  | .ok rs =>
    for r in rs do
      if r.obligation.label.startsWith "insertLoopInvAssert" then continue
      match r.outcome with
      | .ok o =>
        let log := o.solverLog.toList.flatMap (·.toList)
        let raw := (log.find? (·.phase == "solver.val")).map (kind ·.result)
        let lifted := (log.reverse.find? (·.phase == "lambdaLift")).map (kind ·.result)
        IO.println s!"{r.obligation.label}: solver {raw.getD "-"}, lambdaLift {lifted.getD "-"}"
      | .error e => IO.println s!"{r.obligation.label}: error {e}"

/--
info: marked: solver sat, lambdaLift unknown
unmarked: solver sat, lambdaLift sat
viaCall: solver sat, lambdaLift unknown
afterLoop: solver sat, lambdaLift unknown
-/
#guard_msgs in
#eval lambdaLiftVerdicts spuriousVerdictPgm

/-! ## Which lambdas share a lifted function -/

-- Lambdas equal up to the names of their bound variables share one function,
-- but not lambdas whose bound variables or captures have different types.
def sharingPgm :=
#strata
program Core;

function gi(f : int -> int) : int;
function gb(f : bool -> bool) : int;
function gc(f : int -> bool) : int;

procedure Test(i : int, b : bool)
{
  assert [same]: gi(fun x : int => x) == gi(fun y : int => y);
  assert [binderType]: gi(fun x : int => x) == gb(fun x : bool => x);
  assert [captureType]: gc(fun x : int => x == i) == gb(fun x : bool => x == b);
};
#end

-- For each assertion, the lifted functions its two lambdas became, left then right:
-- `same` uses one function twice; `binderType` and `captureType` use two each, so
-- four functions in all.
/-- info: [(same, [$__lam_0, $__lam_0]), (binderType, [$__lam_0, $__lam_1]), (captureType, [$__lam_2, $__lam_3])] -/
#guard_msgs in
#eval show IO Unit from do
  let p' ← liftedProgram sharingPgm
  let lifted (e : _root_.Core.Expression.Expr) : List String :=
    (e.getOps.map (·.name)).filter (·.startsWith Core.NameMangling.liftedLambdaPrefix)
  IO.println (p'.decls.flatMap fun (d : _root_.Core.Decl) => match d with
    | .proc q _ => q.body.statements.filterMap fun
      | .cmd (.cmd (.assert l e _)) => some (l, lifted e)
      | _ => none
    | _ => [])

-- Symbolic evaluation substitutes `f` at both of its uses, so the two
-- occurrences of the lambda are one shared subterm when `lambdaLift` runs. The
-- check that skips declarations with nothing to lift visits it once, and still
-- finds the lambda: the obligation reaches the solver and passes, where a lambda
-- left in would be an encoding error.
def sharedLambdaPgm :=
#strata
program Core;

function g(f : int -> int) : int;

procedure Shared(y : int)
{
  var f : int -> int := fun x : int => int.add(x, y);
  assert [shared]: g(f) == g(f);
};
#end

/--
info:
Obligation: shared
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify sharedLambdaPgm (options := .quiet)

/-! ## A pipeline without `lambdaLift` -/

-- The back end requires `noLambdas`, so a pipeline that leaves out
-- `lambdaLift` is rejected when it is assembled.
/-- info: phase #16 `the verification back end` requires `noLambdas` but preceding phases only guarantee `noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, hasObligationForm, noProcedureContracts, noPolymorphicProcedures, noPolymorphicFunctions, typeAnnotated, exitsCovered` -/
#guard_msgs in
#eval match Strata.Core.validatePipeline ((_root_.Core.corePipelinePhases .quiet).filter
    (·.phase.name != "lambdaLift")) with
  | .ok _ => IO.println "accepted"
  | .error e => IO.println e

-- With the default pipeline, the lambda is lifted and its obligation reaches
-- the solver; the obligation next to it is unaffected.
def strayLambdaPgm :=
#strata
program Core;

function g(f : int -> int) : int;

procedure Test(y : int)
{
  assert [usesLambda]: g(fun x : int => int.add(x, y)) == 0;
  assert [plain]: int.add(y, 0) == y;
};
#end

/--
info:
Obligation: usesLambda
Property: assert
Result: ❓ unknown

Obligation: plain
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify strayLambdaPgm (options := .quiet)

-- A lambda in the axioms of a function no obligation reaches is never encoded. The
-- source syntax attaches no axiom to a function, so the test moves the program axiom
-- `unusedAx` onto the function `unused`, which nothing applies. Then the program satisfies
-- `noLambdas`, and its verdict is the one it would be without that function. As a
-- program axiom, the lambda is read.
def unreachedAxiomLambdaPgm :=
#strata
program Core;

function g(f : int -> int) : int;
function unused(i : int) : int;
axiom [unusedAx]: forall i : int :: g(fun x : int => int.add(x, i)) == i;

procedure P(y : int)
{
  assert [plain]: int.add(y, 0) == y;
};
#end

/-- `unreachedAxiomLambdaPgm`, type checked, with its axiom moved onto `unused`. -/
private def axiomOnUnused : IO _root_.Core.Program := do
  let .ok p := _root_.Core.typeCheck .quiet (translate unreachedAxiomLambdaPgm)
    | throw (IO.userError "type checking failed")
  let ax := p.decls.findSome? fun (d : _root_.Core.Decl) => match d with
    | .ax a _ => some a.e
    | _ => none
  let some ax := ax | throw (IO.userError "no axiom")
  return { decls := p.decls.filterMap fun (d : _root_.Core.Decl) => match d with
    | .ax _ _ => none
    | .func f md => some (if f.name.name == "unused" then .func { f with axioms := [ax] } md
        else .func f md)
    | d => some d }

/--
info: as a program axiom, noLambdas holds: false
on an unreached function, noLambdas holds: true
plain ✅ pass
-/
#guard_msgs in
#eval show IO Unit from do
  let .ok p := _root_.Core.typeCheck .quiet (translate unreachedAxiomLambdaPgm)
    | throw (IO.userError "type checking failed")
  let holds (q : _root_.Core.Program) :=
    (_root_.Core.ProgramFact.noLambdas.check?.map (· q)).getD false
  IO.println s!"as a program axiom, noLambdas holds: {holds p}"
  let q ← axiomOnUnused
  IO.println s!"on an unreached function, noLambdas holds: {holds q}"
  match ← (Strata.Core.verifyProgram q _root_.Core.VerifyOptions.quiet).toBaseIO with
  | .ok rs => IO.println (", ".intercalate (rs.toList.map fun r =>
      s!"{r.obligation.label} {r.formatOutcome}"))
  | .error e => IO.println s!"error: {e}"



-- Captures of every kind get a typed parameter of the lifted function: a procedure
-- parameter (`y`), a local (`z`), and the binder of an enclosing lambda (`u`), whose
-- types come from their annotations and from the enclosing binder's.
def captureKindsPgm :=
#strata
program Core;

function g(f : int -> int) : int;
function h(f : int -> int -> int) : int;

procedure Kinds(y : int)
{
  var z : int := int.add(y, 1);
  assert [kinds]: h(fun u : int => fun x : int => int.add(int.add(x, u), int.add(y, z)))
    == h(fun u : int => fun x : int => int.add(int.add(x, u), int.add(y, z)));
};
#end

/-- info: [($__lam_0, [int, int, int]), ($__lam_1, [int, int])] -/
#guard_msgs in
#eval do
  let p' ← liftedProgram captureKindsPgm
  IO.println (p'.decls.filterMap fun (d : _root_.Core.Decl) => match d with
    | .func f _ => if f.name.name.startsWith Core.NameMangling.liftedLambdaPrefix then
        some (f.name.name, f.inputs.values.map fun t => toString (Std.format t)) else none
    | _ => none)

-- A program with no abstraction, no partial application and no function value, here a
-- full application of a two-argument operator, comes out of `lambdaLift` unchanged.
def firstOrderPgm :=
#strata
program Core;

function c() : int;

procedure P(y : int)
spec {
  requires int.gt(y, 0);
}
{
  assume [allInts]: forall i : int :: int.add(i, y) == int.add(y, i);
  assert [sum]: int.sub(int.add(y, c()), c()) == y;
};
#end

/-- info: unchanged -/
#guard_msgs in
#eval do
  let p := (TransM.run Inhabited.default (translateProgram firstOrderPgm)).fst
  let .ok p := _root_.Core.typeCheck .quiet p | throw (IO.userError "type checking failed")
  let (r, _) := (_root_.Core.LambdaLift.run p).run _root_.Core.Transform.CoreTransformState.emp
  let .ok (changed, p') := r | throw (IO.userError "lambdaLift failed")
  IO.println (if !changed && p' == p then "unchanged" else "changed")

/-! ## What `lambdaLift` keeps

The phase claims `noLambdas` and a list of preserved facts, without a proof. On every
program of this file that meets its requirements after type checking (31 of them; the
others keep beta redexes or polymorphic functions, which earlier phases remove), each claim is
checked on its output: `noLambdas` holds, and each preserved fact that held on the input
and has an executable check (`ProgramFact.check?`) still holds. `typeAnnotated` has no
check, since confirming annotations are present does not confirm they are right; its
syntactic part, every expression fully annotated, is checked too. The statement facts
hold because the only statements the phase adds are `assume`s placed before a statement
or at the start of a body, never after the last one: an `assume` is in obligation and
tree form, declares, assigns and exits nothing, is not a call, loop or conditional, and
an arm it is added to keeps its checks. -/

/-- The programs of this file the claims are checked on. -/
private def allPrograms : List (String × StrataDDM.Program) :=
  [("lambdaIdentityPgm", (lambdaIdentityPgm : StrataDDM.Program)),
   ("lambdaNestedPgm", (lambdaNestedPgm : StrataDDM.Program)),
   ("lambdaApplyPgm", (lambdaApplyPgm : StrataDDM.Program)),
   ("lambdaApplyNoInlinePgm", (lambdaApplyNoInlinePgm : StrataDDM.Program)),
   ("lambdaInBodyPgm", (lambdaInBodyPgm : StrataDDM.Program)),
   ("nestedRedexPgm", (nestedRedexPgm : StrataDDM.Program)),
   ("liftArgRedexPgm", (liftArgRedexPgm : StrataDDM.Program)),
   ("constLamPgm", (constLamPgm : StrataDDM.Program)),
   ("dupRedexPgm", (dupRedexPgm : StrataDDM.Program)),
   ("underBinderPgm", (underBinderPgm : StrataDDM.Program)),
   ("haveAliasPgm", (haveAliasPgm : StrataDDM.Program)),
   ("recHigherOrderPgm", (recHigherOrderPgm : StrataDDM.Program)),
   ("recLambdaInBodyPgm", (recLambdaInBodyPgm : StrataDDM.Program)),
   ("lambdaInAssertPgm", (lambdaInAssertPgm : StrataDDM.Program)),
   ("polyApplyPgm", (polyApplyPgm : StrataDDM.Program)),
   ("polyComposePgm", (polyComposePgm : StrataDDM.Program)),
   ("polyLambdaPgm", (polyLambdaPgm : StrataDDM.Program)),
   ("polyIdentityLambdaPgm", (polyIdentityLambdaPgm : StrataDDM.Program)),
   ("polyRecLambdaPgm", (polyRecLambdaPgm : StrataDDM.Program)),
   ("multiBindingLambdaPgm", (multiBindingLambdaPgm : StrataDDM.Program)),
   ("exprApplyPgm", (exprApplyPgm : StrataDDM.Program)),
   ("polyDatatypeFnInstExprAppPgm", (polyDatatypeFnInstExprAppPgm : StrataDDM.Program)),
   ("lambdaInSpecPgm", (lambdaInSpecPgm : StrataDDM.Program)),
   ("curryPgm", (curryPgm : StrataDDM.Program)),
   ("lambdaInCondPgm", (lambdaInCondPgm : StrataDDM.Program)),
   ("higherOrderLambdaPgm", (higherOrderLambdaPgm : StrataDDM.Program)),
   ("datatypeFnFieldLambdaPgm", (datatypeFnFieldLambdaPgm : StrataDDM.Program)),
   ("datatypeFnFieldSymbolicPgm", (datatypeFnFieldSymbolicPgm : StrataDDM.Program)),
   ("datatypeFnFieldSymbolicWrongPgm", (datatypeFnFieldSymbolicWrongPgm : StrataDDM.Program)),
   ("datatypeCurriedFnFieldPgm", (datatypeCurriedFnFieldPgm : StrataDDM.Program)),
   ("polyDatatypeFnInstPgm", (polyDatatypeFnInstPgm : StrataDDM.Program)),
   ("traitWitnessPgm", (traitWitnessPgm : StrataDDM.Program)),
   ("capturingLambdaPgm", (capturingLambdaPgm : StrataDDM.Program)),
   ("partialApplicationPgm", (partialApplicationPgm : StrataDDM.Program)),
   ("precondFnValuePgm", (precondFnValuePgm : StrataDDM.Program)),
   ("treeThroughFunctionPgm", (treeThroughFunctionPgm : StrataDDM.Program)),
   ("precondUnderLambdaPgm", (precondUnderLambdaPgm : StrataDDM.Program)),
   ("divUnderLambdaPgm", (divUnderLambdaPgm : StrataDDM.Program)),
   ("shadowedPrecondPgm", (shadowedPrecondPgm : StrataDDM.Program)),
   ("spuriousModelsPgm", (spuriousModelsPgm : StrataDDM.Program)),
   ("spuriousLemmaPgm", (spuriousLemmaPgm : StrataDDM.Program)),
   ("spuriousAxiomLemmaPgm", (spuriousAxiomLemmaPgm : StrataDDM.Program)),
   ("spuriousVerdictPgm", (spuriousVerdictPgm : StrataDDM.Program)),
   ("sharingPgm", (sharingPgm : StrataDDM.Program)),
   ("strayLambdaPgm", (strayLambdaPgm : StrataDDM.Program)),
   ("captureKindsPgm", (captureKindsPgm : StrataDDM.Program)),
   ("firstOrderPgm", (firstOrderPgm : StrataDDM.Program))]

/-- The claims of `lambdaLift` that fail on its output for `pgm`, or `none` when `pgm`
    does not meet its requirements after type checking or is rejected. -/
private def failedClaims (pgm : StrataDDM.Program) : Option (List String) := Id.run do
  let p := (TransM.run Inhabited.default (translateProgram pgm)).fst
  let .ok p := _root_.Core.typeCheck .quiet p | return none
  let reqs := [_root_.Core.ProgramFact.noCFGBodies, .noBetaRedexes,
    .noPolymorphicProcedures, .noPolymorphicFunctions]
  unless reqs.all (fun f => (f.check?.map (· p)).getD true) do return none
  let (r, _) := (_root_.Core.LambdaLift.run p).run _root_.Core.Transform.CoreTransformState.emp
  let .ok (_, p') := r | return none
  let mut failed := []
  unless (_root_.Core.ProgramFact.noLambdas.check?.map (· p')).getD false do
    failed := "noLambdas" :: failed
  for f in Strata.Pipeline.factsOf _root_.Core.lambdaLiftPipelinePhase.preserves do
    if let some c := f.check? then
      if c p && !c p' then failed := f.name :: failed
  if _root_.Core.Program.allExprs Lambda.LExpr.fullyAnnotated p &&
      !_root_.Core.Program.allExprs Lambda.LExpr.fullyAnnotated p' then
    failed := "fullyAnnotated" :: failed
  return some failed.reverse

/-- info: checked: 31
failing: [] -/
#guard_msgs in
#eval do
  let results : List (String × List String) :=
    allPrograms.filterMap fun (n, pgm) => (failedClaims pgm).map fun fs => (n, fs)
  IO.println s!"checked: {results.length}"
  IO.println s!"failing: {results.filter fun (r : String × List String) => !r.2.isEmpty}"

/-! ## Where the `noLambdas` check looks

`assertNoLambdas`, the check a pipeline without `lambdaLift` can end with, rejects a
lambda in every position the back end reads: a program axiom, a lemma, a procedure's
contract, a statement, a quantifier's body and its trigger, and the body of a function
one of these reaches. Each program below has one lambda in one position; the check, run
on it after type checking, rejects it and names the lambda. A lambda the back end never
reads does not count: in the body of a function nothing reaches (`unreachedFnBody`), in
an inline function's body once its uses are inlined (`inlinedAway`), or in a function's
precondition, which the back end does not emit. A `distinct` declaration lists constant
names only, so it cannot hold a lambda. -/

def lamAt_fnBody :=
#strata
program Core;
function g(f : int -> int) : int;
function h() : int { g(fun x : int => x) }
axiom [usesH]: h() == 0;
#end

def lamAt_unreachedFnBody :=
#strata
program Core;
function g(f : int -> int) : int;
function h() : int { g(fun x : int => x) }
#end

def lamAt_inlinedAway :=
#strata
program Core;
inline function app (f : int -> int, v : int) : int { f(v) }
inline function h (v : int) : int { app(fun y : int => int.add(y, 1), v) }
procedure R (a : int)
{
  assert [r]: int.add(a, 1) == int.add(a, 1);
};
#end

def lamAt_fnPrecondition :=
#strata
program Core;
function g(f : int -> int) : int;
function h(y : int) : int
  requires g(fun x : int => x) == y;
{ y }
#end

def lamAt_axiom :=
#strata
program Core;
function g(f : int -> int) : int;
axiom [ax]: g(fun x : int => x) == 0;
#end

def lamAt_lemma :=
#strata
program Core;
function g(f : int -> int) : int;
lemma [lm]: g(fun x : int => x) == g(fun x : int => x);
#end

def lamAt_requires :=
#strata
program Core;
function g(f : int -> int) : int;
procedure P()
spec {
  requires g(fun x : int => x) == 0;
}
{ };
#end

def lamAt_ensures :=
#strata
program Core;
function g(f : int -> int) : int;
procedure P(out r : int)
spec {
  ensures r == g(fun x : int => x);
}
{ r := 0; };
#end

def lamAt_assert :=
#strata
program Core;
function g(f : int -> int) : int;
procedure P()
{
  assert [a]: g(fun x : int => x) == 0;
};
#end

def lamAt_quantBody :=
#strata
program Core;
function g(f : int -> int) : int;
procedure P()
{
  assume [q]: forall i : int :: g(fun x : int => int.add(x, i)) == i;
};
#end

def lamAt_trigger :=
#strata
program Core;
function g(f : int -> int) : int;
function k(i : int) : int;
axiom [tr]: forall i : int :: { g(fun x : int => int.add(x, i)) } k(i) == g(fun x : int => int.add(x, i));
#end

-- The verdict of `assertNoLambdas` on each program, and its message when it rejects.
/--
info: fnBody: rejected, located: ❌ Expected no lambda, since the verification back end has no term for one, but found the lambda `fun x : int => …`. Run `lambdaLift` before the back end.
unreachedFnBody: accepted
inlinedAway: accepted
fnPrecondition: accepted
axiom: rejected, located: ❌ Expected no lambda, since the verification back end has no term for one, but found the lambda `fun x : int => …`. Run `lambdaLift` before the back end.
lemma: rejected, located: ❌ Expected no lambda, since the verification back end has no term for one, but found the lambda `fun x : int => …`. Run `lambdaLift` before the back end.
requires: rejected, located: ❌ Expected no lambda, since the verification back end has no term for one, but found the lambda `fun x : int => …`. Run `lambdaLift` before the back end.
ensures: rejected, located: ❌ Expected no lambda, since the verification back end has no term for one, but found the lambda `fun x : int => …`. Run `lambdaLift` before the back end.
assert: rejected, located: ❌ Expected no lambda, since the verification back end has no term for one, but found the lambda `fun x : int => …`. Run `lambdaLift` before the back end.
quantBody: rejected, located: ❌ Expected no lambda, since the verification back end has no term for one, but found the lambda `fun x : int => …`. Run `lambdaLift` before the back end.
trigger: rejected, located: ❌ Expected no lambda, since the verification back end has no term for one, but found the lambda `fun x : int => …`. Run `lambdaLift` before the back end.
-/
#guard_msgs in
#eval do
  let progs : List (String × StrataDDM.Program) :=
    [("fnBody", (lamAt_fnBody : StrataDDM.Program)),
   ("unreachedFnBody", (lamAt_unreachedFnBody : StrataDDM.Program)),
   ("inlinedAway", (lamAt_inlinedAway : StrataDDM.Program)),
   ("fnPrecondition", (lamAt_fnPrecondition : StrataDDM.Program)),
   ("axiom", (lamAt_axiom : StrataDDM.Program)),
   ("lemma", (lamAt_lemma : StrataDDM.Program)),
   ("requires", (lamAt_requires : StrataDDM.Program)),
   ("ensures", (lamAt_ensures : StrataDDM.Program)),
   ("assert", (lamAt_assert : StrataDDM.Program)),
   ("quantBody", (lamAt_quantBody : StrataDDM.Program)),
   ("trigger", (lamAt_trigger : StrataDDM.Program))]
  for (n, pgm) in progs do
    let p := (TransM.run Inhabited.default (translateProgram pgm)).fst
    match _root_.Core.typeCheck .quiet p with
    | .error e => IO.println s!"{n}: type error {e}"
    | .ok p =>
      let phase := _root_.Core.ProgramFact.assertPhase .noLambdas
      match (phase.transform p).run.run _root_.Core.Transform.CoreTransformState.emp with
      | (.ok _, _) => IO.println s!"{n}: accepted"
      | (.error e, _) =>
        let located := if e.fileRange == Strata.FileRange.unknown then "unlocated" else "located"
        IO.println s!"{n}: rejected, {located}: {e.message}"

/-! ## A function whose argument is a function

`A -> B` is the SMT array `(Array A B)`, so a function type whose argument is a function
would be an array indexed by an array, which cvc5 rejects; so would a map keyed by a
function or a set of functions under array theory. The encoder refuses such a type with a message, for a value
of it and for a datatype field of it. -/

def functionOfFunctionPgm :=
#strata
program Core;

function apply0(f : int -> int) : int { f(0) }
function g2(k : (int -> int) -> int) : int;

procedure Q()
{
  assert [hol]: g2(fun f : int -> int => f(0)) == g2(apply0);
};
#end

/--
info: hol 🚨 SMT Encoding Error! Cannot encode the type '(arrow (arrow int int) int)' to SMT: its sort is an array indexed by an array, which cvc5 rejects.
-/
#guard_msgs in
#eval printVerdicts functionOfFunctionPgm

def fieldOfFunctionPgm :=
#strata
program Core;

datatype B { MkB(k : (int -> int) -> int) };

procedure Q(b : B)
{
  assert [field]: B..isMkB(b);
};
#end

/-- error: Cannot encode datatype 'B' to SMT: constructor 'MkB' has field 'k' of type '(arrow (arrow int int) int)', whose SMT sort is an array indexed by an array, which cvc5 rejects. -/
#guard_msgs in
#eval Strata.Core.verify fieldOfFunctionPgm (options := .quiet)

-- Under array theory, a map keyed by a function is an array indexed by an array. Only
-- the obligation whose query needs that sort gets the error; the program's other
-- obligation keeps its verdict.
def mapOfFunctionsPgm :=
#strata
program Core;

procedure M(m : Map (int -> int) int, h : int -> int, y : int)
{
  assert [mapKey]: m[h] == 0;
  assert [other]: int.lt(y, int.add(y, 1));
};
#end

/--
info: mapKey 🚨 SMT Encoding Error! Cannot encode the type '(Map (arrow int int) int)' to SMT: its sort is an array indexed by an array, which cvc5 rejects; run without --use-array-theory.
other ✅ pass
-/
#guard_msgs in
#eval printVerdicts mapOfFunctionsPgm (useArrayTheory := true)

-- Under array theory, a function whose argument is a map would be an array indexed by an
-- array, so a variable of that type is encoded as a free variable whose argument is a
-- function is: comparing two of them gets a verdict, as on a build where every function
-- type is an opaque sort, and so does the program's other obligation.
def fnOfMapPgm :=
#strata
program Core;

procedure Q(f : (Map int int) -> int, h : (Map int int) -> int, y : int)
{
  assert [fnOfMap]: f == h;
  assert [other]: int.lt(y, int.add(y, 1));
};
#end

/--
info: fnOfMap ❌ fail
other ✅ pass
-/
#guard_msgs in
#eval printVerdicts fnOfMapPgm (useArrayTheory := true)

-- A function-typed variable used as a value is not lifted, so comparing two of them is an
-- ordinary query over arrays, and its counterexample stands.
def fnVarEqPgm :=
#strata
program Core;

procedure Eq(f : int -> int, g : int -> int)
{
  assert [fEqG]: f == g;
};
#end

/-- info: fEqG ❌ fail -/
#guard_msgs in
#eval printVerdicts fnVarEqPgm

-- A free variable whose argument is a function is an uninterpreted function of its
-- arguments when applied, and a constant of an opaque sort when used as a value, so
-- both get a verdict.
def fnOfFnVarPgm :=
#strata
program Core;

procedure K(k : (int -> int) -> int, h : int -> int)
{
  assert [applied]: k(h) == k(h);
};

procedure K2(k : (int -> int) -> int, k2 : (int -> int) -> int)
{
  assert [asValue]: k == k2;
};

procedure K3(b : bool, k : (int -> int) -> int, k2 : (int -> int) -> int, h : int -> int)
{
  assert [merged]: (if b then k else k2)(h) == (if b then k(h) else k2(h));
};
#end

/--
info: applied ✅ pass
asValue ❌ fail
merged ✅ pass
-/
#guard_msgs in
#eval printVerdicts fnOfFnVarPgm

-- Such a variable can only be fully applied: applied to fewer arguments than its
-- uninterpreted function takes, it gets an error naming the partial application, and a
-- full application keeps its verdict.
def fnOfFnPartialPgm :=
#strata
program Core;

function g(f : int -> int) : int;

procedure P(k : (int -> int) -> int -> int, h1 : int -> int, h2 : int -> int)
{
  assert [fullBad]: k(h1, 0) == k(h2, 0);
  assert [partialBad]: g(k(h1)) == g(k(h2));
};
#end

/--
info: fullBad ❌ fail
partialBad 🚨 SMT Encoding Error! Cannot encode partial application of k@1 to SMT: its type '(arrow (arrow int int) (arrow int int))' would be an array indexed by an array, so it is encoded as an uninterpreted function of its 2 arguments, but is applied to 1.
-/
#guard_msgs in
#eval printVerdicts fnOfFnPartialPgm

-- An operator whose argument is a function, used as a value: its array sort would be
-- indexed by an array, so the obligation gets an encoding error rather than a sort
-- the solver rejects.
def fnOfFnOpValuePgm :=
#strata
program Core;

function apply(f : int -> int) : int;
function k(h : (int -> int) -> int) : int;

procedure P()
{
  assert [opValue]: k(apply) == 0;
};
#end

/--
info: opValue 🚨 SMT Encoding Error! Cannot encode the type '(arrow (arrow int int) int)' to SMT: its sort is an array indexed by an array, which cvc5 rejects.
-/
#guard_msgs in
#eval printVerdicts fnOfFnOpValuePgm

/-! ## Lifting only when the check would refuse

`lambdaLiftIfNeeded` runs `lambdaLift` only on a program that does not satisfy
`noLambdas`. A pipeline that does not lift lambdas can end with it and then
`assertNoLambdas`: a program the check would refuse is lifted instead, and every other
program reaches the back end unchanged. -/

/-- The default phases with `lambdaLift` replaced by `lambdaLiftIfNeeded`, then the
    `noLambdas` check. -/
private def liftIfNeededPhases : List _root_.Core.PipelinePhase :=
  ((_root_.Core.corePipelinePhases .quiet).filter (·.phase.name != "lambdaLift")) ++
    [_root_.Core.lambdaLiftIfNeededPipelinePhase,
     _root_.Core.ProgramFact.assertPhase .noLambdas]

-- On a program the check accepts, the phase changes nothing, including one whose only
-- lambda the back end never reads (`lamAt_unreachedFnBody`).
/--
info: firstOrder: changed false
unreachedFnBody: changed false
-/
#guard_msgs in
#eval show IO Unit from do
  for (n, pgm) in [("firstOrder", firstOrderPgm), ("unreachedFnBody", lamAt_unreachedFnBody)] do
    let .ok p := _root_.Core.typeCheck .quiet (translate pgm)
      | throw (IO.userError s!"{n}: type checking failed")
    match (_root_.Core.LambdaLift.runIfNeeded p).run _root_.Core.Transform.CoreTransformState.emp with
    | (.ok (changed, _), _) => IO.println s!"{n}: changed {changed}"
    | (.error e, _) => IO.println s!"{n}: error {e.message}"

-- The four programs whose only lambda the check reads without any query reaching the
-- encoder. Each has no obligation; `assertNoLambdas` alone refuses each (see above).
-- With `lambdaLiftIfNeeded` first, each is lifted, passes the check, and verifies with
-- no obligation, so nothing fails.
/--
info: axiom: 0 obligations
trigger: 0 obligations
quantBody: 0 obligations
fnBody: 0 obligations
-/
#guard_msgs in
#eval show IO Unit from do
  let .ok vp := Strata.Core.validatePipeline liftIfNeededPhases
    | throw (IO.userError "pipeline rejected")
  for (n, pgm) in [("axiom", lamAt_axiom), ("trigger", lamAt_trigger),
      ("quantBody", lamAt_quantBody), ("fnBody", lamAt_fnBody)] do
    match ← (Strata.Core.verifyProgram (translate pgm) _root_.Core.VerifyOptions.quiet
        (pipeline := some vp)).toBaseIO with
    | .ok rs => IO.println s!"{n}: {rs.toList.length} obligations"
    | .error e => IO.println s!"{n}: error {e}"

-- `lambdaLiftIfNeeded` also runs on a program without a written lambda that `lambdaLift`
-- changes: a partial application to eta-expand (`partialApp`), and a quantifier over a
-- function type whose obligations it marks (`quantFn`). Each gets the default pipeline's
-- verdict, unknown, instead of an encoding error or a counterexample from a model that
-- may be spurious.
def liftIfNeededPartialAppPgm :=
#strata
program Core;

function sub(x : int, y : int) : int { int.sub(x, y) }
function g(f : int -> int) : int;

procedure Test()
{
  assert [partialApp]: g(sub(1)) == 0;
};
#end

def liftIfNeededQuantFnPgm :=
#strata
program Core;

function c() : int;

procedure Test()
{
  assume [allFns]: forall f : int -> int :: f(0) == c() || f(0) != c();
  assert [quantFn]: c() == 1;
};
#end

/--
info: partialApp: ❓ unknown
quantFn: ❓ unknown
-/
#guard_msgs in
#eval show IO Unit from do
  let .ok vp := Strata.Core.validatePipeline liftIfNeededPhases
    | throw (IO.userError "pipeline rejected")
  for pgm in [liftIfNeededPartialAppPgm, liftIfNeededQuantFnPgm] do
    match ← (Strata.Core.verifyProgram (translate pgm) _root_.Core.VerifyOptions.quiet
        (pipeline := some vp)).toBaseIO with
    | .ok rs => for r in rs.toList do IO.println s!"{r.obligation.label}: {r.formatOutcome}"
    | .error e => IO.println s!"error: {e}"

/-! ## What the encoder emits is what `noLambdas` reads

`Program.liveExprs` decides which functions' bodies and axioms `noLambdas` reads by its own
walk over function names, while the SMT encoder decides per query which functions to emit.
The check is accurate as long as every program function the encoder emits is one
`liveExprs` reaches. This test runs each program through the default pipeline, writes its
SMT queries without solving them, and checks that every program function they declare or
define is applied in a live expression. -/

/-- The names an SMT-LIB script declares or defines. -/
private def smtDeclaredNames (text : String) : List String := Id.run do
  let mut out := []
  for kw in ["(declare-fun ", "(define-fun ", "(define-fun-rec ", "(declare-const "] do
    for part in (text.splitOn kw).drop 1 do
      let name := if part.startsWith "|" then (part.drop 1).takeWhile (· != '|')
        else part.takeWhile (fun c => c != ' ' && c != '(' && c != ')')
      out := name.toString :: out
  return out

/-- The program functions the encoder emits for `p` but `liveExprs` does not reach. -/
private def emittedOutsideLive (p : _root_.Core.Program) : IO (List String) := do
  let mut s : _root_.Core.Transform.CoreTransformState :=
    { _root_.Core.Transform.CoreTransformState.emp with factory := _root_.Core.Factory }
  let mut q := p
  for ph in _root_.Core.corePipelinePhases .quiet do
    match (ph.transform q).run.run s with
    | (.ok (_, q'), s') => q := q'; s := s'
    | (.error e, _) => throw (IO.userError s!"{ph.phase.name}: {e.message}")
  let funcs : List String := q.decls.flatMap fun
    | .func f _ => [f.name.name]
    | .recFuncBlock fs _ => fs.map (·.name.name)
    | _ => []
  let applied : Std.HashSet String := q.liveExprs.foldl (fun acc e =>
    e.getOps.foldl (fun acc o => acc.insert o.name) acc) {}
  let dir ← IO.FS.createTempDir
  let opts := { _root_.Core.VerifyOptions.quiet with
    vcDirectory := some dir, alwaysGenerateSMT := true, skipSolver := true }
  let _ ← (_root_.Core.verify p dir opts).toBaseIO
  let mut emitted : Std.HashSet String := {}
  for ent in ← dir.readDir do
    if ent.path.extension == some "smt2" then
      for n in smtDeclaredNames (← IO.FS.readFile ent.path) do emitted := emitted.insert n
  IO.FS.removeDirAll dir
  return funcs.filter fun n => emitted.contains n && !applied.contains n

-- `precondFnValuePgm` has an obligation that symbolic evaluation already finds false;
-- `Core.verify` reports it while it writes the queries.
/--
info:

Obligation assert_unchecked_calls_pos_0: failed!

Result obtained during evaluation.
every emitted program function is live: true
-/
#guard_msgs in
#eval do
  let progs : List (String × StrataDDM.Program) :=
    [("fnBody", lamAt_fnBody), ("unreachedFnBody", lamAt_unreachedFnBody),
     ("inlinedAway", lamAt_inlinedAway), ("fnPrecondition", lamAt_fnPrecondition),
     ("axiom", lamAt_axiom), ("lemma", lamAt_lemma), ("requires", lamAt_requires),
     ("ensures", lamAt_ensures), ("assert", lamAt_assert), ("quantBody", lamAt_quantBody),
     ("trigger", lamAt_trigger), ("capturing", capturingLambdaPgm),
     ("partialApplication", partialApplicationPgm), ("traitWitness", traitWitnessPgm),
     ("datatypeFnField", datatypeFnFieldLambdaPgm), ("precondFnValue", precondFnValuePgm),
     ("spuriousModels", spuriousModelsPgm), ("sharing", sharingPgm),
     ("unreachedAxiom", unreachedAxiomLambdaPgm)]
  let mut ok := true
  for (n, pgm) in progs do
    let .ok p := _root_.Core.typeCheck .quiet (translate pgm)
      | throw (IO.userError s!"{n}: type checking failed")
    let out ← emittedOutsideLive p
    unless out.isEmpty do
      ok := false
      IO.println s!"{n}: emitted outside the live set: {out}"
  IO.println s!"every emitted program function is live: {ok}"

end
