/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.StatementEval

namespace Core
---------------------------------------------------------------------

section Tests

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative (PureFunc)

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(x : int) → #18]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_18
Property: assert
Assumptions:
Proof Obligation:
#true
-/
#guard_msgs in
#eval (evalOne ∅ ∅ [.init "x" t[int] eb[#0],
                    .set "x" eb[#18],
                    .assert "x_eq_18" eb[x == #18]]) |>.snd |> format

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(y : int) → _yinit
(x : int) → _yinit]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_12
Property: assert
Assumptions:
Proof Obligation:
(_yinit == #12)
-/
#guard_msgs in
#eval (evalOne
  ((Env.init (empty_factory := true)).pushScope [("y", (mty[int], eb[_yinit]))])
  ∅
  [.init "x" t[int] eb[#0],
  .set "x" eb[y],
  .assert "x_eq_12" eb[x == #12]]) |>.snd |> format

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(x : bool) → (x == #true)]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
-/
#guard_msgs in
-- NOTE: no error during evaluation here; the typechecker should flag this
-- though because `x` can't appear in its own initialization expression.
#eval evalOne ∅ ∅
       [
       .init "x" t[bool] eb[x == #true]
       ] |>.snd |> format

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(minit : (arrow int int)) → (_minit : (arrow int int))
(m : (arrow int int)) → (λ (if (%0 == #3) then #30 else ((λ (if (%0 == #2) then #20 else ((λ (if (%0 == #1) then #10 else ((_minit : (arrow int int))
         %0)))
      %0)))
   %0)))
(m0 : int) → ((_minit : (arrow int int)) #0)]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: m_5_eq_50
Property: assert
Assumptions:
Proof Obligation:
(((_minit : (arrow int int)) #5) == #50)

Label: m_2_eq_20
Property: assert
Assumptions:
Proof Obligation:
#true

Label: m_1_eq_10
Property: assert
Assumptions:
Proof Obligation:
#true
-/
#guard_msgs in
#eval (evalOne
  ((Env.init (empty_factory := true)).pushScope
    [("minit", (mty[int → int], eb[(_minit : int → int)]))])
  ∅
  [.init "m" t[int → int] eb[minit],
  .init "m0" t[int] eb[(m #0)],
  .set "m" eb[λ (if (%0 == #1) then #10 else ((m : int → int) %0))],
  .set "m" eb[λ (if (%0 == #2) then #20 else ((m : int → int) %0))],
  .assert "m_5_eq_50" eb[(m #5) == #50],
  .assert "m_2_eq_20" eb[(m #2) == #20],
  .set "m" eb[λ (if (%0 == #3) then #30 else ((m : int → int) %0))],
  .assert "m_1_eq_10" eb[(m #1) == #10]
  ]) |>.snd |> format

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[minit → _minit
(m : (arrow int int)) → (λ (if (%0 == #3) then #30 else ((λ (if (%0 == #2) then #20 else ((λ (if (%0 == #1) then #10 else (_minit
         %0)))
      %0)))
   %0)))]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: m_5_eq_50
Property: assert
Assumptions:
Proof Obligation:
((_minit #5) == #50)

Label: m_2_eq_20
Property: assert
Assumptions:
Proof Obligation:
#true

Label: m_1_eq_10
Property: assert
Assumptions:
Proof Obligation:
#true
-/
#guard_msgs in
#eval (evalOne
  ((Env.init (empty_factory := true)).pushScope [("minit", (none, eb[_minit]))])
  ∅
  [.init "m" t[int → int] eb[minit],
  .set "m" eb[λ (if (%0 == #1) then #10 else (m %0))],
  .set "m" eb[λ (if (%0 == #2) then #20 else (m %0))],
  .assert "m_5_eq_50" eb[(m #5) == #50],
  .assert "m_2_eq_20" eb[(m #2) == #20],
  .set "m" eb[λ (if (%0 == #3) then #30 else (m %0))],
  .assert "m_1_eq_10" eb[(m #1) == #10]
  ]) |>.snd |> format



private def prog1 : Statements :=
 [
 .init "x" t[int] eb[#0],
 .init "y" t[int] eb[#6],
 .block "label_0"

   [Statement.init "z" t[bool] eb[zinit],
    Statement.assume "z_false" eb[z == #false],

   .ite eb[z == #false]
     [Statement.set "x" eb[y]]
     -- The "trivial" assertion, though unreachable, is still verified away by the
     -- PE because the conclusion of the proof obligation evaluates to `true`.
     -- However, if the conclusion were anything else (including `false`) and
     -- the path conditions weren't empty, then this proof obligation would be
     -- sent on to the SMT solver.
     [Statement.assert "trivial" eb[#true]],

   Statement.assert "x_eq_y_label_0" eb[x == y],
   ],
 .assert "x_eq_y" eb[x == y]
 ]

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(x : int) → (if (zinit == #false) then #6 else #0)
(y : int) → #6
zinit → zinit]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:



Datatypes:

Path Conditions:
(z_false, (zinit == #false))
(<label_ite_cond_true: (z == #false)>, (if (zinit == #false) then (zinit == #false) else #true)) (<label_ite_cond_false: !(z == #false)>, (if (if (zinit == #false) then #false else #true) then (if (zinit == #false) then #false else #true) else #true))


Warnings:
[]
Deferred Proof Obligations:
Label: trivial
Property: assert
Assumptions:
(<label_ite_cond_false: !(z == #false)>, (if (zinit == #false) then #false else #true))
(z_false, (zinit == #false))
Proof Obligation:
#true

Label: x_eq_y_label_0
Property: assert
Assumptions:
(z_false, (zinit == #false))
(<label_ite_cond_true: (z == #false)>, (if (zinit == #false) then (zinit == #false) else #true)) (<label_ite_cond_false: !(z == #false)>, (if (if (zinit == #false) then #false else #true) then (if (zinit == #false) then #false else #true) else #true))
Proof Obligation:
((if (zinit == #false) then #6 else #0) == #6)

Label: x_eq_y
Property: assert
Assumptions:
(z_false, (zinit == #false))
(<label_ite_cond_true: (z == #false)>, (if (zinit == #false) then (zinit == #false) else #true)) (<label_ite_cond_false: !(z == #false)>, (if (if (zinit == #false) then #false else #true) then (if (zinit == #false) then #false else #true) else #true))
Proof Obligation:
((if (zinit == #false) then #6 else #0) == #6)
-/
#guard_msgs in
#eval (evalOne ∅ ∅ prog1) |>.snd |> format


private def prog2 : Statements := [
  .init "x" t[int] eb[#0],
  .set "x" eb[#1],
  .havoc "x",
  .assert "x_eq_1" eb[x == #1], -- error
  .havoc "x",
  .set "x" eb[#8]
]

/--
info: {
  init (x : int) := #0
  x := #1
  havoc x
  assert [x_eq_1] ($__x0 == #1)
  havoc x
  x := #8
}
-/
#guard_msgs in
#eval (evalOne ∅ ∅ prog2) |>.fst |> format

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(x : int) → #8]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 2
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_1
Property: assert
Assumptions:
Proof Obligation:
(($__x0 : int) == #1)
-/
#guard_msgs in
#eval (evalOne ∅ ∅ prog2) |>.snd |> format

/--
Test funcDecl: declare a helper function and use it
-/
def testFuncDecl : List Statement :=
  let doubleFunc : PureFunc Expression := {
    name := CoreIdent.unres "double",
    typeArgs := [],
    isConstr := false,
    inputs := [(CoreIdent.unres "x", .forAll [] .int)],
    output := .forAll [] .int,
    body := some eb[((~Int.Add x) x)],
    attr := #[],
    concreteEval := none,
    axioms := []
  }
  [
    .funcDecl doubleFunc,
    .init "y" t[int] eb[(~double #5)],
    .assert "y_eq_10" eb[y == #10]
  ]

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(y : int) → (~double #5)]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:
func double :  ((x : int)) → int :=
  ((~Int.Add x x))


Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: y_eq_10
Property: assert
Assumptions:
Proof Obligation:
((~double #5) == #10)
-/
#guard_msgs in
#eval (evalOne ∅ ∅ testFuncDecl) |>.snd |> format

/--
Test funcDecl with variable capture: function captures variable value at declaration time,
not affected by subsequent mutations
-/
def testFuncDeclSymbolic : List Statement :=
  let addNFunc : PureFunc Expression := {
    name := CoreIdent.unres "addN",
    typeArgs := [],
    isConstr := false,
    inputs := [(CoreIdent.unres "x", .forAll [] .int)],
    output := .forAll [] .int,
    body := some eb[((~Int.Add x) n)],  -- Captures 'n' at declaration time
    attr := #[],
    concreteEval := none,
    axioms := []
  }
  [
    .init "n" t[int] eb[#10],  -- Initialize n to 10
    .funcDecl addNFunc,  -- Function captures n = 10 at declaration time
    .set "n" eb[#20],  -- Mutate n to 20
    .init "result" t[int] eb[(~addN #5)],  -- Call function
    .assert "result_eq_15" eb[result == #15]  -- Result is 5 + 10 = 15 (uses captured value)
  ]

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(n : int) → #20
(result : int) → (~addN #5)]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:
func addN :  ((x : int)) → int :=
  ((~Int.Add x #10))


Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: result_eq_15
Property: assert
Assumptions:
Proof Obligation:
((~addN #5) == #15)
-/
#guard_msgs in
#eval (evalOne ∅ ∅ testFuncDeclSymbolic) |>.snd |> format

/--
Test polymorphic funcDecl: declare a polymorphic function `choose` that takes a boolean
and two values of type `a`, returning the first if true, second if false.
Then use it with multiple concrete type instantiations (int and bool).

The function has the `inline` attribute so its body gets expanded during evaluation,
allowing us to verify that the function definition is actually being used.
-/
def testPolymorphicFuncDecl : List Statement :=
  let chooseFunc : PureFunc Expression := {
    name := CoreIdent.unres "choose",
    typeArgs := ["a"],  -- Polymorphic type parameter
    isConstr := false,
    inputs := [
      (CoreIdent.unres "cond", .forAll [] .bool),
      (CoreIdent.unres "x", .forAll [] (.ftvar "a")),
      (CoreIdent.unres "y", .forAll [] (.ftvar "a"))
    ],
    output := .forAll [] (.ftvar "a"),
    body := some eb[(if cond then x else y)],
    attr := #["inline"],  -- Enable inlining so body is expanded during evaluation
    concreteEval := none,
    axioms := []
  }
  [
    .funcDecl chooseFunc,
    -- Use with int type (curried application)
    .init "intResult" t[int] eb[(((~choose #true) #1) #2)],
    .assert "intResult_eq_1" eb[intResult == #1],
    -- Use with bool type (curried application)
    .init "boolResult" t[bool] eb[(((~choose #false) #true) #false)],
    .assert "boolResult_eq_false" eb[boolResult == #false]
  ]

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(intResult : int) → #1
(boolResult : bool) → #false]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:
@[#[inline]]
func choose : ∀[a]. ((cond : bool) (x : a) (y : a)) → a :=
  ((if cond then x else y))


Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: intResult_eq_1
Property: assert
Assumptions:
Proof Obligation:
#true

Label: boolResult_eq_false
Property: assert
Assumptions:
Proof Obligation:
#true
-/
#guard_msgs in
#eval (evalOne ∅ ∅ testPolymorphicFuncDecl) |>.snd |> format

end Tests
---------------------------------------------------------------------
end Core
