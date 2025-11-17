/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.StatementEval

namespace Boogie
---------------------------------------------------------------------

section Tests

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Boogie.Syntax

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



Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_18
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



Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_12
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
(m : (arrow int int)) → (λ (if (%0 == #3) then #30 else ((λ (if (%0 == #2) then #20 else ((λ (if (%0 == #1) then #10 else ((_minit : (arrow int int)) %0))) %0))) %0)))
(m0 : int) → ((_minit : (arrow int int)) #0)]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:



Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: m_5_eq_50
Assumptions:
Proof Obligation:
(((_minit : (arrow int int)) #5) == #50)

Label: m_2_eq_20
Assumptions:
Proof Obligation:
#true

Label: m_1_eq_10
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
(m : (arrow int int)) → (λ (if (%0 == #3) then #30 else ((λ (if (%0 == #2) then #20 else ((λ (if (%0 == #1) then #10 else (_minit %0))) %0))) %0)))]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:



Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: m_5_eq_50
Assumptions:
Proof Obligation:
((_minit #5) == #50)

Label: m_2_eq_20
Assumptions:
Proof Obligation:
#true

Label: m_1_eq_10
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
 .block "label_0" { ss :=

   [Statement.init "z" t[bool] eb[zinit],
    Statement.assume "z_false" eb[z == #false],

   .ite eb[z == #false]
     { ss := [Statement.set "x" eb[y]] }
     -- The "trivial" assertion, though unreachable, is still verified away by the
     -- PE because the conclusion of the proof obligation evaluates to `true`.
     -- However, if the conclusion were anything else (including `false`) and
     -- the path conditions weren't empty, then this proof obligation would be
     -- sent on to the SMT solver.
     { ss := [Statement.assert "trivial" eb[#true]]},

   Statement.assert "x_eq_y_label_0" eb[x == y],
   ]},
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



Path Conditions:
(z_false, (zinit == #false))
(<label_ite_cond_true: (z == #false)>, (if (zinit == #false) then (zinit == #false) else #true)) (<label_ite_cond_false: !(z == #false)>, (if (if (zinit == #false) then #false else #true) then (if (zinit == #false) then #false else #true) else #true))


Warnings:
[]
Deferred Proof Obligations:
Label: trivial
Assumptions:
(<label_ite_cond_false: !(z == #false)>, (if (zinit == #false) then #false else #true))
(z_false, (zinit == #false))
Proof Obligation:
#true

Label: x_eq_y_label_0
Assumptions:
(z_false, (zinit == #false))
(<label_ite_cond_true: (z == #false)>, (if (zinit == #false) then (zinit == #false) else #true)) (<label_ite_cond_false: !(z == #false)>, (if (if (zinit == #false) then #false else #true) then (if (zinit == #false) then #false else #true) else #true))
Proof Obligation:
((if (zinit == #false) then #6 else #0) == #6)

Label: x_eq_y
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
info: init (x : int) := #0
x := #1
#[<var x: ($__x0 : int)>] havoc x
assert [x_eq_1] ($__x0 == #1)
#[<var x: ($__x1 : int)>] havoc x
x := #8
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



Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_1
Assumptions:
Proof Obligation:
(($__x0 : int) == #1)
-/
#guard_msgs in
#eval (evalOne ∅ ∅ prog2) |>.snd |> format

end Tests
---------------------------------------------------------------------
end Boogie
