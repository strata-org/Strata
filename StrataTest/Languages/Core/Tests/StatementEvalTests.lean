/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.StatementEval

meta section

namespace Core
---------------------------------------------------------------------

section Tests

open Std (ToFormat Format format)
open Statement Core.Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative (PureFunc)

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(x : int) → 18]

Evaluation Config:
Eval Depth: 200
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
true
-/
#guard_msgs in
#eval (evalOne ∅ ∅ [.init "x" t[int] (.det eb[#0]) .empty,
                    .set "x" eb[#18] .empty,
                    .assert "x_eq_18" eb[x == #18] .empty]) |> format

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
_yinit == 12
-/
#guard_msgs in
#eval (evalOne
  ((Env.init (empty_factory := true)).pushScope [("y", (mty[int], eb[_yinit]))])
  ∅
  [.init "x" t[int] (.det eb[#0]) .empty,
  .set "x" eb[y] .empty,
  .assert "x_eq_12" eb[x == #12] .empty]) |> format

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(x : bool) → x == true]

Evaluation Config:
Eval Depth: 200
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
       .init "x" t[bool] (.det eb[x == #true]) .empty
       ] |> format

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(minit : (arrow int int)) → _minit
(m : (arrow int int)) → fun __q0 : ($__unknown_type) => (if __q0 == 3 then 30 else (fun __q1 : ($__unknown_type) => (if __q1 == 2 then 20 else (fun __q2 : ($__unknown_type) => (if __q2 == 1 then 10 else _minit(__q2)))(__q1)))(__q0))
(m0 : int) → _minit(0)]

Evaluation Config:
Eval Depth: 200
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
_minit(5) == 50

Label: m_2_eq_20
Property: assert
Assumptions:
Proof Obligation:
true

Label: m_1_eq_10
Property: assert
Assumptions:
Proof Obligation:
true
-/
#guard_msgs in
#eval (evalOne
  ((Env.init (empty_factory := true)).pushScope
    [("minit", (mty[int → int], eb[(_minit : int → int)]))])
  ∅
  [.init "m" t[int → int] (.det eb[minit]) .empty,
  .init "m0" t[int] (.det eb[(m #0)]) .empty,
  .set "m" eb[λ (if (%0 == #1) then #10 else ((m : int → int) %0))] .empty,
  .set "m" eb[λ (if (%0 == #2) then #20 else ((m : int → int) %0))] .empty,
  .assert "m_5_eq_50" eb[(m #5) == #50] .empty,
  .assert "m_2_eq_20" eb[(m #2) == #20] .empty,
  .set "m" eb[λ (if (%0 == #3) then #30 else ((m : int → int) %0))] .empty,
  .assert "m_1_eq_10" eb[(m #1) == #10] .empty
  ]) |> format

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[minit → _minit
(m : (arrow int int)) → fun __q0 : ($__unknown_type) => (if __q0 == 3 then 30 else (fun __q1 : ($__unknown_type) => (if __q1 == 2 then 20 else (fun __q2 : ($__unknown_type) => (if __q2 == 1 then 10 else _minit(__q2)))(__q1)))(__q0))]

Evaluation Config:
Eval Depth: 200
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
_minit(5) == 50

Label: m_2_eq_20
Property: assert
Assumptions:
Proof Obligation:
true

Label: m_1_eq_10
Property: assert
Assumptions:
Proof Obligation:
true
-/
#guard_msgs in
#eval (evalOne
  ((Env.init (empty_factory := true)).pushScope [("minit", (none, eb[_minit]))])
  ∅
  [.init "m" t[int → int] (.det eb[minit]) .empty,
  .set "m" eb[λ (if (%0 == #1) then #10 else (m %0))] .empty,
  .set "m" eb[λ (if (%0 == #2) then #20 else (m %0))] .empty,
  .assert "m_5_eq_50" eb[(m #5) == #50] .empty,
  .assert "m_2_eq_20" eb[(m #2) == #20] .empty,
  .set "m" eb[λ (if (%0 == #3) then #30 else (m %0))] .empty,
  .assert "m_1_eq_10" eb[(m #1) == #10] .empty
  ]) |> format



private def prog1 : Statements :=
 [
 .init "x" t[int] (.det eb[#0]) .empty,
 .init "y" t[int] (.det eb[#6]) .empty,
 .block "label_0"

   [Statement.init "z" t[bool] (.det eb[zinit]) .empty,
    Statement.assume "z_false" eb[z == #false] .empty,

   .ite (.det eb[z == #false])
     [Statement.set "x" eb[y] .empty]
     -- The "trivial" assertion, though unreachable, is still verified away by the
     -- PE because the conclusion of the proof obligation evaluates to `true`.
     -- However, if the conclusion were anything else (including `false`) and
     -- the path conditions weren't empty, then this proof obligation would be
     -- sent on to the SMT solver.
     [Statement.assert "trivial" eb[#true] .empty]
     .empty,

   Statement.assert "x_eq_y_label_0" eb[x == y] .empty,
   ]
   .empty,
 .assert "x_eq_y" eb[x == y] .empty
 ]

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(x : int) → if zinit == false then 6 else 0
(y : int) → 6
zinit → zinit]

Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:
(z_false, zinit == false)
(<label_ite_cond_true: z == false>, if zinit == false then zinit == false else true)
(<label_ite_cond_false: !(z == false)>, if if zinit == false then false else true then if zinit == false then false else true else true)


Warnings:
[]
Deferred Proof Obligations:
Label: trivial
Property: assert
Assumptions:
(<label_ite_cond_false: !(z == false)>, if zinit == false then false else true)
(z_false, zinit == false)
Proof Obligation:
true

Label: x_eq_y_label_0
Property: assert
Assumptions:
(z_false, zinit == false)
(<label_ite_cond_true: z == false>, if zinit == false then zinit == false else true)
(<label_ite_cond_false: !(z == false)>, if if zinit == false then false else true then if zinit == false then false else true else true)
Proof Obligation:
(if zinit == false then 6 else 0) == 6

Label: x_eq_y
Property: assert
Assumptions:
(z_false, zinit == false)
(<label_ite_cond_true: z == false>, if zinit == false then zinit == false else true)
(<label_ite_cond_false: !(z == false)>, if if zinit == false then false else true then if zinit == false then false else true else true)
Proof Obligation:
(if zinit == false then 6 else 0) == 6
-/
#guard_msgs in
#eval (evalOne ∅ ∅ prog1) |> format


private def prog2 : Statements := [
  .init "x" t[int] (.det eb[#0]) .empty,
  .set "x" eb[#1] .empty,
  .havoc "x" .empty,
  .assert "x_eq_1" eb[x == #1] .empty, -- error
  .havoc "x" .empty,
  .set "x" eb[#8] .empty
]

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(x : int) → 8]

Evaluation Config:
Eval Depth: 200
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
x@1 == 1
-/
#guard_msgs in
#eval (evalOne ∅ ∅ prog2) |> format


-- Nondet if is rejected by the evaluator: it must be eliminated (via the
-- nondetElim transform) before symbolic evaluation, so the env is left in an
-- error state.
/--
info: Error:
some [ERROR] nondeterministic `if *` reached symbolic evaluation; run the nondetElim transform to eliminate nondeterministic control first
Subst Map:

Expression Env:
State:
[(x : int) → 0]

Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
-/
#guard_msgs in
#eval (evalOne ∅ ∅ [.init "x" t[int] (.det eb[#0]) .empty,
                    .ite .nondet
                      [Statement.set "x" eb[#1] .empty]
                      [Statement.set "x" eb[#2] .empty]
                      .empty,
                    .assert "x_pos" eb[(x == #1)] .empty]) |> format

end Tests
---------------------------------------------------------------------
end Core

end
