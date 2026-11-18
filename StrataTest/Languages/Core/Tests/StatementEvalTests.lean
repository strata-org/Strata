/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.StatementEval
meta import StrataTest.DL.Lambda.RenamingFixtures

meta section

namespace Core
---------------------------------------------------------------------

section Tests

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative (PureFunc)

/--
info: Error:
none
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
#eval (evalOne ∅ [.init "x" t[int] (.det eb[#0]) .empty,
                    .set "x" eb[#18] .empty,
                    .assert "x_eq_18" eb[x == #18] .empty]) |> format

/--
info: Error:
none
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
  [.init "x" t[int] (.det eb[#0]) .empty,
  .set "x" eb[y] .empty,
  .assert "x_eq_12" eb[x == #12] .empty]) |> format

/--
info: Error:
none
Expression Env:
State:
[(x : bool) → x@1 == true]

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
#eval evalOne ∅
       [
       .init "x" t[bool] (.det eb[x == #true]) .empty
       ] |> format

/--
info: Error:
none
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
Expression Env:
State:
[(x : int) → if zinit@1 == false then 6 else 0
(y : int) → 6
zinit → zinit@1]

Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:
(z_false, zinit@1 == false)
(<label_ite_cond_true: z == false>, if zinit@1 == false then zinit@1 == false else true)
(<label_ite_cond_false: !(z == false)>, if if zinit@1 == false then false else true then if zinit@1 == false then false else true else true)


Warnings:
[]
Deferred Proof Obligations:
Label: trivial
Property: assert
Assumptions:
(<label_ite_cond_false: !(z == false)>, if zinit@1 == false then false else true)
(z_false, zinit@1 == false)
Proof Obligation:
true

Label: x_eq_y_label_0
Property: assert
Assumptions:
(z_false, zinit@1 == false)
(<label_ite_cond_true: z == false>, if zinit@1 == false then zinit@1 == false else true)
(<label_ite_cond_false: !(z == false)>, if if zinit@1 == false then false else true then if zinit@1 == false then false else true else true)
Proof Obligation:
(if zinit@1 == false then 6 else 0) == 6

Label: x_eq_y
Property: assert
Assumptions:
(z_false, zinit@1 == false)
(<label_ite_cond_true: z == false>, if zinit@1 == false then zinit@1 == false else true)
(<label_ite_cond_false: !(z == false)>, if if zinit@1 == false then false else true then if zinit@1 == false then false else true else true)
Proof Obligation:
(if zinit@1 == false then 6 else 0) == 6
-/
#guard_msgs in
#eval (evalOne ∅ prog1) |> format


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
#eval (evalOne ∅ prog2) |> format


-- Nondet if is rejected by the evaluator: it must be eliminated (via the
-- nondetElim transform) before symbolic evaluation, so the env is left in an
-- error state.
/--
info: Error:
some [ERROR] nondeterministic `if *` reached symbolic evaluation; run the nondetElim transform to eliminate nondeterministic control first
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
#eval (evalOne ∅ [.init "x" t[int] (.det eb[#0]) .empty,
                    .ite .nondet
                      [Statement.set "x" eb[#1] .empty]
                      [Statement.set "x" eb[#2] .empty]
                      .empty,
                    .assert "x_pos" eb[(x == #1)] .empty]) |> format

/-! ### A call's contract does not depend on type variable names

`p<a, b>(x : a, y : b)` requires `opPair(x, y)`, with `opPair : a → b → bool`. Calling `p(u, v)`
with `u : b` and `v : a`, and the same call with the caller's `b` and `a` renamed to `d` and
`c`, gives the same precondition up to that renaming. -/

private def contractRenamed (tyU tyV : Lambda.LMonoTy) : Format :=
  let tvA : Lambda.LMonoTy := .ftvar "a"
  let tvB : Lambda.LMonoTy := .ftvar "b"
  let pre : Expression.Expr := Lambda.RenamingFixtures.opPairCall Core.coreLoc tvA tvB
  let proc : Procedure :=
    { header := { name := "p", typeArgs := ["a", "b"],
                  inputs := [("x", tvA), ("y", tvB)], outputs := [] },
      spec := { preconditions := [("pre", ⟨pre, .Default, #[]⟩)], postconditions := [] } }
  let E := { Env.init with program := { decls := [.proc proc .empty] } }
  let (_, E) := Command.inlineCallContract E [] "p"
    [.fvar Core.coreLoc "u" (some tyU), .fvar Core.coreLoc "v" (some tyV)] .empty
  Format.joinSep (E.deferred.toList.map fun ob =>
    (Lambda.LExpr.instToFormatLExpr CoreLParams.mono).format ob.obligation) Format.line

/-- info: ((~opPair : (arrow b (arrow a bool))) (u : b) (v : a)) -/
#guard_msgs in
#eval contractRenamed (.ftvar "b") (.ftvar "a")

/-- info: ((~opPair : (arrow d (arrow c bool))) (u : d) (v : c)) -/
#guard_msgs in
#eval contractRenamed (.ftvar "d") (.ftvar "c")

/-! `q<a, b, c>(x : a, y : b) returns (r : a)` requires `opQ(x, y, k)`, with
`opQ : a → b → c → bool` and `k : c`. In `w := q(u, v)`, `u` has no known type, `v : a` fixes the
callee's `b`, and `w : b` fixes its `a`. Renaming the caller's `b` and `a` to `d` and `c` renames
the precondition alike; no argument fixes the callee's `c`, which becomes `$__callty2`. -/

private def contractRenamedOut (tyV tyW : Lambda.LMonoTy) : Format :=
  let tvA : Lambda.LMonoTy := .ftvar "a"
  let tvB : Lambda.LMonoTy := .ftvar "b"
  let tvC : Lambda.LMonoTy := .ftvar "c"
  let pre : Expression.Expr :=
    .app Core.coreLoc (.app Core.coreLoc
                       (.app Core.coreLoc (.op Core.coreLoc "opQ"
                                           (some (.arrow tvA (.arrow tvB (.arrow tvC .bool)))))
      (.fvar Core.coreLoc "x" (some tvA))) (.fvar Core.coreLoc "y" (some tvB)))
          (.op Core.coreLoc "k" (some tvC))
  let proc : Procedure :=
    { header := { name := "q", typeArgs := ["a", "b", "c"],
                  inputs := [("x", tvA), ("y", tvB)], outputs := [("r", tvA)] },
      spec := { preconditions := [("pre", ⟨pre, .Default, #[]⟩)], postconditions := [] } }
  let E := { Env.init with program := { decls := [.proc proc .empty] } }
  let E := E.insertInContext ("w", some tyW) (.fvar Core.coreLoc "w" (some tyW))
  let (_, E) := Command.inlineCallContract E ["w"] "q"
    [.fvar Core.coreLoc "u" none, .fvar Core.coreLoc "v" (some tyV)] .empty
  Format.joinSep (E.deferred.toList.map fun ob =>
    (Lambda.LExpr.instToFormatLExpr CoreLParams.mono).format ob.obligation) Format.line

/--
info: ((~opQ : (arrow b (arrow a (arrow $__callty2 bool)))) u (v : a) (~k : $__callty2))
-/
#guard_msgs in
#eval contractRenamedOut (.ftvar "a") (.ftvar "b")

/--
info: ((~opQ : (arrow d (arrow c (arrow $__callty2 bool)))) u (v : c) (~k : $__callty2))
-/
#guard_msgs in
#eval contractRenamedOut (.ftvar "c") (.ftvar "d")

end Tests
---------------------------------------------------------------------
end Core

end
