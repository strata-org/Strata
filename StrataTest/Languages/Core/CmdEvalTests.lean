/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.CmdEval

/-! ## Tests for CmdEval -/

namespace Core
open Lambda Imperative
open Std (ToFormat Format format)
open LExpr.SyntaxMono LTy.Syntax Core.Syntax

private def testProgram1 : Cmds Expression :=
  [.init "x" t[int] (some eb[#0]) .empty,
   .set "x" eb[#10] .empty,
   .assert "x_value_eq" eb[x == #10] .empty]

/--
info: Commands:
init (x : int) := #0
x := #10
assert [x_value_eq] #true

State:
Error:
none
Subst Map:

Expression Env:
State:
[(x : int) → #10]

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
Label: x_value_eq
Property: assert
Assumptions:
Proof Obligation:
#true
-/
#guard_msgs in
#eval format $ Imperative.Cmds.eval (Env.init (empty_factory := true)) testProgram1

private def testProgram2 : Cmds Expression :=
  [.init "x" t[int] (some eb[(y : int)]) .empty,
   .assert "x_eq_12" eb[x == #12] .empty]

/--
info: Commands:
init (x : int) := (y : int)
assert [x_eq_12] ((y : int) == #12)

State:
Error:
none
Subst Map:

Expression Env:
State:
[(y : int) → (y : int)
(x : int) → (y : int)]

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
((y : int) == #12)
-/
#guard_msgs in
#eval format $ Imperative.Cmds.eval (Env.init (empty_factory := true)) testProgram2

end Core
