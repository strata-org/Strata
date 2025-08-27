/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.DL.Imperative.ArithExpr
import StrataTest.DL.Imperative.ArithEval
import StrataTest.DL.Imperative.ArithType

---------------------------------------------------------------------
namespace Arith
open Std (ToFormat Format format)

def typeCheckAndPartialEval (cmds : Commands) : Except Format (Commands × Eval.State) := do
  let (cmds, _T) ← Imperative.Cmds.typeCheck TEnv.init cmds
  let (cmds, S) := Imperative.Cmds.eval Eval.State.init cmds
  return (cmds, S)

private def testProgram1 : Commands :=
  [.init "x" .Num (.Var "y" (.some .Num)),
   .havoc "x",
   .assert "x_value_eq" (.Eq (.Var "x" .none) (.Var "y" none))]

/--
info: ok: Commands:
init (x : Num) := (y : Num)
#[<var x: ($__x0 : Num)>] havoc x
assert [x_value_eq] ($__x0 : Num) = (y : Num)

State:
error: none
warnings: []
deferred: #[Label: x_value_eq
 Assumptions: ⏎
 Obligation: ($__x0 : Num) = (y : Num)
 Metadata: ⏎
 ]
pathConditions: ⏎
env: (y, (Num, (y : Num))) (x, (Num, ($__x0 : Num)))
genNum: 1
-/
#guard_msgs in
#eval do let (cmds, S) ← typeCheckAndPartialEval testProgram1
         return format (cmds, S)


private def testProgram2 : Commands :=
  [.init "x" .Num (.Num 0),
   .set "x" (.Plus (.Var "x" .none) (.Num 100)),
   .assert "x_value_eq" (.Eq (.Var "x" .none) (.Num 100))]

/--
info: ok: Commands:
init (x : Num) := 0
x := 100
assert [x_value_eq] true

State:
error: none
warnings: []
deferred: #[Label: x_value_eq
 Assumptions: ⏎
 Obligation: true
 Metadata: ⏎
 ]
pathConditions: ⏎
env: (x, (Num, 100))
genNum: 0
-/
#guard_msgs in
#eval do let (cmds, S) ← typeCheckAndPartialEval testProgram2
         return format (cmds, S)

end Arith
---------------------------------------------------------------------
