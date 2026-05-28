/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.StatementEval
import Strata.Languages.Core.ProcedureEval

namespace Core

section InlineCallBodyTests

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative

/-! ## Setup: a callee that writes 42 to its output

  ```
  proc set_to_42(out r : int) {
    set r := 42;
  }
  ```
-/

private def calleeSetTo42 : Procedure :=
  { header :=
      { name := "set_to_42",
        typeArgs := [],
        inputs := [],
        outputs := [("r", mty[int])] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [.set "r" eb[#42] .empty] }

/-- Build an Env with `set_to_42` in the program and the given call policy. -/
private def mkEnv (policy : CallPolicy) : Env :=
  let prog : Program := { decls := [.proc calleeSetTo42 .empty] }
  { (∅ : Env) with
    program := prog,
    callPolicy := policy,
    fuel := 100 }

/-! ## Test 1: Under `.Body` policy, `assert x == 42` simplifies to `true`.

The caller:
```
var x : int := 0;
call set_to_42 (out x);
assert "x_eq_42" : x == 42;
```

Under `.Body` policy, `inlineCallBody` evaluates the callee body, discovers that
`r` (and hence `x`) is 42, and the assertion reduces to `42 == 42` = `true`.
The deferred proof obligation is `true`.
-/

private def callerStmts : Statements :=
  [ .init "x" t[int] (.det eb[#0]) .empty,
    Statement.call "set_to_42" [.outArg "x"] .empty,
    .assert "x_eq_42" eb[x == #42] .empty ]

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[x → 42]

Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_42
Property: assert
Assumptions:
Proof Obligation:
true
-/
#guard_msgs in
#eval (evalOne (mkEnv .Body) ∅ callerStmts) |> format

/-! ## Test 2: Under `.Contract` policy, `assert x == 42` is deferred as `fresh_x == 42`.

The contract-based evaluation havocs `x` to a fresh variable.  The deferred
obligation is `fresh_x == 42`, which is not trivially true (it depends on the
solver).
-/

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(x : int) → x@1]

Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:



Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_42
Property: assert
Assumptions:

Proof Obligation:
x@1 == 42
-/
#guard_msgs in
-- Under .Contract policy with no postconditions, x is havoc'd to a fresh var.
-- The assert x_eq_42 deferred obligation is x@1 == 42 (non-trivial, requires solver).
-- This contrasts with .Body policy where the obligation reduces to `true`.
#eval (evalOne (mkEnv .Contract) ∅ callerStmts) |> format

end InlineCallBodyTests

/-! ## CFG-body tests -/

section InlineCallBodyCFGTests

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative

/-! ### Setup: a CFG-bodied callee that writes 42 to its output.

  Equivalent structured body:
  ```
  proc cfg_set_to_42(out r : int) {
    set r := 42;
  }
  ```
  But expressed as a two-block CFG: `entry` sets `r`, then `goto done`; `done`
  finishes.
-/

private def calleeCFGSetTo42 : Procedure :=
  { header :=
      { name := "cfg_set_to_42",
        typeArgs := [],
        inputs := [],
        outputs := [("r", mty[int])] },
    spec := { preconditions := [], postconditions := [] },
    body := .cfg
      { entry := "entry",
        blocks := [
          ("entry", { cmds  := [CmdExt.cmd (Cmd.set "r" (.det eb[#42]) .empty)],
                      transfer := .goto "done" }),
          ("done",  { cmds  := [],
                      transfer := .finish })
        ] } }

private def mkCFGEnv (policy : CallPolicy) (fuel : Nat := 100) : Env :=
  let prog : Program := { decls := [.proc calleeCFGSetTo42 .empty] }
  { (∅ : Env) with
    program := prog,
    callPolicy := policy,
    fuel := fuel }

private def callerCFGStmts : Statements :=
  [ .init "x" t[int] (.det eb[#0]) .empty,
    Statement.call "cfg_set_to_42" [.outArg "x"] .empty,
    .assert "x_eq_42" eb[x == #42] .empty ]

/-! ## Test 3: CFG-body callee under `.Body` — assertion reduces to `true`.

Under `.Body` policy, `inlineCallBody` now walks the CFG, discovers that `r`
(and hence `x`) is 42, and the assertion reduces to `42 == 42` = `true`.
The deferred proof obligation is `true`.
-/

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[x → 42]

Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_42
Property: assert
Assumptions:
Proof Obligation:
true
-/
#guard_msgs in
#eval (evalOne (mkCFGEnv .Body) ∅ callerCFGStmts) |> format

/-! ## Test 4: CFG-body callee under `.Contract` — assertion deferred as `x@1 == 42`.

Under `.Contract` policy, x is havoc'd to a fresh variable; the obligation is non-trivial.
-/

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(x : int) → x@1]

Evaluation Config:
Eval Depth: 200
Factory Functions:



Datatypes:

Path Conditions:



Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_42
Property: assert
Assumptions:

Proof Obligation:
x@1 == 42
-/
#guard_msgs in
#eval (evalOne (mkCFGEnv .Contract) ∅ callerCFGStmts) |> format

/-! ### Setup: a looping CFG callee (back-edge) for fuel-exhaustion tests.

  ```
  proc looper(out r : int) {
  loop:
    set r := 1;
    goto loop;
  }
  ```

  The CFG has a back-edge `loop → loop`; without a fuel budget the symbolic
  evaluator would loop forever.  With low fuel it surfaces `OutOfFuel`.
-/

private def calleeLooper : Procedure :=
  { header :=
      { name := "looper",
        typeArgs := [],
        inputs := [],
        outputs := [("r", mty[int])] },
    spec := { preconditions := [], postconditions := [] },
    body := .cfg
      { entry := "loop",
        blocks := [
          ("loop", { cmds  := [CmdExt.cmd (Cmd.set "r" (.det eb[#1]) .empty)],
                     transfer := .goto "loop" })
        ] } }

private def mkLooperEnv (policy : CallPolicy) (fuel : Nat) : Env :=
  let prog : Program := { decls := [.proc calleeLooper .empty] }
  { (∅ : Env) with
    program := prog,
    callPolicy := policy,
    fuel := fuel }

private def callerLooperStmts : Statements :=
  [ .init "x" t[int] (.det eb[#0]) .empty,
    Statement.call "looper" [.outArg "x"] .empty,
    .assert "x_eq_1" eb[x == #1] .empty ]

/-! ## Test 5: CFG loop under `.Body` with low fuel → `OutOfFuel` error.

With fuel = 3 (1 for the call setup, then each block visit costs 1), the
CFG walker exhausts fuel after a few loop iterations and surfaces `OutOfFuel`.
-/

/--
info: has OutOfFuel error: true
-/
#guard_msgs in
#eval do
  let E := evalOne (mkLooperEnv .Body 3) ∅ callerLooperStmts
  let isOutOfFuel := match E.error with | some .OutOfFuel => true | _ => false
  IO.println s!"has OutOfFuel error: {isOutOfFuel}"

/-! ## Test 6: CFG loop under `.BodyOrContract` with low fuel → falls back to contract.

When the body path hits `OutOfFuel`, `.BodyOrContract` falls back to the
contract path, which havocs `x` to a fresh fvar.  The `assert x_eq_1`
obligation is then `x@1 == 1` (non-trivial), not `true`.
-/

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(x : int) → x@1]

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
#eval (evalOne (mkLooperEnv .BodyOrContract 3) ∅ callerLooperStmts) |> format

end InlineCallBodyCFGTests

end Core
