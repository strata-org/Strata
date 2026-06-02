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

/-! ## Multi-path body-eval tests

These tests cover the case where a callee's body produces multiple
result envs (a CFG with a symbolic `condGoto` that doesn't reconverge).
Before the multi-path command-eval landing, this path produced a `.Misc`
error and `--call-policy bodyOrContract` fell back to contract. After
the change, the per-path envs flow upward through `evalAuxGo`'s
active-path machinery and each path's assertions are evaluated
independently.
-/

section InlineCallBodyMultipathTests

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative

/-! ### Setup: CFG callee with a symbolic branch that does not reconverge.

  ```
  proc maybe_one(in b : bool, out r : int) {
    entry:  goto tt, ff   when b
    tt:     set r := 1; finish
    ff:     set r := 2; finish
  }
  ```
-/

private def calleeMaybeOne : Procedure :=
  { header :=
      { name := "maybe_one",
        typeArgs := [],
        inputs := [("b", mty[bool])],
        outputs := [("r", mty[int])] },
    spec := { preconditions := [], postconditions := [] },
    body := .cfg
      { entry := "entry",
        blocks := [
          ("entry", { cmds := [],
                      transfer := .condGoto eb[b] "tt" "ff" .empty }),
          ("tt",    { cmds := [CmdExt.cmd (Cmd.set "r" (.det eb[#1]) .empty)],
                      transfer := .finish }),
          ("ff",    { cmds := [CmdExt.cmd (Cmd.set "r" (.det eb[#2]) .empty)],
                      transfer := .finish })
        ] } }

private def mkMaybeEnv (policy : CallPolicy) : Env :=
  let prog : Program := { decls := [.proc calleeMaybeOne .empty] }
  { (∅ : Env) with
    program := prog,
    callPolicy := policy,
    fuel := 100 }

private def callerMaybeStmts : Statements :=
  [ .init "guard" t[bool] .nondet .empty,
    .init "x" t[int] (.det eb[#0]) .empty,
    Statement.call "maybe_one" [.inArg eb[guard], .outArg "x"] .empty,
    .assert "x_eq_1" eb[x == #1] .empty ]

/-! ## Test 7: `.Body` policy fans out — one provable path, one failing path.

The CFG forks on `b == guard` (symbolic). Path 1 (`b == true`) sets `r := 1`,
caller's `x_eq_1` simplifies to `true`. Path 2 (`b == false`) sets `r := 2`,
caller's `x_eq_1` evaluates to `false` and surfaces `AssertFail` on that path.
The resulting env list has length 2 with the expected per-path verdicts.
-/

/--
info: 2 envs
env 0: error=none, x→1
env 1: error=AssertFail x_eq_1, x→2
-/
#guard_msgs in
#eval do
  let envs := (Statement.eval (mkMaybeEnv .Body) ∅ callerMaybeStmts).fst
  IO.println s!"{envs.length} envs"
  let mut i := 0
  for e in envs do
    let errStr := match e.error with
      | none => "none"
      | some (.AssertFail label _) => s!"AssertFail {label}"
      | some _ => "other"
    let xStr := match e.exprEnv.state.findD ⟨"x", ()⟩ (none, .fvar () ⟨"x", ()⟩ none) with
      | (_, e) => toString (format e)
    IO.println s!"env {i}: error={errStr}, x→{xStr}"
    i := i + 1

/-! ## Test 8: `.Contract` policy is unchanged — single env, fresh-fvar lhs.

Under `.Contract`, no body-eval occurs; the existing single-env path produces
exactly the legacy behaviour (havoc'd lhs, deferred `x@1 == 1`).
-/

/--
info: 1 envs
env 0: error=none
deferred obligation: x@1 == 1
-/
#guard_msgs in
#eval do
  let envs := (Statement.eval (mkMaybeEnv .Contract) ∅ callerMaybeStmts).fst
  IO.println s!"{envs.length} envs"
  let mut i := 0
  for e in envs do
    let errStr := match e.error with
      | none => "none"
      | some _ => "other"
    IO.println s!"env {i}: error={errStr}"
    for o in e.deferred do
      IO.println s!"deferred obligation: {format o.obligation}"
    i := i + 1

/-! ## Test 9: `.BodyOrContract` exposes body-eval verdicts (no fallback).

Multi-path success is no longer a body-eval failure: the contract fallback only
triggers on `OutOfFuel` or `.Misc`. So `.BodyOrContract` produces the same
2-env fan-out as `.Body`.
-/

/--
info: 2 envs
-/
#guard_msgs in
#eval do
  let envs := (Statement.eval (mkMaybeEnv .BodyOrContract) ∅ callerMaybeStmts).fst
  IO.println s!"{envs.length} envs"

end InlineCallBodyMultipathTests

end Core
