/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.InterpreterCFG
meta import Strata.Languages.Core.InterpreterEval

/-! # `runCoreInterpCFG` tests

A concrete executed run of a multi-block CFG under the faithful-legacy `EvalM`
instance that fetches a block, runs a command, follows a conditional transfer,
and reaches a terminal config; and an executed run of a CFG whose block contains a
`.call`, confirming the driver dispatches the call through the procedure table. -/

meta section

namespace InterpreterCFGTest

open Core Lambda Imperative

private def id (name : String) : CoreIdent := ⟨name, ()⟩
private def int (n : Int) : Expression.Expr := .intConst default n
private def md : MetaData Expression := #[]
private def xVar : Expression.Expr := .fvar default (id "x") (some .int)

/-- A `CmdExt`-wrapped base command. -/
private def setX (v : Int) : Command := .cmd (.set (id "x") (.det (int v)) md)
private def coverX (label : String) : Command := .cmd (.cover label (.eq default xVar (int 2)) md)

/-- Start store with `x` predefined to `1`. -/
private def store0 : RStore Expression :=
  fun n => if n == id "x" then some (int 1) else none

private def π : String → Option Procedure := fun _ => none

/-! ## A CFG block containing a `.call`

The call-aware command type `Command = CmdExt Expression` lets a `.call` sit in a CFG
block, and the driver dispatches it through the procedure table `π`.  `π` resolves no
procedure, so the run halts at the call with `unsupportedCalleeNotFound`. -/
private def callCfg : CFG String (DetBlock String Command Expression) :=
  { entry := "b0",
    blocks := [("b0", ⟨[CmdExt.call "callee" [] md], .finish md⟩)] }

/-- The start environment: store `store0` at `Core.Factory`. -/
private def env0 : IEnv Expression := { store := .ofStore store0, factory := Core.Factory }

#guard match (((runCoreInterpCFG (m := EvalM) π 100
    (.atBlock callCfg "b0" env0)).run (EvalOpts.legacy 100)).run).run {} with
  | (.error (.stuck (.unsupportedCalleeNotFound "callee")), _) => true
  | _ => false

/-! ## A concrete executed run

The run of `cfg` takes the `true` branch of the conditional transfer, emits the cover
event of `b1`, and halts at `.terminal` with `x = 2`. -/
private def cfg : CFG String (DetBlock String Command Expression) :=
  { entry := "b0",
    blocks :=
      [("b0", ⟨[setX 2], .condGoto (.eq default xVar (int 2)) "b1" "b2" md⟩),
       ("b1", ⟨[coverX "reached"], .finish md⟩),
       ("b2", ⟨[], .finish md⟩)] }

/-- Final store of a faithful-legacy CFG run that ends in a `.terminal` config; `none` for
    every other outcome, including an assert halt. -/
private def runCFGEvalStore (fuel : Nat)
    (c : ICFGConfig String Command Expression) : Option (RStore Expression) :=
  match (((runCoreInterpCFG (m := EvalM) π fuel c).run
            (EvalOpts.legacy fuel)).run).run {} with
  | (.ok (.terminal ρ), _) => some ρ.store.get
  | _ => none

-- The run reaches the terminal with `x = 2`.
#guard (runCFGEvalStore 100 (.atBlock cfg "b0" env0)).bind (fun s => s (id "x"))
  == some (int 2)

/-- Labels of the `cover` events a faithful-legacy CFG run emits, in emission order. -/
private def runCFGEvalCovers (fuel : Nat) (c : ICFGConfig String Command Expression) :
    List String :=
  ((((runCoreInterpCFG (m := EvalM) π fuel c).run
      (EvalOpts.legacy fuel)).run).run {}).2.traceRev.reverse.filterMap fun
    | .cover a => some a.label
    | _ => none

-- The conditional transfer takes the `true` branch: `b1`'s cover is the only cover emitted.
#guard runCFGEvalCovers 100 (.atBlock cfg "b0" env0) == ["reached"]

end InterpreterCFGTest
