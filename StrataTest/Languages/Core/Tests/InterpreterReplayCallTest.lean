/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.InterpreterReplay
meta import Strata.Languages.Core.InterpreterEval

/-! # Behavioral tests of `Core.replayWithM` on a program with a `.call` to `Double(5, out y)`:
genuine, spurious, and cantValidate with the empty callee table; and of replay and `EvalM` on
a call whose callee body exits through an unmatched label -/

meta section

namespace InterpreterReplayCallTest

open Core Lambda Imperative

private def id (name : String) : CoreIdent := ⟨name, ()⟩
private def int (n : Int) : Expression.Expr := .intConst default n
private def md : MetaData Expression := #[]
private def yVar : Expression.Expr := .fvar default (id "y") (some .int)

/-- Callee `Double(n : int, out result : int) { result := n; }`. -/
private def doubleProc : Procedure := {
  header := { name := id "Double", typeArgs := [],
              inputs := [(id "n", (.int : Lambda.LMonoTy))],
              outputs := [(id "result", (.int : Lambda.LMonoTy))] }
  spec := { preconditions := [], postconditions := [] }
  body := .structured
    [ .cmd (.cmd (.set (id "result") (.det (.fvar default (id "n") (some .int))) md)) ] }

/-- Procedure environment resolving `Double`. -/
private def piEnv : String → Option Procedure :=
  fun n => if n == "Double" then some doubleProc else none

/-- `call Double(5, out y)`. -/
private def callStmt : Statement :=
  .cmd (CmdExt.call "Double" [.inArg (int 5), .outArg (id "y")] md)

/-- Target assert `y == rhs`. -/
private def assertTgt (rhs : Int) : Statement :=
  .cmd (.cmd (.assert "tgt" (.eq default yVar (int rhs)) md))

/-- The target assertion id matching `assertTgt rhs` (label and metadata). -/
private def tgtId (_rhs : Int) : Imperative.AssertId Expression :=
  { label := "tgt", md := md }

/-- Caller env: `y` is defined before the call. -/
private def callerEnv : Imperative.IEnv Expression :=
  .ofStore (fun n => if n == id "y" then some (int 0) else none) Core.Factory

private def cexFail : CexA Expression Command :=
  { cfg := .stmts [callStmt, assertTgt 6] callerEnv, oracle := [] }
private def cexPass : CexA Expression Command :=
  { cfg := .stmts [callStmt, assertTgt 5] callerEnv, oracle := [] }

-- The call writes the callee output (5) back into `y`, so `y == 6` fails: genuine.
#guard replayWithM cexFail (tgtId 6) 100 piEnv == .genuine

-- `y == 5` holds: spurious.
#guard replayWithM cexPass (tgtId 5) 100 piEnv == .spurious

-- The empty callee table refuses the call: cantValidate.
#guard replayWithM cexFail (tgtId 6) 100 == .cantValidate (.unsupportedCalleeNotFound "Double")

/-! ## A callee body that exits through an unmatched label -/

/-- `set result := v`. -/
private def setResult (v : Int) : Statement :=
  .cmd (.cmd (.set (id "result") (.det (int v)) md))

/-- Callee `E(out result : int) { result := 7; exit "nowhere"; result := 99; }`: no block of
    the body is labeled `nowhere`, so the body ends exiting. -/
private def exitProc : Procedure := {
  header := { name := id "E", typeArgs := [], inputs := [],
              outputs := [(id "result", (.int : Lambda.LMonoTy))] }
  spec := { preconditions := [], postconditions := [] }
  body := .structured [setResult 7, .exit "nowhere" md, setResult 99] }

/-- Procedure environment resolving `E`. -/
private def piExit : String → Option Procedure :=
  fun n => if n == "E" then some exitProc else none

/-- `call E(out y)`. -/
private def callExit : Statement := .cmd (CmdExt.call "E" [.outArg (id "y")] md)

private def cexExit : CexA Expression Command :=
  { cfg := .stmts [callExit, assertTgt 7] callerEnv, oracle := [] }

-- Replay stops at the call: the callee body did not end normally.
#guard replayWithM cexExit (tgtId 7) 100 piExit == .cantValidate (.programCallBodyExited "E")

-- `EvalM` stops at the call with the same reason.
#guard (match (runCoreEval piExit 100 cexExit.cfg).1 with
  | .error (.stuck r) => some r
  | _ => none) == some (.programCallBodyExited "E")

end InterpreterReplayCallTest

end -- meta section
