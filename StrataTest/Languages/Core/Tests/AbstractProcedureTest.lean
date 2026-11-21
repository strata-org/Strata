/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.InterpreterReplay
import StrataDDM.Integration.Lean.HashCommands

/-! # Abstract procedures (`Body.abstract`)

A procedure declared without a body is abstract: a call to it asserts its non-free
preconditions, havocs its outputs and assumes its postconditions, and its contract is not checked
against a body. A procedure written with the body `{ }` is a real body that does nothing.

* The translator gives a procedure without a body the body `.abstract`, and one with the body
  `{ }` the body `.structured []`; the printer keeps the two apart.
* The verifier emits no obligation for the postcondition of an abstract procedure, and a call to
  it assumes the postcondition.
* Replay of a call to an abstract callee draws the havocked output from the oracle and records
  the postcondition as an assumption. -/

meta section
open StrataDDM (Program)

namespace Strata.AbstractProcedureTest

def abstractPgm : Program :=
#strata
program Core;
procedure Seven(out result : int)
spec {
  ensures result == 7;
};
procedure Noop(out result : int)
spec {
  ensures false;
}
{
};
procedure Caller(out y : int)
spec {
  ensures y == 7;
}
{
  y := 0;
  call Seven(out y);
};
#end

/-- The Core program of `abstractPgm`. -/
private def corePgm : _root_.Core.Program :=
  (TransM.run Inhabited.default (translateProgram abstractPgm)).fst

/-- The body of procedure `name` of `corePgm`. -/
private def bodyOf (name : String) : Option _root_.Core.Procedure.Body :=
  (_root_.Core.Program.Procedure.find? corePgm ⟨name, ()⟩).map (·.body)

-- No body: `.abstract`.
#guard bodyOf "Seven" == some .abstract

-- The body `{ }`: a real body that does nothing.
#guard bodyOf "Noop" == some (.structured [] false)

/--
info: program Core;

procedure Seven (out result : int)
spec {
  ensures [Seven_ensures_0]: result == 7;
  } ;
procedure Noop (out result : int)
spec {
  ensures [Noop_ensures_0]: false;
  } {
  
};
procedure Caller (out y : int)
spec {
  ensures [Caller_ensures_0]: y == 7;
  } {
  y := 0;
  call Seven(out y);
};
-/
#guard_msgs in
#eval IO.println (Std.format corePgm)

-- The verifier checks no obligation for `Seven`'s postcondition. `Noop`'s postcondition `false`
-- is checked against its empty body, and fails. `Caller`'s postcondition follows from the
-- assumed postcondition of `Seven`.
/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: Noop_ensures_0
Property: assert
Obligation:
false

Label: Caller_ensures_0
Property: assert
Assumptions:
callElimPost_Seven_ensures_0_1: y@2 == 7
Obligation:
y@2 == 7



Obligation Noop_ensures_0: failed!

Result obtained during evaluation.
---
info:
Obligation: Noop_ensures_0
Property: assert
Result: ❌ fail

Obligation: Caller_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify abstractPgm

end Strata.AbstractProcedureTest

/-! ## Replay of a call to an abstract callee -/

namespace AbstractProcedureReplayTest

open Core Lambda Imperative

private def id (name : String) : CoreIdent := ⟨name, ()⟩
private def int (n : Int) : Expression.Expr := .intConst default n
private def md : MetaData Expression := #[]
private def yVar : Expression.Expr := .fvar default (id "y") (some .int)

/-- The postcondition `result == 7` of `Seven`. -/
private def sevenPost : Procedure.Check :=
  { expr := .eq default (.fvar default (id "result") (some .int)) (int 7), md := md }

/-- The abstract `Seven(out result : int)` with postcondition `result == 7`. -/
private def sevenProc : Procedure := {
  header := { name := id "Seven", typeArgs := [], inputs := [],
              outputs := [(id "result", (.int : Lambda.LMonoTy))] }
  spec := { preconditions := [], postconditions := [("post", sevenPost)] }
  body := .abstract }

private def piEnv : String → Option Procedure :=
  fun n => if n == "Seven" then some sevenProc else none

private def callStmt : Statement := .cmd (CmdExt.call "Seven" none [.outArg (id "y")] md)

private def assertTgt (rhs : Int) : Statement :=
  .cmd (.cmd (.assert "tgt" (.eq default yVar (int rhs)) md))

private def tgtId : Imperative.AssertId Expression := { label := "tgt", md := md }

private def callerEnv : Imperative.IEnv Expression :=
  .ofStore (fun n => if n == id "y" then some (int 0) else none) Core.Factory

private def cex (rhs : Int) (oracle : List Expression.Expr) : CexA Expression Command :=
  { cfg := .stmts [callStmt, assertTgt rhs] callerEnv, oracle := oracle }

-- The havocked output is read off the oracle: with `7`, `y == 7` holds.
#guard replayWithM (cex 7 [int 7]) tgtId 100 piEnv == .spurious

-- With `7`, `y == 0` fails: the call writes the havocked value back, not the caller's `0`.
#guard replayWithM (cex 0 [int 7]) tgtId 100 piEnv == .genuine

-- With no value for the havoc, replay stops at the call.
#guard replayWithM (cex 7 []) tgtId 100 piEnv == .cantValidate .oracleExhausted

end AbstractProcedureReplayTest
