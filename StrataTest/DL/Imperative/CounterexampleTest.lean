/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Imperative.Counterexample.Run
meta import Strata.DL.Imperative.Counterexample.BackLink
meta import Strata.DL.Imperative.Interpreter
meta import Strata.DL.Imperative.InterpreterReplay

meta section

namespace CounterexampleTest

open Imperative

/-! A unit test of the generic engine replay validator (`Imperative.runReplay`
over the `ReplayM`/`runInterp` engine) on a toy expression language `Mini`.

The replay engine decides whether a putative counterexample is *genuine* by
replaying its start configuration against the imperative semantics, keyed to a
target event (`haltOn`): a verdict is `genuine` iff some emitted event fires
`haltOn` (`runReplay_genuine_iff`), `cantValidate r` if the run stops with
`StopReason r` before reaching the target, else `spurious`.

Note on choice reasons: the engine's `choose` validates a drawn value with
`ReplayValueOps.isValue`/`hasType` and reports a single `StopReason.illTypedValue`
on failure — it does not distinguish "expected a Boolean" vs "expected a value". So a
non-Boolean choice at a Boolean nondet and a non-value choice at a value nondet both surface
here as `illTypedValue`. -/

inductive Expr where
  | bool (value : Bool)
  | int (value : Int)
  | var (name : String)
  | stuck
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Ty where
  | bool
  | int
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Mini : PureExpr := {
  Ident := String
  EqIdent := inferInstance
  Expr := Expr
  Ty := Ty
  ExprMetadata := Unit
  TyEnv := Unit
  TyContext := Unit
  Factory := Unit
  Val := Expr
  eval := fun _ store expr =>
    match expr with
    | .var name => store name
    | .stuck => none
    | value => some value }

instance : HasBool Mini where
  value := fun _ _ => True
  valueOfTy := fun _ _ _ => True
  tt := .bool true
  ff := .bool false
  tt_is_not_ff := by decide
  boolTy := .bool
  ttVal _ := .bool true
  ffVal _ := .bool false
  ttVal_ne_ffVal _ h := by cases h
  boolIsValOfTy := fun _ => ⟨trivial, trivial⟩

private def valueOps : ReplayValueOps Mini Unit where
  isValue _ value := match value with | .bool _ | .int _ => true | _ => false
  hasType _ value ty := match value, ty with
    | .bool _, .bool | .int _, .int => true
    | _, _ => false
  sameType _ left right := match left, right with
    | .bool _, .bool _ | .int _, .int _ => true
    | _, _ => false

instance : InterpLang Mini :=
  .withMap valueOps (fun _ factory store expr => Mini.eval factory store expr) (fun _ e => some e)
    fun _ value =>
    match value with
    | .bool _ => some .bool
    | .int _ => some .int
    | _ => none

private def emptyStore : RStore Mini := fun _ => none
private def env : IEnv Mini := .ofStore emptyStore ()

/-- The target event: the failing assertion `failure : false`.  Replay is genuine
    exactly when this assert is reached (its event appears in the trace). -/
private def haltOn : IEvent Mini → Bool
  | .assert arg => arg.label == "failure" && arg.expr == Expr.bool false
  | _ => false

/-- Replay `cfg` through the engine runner against the `failure` target. -/
private def run (cfg : IConfig Mini (Cmd Mini)) (oracle : List Expr := [])
    (fuel : Nat := 100) : CEValidationVerdict StopReason :=
  (runReplay (CmdT := Cmd Mini) (runInterp baseStepCmd fuel cfg) {} haltOn oracle).1

private def isGenuine : CEValidationVerdict StopReason → Bool
  | .genuine => true
  | _ => false

private def isSpurious : CEValidationVerdict StopReason → Bool
  | .spurious => true
  | _ => false

private def reason? : CEValidationVerdict StopReason → Option StopReason
  | .cantValidate reason => some reason
  | _ => none

private def failStmt : Stmt Mini (Cmd Mini) :=
  .cmd (.assert "failure" (.bool false) #[])

private def passStmt : Stmt Mini (Cmd Mini) :=
  .cmd (.assert "pass" (.bool true) #[])

-- Deterministic assertions and exact step bounds.
#guard isGenuine (run (.stmt failStmt env) [] 1)
#guard reason? (run (.stmt failStmt env) [] 0) == some .replayFuelExhausted
#guard isSpurious (run (.stmt passStmt env) [] 1)

-- Nondeterministic branch choices select distinct behavior.
private def branchStmt : Stmt Mini (Cmd Mini) :=
  .ite .nondet [failStmt] [passStmt] #[]

#guard isGenuine (run (.stmt branchStmt env) [.bool true])
#guard isSpurious (run (.stmt branchStmt env) [.bool false])
#guard reason? (run (.stmt branchStmt env)) == some .oracleExhausted
#guard reason? (run (.stmt branchStmt env) [.int 0]) == some .illTypedValue

-- Nondeterministic loops consume one Boolean per visit (enter, then exit).
private def loopStmt : Stmt Mini (Cmd Mini) :=
  .loop .nondet none [] [failStmt] #[]

#guard isGenuine (run (.stmt loopStmt env) [.bool true])
#guard isSpurious (run (.stmt loopStmt env) [.bool false])

-- Deterministic init executes; nondeterministic init/set consume concrete values.
private def initThenFail (rhs : ExprOrNondet Mini) : IConfig Mini (Cmd Mini) :=
  .stmts [.cmd (.init "x" .int rhs #[]), failStmt] env

#guard isGenuine (run (initThenFail (.det (.int 7))))
#guard isGenuine (run (initThenFail .nondet) [.int 9])
#guard reason? (run (initThenFail .nondet) [.bool true]) == some .illTypedValue
#guard reason? (run (initThenFail .nondet) [.var "q"]) == some .illTypedValue

private def xStore : RStore Mini := fun name =>
  if name == "x" then some (.int 0) else none
private def xEnv : IEnv Mini := .ofStore xStore ()
private def setThenFail : IConfig Mini (Cmd Mini) :=
  .stmts [.cmd (.set "x" .nondet #[]), failStmt] xEnv

#guard isGenuine (run setThenFail [.int 12])
#guard reason? (run setThenFail [.bool true]) == some .illTypedValue

end CounterexampleTest

end -- meta section
