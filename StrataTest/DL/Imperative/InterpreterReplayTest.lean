/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Imperative.InterpreterReplay

/-! # Behavioral tests of `runReplay` over `baseStepCmd` on the toy language `Mini`: verdicts,
oracle round-trip, and nondeterministic `set` -/

meta section

namespace InterpreterReplayTest

open Imperative

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
  valueOfTy := fun _ value ty => match value, ty with
    | .bool _, .bool | .int _, .int => True
    | _, _ => False
  tt := .bool true
  ff := .bool false
  tt_is_not_ff := by
    intro h
    cases h
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

private def emptyStore : RStore Mini := fun _ => none

/-- Fire on any assert whose condition evaluates to the false literal. -/
private def haltOnFalseAssert : REvent Mini Unit → Bool
  | .assert arg => Mini.eval arg.factory arg.store arg.expr == some (HasBool.ff (P := Mini))
  | _ => false

private instance : InterpLang Mini := .withMap valueOps (fun _ => Mini.eval) (fun _ e => some e)
  fun _ value =>
  match value with
  | .bool _ => some .bool
  | .int _ => some .int
  | _ => none

private def env : IEnv Mini := .ofStore emptyStore ()

private def rcfg : ReplayCfg Mini := {}

private def run (cfg : IConfig Mini (Cmd Mini)) (oracle : List Expr := []) (fuel : Nat := 100) :
    CEValidationVerdict StopReason × List Expr :=
  runReplay (runInterp (baseStepCmd (m := ReplayM Mini)) fuel cfg) rcfg
    haltOnFalseAssert oracle

private def failStmt : Stmt Mini (Cmd Mini) := .cmd (.assert "failure" (.bool false) #[])
private def passStmt : Stmt Mini (Cmd Mini) := .cmd (.assert "pass" (.bool true) #[])
private def branchStmt : Stmt Mini (Cmd Mini) := .ite .nondet [failStmt] [passStmt] #[]
private def loopStmt : Stmt Mini (Cmd Mini) := .loop .nondet none [] [failStmt] #[]
private def initThenFail (rhs : ExprOrNondet Mini) : IConfig Mini (Cmd Mini) :=
  .stmts [.cmd (.init "x" .int rhs #[]), failStmt] env

-- Each verdict is pinned together with the oracle prefix the run consumed.

-- A false assert is genuine, a true assert is spurious.
#guard run (.stmt failStmt env) == (.genuine, [])
#guard run (.stmt passStmt env) == (.spurious, [])
-- Out of fuel with a non-terminal config is a cantValidate.
#guard run (.stmt failStmt env) [] 0 == (.cantValidate .replayFuelExhausted, [])

-- Deterministic and nondeterministic `init`.
#guard run (initThenFail (.det (.int 7))) == (.genuine, [])
#guard run (initThenFail .nondet) [.int 9] == (.genuine, [.int 9])

-- Nondeterministic loop choices.
#guard run (.stmt loopStmt env) [.bool true] == (.genuine, [.bool true])
#guard run (.stmt loopStmt env) [.bool false] == (.spurious, [.bool false])

-- Failure modes: ill-typed choice.
#guard run (initThenFail .nondet) [.bool true] == (.cantValidate .illTypedValue, [])

-- Nondeterministic branch choices, and an exhausted oracle.
#guard run (.stmt branchStmt env) [.bool true] == (.genuine, [.bool true])
#guard run (.stmt branchStmt env) [.bool false] == (.spurious, [.bool false])
#guard run (.stmt branchStmt env) == (.cantValidate .oracleExhausted, [])

-- Oracle round-trip: the reported consumed oracle replays back to genuine.
#guard run (.stmt branchStmt env) (run (.stmt branchStmt env) [.bool true]).2
  == (.genuine, [.bool true])

-- `.set .nondet` draws a value of the current value's type from the oracle; a value of another
-- type is rejected.
private def xStore : RStore Mini := fun name => if name == "x" then some (.int 0) else none
private def xEnv : IEnv Mini := .ofStore xStore ()
private def setThenFail : IConfig Mini (Cmd Mini) :=
  .stmts [.cmd (.set "x" .nondet #[]), failStmt] xEnv

#guard run setThenFail [.int 12] == (.genuine, [.int 12])
#guard run setThenFail [.bool true] == (.cantValidate .illTypedValue, [])

end InterpreterReplayTest

/-! ## A Boolean-typed choice that is neither `tt` nor `ff`

The toy language `Tri` has a third value `unknown` that `choose` accepts at the Boolean type.
A nondeterministic guard resolved to it stops the replay with `expectedBooleanChoice`, even when
both branches fail. -/

namespace InterpreterReplayTest.Tri

open Imperative

inductive Expr where
  | tt
  | ff
  | unknown
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Tri : PureExpr := {
  Ident := String
  EqIdent := inferInstance
  Expr := Expr
  Ty := Unit
  ExprMetadata := Unit
  TyEnv := Unit
  TyContext := Unit
  Factory := Unit
  Val := Expr
  eval := fun _ _ expr => some expr }

instance : HasBool Tri where
  value := fun _ _ => True
  valueOfTy := fun _ _ _ => True
  tt := .tt
  ff := .ff
  tt_is_not_ff := by
    intro h
    cases h
  boolTy := ()
  ttVal _ := .tt
  ffVal _ := .ff
  ttVal_ne_ffVal _ h := by cases h
  boolIsValOfTy := fun _ => ⟨trivial, trivial⟩

private instance : InterpLang Tri :=
  .withMap
    { isValue := fun _ _ => true, hasType := fun _ _ _ => true, sameType := fun _ _ _ => true }
    (fun _ => Tri.eval) (fun _ e => some e) fun _ _ => some ()

private def env : IEnv Tri := .ofStore (fun _ => none) ()

/-- Fire on any assert of the `ff` literal. -/
private def haltOnFalseAssert : REvent Tri Unit → Bool
  | .assert arg => arg.expr == .ff
  | _ => false

private def run (stmt : Stmt Tri (Cmd Tri)) (oracle : List Expr) :
    CEValidationVerdict StopReason × List Expr :=
  runReplay (runInterp (baseStepCmd (m := ReplayM Tri)) 100 (.stmt stmt env)) {}
    haltOnFalseAssert oracle

private def failStmt : Stmt Tri (Cmd Tri) := .cmd (.assert "failure" .ff #[])
private def branchStmt : Stmt Tri (Cmd Tri) := .ite .nondet [failStmt] [failStmt] #[]
private def loopStmt : Stmt Tri (Cmd Tri) := .loop .nondet none [] [failStmt] #[]

-- `tt` and `ff` select a branch; `unknown` is consumed and stops the run.
#guard run branchStmt [.tt] == (.genuine, [.tt])
#guard run branchStmt [.ff] == (.genuine, [.ff])
#guard run branchStmt [.unknown] == (.cantValidate .expectedBooleanChoice, [.unknown])
#guard run loopStmt [.tt] == (.genuine, [.tt])
#guard run loopStmt [.ff] == (.spurious, [.ff])
#guard run loopStmt [.unknown] == (.cantValidate .expectedBooleanChoice, [.unknown])

end InterpreterReplayTest.Tri

end -- meta section
