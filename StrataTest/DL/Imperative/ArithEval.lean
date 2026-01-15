/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import StrataTest.DL.Imperative.ArithExpr
import Strata.DL.Imperative.CmdEval

namespace Arith

/-! ## Instantiate `Imperative`'s Partial Evaluator

We instantiate Imperative's `EvalContext` typeclass with `ArithPrograms`'
specific implementations to obtain a partial evaluator that generates
verification conditions on the fly (i.e., a Strongest-Postconditions
Verification Condition Generator).
-/

---------------------------------------------------------------------
namespace Eval
open Std (ToFormat Format format)
open Imperative

/--
Evaluation state for arithmetic expressions `Expr`. This contains components
necessary to specialize `Cmd.eval`.
-/
structure State where
  /-- A counter to generate fresh variable names. -/
  genNum : Nat := 0
  /-- An environment mapping variables to expressions. -/
  env : Env := []
  /-- Error, if any, encountered during evaluation. -/
  error : Option (EvalError PureExpr) := .none
  /-- Any warnings encountered during evaluation. -/
  warnings : List (EvalWarning PureExpr) := []
  /-- Accrued path conditions. -/
  pathConditions : PathConditions PureExpr := []
  /-- Deferred proof obligations obtained during evaluation, intended to be
      discharged by some other means (e.g., denotation into Lean or encoding
      into SMTLIB). -/
  deferred : ProofObligations PureExpr := #[]

def State.init : State := {}

instance : ToFormat State where
  format s :=
  f!"error: {s.error}{Format.line}\
     warnings: {s.warnings}{Format.line}\
     deferred: {s.deferred}{Format.line}\
     pathConditions: {PathConditions.format' s.pathConditions}{Format.line}\
     env: {s.env}{Format.line}\
     genNum: {s.genNum}{Format.line}"

/--
Evaluator for arithmetic expressions `Expr`.
-/
def eval (s : State) (e : Expr) : Expr :=
  match e with
  | .Plus e1 e2 =>
    match (eval s e1), (eval s e2) with
    | .Num n1, .Num n2 => .Num (n1 + n2)
    | e1', e2' => .Plus e1' e2'
  | .Mul e1 e2 =>
    match (eval s e1), (eval s e2) with
    | .Num n1, .Num n2 => .Num (n1 * n2)
    | e1', e2' => .Mul e1' e2'
  | .Eq e1 e2 =>
    match (eval s e1), (eval s e2) with
    | .Num n1, .Num n2 =>
      (if n1 == n2 then .Bool true else .Bool false)
    | e1', e2' => .Eq e1' e2'
  | .Num n => .Num n
  | .Bool b => .Bool b
  | .Var v ty => match s.env.find? v with | none => .Var v ty | some (_, e) => e

def updateError (s : State) (e : EvalError PureExpr) : State :=
  { s with error := e }

def lookupError (s : State) : Option (EvalError PureExpr) :=
  s.error

def update (s : State) (v : String) (ty : Ty) (e : Expr) : State :=
  { s with env := s.env.insert v (ty, e) }

def lookup (s : State) (v : String) : Option Arith.PureExpr.TypedExpr :=
  match s.env.find? v with
  | some (ty, e) => some (e, ty)
  | none => none

/--
Add free variables to the environment, where the free variable is mapped to
itself (i.e., `v ↦ .Var v ty`).
-/
def preprocess (s : State) (_c : Command) (e : Expr) : Expr × State :=
  let freeVars := e.freeVars.filter (fun (v, _ty) => not (s.env.contains v))
  let new_env := List.foldl (fun env (v, ty) => Map.insert env v (.Num, (Expr.Var v ty))) s.env freeVars
  let s := { s with env := new_env }
  (e, s)

def genFreeVar (s : State) (x : String) (ty : Ty) : Expr × State :=
  let newVar := "$__" ++ x ++ toString s.genNum
  let s := { s with genNum := s.genNum + 1 }
  (.Var newVar ty, s)

def denoteBool (e : Expr) : Option Bool :=
  match e with
  | .Bool b => some b
  | .Var _ _ | .Plus _ _ | .Mul _ _ | .Eq _ _ | .Num _ => none

def addWarning (s : State) (w : EvalWarning PureExpr) : State :=
  { s with warnings := w :: s.warnings }

def getPathConditions (s : State) : PathConditions PureExpr :=
  s.pathConditions

def addPathCondition (s : State) (p : PathCondition PureExpr) : State :=
  { s with pathConditions := s.pathConditions.addInNewest p }

def deferObligation (s : State) (ob : ProofObligation PureExpr) : State :=
  { s with deferred := s.deferred.push ob }

def ProofObligation.freeVars (ob : ProofObligation PureExpr) : List String :=
  let assum_typedvars :=
      ob.assumptions.flatMap (fun e => e.values.flatMap (fun i => i.freeVars))
  (assum_typedvars.map (fun (v, _) => v)) ++
  (ob.obligation.freeVars.map (fun (v, _) => v))

theorem lookupEval (s1 s2 : State) (h : ∀ x, lookup s1 x = lookup s2 x) :
  ∀ e, eval s1 e = eval s2 e := by
  intro e; induction e <;> simp_all [eval]
  case Var v _ =>
    simp_all [lookup]
    have hv := @h v; clear h
    split <;> (split <;> simp_all)
  done

---------------------------------------------------------------------

/--
Instantiation of `EvalContext` for `ArithPrograms`.
-/
instance : EvalContext PureExpr State where
  eval := Arith.Eval.eval
  updateError := Arith.Eval.updateError
  lookupError := Arith.Eval.lookupError
  update := Arith.Eval.update
  lookup := Arith.Eval.lookup
  preprocess := Arith.Eval.preprocess
  genFreeVar := Arith.Eval.genFreeVar
  denoteBool := Arith.Eval.denoteBool
  addWarning := Arith.Eval.addWarning
  getPathConditions := Arith.Eval.getPathConditions
  addPathCondition := Arith.Eval.addPathCondition
  deferObligation := Arith.Eval.deferObligation
  -- lookupEval := Arith.lookupEval

instance : ToFormat (Cmds PureExpr × State) where
  format arg :=
    let fcs := Imperative.formatCmds PureExpr arg.fst
    let fσ := format arg.snd
    format f!"Commands:{Format.line}{fcs}{Format.line}\
              State:{Format.line}{fσ}{Format.line}"

---------------------------------------------------------------------

/- Tests -/

private def testProgram1 : Cmds PureExpr :=
  [.init "x" .Num (.Num 0),
   .set "x" (.Plus (.Var "x" .none) (.Num 100)),
   .assert "x_value_eq" (.Eq (.Var "x" .none) (.Num 100))]

/--
info: Commands:
init (x : Num) := 0
x := 100
assert [x_value_eq] true

State:
error: none
warnings: []
deferred: #[Label: x_value_eq
 Property : assert
 Assumptions: ⏎
 Obligation: true
 Metadata: ⏎
 ]
pathConditions: ⏎
env: (x, (Num, 100))
genNum: 0
-/
#guard_msgs in
#eval format $ Cmds.eval State.init testProgram1


private def testProgram2 : Cmds PureExpr :=
  [.init "x" .Num (.Var "y" .none),
   .havoc "x",
   .assert "x_value_eq" (.Eq (.Var "x" .none) (.Num 100))]

/--
info: Commands:
init (x : Num) := y
havoc x
assert [x_value_eq] ($__x0 : Num) = 100

State:
error: none
warnings: []
deferred: #[Label: x_value_eq
 Property : assert
 Assumptions: ⏎
 Obligation: ($__x0 : Num) = 100
 Metadata: ⏎
 ]
pathConditions: ⏎
env: (y, (Num, y)) (x, (Num, ($__x0 : Num)))
genNum: 1
-/
#guard_msgs in
#eval format $ Cmds.eval State.init testProgram2

---------------------------------------------------------------------

end Eval
end Arith
