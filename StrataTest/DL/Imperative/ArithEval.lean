/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/



import StrataTest.DL.Imperative.ArithExpr
import Strata.DL.Imperative.CmdEval
--import StrataTest.DL.Imperative.DDMDefinition

namespace Arith

abbrev Command := Imperative.Cmd Arith.PureExpr
abbrev Commands := Imperative.Cmds Arith.PureExpr

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
     deferred: {s.deferred}{Format.line}\
     pathConditions: {s.pathConditions}{Format.line}\
     env: {s.env}{Format.line}\
     genNum: {s.genNum}{Format.line}"

/--
Evaluator for arithmetic expressions `Expr`.
-/
def eval (s : State) (e : Expr) : Expr :=
  match e with
  | .add_expr e1 e2 =>
    match (eval s e1), (eval s e2) with
    | .numLit n1, .numLit n2 => .numLit (n1 + n2)
    | e1', e2' => .add_expr e1' e2'
  | .mul_expr e1 e2 =>
    match (eval s e1), (eval s e2) with
    | .numLit n1, .numLit n2 => .numLit (n1 * n2)
    | e1', e2' => .mul_expr e1' e2'
  | .eq_expr ty e1 e2 =>
    match (eval s e1), (eval s e2) with
    | .numLit n1, .numLit n2 =>
      -- Zero is false; any non-zero number is true, but we choose 1 as the
      -- canonical true here.
      .numLit (if n1 == n2 then 1 else 0)
    | e1', e2' => .eq_expr ty e1' e2'
  | .numLit n => .numLit n
  | .ty_expr _ e' => eval s e'
  | .fvar v => match s.env.find? v with | none => .fvar v | some (_, e) => e

def updateError (s : State) (e : EvalError PureExpr) : State :=
  { s with error := e }

def lookupError (s : State) : Option (EvalError PureExpr) :=
  s.error

def update (s : State) (v : Nat) (ty : Ty) (e : Expr) : State :=
  { s with env := s.env.insert v (ty, e) }

def lookup (s : State) (v : Nat) : Option Arith.PureExpr.TypedExpr :=
  match s.env.find? v with
  | some (ty, e) => some (e, ty)
  | none => none

/--
Add free variables to the environment, where the free variable is mapped to
itself (i.e., `v ↦ .Var v`).
-/
def preprocess (s : State) (e : Expr) : Expr × State :=
  let freeVars := e.freeVars.filter (fun v => not (s.env.contains v))
  let new_env := List.foldl (fun env v => Map.insert env v (.num,
      (ArithPrograms.Expr.fvar v))) s.env freeVars
  let s := { s with env := new_env }
  (e, s)

def genFreeVar (s : State) (_:Nat) (_:Ty) : Expr × State :=
  let newVar := s.genNum
  let s := { s with genNum := s.genNum + 1 }
  (ArithPrograms.Expr.fvar newVar, s)

def denoteBool (e : Expr) : Option Bool :=
  match e with
  | .numLit n =>
    -- Non-zero numbers denote true; zero is false.
    some (not (n == 0))
  | _ => none

def getPathConditions (s : State) : PathConditions PureExpr :=
  s.pathConditions

def addPathCondition (s : State) (p : PathCondition PureExpr) : State :=
  { s with pathConditions := s.pathConditions.addInNewest p }

def deferObligation (s : State) (ob : ProofObligation PureExpr) : State :=
  { s with deferred := s.deferred.push ob }

def ProofObligation.freeVars (ob : ProofObligation PureExpr) : List String :=
  let assum_typedvars :=
      ob.assumptions.flatMap (fun e => e.values.flatMap (fun i => i.freeVars))
  (assum_typedvars.map (fun v => "$__" ++ toString v)) ++
  (ob.obligation.freeVars.map (fun v => "$__" ++ toString v))

theorem lookupEval (s1 s2 : State) (h : ∀ x, lookup s1 x = lookup s2 x) :
  ∀ e, eval s1 e = eval s2 e := by
  intro e; induction e <;> simp_all [eval]
  case fvar v =>
    simp_all [lookup]
    have hv := @h v; clear h
    split <;> (split <;> simp_all)
  done

---------------------------------------------------------------------

instance : EvalContext PureExpr State where
  eval := Arith.Eval.eval
  updateError := Arith.Eval.updateError
  lookupError := Arith.Eval.lookupError
  update := Arith.Eval.update
  lookup := Arith.Eval.lookup
  preprocess := Arith.Eval.preprocess
  genFreeVar := Arith.Eval.genFreeVar
  denoteBool := Arith.Eval.denoteBool
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
  [.init 0 .num (.numLit 0),
   .set 0 (.add_expr (.fvar 0) (.numLit 100)),
   .assert "x_value_eq" (.eq_expr .num (.fvar 0) (.numLit 100))]

/--
info:
Obligation x_value_eq proved via evaluation!

---
info: Commands:
init (0 : Num) := 0
0 := 100
assert [x_value_eq] 1

State:
error: none
deferred: #[]
pathConditions: ⏎
env: (0, (Num, 100))
genNum: 0
-/
#guard_msgs in
#eval format $ Cmds.eval State.init testProgram1


private def testProgram2 : Cmds PureExpr :=
  [.init 0 .num (.fvar 1),
   .havoc 0,
   .assert "x_value_eq" (.eq_expr .num (.fvar 0) (.numLit 100))]

/--
info: Commands:
init (0 : Num) := 1
#[<var 0: 0>] havoc 0
assert [x_value_eq] 0 = 100

State:
error: none
deferred: #[Label: x_value_eq
 Assumptions: ⏎
 Obligation: 0 = 100
 Metadata: ⏎
 ]
pathConditions: ⏎
env: (1, (Num, 1)) (0, (Num, 0))
genNum: 1
-/
#guard_msgs in
#eval format $ Cmds.eval State.init testProgram2

---------------------------------------------------------------------

end Eval
end Arith
