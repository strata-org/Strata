/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Boogie.OldExpressions
import Strata.Languages.Boogie.Expressions
import Strata.Languages.Boogie.Env
import Strata.DL.Imperative.EvalContext
import Strata.DL.Imperative.CmdEval

namespace Boogie
open Lambda Imperative
open Std (ToFormat Format format)

---------------------------------------------------------------------
namespace CmdEval

def eval (E : Env) (e : Expression.Expr) : Expression.Expr :=
  LExpr.eval E.exprEnv.config.fuel E.exprEnv e

def updateError (E : Env) (e : EvalError Expression) : Env :=
  { E with error := e }

def lookupError (E : Env) : Option (EvalError Expression) :=
  E.error

def update (E : Env) (v : Expression.Ident) (ty : Expression.Ty) (e : Expression.Expr) : Env :=
  -- We typically do PE after type inference is in place, which is why we
  -- expect `ty` to be a monotype. However, if it is not, we assume -- for
  -- now -- that we are working with untyped expressions.
  -- (TODO): What are the pitfalls of this decision?
  if h : ty.isMonoType then
    E.insertInContext (v, ty.toMonoType h) e
  else
    E.insertInContext (v, none) e

def lookup (E : Env) (v : Expression.Ident) : Option Expression.TypedExpr :=
  match E.exprEnv.state.find? v with
  | some (ty, e) =>
    match ty with
    | some mty => some (e, .forAll [] mty)
    | none => some (e, .forAll ["α"] (.ftvar "α"))
  | none => none

def preprocess (E : Env) (c : Cmd Expression) (e : Expression.Expr) : Expression.Expr × Env :=
  let substMap := oldVarSubst E.substMap E
  let e' := OldExpressions.substsOldExpr substMap e
  match c with
  | .init _ _ _ _ =>
    -- The type checker only allows free variables to appear in `init`
    -- statements, so we only need to compute them when we see an `init`
    -- command.
    -- See `CmdType.lean` for details.
    let freeVars := e.freeVars
    let E' := E.insertFreeVarsInOldestScope freeVars
    (e', E')
  | _ => (e', E)

def genFreeVar (E : Env) (x : Expression.Ident) (ty : Expression.Ty) : Expression.Expr × Env :=
  if h : ty.isMonoType then
    E.genFVar (x, ty.toMonoType h)
  else
    E.genFVar (x, none)

def denoteBool (e : Expression.Expr) : Option Bool :=
  Lambda.LExpr.denoteBool e

def addWarning (E : Env) (w : EvalWarning Expression) : Env :=
  { E with warnings := w :: E.warnings }

def getPathConditions (E : Env) : PathConditions Expression :=
  E.pathConditions

def addPathCondition (E : Env) (p : PathCondition Expression) : Env :=
  match p with
  | [] => E
  | (label, e) :: prest =>
    let new_path_conditions := E.pathConditions.insert label e
    let E := { E with pathConditions := new_path_conditions }
    addPathCondition E prest

def deferObligation (E : Env) (ob : ProofObligation Expression) : Env :=
  { E with deferred := E.deferred.push ob }

/-
theorem lookupEval (E1 E2 : Env) (h : ∀x, lookup E1 x = lookup E2 x) :
  ∀ e, eval E1 e = eval E2 e := by
  intro e; induction e <;> simp_all [eval]
  case const c maybe_mty  =>
    have hc := @h c; clear h
    simp [lookup] at hc
    try repeat (split at hc); all_goals try simp_all
    repeat sorry
  repeat sorry
-/


---------------------------------------------------------------------

instance : EvalContext Expression Env where
  eval              := CmdEval.eval
  updateError       := CmdEval.updateError
  lookupError       := CmdEval.lookupError
  update            := CmdEval.update
  lookup            := CmdEval.lookup
  preprocess        := CmdEval.preprocess
  genFreeVar        := CmdEval.genFreeVar
  denoteBool        := CmdEval.denoteBool
  addWarning        := CmdEval.addWarning
  getPathConditions := CmdEval.getPathConditions
  addPathCondition  := CmdEval.addPathCondition
  deferObligation   := CmdEval.deferObligation
  -- lookupEval        := Boogie.lookupEval

instance : ToFormat (Cmds Expression × Env) where
  format arg :=
    let fcs := Imperative.formatCmds Expression arg.fst
    let fσ := format arg.snd
    format f!"Commands:{Format.line}{fcs}{Format.line}\
              State:{Format.line}{fσ}{Format.line}"

---------------------------------------------------------------------

open LExpr.SyntaxMono LTy.Syntax Boogie.Syntax
private def testProgram1 : Cmds Expression :=
  [.init "x" t[int] eb[#0],
   .set "x" eb[#10],
   .assert "x_value_eq" eb[x == #10]]

/--
info: Commands:
init (x : int) := #0
x := #10
assert [x_value_eq] #true

State:
Error:
none
Subst Map:

Expression Env:
State:
[(x : int) → #10]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:



Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: x_value_eq
Assumptions:
Proof Obligation:
#true
-/
#guard_msgs in
#eval format $ Imperative.Cmds.eval Env.init testProgram1

private def testProgram2 : Cmds Expression :=
  [.init "x" t[int] eb[(y : int)],
   .assert "x_eq_12" eb[x == #12]]

/--
info: Commands:
init (x : int) := (y : int)
assert [x_eq_12] ((y : int) == #12)

State:
Error:
none
Subst Map:

Expression Env:
State:
[(y : int) → (y : int)
(x : int) → (y : int)]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:



Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_12
Assumptions:
Proof Obligation:
((y : int) == #12)
-/
#guard_msgs in
#eval format $ Imperative.Cmds.eval Env.init testProgram2

end CmdEval
---------------------------------------------------------------------
end Boogie
