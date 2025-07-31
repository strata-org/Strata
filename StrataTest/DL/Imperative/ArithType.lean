/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.CmdType
import StrataTest.DL.Imperative.ArithExpr

namespace Arith

/-! ## Instantiate `Imperative`'s Type Checker

We instantiate Imperative's `TypeContext` typeclass with `ArithPrograms`'
specific implementations to obtain a type checker.
-/

namespace TypeCheck
open Std (ToFormat Format format)
open Imperative

---------------------------------------------------------------------

def isBoolType (ty : Ty) : Bool :=
  match ty with | .Bool => true | _ => false

def preprocess (T : TEnv) (ty : Ty) : Except Format (Ty × TEnv) :=
  .ok (ty, T)

def postprocess (T : TEnv) (ty : Ty) : Except Format (Ty × TEnv) :=
  .ok (ty, T)

def update (T : TEnv) (x : String) (ty : Ty) : TEnv :=
  T.insert x ty

def lookup (T : TEnv) (x : String) : Option Ty :=
  T.find? x

/-- Type inference for `ArithPrograms`' commands. -/
def inferType (T : TEnv) (c : Cmd PureExpr) (e : Expr) : Except Format (Expr × Ty × TEnv) := do
  match e with
  | .Num _ => .ok (e, .Num, T)
  | .Bool _ => .ok (e, .Bool, T)
  | .Var x xty =>
    -- We allow _annotated_ free variables to appear in the `init`
    -- statements.
    let T ← match c with
      | .init _ _ init_e _ =>
        let init_e_fvs := Expr.freeVars init_e
        if init_e_fvs.any (fun (_, ty) => ty.isNone) then
          .error f!"Cannot infer the types of free variables in the initialization expression!\n\
                    {e}"
        else
          let init_e_fvs := init_e_fvs.map (fun (x, ty) => (x, ty.get!))
          .ok (List.foldl (fun T (x, ty) => Map.insert T x ty) T init_e_fvs)
      | _ => .ok T
    match T.find? x with
    | some ty =>
      match xty with
      | none => .ok (e, ty, T)
      | some xty =>
        if xty == ty then
          .ok (e, ty, T)
        else
          .error f!"Variable {x} annotated with {xty} but has type {ty} in the context!"
    | none => .error f!"Variable {x} not found in type context!"
  | .Plus e1 e2 | .Mul e1 e2 =>
    let (_, e1t, T) ← inferType T c e1
    let (_, e2t, T) ← inferType T c e2
    if e1t == .Num && e2t == .Num then
      .ok (e, .Num, T)
    else
      .error f!"Type checking failed for {e}"
  | .Eq e1 e2 =>
    let (_, e1t, T) ← inferType T c e1
    let (_, e2t, T) ← inferType T c e2
    if e1t == .Num && e2t == .Num then
      .ok (e, .Bool, T)
    else
      .error f!"Type checking failed for {e}"

/-- Unify `ArithPrograms`' types. -/
def unifyTypes (T : TEnv) (constraints : List (Ty × Ty)) : Except Format TEnv :=
  match constraints with
  | [] => .ok T
  | (t1, t2) :: crest =>
    if t1 == t2 then
      unifyTypes T crest
    else
      .error f!"Types {t1} and {t2} cannot be unified!"

/--
Instantiation of `TypeContext` for `ArithPrograms`.
-/
instance : TypeContext PureExpr TEnv where
  isBoolType := Arith.TypeCheck.isBoolType
  freeVars := (fun e => (Arith.Expr.freeVars e).map (fun (v, _) => v))
  preprocess := Arith.TypeCheck.preprocess
  postprocess := Arith.TypeCheck.postprocess
  update := Arith.TypeCheck.update
  lookup := Arith.TypeCheck.lookup
  inferType := Arith.TypeCheck.inferType
  unifyTypes := Arith.TypeCheck.unifyTypes

instance : ToFormat (Cmds PureExpr × TEnv) where
  format arg :=
    let fcs := Imperative.formatCmds PureExpr arg.fst
    let ft := format arg.snd
    format f!"Commands:{Format.line}{fcs}{Format.line}\
              TEnv:{Format.line}{ft}{Format.line}"

---------------------------------------------------------------------

private def testProgram1 : Cmds Arith.PureExpr :=
  [.init "x" .Num (.Num 0),
   .set "x" (.Plus (.Var "x" .none) (.Num 100)),
   .assert "x_value_eq" (.Eq (.Var "x" .none) (.Num 100))]

/--
info: ok: Commands:
init (x : Num) := 0
x := x + 100
assert [x_value_eq] x = 100

TEnv:
(x, Num)
-/
#guard_msgs in
#eval do let (cs, τ) ← Cmds.typeCheck TEnv.init testProgram1
          return format (cs, τ)

private def testProgram2 : Cmds Arith.PureExpr :=
  [.init "x" .Bool (.Num 0)]

/-- info: error: Types .Bool and Num cannot be unified! -/
#guard_msgs in
#eval do let (cs, τ) ← Cmds.typeCheck TEnv.init testProgram2
          return format (cs, τ)

private def testProgram3 : Cmds Arith.PureExpr :=
  [.init "x" .Bool (.Var "x" .none)]

/--
info: error: Type Checking [init (x : .Bool) := x]: Variable x cannot appear in its own initialization expression!
-/
#guard_msgs in
#eval do let (cs, τ) ← Cmds.typeCheck TEnv.init testProgram3
          return format (cs, τ)

private def testProgram4 : Cmds Arith.PureExpr :=
  [.init "x" .Num (.Num 5),
   .set "x" (.Var "x" .none)]

/--
info: ok: Commands:
init (x : Num) := 5
x := x

TEnv:
(x, Num)
-/
#guard_msgs in
#eval do let (cs, τ) ← Cmds.typeCheck TEnv.init testProgram4
          return format (cs, τ)


private def testProgram5 : Cmds Arith.PureExpr :=
  [.init "x" .Num (.Num 5),
   .init "x" .Bool (.Eq (.Num 1) (.Num 2))]

/--
info: error: Type Checking [init (x : .Bool) := 1 = 2]: Variable x of type Num already in context.
-/
#guard_msgs in
#eval do let (cs, τ) ← Cmds.typeCheck TEnv.init testProgram5
          return format (cs, τ)

private def testProgram6 : Cmds Arith.PureExpr :=
  [.init "x" .Num (.Var "y" .none)]

/--
info: error: Cannot infer the types of free variables in the initialization expression!
y
-/
#guard_msgs in
#eval do let (cs, τ) ← Cmds.typeCheck TEnv.init testProgram6
          return format (cs, τ)

private def testProgram7 : Cmds Arith.PureExpr :=
  [.init "x" .Num (.Plus (.Var "y" (some .Num)) (.Var "z" (some .Num)))]

/--
info: ok: Commands:
init (x : Num) := (y : Num) + (z : Num)

TEnv:
(y, Num) (z, Num) (x, Num)
-/
#guard_msgs in
#eval do let (cs, τ) ← Cmds.typeCheck TEnv.init testProgram7
          return format (cs, τ)

private def testProgram8 : Cmds Arith.PureExpr :=
  [.init "x" .Num (.Num 1),
   .set "x" (.Var "y" (some .Num))]

/-- info: error: Variable y not found in type context! -/
#guard_msgs in
#eval do let (cs, τ) ← Cmds.typeCheck TEnv.init testProgram8
          return format (cs, τ)

---------------------------------------------------------------------

end TypeCheck
end Arith
