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

import Strata.DL.Imperative.CmdType
import StrataTest.DL.Imperative.ArithExpr

namespace Arith
namespace TypeCheck
open Std (ToFormat Format format)
open Imperative

---------------------------------------------------------------------

def isBoolType (ty : Ty) : Bool :=
  match ty with | .bool => true | _ => false

def preprocess (T : TEnv) (ty : Ty) : Except Format (Ty × TEnv) :=
  .ok (ty, T)

def postprocess (T : TEnv) (ty : Ty) : Except Format (Ty × TEnv) :=
  .ok (ty, T)

def update (T : TEnv) (x : Nat) (ty : Ty) : TEnv :=
  T.insert x ty

def lookup (T : TEnv) (x : Nat) : Option Ty :=
  T.find? x

def inferType (T : TEnv) (c : Cmd PureExpr) (e : Expr) : Except Format (Expr × Ty × TEnv) := do
  match e with
  | .numLit _ => .ok (e, .num, T)
  | .ty_expr ty e' =>
    match e', c with
    -- We allow _annotated_ free variables to appear in the `init`
    -- statements.
    | .fvar v, .init _ _ _ _ =>
      .ok (e, ty, Map.insert T v ty)
    | _,_ =>
      let (_,et,T) ← inferType T c e'
      match et, ty with
      | .num, .num => .ok (e, .num, T)
      | .bool, .bool => .ok (e, .bool, T)
      | _,_ => .error f!"The annotated type does not match"
  | .fvar x =>
    match T.find? x with
    | some ty => .ok (e, ty, T)
    | none =>
      -- A free variable will fail type inference, but once this is wrapped with
      -- .ty_expr ('v : ty'), the overall result will be successfully 'ty'.
      .error f!"Variable {x} not found in type context!"
  | .add_expr e1 e2 | .mul_expr e1 e2 =>
    let (_, e1t, T) ← inferType T c e1
    let (_, e2t, T) ← inferType T c e2
    match e1t, e2t with
    | .num, .num => .ok (e, .num, T)
    | _, _ => .error f!"Type checking failed for {e}"
  | .eq_expr ty e1 e2 =>
    let (_, e1t, T) ← inferType T c e1
    let (_, e2t, T) ← inferType T c e2
    match ty, e1t, e2t with
    | .num, .num, .num => .ok (e, .bool, T)
    | _,_,_ => .error f!"Type checking failed for {e}"

def unifyTypes (T : TEnv) (constraints : List (Ty × Ty)) : Except Format TEnv :=
  match constraints with
  | [] => .ok T
  | (t1, t2) :: crest =>
    match t1, t2 with
    | .num, .num => unifyTypes T crest
    | .bool, .bool => unifyTypes T crest
    | _, _ => .error f!"Types {t1} and {t2} cannot be unified!"

instance : TypeContext PureExpr TEnv where
  isBoolType := Arith.TypeCheck.isBoolType
  freeVars := (fun e => Arith.Expr.freeVars e)
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
  [.init 0 .num (.numLit 0),
   .set 0 (.add_expr (.fvar 0) (.numLit 100)),
   .assert "x_value_eq" (.eq_expr .num (.fvar 0) (.numLit 100))]

/--
info: ok: Commands:
init (0 : Num) := 0
0 := 0 + 100
assert [x_value_eq] 0 = 100

TEnv:
(0, Num)
-/
#guard_msgs in
#eval do let (cs, τ) ← Cmds.typeCheck TEnv.init testProgram1
          return format (cs, τ)

private def testProgram2 : Cmds Arith.PureExpr :=
  [.init 0 .bool (.numLit 0)]

/-- info: error: Types .Bool and Num cannot be unified! -/
#guard_msgs in
#eval do let (cs, τ) ← Cmds.typeCheck TEnv.init testProgram2
          return format (cs, τ)

private def testProgram3 : Cmds Arith.PureExpr :=
  [.init 0 .bool (.fvar 0)]

/--
info: error: Type Checking [init (0 : .Bool) := 0]: Variable 0 cannot appear in its own initialization expression!
-/
#guard_msgs in
#eval do let (cs, τ) ← Cmds.typeCheck TEnv.init testProgram3
          return format (cs, τ)

private def testProgram4 : Cmds Arith.PureExpr :=
  [.init 0 .num (.numLit 5),
   .set 0 (.fvar 0)]

/--
info: ok: Commands:
init (0 : Num) := 5
0 := 0

TEnv:
(0, Num)
-/
#guard_msgs in
#eval do let (cs, τ) ← Cmds.typeCheck TEnv.init testProgram4
          return format (cs, τ)


private def testProgram5 : Cmds Arith.PureExpr :=
  [.init 0 .num (.numLit 5),
   .init 0 .bool (.eq_expr .num (.numLit 1) (.numLit 2))]

/--
info: error: Type Checking [init (0 : .Bool) := 1 = 2]: Variable 0 of type Num already in context.
-/
#guard_msgs in
#eval do let (cs, τ) ← Cmds.typeCheck TEnv.init testProgram5
          return format (cs, τ)

private def testProgram6 : Cmds Arith.PureExpr :=
  [.init 0 .num (.fvar 1)]

/--
info: error: Variable 1 not found in type context!
-/
#guard_msgs in
#eval do let (cs, τ) ← Cmds.typeCheck TEnv.init testProgram6
          return format (cs, τ)

private def testProgram7 : Cmds Arith.PureExpr :=
  [.init 0 .num (.add_expr (.ty_expr .num (.fvar 1))
      (.ty_expr .num (.fvar 2)))]

/--
info: ok: Commands:
init (0 : Num) := (1 : Num) + (2 : Num)

TEnv:
(1, Num) (2, Num) (0, Num)
-/
#guard_msgs in
#eval do let (cs, τ) ← Cmds.typeCheck TEnv.init testProgram7
          return format (cs, τ)

private def testProgram8 : Cmds Arith.PureExpr :=
  [.init 0 .num (.numLit 1),
   .set 0 (.ty_expr .num (.fvar 1))]

/-- info: error: Variable 1 not found in type context! -/
#guard_msgs in
#eval do let (cs, τ) ← Cmds.typeCheck TEnv.init testProgram8
          return format (cs, τ)

---------------------------------------------------------------------

end TypeCheck
end Arith
