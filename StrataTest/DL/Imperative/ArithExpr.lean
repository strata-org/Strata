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

import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.EvalError
import Strata.DL.Util.Maps
import StrataTest.DL.Imperative.DDMDefinition

namespace Arith
open Std (ToFormat Format format)
open Imperative

---------------------------------------------------------------------

abbrev Ty := ArithPrograms.ArithProgramsType

instance : ToFormat Ty where
  format t := match t with | .num => "Num" | .bool => ".Bool"

/--
A type environment maps variable names to types.
-/
abbrev TEnv := Map Nat Ty

def TEnv.init : TEnv := []

instance : ToFormat TEnv where
  format := Map.format'

/--
Simple arithmetic expressions that will be used to specialize Imperative's
partial evaluator.
-/
abbrev Expr := ArithPrograms.Expr

def Expr.format (e : Expr) : Format :=
  match e with
  | .add_expr e1 e2 => f!"{Expr.format e1} + {Expr.format e2}"
  | .mul_expr e1 e2 => f!"{Expr.format e1} × {Expr.format e2}"
  | .eq_expr ty e1 e2 => f!"{Expr.format e1} = {Expr.format e2}"
  | .ty_expr ty e => f!"({Expr.format e} : {ty})"
--  | .Var v (.some ty) => f!"({v} : {ty})"
  | .fvar v => f!"{v}"
  | .numLit n => f!"{n}"

instance : ToFormat Expr where
  format := Expr.format

def Expr.freeVars (e : Expr) : List Nat :=
  match e with
  | .add_expr e1 e2 => Expr.freeVars e1 ++ Expr.freeVars e2
  | .mul_expr e1 e2 => Expr.freeVars e1 ++ Expr.freeVars e2
  | .eq_expr ty e1 e2 => Expr.freeVars e1 ++ Expr.freeVars e2
  | .numLit _ => []
  | .ty_expr ty e => Expr.freeVars e -- TODO: fix
  | .fvar v => [v]

/--
An environment maps variable names to their types and corresponding
values (expressions).
-/
abbrev Env := Map Nat (Ty × Expr)

instance : ToFormat Env where
  format := Map.format'

abbrev PureExpr : PureExpr :=
   { Ident := Nat,
     Expr := Expr,
     Ty := Ty,
     TyEnv := TEnv,
     EvalEnv := Env,
     EqIdent := instDecidableEqNat }

/-
-- Here is an alternate formulation for untyped Arith expressions.
/--
We will ignore types for this test; as such, `Expr` will be treated as untyped.
-/
inductive Untyped where
  | All
  deriving Repr

instance : ToFormat Untyped where
  format _ := f!".All"

abbrev PureExpr : PureExpr :=
   { Ident := String,
     Expr := Expr,
     Ty := Untyped,
     TyEnv := Empty,
     EvalEnv :=  Env }
-/

---------------------------------------------------------------------

end Arith
