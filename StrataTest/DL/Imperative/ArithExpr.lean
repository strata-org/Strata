/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.EvalError
import Strata.DL.Util.Maps

namespace Arith
open Std (ToFormat Format format)
open Imperative

---------------------------------------------------------------------

/-! ## Abstract Syntax for `ArithPrograms`

NOTE: The Concrete Syntax is defined in `DDMDefinition.lean`.

A good design choice for abstract syntax is one that is amenable to
transformations, debugging, and analyses. The DDM-generated code may or may not
serve your purpose. For example, for `ArithPrograms`, perhaps you would like to
see named variables instead of de Bruijn indices, which is what the DDM
generates.

Here, we define the abstract syntax for `ArithPrograms`. For this simple
dialect, this is in fact quite similar to the DDM-generated one, except that we
have `Var : String → Option Ty` that have both the variable names and optionally
their types instead of DDM's `.fvar`s.
-/

/-- Types in `ArithPrograms` -/
inductive Ty where
  | Num | Bool
  deriving DecidableEq, Repr, Inhabited

instance : ToFormat Ty where
  format t := match t with | .Num => "Num" | .Bool => ".Bool"

/--
A type environment maps variable names to types.
-/
abbrev TEnv := Map String Ty

def TEnv.init : TEnv := []

instance : ToFormat TEnv where
  format := Map.format'

/--
Simple arithmetic expressions that will be used to specialize Imperative's
partial evaluator.
-/
inductive Expr where
  | Plus (e1 e2 : Expr)
  | Mul (e1 e2 : Expr)
  | Eq (e1 e2 : Expr)
  | Num (n : Nat)
  | Bool (b : Bool)
  | Var (v : String) (ty : Option Ty)
  deriving Inhabited, Repr

def Expr.format (e : Expr) : Format :=
  match e with
  | .Plus e1 e2 => f!"{Expr.format e1} + {Expr.format e2}"
  | .Mul e1 e2 => f!"{Expr.format e1} × {Expr.format e2}"
  | .Eq e1 e2 => f!"{Expr.format e1} = {Expr.format e2}"
  | .Var v (.some ty) => f!"({v} : {ty})"
  | .Var v .none => f!"{v}"
  | .Num n => f!"{n}"
  | .Bool b => f!"{b}"

instance : ToFormat Expr where
  format := Expr.format

def Expr.freeVars (e : Expr) : List (String × Option Ty) :=
  match e with
  | .Plus e1 e2 => e1.freeVars ++ e2.freeVars
  | .Mul e1 e2 => e1.freeVars ++ e2.freeVars
  | .Eq e1 e2 => e1.freeVars ++ e2.freeVars
  | .Num _ => []
  | .Bool _ => []
  | .Var v ty => [(v, ty)]

/--
An environment maps variable names to their types and corresponding
values (expressions).
-/
abbrev Env := Map String (Ty × Expr)

instance : ToFormat Env where
  format := Map.format'

abbrev PureExpr : PureExpr :=
   { Ident := String,
     Expr := Expr,
     Ty := Ty,
     ExprMetadata := Unit,
     TyEnv := TEnv,
     TyContext := Unit,
     EvalEnv := Env,
     EqIdent := instDecidableEqString }

/-- A Command of `ArithPrograms` -/
abbrev Command := Imperative.Cmd Arith.PureExpr
/-- Commands in `ArithPrograms` -/
abbrev Commands := Imperative.Cmds Arith.PureExpr

---------------------------------------------------------------------
end Arith
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
