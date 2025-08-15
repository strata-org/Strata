/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.DDMTransform.Parse
import Strata.DL.Imperative.Stmt
import Strata.DL.Lambda.Lambda
import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.Identifiers

-- We define the AST for our language here.

-- The CST and grammar are defined in `DDMTransform/Parse.lean`
-- The conversion to this AST are defined in `DDMTransform/Translate.lean`
-- Typechecking is done in ___ (TODO)
-- We symbolically execute the C_Simp program in ___, collecting path conditions. (TODO)

namespace Strata
namespace C_Simp

-- Our expression language is `DL/Lambda`
abbrev Expression : Imperative.PureExpr := {
  Ident := String,
  Expr := Lambda.LExpr Lambda.LMonoTy String,
  Ty := Lambda.LTy,
  TyEnv := Lambda.TEnv String,
  EvalEnv := Lambda.LState String,
  EqIdent := String.decEq
}


def Command := Imperative.Cmd Expression

def Statement := Imperative.Stmt Expression Command

instance : Imperative.HasVarsImp Expression Command where
  definedVars := Imperative.Cmd.definedVars
  modifiedVars := Imperative.Cmd.modifiedVars

-- Our statement language is `DL/Imp` with `DL/Lambda` as the expression language

-- A program is a list of functions. We start by defining functions

structure Function where
  name: Expression.Ident
  pre : Expression.Expr
  post : Expression.Expr
  body : List Statement
  ret_ty : Lambda.LMonoTy
  inputs : Map Expression.Ident Lambda.LMonoTy
deriving Inhabited

structure Program where
  funcs : List Function

-- Instances
open Std (ToFormat Format format)

instance [ToFormat Expression.Ident] [ToFormat Expression.Expr] [ToFormat Expression.Ty] : ToFormat Command where
  format c := Imperative.formatCmd Expression c

instance [ToFormat Expression.Ident] [ToFormat Expression.Expr] [ToFormat Expression.Ty] [ToFormat Command]:
  ToFormat (List Statement) where
  format ss := Imperative.formatStmts Expression ss

instance : Std.ToFormat Function where
  format f :=
    "function " ++ Std.format f.name ++ " {\n" ++
    "  pre: " ++ Std.format f.pre ++ "\n" ++
    "  post: " ++ Std.format f.post ++ "\n" ++
    "  body:\n" ++ Std.format f.body ++ "\n" ++
    "}"

instance : Std.ToFormat Program where
  format p := Std.Format.joinSep (p.funcs.map Std.format) Std.Format.line

---------------------------------------------------------------------

instance : ToString (Program) where
  toString p := toString (Std.format p)

end C_Simp
end Strata
