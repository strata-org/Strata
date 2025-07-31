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



import Strata.DL.Imperative.MetaData
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.HasVars

---------------------------------------------------------------------

namespace Imperative

/-! # Imperative dialect: non-deterministic statements -/

inductive NondetStmt (P : PureExpr) (Cmd : Type) : Type where
  | cmd      (cmd : Cmd)
  | seq      (s1 s2 : NondetStmt P Cmd)
  | choice   (s1 s2 : NondetStmt P Cmd)
  | loop     (s : NondetStmt P Cmd)
  deriving Inhabited

abbrev NondetStmt.init {P : PureExpr} (name : P.Ident) (ty : P.Ty) (expr : P.Expr) (md : MetaData P := .empty) :=
  NondetStmt.cmd (P:=P) (Cmd.init name ty expr md)
abbrev NondetStmt.set {P : PureExpr} (name : P.Ident) (expr : P.Expr) (md : MetaData P := .empty) :=
  NondetStmt.cmd (P:=P) (Cmd.set name expr md)
abbrev NondetStmt.havoc {P : PureExpr} (name : P.Ident) (md : MetaData P := .empty) :=
  NondetStmt.cmd (P:=P) (Cmd.havoc name md)
abbrev NondetStmt.assert {P : PureExpr} (label : String) (b : P.Expr) (md : MetaData P := .empty) :=
  NondetStmt.cmd (P:=P) (Cmd.assert label b md)
abbrev NondetStmt.assume {P : PureExpr} (label : String) (b : P.Expr) (md : MetaData P := .empty) :=
  NondetStmt.cmd (P:=P) (Cmd.assume label b md)

mutual
/-- Get all variables defined by the statement `s`. -/
def NondetStmt.definedVars [HasVarsImp P C] (s : NondetStmt P C) : List P.Ident :=
  match s with
  | .cmd c => HasVarsImp.definedVars c
  | .seq s1 s2 => NondetStmt.definedVars s1 ++ NondetStmt.definedVars s2
  | .choice s1 s2 => NondetStmt.definedVars s1 ++ NondetStmt.definedVars s2
  | .loop s => NondetStmt.definedVars s

def NondetStmts.definedVars [HasVarsImp P C] (ss : List (NondetStmt P C)) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => NondetStmt.definedVars s ++ NondetStmts.definedVars srest
end

mutual
/-- Get all variables modified by the statement `s`. -/
def NondetStmt.modifiedVars [HasVarsImp P C] (s : NondetStmt P C) : List P.Ident :=
  match s with
  | .cmd c => HasVarsImp.modifiedVars c
  | .seq s1 s2 => NondetStmt.modifiedVars s1 ++ NondetStmt.modifiedVars s2
  | .choice s1 s2 => NondetStmt.modifiedVars s1 ++ NondetStmt.modifiedVars s2
  | .loop s => NondetStmt.modifiedVars s

def NondetStmts.modifiedVars [HasVarsImp P C] (ss : List (NondetStmt P C)) : List P.Ident :=
  match ss with
  | [] => []
  | s :: srest => NondetStmt.modifiedVars s ++ NondetStmts.modifiedVars srest
end

instance (P : PureExpr) [HasVarsImp P C] : HasVarsImp P (NondetStmt P C) where
  definedVars := NondetStmt.definedVars
  modifiedVars := NondetStmt.modifiedVars

---------------------------------------------------------------------

/-! ## Formatting -/

open Std (ToFormat Format format)

def formatNondetStmt (P : PureExpr) (s : NondetStmt P C)
  [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C]: Format :=
  match s with
  | .cmd cmd => format cmd
  | .seq s1 s2 => f!"({formatNondetStmt P s1}) ; ({formatNondetStmt P s2})"
  | .choice s1 s2 => f!"({formatNondetStmt P s1}) | ({formatNondetStmt P s2})"
  | .loop s => f!"({formatNondetStmt P s})*"

instance [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] [ToFormat C]
        : ToFormat (NondetStmt P C) where
  format s := formatNondetStmt P s

---------------------------------------------------------------------

end Imperative
