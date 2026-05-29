/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Expressions
public import Strata.Languages.Core.Identifiers
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Function
public import Strata.Languages.Core.TypeDecl
public import Strata.Languages.Core.Program

/-!
CoreMatch's intermediate representation. The translator emits values
of these types; `ToCore` lowers them to plain `Core.Program`.
-/

namespace Strata.CoreMatch

open Core Lambda

public section

mutual

inductive MExpr where
  | core   (e : Core.Expression.Expr)
  | matchE (scrut : MExpr) (dtName : String) (arms : List MArm)
  deriving Inhabited

/--
Expression-level match arm. Constructor arms carry a pre-curried case
function `caseFn = λb₁:T₁. … λbₖ:Tₖ. body` in de Bruijn form, ready
to be passed straight to the eliminator. Wildcard arm bodies must be
closed; compilation pads them per uncovered constructor.
-/
inductive MArm where
  | ctor (ctor : String) (caseFn : MExpr) : MArm
  | wild (body : MExpr) : MArm
  deriving Inhabited

end

/--
Statement-level match arm. The body already includes the
`var b : T := D..f(scrut);` binder-init statements; lowering only
threads the scrutinee through the testers.
-/
inductive MStmtArm : Type where
  | ctor (ctor : String) (body : List Core.Statement) : MStmtArm
  | wild (body : List Core.Statement) : MStmtArm
  deriving Inhabited

inductive MStmt : Type where
  | core      (s : Core.Statement) : MStmt
  | matchStmt (scrutinee : Core.Expression.Expr)
              (dtName    : String)
              (arms      : List MStmtArm)
              : MStmt

@[expose] abbrev MStmts := List MStmt

@[expose] def MStmt.ofCore (s : Core.Statement) : MStmt := .core s

@[expose] def MStmts.ofCore (ss : List Core.Statement) : MStmts :=
  ss.map MStmt.ofCore

@[expose] def MExpr.ofCore (e : Core.Expression.Expr) : MExpr := .core e

structure MFunction where
  name     : Core.Expression.Ident
  typeArgs : List Lambda.TyIdentifier := []
  inputs   : List (Core.CoreIdent × Lambda.LMonoTy)
  output   : Lambda.LMonoTy
  body     : Option MExpr := none
  deriving Inhabited

structure MProcedure where
  header : Core.Procedure.Header
  spec   : Core.Procedure.Spec := default
  body   : List MStmt := []
  deriving Inhabited

inductive MDecl where
  | type     (t : Core.TypeDecl) (md : Imperative.MetaData Core.Expression)
  | ax       (a : Core.Axiom) (md : Imperative.MetaData Core.Expression)
  | distinct (name : Core.Expression.Ident)
             (es : List Core.Expression.Expr)
             (md : Imperative.MetaData Core.Expression)
  | proc     (d : MProcedure) (md : Imperative.MetaData Core.Expression)
  | func     (f : MFunction) (md : Imperative.MetaData Core.Expression)
  deriving Inhabited

@[expose] abbrev MDecls := List MDecl

structure MProgram where
  decls : MDecls := []
  deriving Inhabited

end

end Strata.CoreMatch
