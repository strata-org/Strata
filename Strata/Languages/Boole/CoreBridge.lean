/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Program
import Strata.Languages.Core.Statement
import Strata.DL.Lambda.LExpr

namespace Strata.Boole.CoreBridge

open Lambda

/-- Lift a monomorphic type into Core's `Ty` wrapper. -/
def monoTyToTy (ty : LMonoTy) : Core.Expression.Ty :=
  .forAll [] ty

/--
Build nested quantifiers from a list of binder types.

The first type in `tys` becomes the outermost quantifier.
-/
def mkQuants (isForall : Bool) (tys : List LMonoTy) (body : Core.Expression.Expr) : Core.Expression.Expr :=
  let q := if isForall then Lambda.QuantifierKind.all else Lambda.QuantifierKind.exist
  tys.foldr (fun ty acc => .quant () q "" (some ty) (.bvar () 0) acc) body

def mkExprIte
    (cond thenExpr elseExpr : Core.Expression.Expr)
    : Core.Expression.Expr :=
  .ite () cond thenExpr elseExpr

def mkExprEq
    (lhs rhs : Core.Expression.Expr)
    : Core.Expression.Expr :=
  .eq () lhs rhs

def mkExprNot
    (e : Core.Expression.Expr)
    : Core.Expression.Expr :=
  .app () Core.boolNotOp e

def mkExprOld
    (e : Core.Expression.Expr)
    : Except String Core.Expression.Expr :=
  match e with
  | .fvar m ident ty => .ok (.fvar m (Core.CoreIdent.mkOld ident.name) ty)
  | _ => .error s!"old: expected an identifier, got {e}"

def mkExprMapSelect
    (mapExpr idxExpr : Core.Expression.Expr)
    : Core.Expression.Expr :=
  Lambda.LExpr.mkApp () Core.mapSelectOp [mapExpr, idxExpr]

def mkExprMapUpdate
    (mapExpr idxExpr valExpr : Core.Expression.Expr)
    : Core.Expression.Expr :=
  Lambda.LExpr.mkApp () Core.mapUpdateOp [mapExpr, idxExpr, valExpr]

def mkExprBoolAnd
    (lhs rhs : Core.Expression.Expr)
    : Core.Expression.Expr :=
  Lambda.LExpr.mkApp () Core.boolAndOp [lhs, rhs]

def mkExprBoolOr
    (lhs rhs : Core.Expression.Expr)
    : Core.Expression.Expr :=
  Lambda.LExpr.mkApp () Core.boolOrOp [lhs, rhs]

def mkExprBoolEquiv
    (lhs rhs : Core.Expression.Expr)
    : Core.Expression.Expr :=
  Lambda.LExpr.mkApp () Core.boolEquivOp [lhs, rhs]

def mkExprBoolImplies
    (lhs rhs : Core.Expression.Expr)
    : Core.Expression.Expr :=
  Lambda.LExpr.mkApp () Core.boolImpliesOp [lhs, rhs]

def mkExprIntLe
    (lhs rhs : Core.Expression.Expr)
    : Core.Expression.Expr :=
  Lambda.LExpr.mkApp () Core.intLeOp [lhs, rhs]

def mkExprIntAdd
    (lhs rhs : Core.Expression.Expr)
    : Core.Expression.Expr :=
  Lambda.LExpr.mkApp () Core.intAddOp [lhs, rhs]

def mkExprIntSub
    (lhs rhs : Core.Expression.Expr)
    : Core.Expression.Expr :=
  Lambda.LExpr.mkApp () Core.intSubOp [lhs, rhs]

def mkExprTypedIntUn
    (op : String)
    (arg : Core.Expression.Expr)
    : Core.Expression.Expr :=
  let iop : Core.Expression.Expr := .op () ⟨s!"Int.{op}", ()⟩ none
  .app () iop arg

def mkExprTypedIntBin
    (op : String)
    (lhs rhs : Core.Expression.Expr)
    : Core.Expression.Expr :=
  let iop : Core.Expression.Expr := .op () ⟨s!"Int.{op}", ()⟩ none
  .mkApp () iop [lhs, rhs]

def mkInitStmt
    (name : Core.Expression.Ident)
    (ty : Core.Expression.Ty)
    (rhs : Option Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    : Core.Statement :=
  Core.Statement.init name ty rhs md

def mkSetStmt
    (name : Core.Expression.Ident)
    (rhs : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    : Core.Statement :=
  Core.Statement.set name rhs md

def mkAssumeStmt
    (label : String)
    (cond : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    : Core.Statement :=
  Core.Statement.assume label cond md

def mkAssertStmt
    (label : String)
    (cond : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    : Core.Statement :=
  Core.Statement.assert label cond md

def mkCoverStmt
    (label : String)
    (cond : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    : Core.Statement :=
  Core.Statement.cover label cond md

def mkHavocStmt
    (name : Core.Expression.Ident)
    (md : Imperative.MetaData Core.Expression)
    : Core.Statement :=
  Core.Statement.havoc name md

def mkCallStmt
    (lhs : List Core.Expression.Ident)
    (procName : String)
    (args : List Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    : Core.Statement :=
  Core.Statement.call lhs procName args md

def mkIteStmt
    (cond : Core.Expression.Expr)
    (thenBody elseBody : List Core.Statement)
    (md : Imperative.MetaData Core.Expression)
    : Core.Statement :=
  .ite cond thenBody elseBody md

def mkLoopStmt
    (guard : Core.Expression.Expr)
    (measure : Option Core.Expression.Expr)
    (invs : List Core.Expression.Expr)
    (body : List Core.Statement)
    (md : Imperative.MetaData Core.Expression)
    : Core.Statement :=
  .loop guard measure invs body md

def mkBlockStmt
    (label : String)
    (body : List Core.Statement)
    (md : Imperative.MetaData Core.Expression)
    : Core.Statement :=
  .block label body md

def mkExitStmt
    (label : Option String)
    (md : Imperative.MetaData Core.Expression)
    : Core.Statement :=
  .exit label md

def mkTypeDeclStmt
    (t : TypeConstructor)
    (md : Imperative.MetaData Core.Expression)
    : Core.Statement :=
  Core.Statement.typeDecl t md

def mkFuncDeclStmt
    (f : Imperative.PureFunc Core.Expression)
    (md : Imperative.MetaData Core.Expression)
    : Core.Statement :=
  .funcDecl f md

def mkVarDecl
    (name : Core.Expression.Ident)
    (ty : Core.Expression.Ty)
    (rhs : Option Core.Expression.Expr)
    : Core.Decl :=
  .var name ty rhs

def mkTypeConDecl
    (name : String)
    (params : List String)
    : Core.Decl :=
  .type (.con { name := name, params := params })

def mkTypeSynDecl
    (name : String)
    (typeArgs : List String)
    (rhs : LMonoTy)
    : Core.Decl :=
  .type (.syn { name := name, typeArgs := typeArgs, type := rhs })

def mkTypeDataDecl
    (dts : List (Lambda.LDatatype Unit))
    : Core.Decl :=
  .type (.data dts)

def mkAxiomDecl
    (name : String)
    (e : Core.Expression.Expr)
    : Core.Decl :=
  .ax { name := name, e := e }

def mkDistinctDecl
    (name : Core.Expression.Ident)
    (es : List Core.Expression.Expr)
    : Core.Decl :=
  .distinct name es

def mkProcDecl
    (p : Core.Procedure)
    : Core.Decl :=
  .proc p

def mkFuncDecl
    (f : Core.Function)
    : Core.Decl :=
  .func f

end Strata.Boole.CoreBridge
