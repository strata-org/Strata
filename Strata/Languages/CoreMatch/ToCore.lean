/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.CoreMatch.CoreMatch
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Expressions
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Function
public import Strata.Languages.Core.TypeDecl
public import Strata.Languages.Core.Program
public import Strata.DL.Lambda.LExpr
public import Strata.DL.Util.Map

/-!
Lower CoreMatch's intermediate representation to plain `Core.Program`.
Expression-level matches lower to applications of the auto-generated
structural eliminator `D$Elim`; statement-level matches lower to a
nested `if` chain over the auto-generated testers `D..isCᵢ`.
-/

namespace Strata.CoreMatch.ToCore

open Core Lambda Imperative
open Strata.CoreMatch

public section

@[expose] def elimName     (datatype : String) : String := datatype ++ "$Elim"
@[expose] def testerName   (datatype ctor : String) : String := datatype ++ "..is" ++ ctor
@[expose] def accessorName (datatype field : String) : String := datatype ++ ".." ++ field

def opE (name : String) : Core.Expression.Expr :=
  LExpr.op () ⟨name, ()⟩ none

def applyAll (head : Core.Expression.Expr)
    (args : List Core.Expression.Expr) : Core.Expression.Expr :=
  args.foldl (fun acc a => LExpr.app () acc a) head

@[expose]
def findDatatype (decls : List Core.Decl) (name : String)
    : Option (LDatatype Unit) := Id.run do
  for d in decls do
    if let .type (.data block) _ := d then
      for dt in block do
        if dt.name == name then return some dt
  return none

/--
Sentinel emitted in the case slot for a constructor that has no
matching arm. Unreachable when the redundancy checker has run; if
emitted it surfaces downstream as an unbound symbol.
-/
def missingArmPlaceholder (ctor : String) : Core.Expression.Expr :=
  LExpr.fvar () ⟨"__coreMatch_missing_" ++ ctor, ()⟩ none

def padToCtorArity (c : LConstr Unit) (body : Core.Expression.Expr)
    : Core.Expression.Expr :=
  LExpr.absMulti () (c.args.map (·.2)) body

@[expose]
partial def compileMExprWith
    (lookup : String → Option (LDatatype Unit))
    (e : MExpr) : Core.Expression.Expr :=
  match e with
  | .core e0 => e0
  | .matchE scrut dtName arms =>
    let scrutE := compileMExprWith lookup scrut
    match lookup dtName with
    | none => LExpr.fvar () ⟨"__coreMatch_unknown_dt_" ++ dtName, ()⟩ none
    | some dt =>
      let ctorMap : Map String MExpr := Map.ofList <| arms.filterMap fun
        | .ctor c f => some (c, f) | .wild _ => none
      let wild? : Option MExpr :=
        arms.findSome? fun | .wild b => some b | _ => none
      let caseFor (c : LConstr Unit) : Core.Expression.Expr :=
        match ctorMap.find? c.name.name with
        | some f => compileMExprWith lookup f
        | none =>
          match wild? with
          | some b => padToCtorArity c (compileMExprWith lookup b)
          | none   => missingArmPlaceholder c.name.name
      applyAll (opE (elimName dtName)) (scrutE :: dt.constrs.map caseFor)

@[expose]
def compileMExpr (decls : List Core.Decl) (e : MExpr) : Core.Expression.Expr :=
  compileMExprWith (findDatatype decls) e

def mkTesterApp (dtName ctor : String)
    (scrut : Core.Expression.Expr) : Core.Expression.Expr :=
  LExpr.app () (opE (testerName dtName ctor)) scrut

def stmtsBlockOrSingle : List Core.Statement → Core.Statement
  | [s] => s
  | ss  => Imperative.Stmt.block "" ss {}

def assertFalse (label : String) : Core.Statement :=
  Core.Statement.assert label (LExpr.const () (LConst.boolConst false)) {}

@[expose]
def compileMatchArms
    (scrut : Core.Expression.Expr)
    (dtName : String)
    (dt : LDatatype Unit)
    (arms : List MStmtArm) : Core.Statement :=
  let armMap : Map String (List Core.Statement) := Map.ofList <| arms.filterMap fun
    | .ctor c body => some (c, body) | .wild _ => none
  let wildcard? := arms.findSome? fun | .wild body => some body | _ => none
  let fallback := wildcard?.getD [assertFalse "coreMatch_nonexhaustive"]
  dt.constrs.foldr (init := stmtsBlockOrSingle fallback) fun c acc =>
    Imperative.Stmt.ite
      (Imperative.ExprOrNondet.det (mkTesterApp dtName c.name.name scrut))
      ((armMap.find? c.name.name).getD fallback)
      [acc] {}

@[expose]
def compileMStmt (decls : List Core.Decl) : MStmt → List Core.Statement
  | .core c => [c]
  | .matchStmt scrut dtName arms =>
    match findDatatype decls dtName with
    | none    => [assertFalse ("coreMatch_unknown_dt_" ++ dtName)]
    | some dt => [compileMatchArms scrut dtName dt arms]

@[expose]
def compileMStmts (decls : List Core.Decl) (ss : List MStmt)
    : List Core.Statement :=
  ss.flatMap (compileMStmt decls)

@[expose]
def compileFunction (decls : List Core.Decl) (f : MFunction) : Core.Function :=
  { name := f.name
    typeArgs := f.typeArgs
    inputs := f.inputs
    output := f.output
    body := f.body.map (compileMExpr decls)
    attr := #[]
    concreteEval := none
    axioms := []
    preconditions := []
    isConstr := false }

@[expose]
def compileProcedure (decls : List Core.Decl) (p : MProcedure) : Core.Procedure :=
  { header := p.header
    spec := p.spec
    body := compileMStmts decls p.body }

@[expose]
def compileDecl (decls : List Core.Decl) (d : MDecl) : Core.Decl :=
  match d with
  | .type t md       => .type t md
  | .ax a md         => .ax a md
  | .distinct n e md => .distinct n e md
  | .proc p md       => .proc (compileProcedure decls p) md
  | .func f md       => .func (compileFunction decls f) md

@[expose]
def compileProgram (p : MProgram) : Core.Program :=
  let decls : List Core.Decl :=
    p.decls.foldl (init := []) fun acc d =>
      acc ++ [compileDecl acc d]
  { decls := decls }

end

end Strata.CoreMatch.ToCore
