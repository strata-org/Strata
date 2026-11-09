/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.AST
public import Strata.Languages.Core.Program

namespace Cortex

public section

open Imperative Lambda

abbrev LBlock := DetBlock Label IRCmd Core.Expression
abbrev LCFG := DetCFG Core.Expression IRCmd

structure Module where
  program : Program
  decls : List Core.Decl := []

structure Pass where
  name : String
  run : Module → Except String Module

def mkFvar (n : String) : Expr := .fvar () ⟨n, ()⟩ none
def mkOp (n : String) : Expr := .op () ⟨n, ()⟩ none
def mkApp (f : Expr) (args : List Expr) : Expr := args.foldl (fun acc a => .app () acc a) f
def mkCall (n : String) (args : List Expr) : Expr := mkApp (mkOp n) args
def tt : Expr := .const () (.boolConst true)
def ff : Expr := .const () (.boolConst false)
def intLit (i : Int) : Expr := .const () (.intConst i)
def mono (t : LMonoTy) : LTy := .forAll [] t
def tcon (n : String) : LMonoTy := .tcons n []

partial def mapMonoTy (f : String → Option LMonoTy) : LMonoTy → LMonoTy
  | .tcons n [] => (f n).getD (.tcons n [])
  | .tcons n args => .tcons n (args.map (mapMonoTy f))
  | t => t

def mapLTy (f : String → Option LMonoTy) : LTy → LTy
  | .forAll vs t => .forAll vs (mapMonoTy f t)

partial def mapExprTys (f : String → Option LMonoTy) : Expr → Expr
  | .op m o ty => .op m o (ty.map (mapMonoTy f))
  | .fvar m n ty => .fvar m n (ty.map (mapMonoTy f))
  | .abs m n ty e => .abs m n (ty.map (mapMonoTy f)) (mapExprTys f e)
  | .quant m k n ty tr e => .quant m k n (ty.map (mapMonoTy f)) (mapExprTys f tr) (mapExprTys f e)
  | .app m a b => .app m (mapExprTys f a) (mapExprTys f b)
  | .ite m c t e => .ite m (mapExprTys f c) (mapExprTys f t) (mapExprTys f e)
  | .eq m a b => .eq m (mapExprTys f a) (mapExprTys f b)
  | e => e

partial def mapExpr (f : Expr → Option Expr) (e : Expr) : Expr :=
  match f e with
  | some e' => e'
  | none =>
    match e with
    | .abs m n ty b => .abs m n ty (mapExpr f b)
    | .quant m k n ty tr b => .quant m k n ty (mapExpr f tr) (mapExpr f b)
    | .app m a b => .app m (mapExpr f a) (mapExpr f b)
    | .ite m c t e => .ite m (mapExpr f c) (mapExpr f t) (mapExpr f e)
    | .eq m a b => .eq m (mapExpr f a) (mapExpr f b)
    | e => e

def substFvars (σ : List (String × Expr)) (e : Expr) : Expr :=
  mapExpr (fun
    | .fvar _ n _ => σ.lookup n.name
    | _ => none) e

def mapExprOrNondet (g : Expr → Expr) : ExprOrNondet Core.Expression → ExprOrNondet Core.Expression
  | .det e => .det (g e)
  | .nondet => .nondet

def mapBaseCmd (g : Expr → Expr) (t : LTy → LTy) : Cmd Core.Expression → Cmd Core.Expression
  | .init x ty e md => .init x (t ty) (mapExprOrNondet g e) md
  | .set x e md => .set x (mapExprOrNondet g e) md
  | .assert l b md => .assert l (g b) md
  | .assume l b md => .assume l (g b) md
  | .cover l b md => .cover l (g b) md

def mapCmdExprs (g : Expr → Expr) (t : LTy → LTy) : IRCmd → IRCmd
  | .cmd c => .cmd (mapBaseCmd g t c)
  | .new x ty md => .new x ty md
  | .readField x o f md => .readField x (g o) f md
  | .writeField o f v md => .writeField (g o) f (g v) md
  | .instanceOf x o ty md => .instanceOf x (g o) ty md
  | .call lhs p args md => .call lhs p (args.map g) md
  | .virtualCall lhs o meth args md => .virtualCall lhs o meth (args.map g) md
  | .throw e md => .throw (g e) md

def mapTransfer (g : Expr → Expr) : DetTransferCmd Label Core.Expression → DetTransferCmd Label Core.Expression
  | .condGoto c lt lf md => .condGoto (g c) lt lf md
  | .finish md => .finish md

def mapBlock (h : IRCmd → List IRCmd) (g : Expr → Expr) (b : LBlock) : LBlock :=
  { cmds := b.cmds.flatMap h, transfer := mapTransfer g b.transfer }

def mapBody (h : IRCmd → List IRCmd) (g : Expr → Expr) (b : Body) : Body :=
  { b with cfg := { b.cfg with blocks := b.cfg.blocks.map fun (l, blk) => (l, mapBlock h g blk) } }

def mapProgramTys (f : String → Option LMonoTy) (p : Program) : Program :=
  let t := mapLTy f
  let g := mapExprTys f
  let params := fun (ps : List (Core.Expression.Ident × LTy)) => ps.map fun (x, ty) => (x, t ty)
  { p with
    composites := p.composites.map fun c =>
      { c with fields := c.fields.map fun fd => { fd with ty := t fd.ty } }
    constrained := p.constrained.map fun c => { c with base := t c.base, constraint := g c.constraint }
    globals := params p.globals
    procedures := p.procedures.map fun pr =>
      { pr with
        inputs := params pr.inputs
        outputs := params pr.outputs
        body := pr.body.map (mapBody (fun c => [mapCmdExprs g t c]) g) } }

def mapConstrTys (f : String → Option LMonoTy) (c : LConstr Unit) : LConstr Unit :=
  { c with args := c.args.map fun (n, ty) => (n, mapMonoTy f ty) }

def mapDatatypeTys (f : String → Option LMonoTy) (dt : LDatatype Unit) : LDatatype Unit where
  name := dt.name
  typeArgs := dt.typeArgs
  constrs := dt.constrs.map (mapConstrTys f)
  constrs_ne := by have := dt.constrs_ne; simpa using this

def mapDeclTys (f : String → Option LMonoTy) : Core.Decl → Core.Decl
  | .type (.data dts) md =>
    .type (.data (dts.map (mapDatatypeTys f))) md
  | .func fn md =>
    .func { fn with
      inputs := fn.inputs.map fun (n, ty) => (n, mapMonoTy f ty)
      output := mapMonoTy f fn.output
      body := fn.body.map (mapExprTys f) } md
  | d => d

def Module.mapTys (f : String → Option LMonoTy) (m : Module) : Module :=
  { program := mapProgramTys f m.program, decls := m.decls.map (mapDeclTys f) }

def Module.mapProcedures (f : Procedure → Procedure) (m : Module) : Module :=
  { m with program := { m.program with procedures := m.program.procedures.map f } }

def Module.refuseVirtualCalls (m : Module) (pass : String) : Except String Unit :=
  if m.program.hasVirtualCall then .error s!"Cortex `virtualCall` must be lowered by LowerDispatch before {pass}"
  else .ok ()

def Body.maxFresh (b : Body) : Nat := b.cfg.blocks.length

end

end Cortex
