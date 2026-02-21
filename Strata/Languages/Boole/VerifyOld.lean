/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boole.Boole
import Strata.Languages.Boole.DDMTransform.Parse
import Strata.Languages.Boole.DDMTransform.TranslateOld
import Strata.Languages.Core.Verifier
import Strata.DL.Imperative.Stmt

/--
Legacy Boole verification path:
`Strata.Program` -> handwritten `translateProgram` -> legacy `Boole.Program`
-> handwritten `toCoreProgram` -> `Core.verify`.

Kept for comparison/migration; the active pipeline is in `Verify.lean`
and uses generated `BooleDDM.Program.ofAst`.
-/
def Lambda.LExpr.replaceExpr (e : Lambda.LExpr T) (f : Lambda.LExpr T → Option (Lambda.LExpr T))
  : Lambda.LExpr T :=
  match f e with
  | some e => e
  | none =>
    match e with
    | .const m c => .const m c
    | .op m o ty => .op m o ty
    | .bvar m n => .bvar m n
    | .fvar m n ty => .fvar m n ty
    | .abs m ty e' => .abs m ty (replaceExpr e' f)
    | .quant m k ty tr e' => .quant m k ty (replaceExpr tr f) (replaceExpr e' f)
    | .app m fn arg => .app m (replaceExpr fn f) (replaceExpr arg f)
    | .ite m c t e' => .ite m (replaceExpr c f) (replaceExpr t f) (replaceExpr e' f)
    | .eq m e1 e2 => .eq m (replaceExpr e1 f) (replaceExpr e2 f)

namespace Core

def Command.replaceExpr (c : Core.Command) (f : Expression.Expr → Option Expression.Expr) : Core.Command :=
  match c with
  | .cmd (.init name ty e md) => .cmd (.init name ty (e.replaceExpr f) md)
  | .cmd (.set name e md) => .cmd (.set name (e.replaceExpr f) md)
  | .cmd (.havoc name md) => .cmd (.havoc name md)
  | .cmd (.assert label b md) => .cmd (.assert label (b.replaceExpr f) md)
  | .cmd (.assume label b md) => .cmd (.assume label (b.replaceExpr f) md)
  | .cmd (.cover label b md) => .cmd (.cover label (b.replaceExpr f) md)
  | .call lhs name args md => .call lhs name (args.map (·.replaceExpr f)) md

mutual

def Imperative.Stmt.replaceExpr (s : Imperative.Stmt Core.Expression Core.Command) (f : Expression.Expr → Option Expression.Expr) : Imperative.Stmt Core.Expression Core.Command :=
  match s with
  | .cmd c => .cmd (Command.replaceExpr c f)
  | .block l b md => .block l (Imperative.Block.replaceExpr b f) md
  | .ite cond thenb elseb md => .ite (cond.replaceExpr f) (Imperative.Block.replaceExpr thenb f) (Imperative.Block.replaceExpr elseb f) md
  | .loop guard measure invariant body md =>
    .loop (guard.replaceExpr f) (measure.map (·.replaceExpr f)) (invariant.map (·.replaceExpr f)) (Imperative.Block.replaceExpr body f) md
  | .goto label md => .goto label md
  | .funcDecl decl md => .funcDecl decl md

def Imperative.Block.replaceExpr (bss : Imperative.Block Core.Expression Core.Command) (f : Expression.Expr → Option Expression.Expr) : Imperative.Block Core.Expression Core.Command :=
  let ss : List (Imperative.Stmt Core.Expression Core.Command) := bss.map fun s =>
    Imperative.Stmt.replaceExpr s f
  ss

end

end Core

namespace Strata.Boole

def toCoreExpr (e : Boole.Expression.Expr) : Core.Expression.Expr :=
  match e with
  | .const c ty => .const c ty
  | .op m o ty => .op m ⟨o.name, .unres⟩ ty
  | .bvar m n => .bvar m n
  | .fvar m n ty => .fvar m ⟨n.name, .unres⟩ ty
  | .abs m ty e => .abs m ty (toCoreExpr e)
  | .quant m k ty tr e => .quant m k ty (toCoreExpr tr) (toCoreExpr e)
  | .app m fn e => .app m (toCoreExpr fn) (toCoreExpr e)
  | .ite m c t e => .ite m (toCoreExpr c) (toCoreExpr t) (toCoreExpr e)
  | .eq m e1 e2 => .eq m (toCoreExpr e1) (toCoreExpr e2)

def ofCoreExpr (e : Core.Expression.Expr) : Boole.Expression.Expr :=
  match e with
  | .const m c => .const m c
  | .op m o ty => .op m ⟨o.name, .unres⟩ ty
  | .bvar m n => .bvar m n
  | .fvar m n ty => .fvar m ⟨n.name, .unres⟩ ty
  | .abs m ty e => .abs m ty (ofCoreExpr e)
  | .quant m k ty tr e => .quant m k ty (ofCoreExpr tr) (ofCoreExpr e)
  | .app m fn e => .app m (ofCoreExpr fn) (ofCoreExpr e)
  | .ite m c t e => .ite m (ofCoreExpr c) (ofCoreExpr t) (ofCoreExpr e)
  | .eq m e1 e2 => .eq m (ofCoreExpr e1) (ofCoreExpr e2)

def toCoreVisibility (v : Boole.Visibility) : Core.Visibility :=
  match v with
  | .unres => .unres
  | .glob => .glob
  | .locl => .locl
  | .temp => .temp

def toCoreIdent (id : Expression.Ident) : Core.Expression.Ident :=
  ⟨id.name, toCoreVisibility id.metadata⟩

def toCoreField (f : Imperative.MetaDataElem.Field Boole.Expression) : Imperative.MetaDataElem.Field Core.Expression :=
  match f with
  | .var v => .var (toCoreIdent v)
  | .label l => .label l

def toCoreValue (v : Imperative.MetaDataElem.Value Boole.Expression) : Imperative.MetaDataElem.Value Core.Expression :=
  match v with
  | .expr e => .expr (toCoreExpr e)
  | .msg s => .msg s
  | .fileRange r => .fileRange r

def ofCoreLParamsMetaData (md : Core.CoreLParams.Metadata) : Boole.BooleLParams.Metadata :=
  md

def toCoreMetaDataElem (md : Imperative.MetaDataElem Boole.Expression) : Imperative.MetaDataElem Core.Expression :=
  { fld := toCoreField md.fld, value := toCoreValue md.value }

def toCoreMetaData (md : Imperative.MetaData Boole.Expression) : Imperative.MetaData Core.Expression :=
  md.map toCoreMetaDataElem

def toCoreCmd (c : Boole.Command) : Core.Command :=
  match c with
  | .cmd (.init name ty e md) => .cmd (.init (toCoreIdent name) ty (toCoreExpr e) (toCoreMetaData md))
  | .cmd (.set name e md) => .cmd (.set (toCoreIdent name) (toCoreExpr e) (toCoreMetaData md))
  | .cmd (.havoc name md) => .cmd (.havoc (toCoreIdent name) (toCoreMetaData md))
  | .cmd (.assert label b md) => .cmd (.assert label (toCoreExpr b) (toCoreMetaData md))
  | .cmd (.assume label b md) => .cmd (.assume label (toCoreExpr b) (toCoreMetaData md))
  | .cmd (.cover label b md) => .cmd (.cover label (toCoreExpr b) (toCoreMetaData md))
  | .call lhs name args md => .call (lhs.map toCoreIdent) name (args.map toCoreExpr) (toCoreMetaData md)

mutual

def toCoreFuncDecl (decl : Imperative.PureFunc Boole.Expression) : Imperative.PureFunc Core.Expression :=
  { name := toCoreIdent decl.name
    inputs := decl.inputs.map fun (k, v) => (toCoreIdent k, v)
    output := decl.output }

def toCoreStmt (s : Boole.Statement) : Core.Statement :=
  match s with
  | .cmd c => .cmd (toCoreCmd c)
  | .block l b md => .block l (toCoreBlock b) (toCoreMetaData md)
  | .ite cond thenb elseb md => .ite (toCoreExpr cond) (toCoreBlock thenb) (toCoreBlock elseb) (toCoreMetaData md)
  | .loop guard measure invariant body md =>
    .loop (toCoreExpr guard) (measure.map toCoreExpr) (invariant.map toCoreExpr) (toCoreBlock body) (toCoreMetaData md)
  | .for var ty init guard step measure invariant body md =>
    let init := .cmd (.cmd (.init (toCoreIdent var) ty (toCoreExpr init)))
    let step := .cmd (.cmd (.set (toCoreIdent var) (toCoreExpr step)))
    let body := (toCoreBlock body) ++ [step]
    let loop := .loop (toCoreExpr guard) (measure.map toCoreExpr) (invariant.map toCoreExpr) body
    .block "for" [init, loop] (toCoreMetaData md)
  | .forto dir var ty init limit step measure invariant body md =>
    let init := .cmd (.cmd (.init (toCoreIdent var) ty (toCoreExpr init)))
    let guard := Lambda.LExpr.mkApp () Core.intLeOp [.fvar () ⟨var.name, .unres⟩ none, toCoreExpr limit]
    let step := match step with
      | none => Lambda.LExpr.intConst () 1
      | some e => toCoreExpr e
    let op := if dir then Core.intAddOp else Core.intSubOp
    let step := Lambda.LExpr.mkApp () op [.fvar () ⟨var.name, .unres⟩ none, step]
    let step := .cmd (.cmd (.set (toCoreIdent var) step))
    let body := (toCoreBlock body) ++ [step]
    let loop := .loop guard (measure.map toCoreExpr) (invariant.map toCoreExpr) body
    .block "for" [init, loop] (toCoreMetaData md)
  | .goto label md => .goto label (toCoreMetaData md)
  | .funcDecl decl md => .funcDecl (toCoreFuncDecl decl) (toCoreMetaData md)

def toCoreBlock (bss : Boole.Block Boole.Expression Boole.Command) : Imperative.Block Core.Expression Core.Command :=
  let ss : List (Core.Statement) := bss.map fun s =>
    toCoreStmt s
  ss

end

def toCoreFunction (f : Boole.Function) : Core.Function :=
  { name     := toCoreIdent f.name
    typeArgs := f.typeArgs
    inputs   := f.inputs.map fun (k, v) => (toCoreIdent k, v)
    output   := f.output
    body     := f.body.map toCoreExpr
    attr     := f.attr
    concreteEval := f.concreteEval.map fun f md es => (f (ofCoreLParamsMetaData md) (es.map ofCoreExpr)).map toCoreExpr
    axioms   := f.axioms.map toCoreExpr }

def toCoreProcedureHeader (p : Boole.Procedure.Header) : Core.Procedure.Header :=
  { name     := toCoreIdent p.name
    typeArgs := p.typeArgs
    inputs   := p.inputs.map fun (k, v) => (toCoreIdent k, v)
    outputs  := p.outputs.map fun (k, v) => (toCoreIdent k, v) }

def toCoreProcedureCheckAttr (a : Boole.Procedure.CheckAttr) : Core.Procedure.CheckAttr :=
  match a with
  | .Free => .Free
  | .Default => .Default

def toCoreProcedureCheck (c : Boole.Procedure.Check) : Core.Procedure.Check :=
  { expr := toCoreExpr c.expr
    attr := toCoreProcedureCheckAttr c.attr }

def toCoreLabel (l : Boole.BooleLabel) : Core.CoreLabel :=
  l

def toCoreProcedureSpec (spec : Boole.Procedure.Spec) : Core.Procedure.Spec :=
  { modifies      := spec.modifies.map toCoreIdent
    preconditions  := spec.preconditions.map fun (l, e) => (toCoreLabel l, toCoreProcedureCheck e)
    postconditions := spec.postconditions.map fun (l, e) => (toCoreLabel l, toCoreProcedureCheck e) }

def toCoreProcedure (p : Boole.Procedure) : Core.Procedure :=
  { header := toCoreProcedureHeader p.header
    spec   := toCoreProcedureSpec p.spec
    body   := p.body.map toCoreStmt }

def toCoreBoundedness (b : Boole.Boundedness) : Core.Boundedness :=
  match b with
  | .Finite => .Finite
  | .Infinite => .Infinite

def toCoreTypeConstructor (tc : Boole.TypeConstructor) : Core.TypeConstructor :=
  { bound := toCoreBoundedness tc.bound
    name  := tc.name
    numargs  := tc.numargs }

def toCoreTypeSynonym (ts : Boole.TypeSynonym) : Core.TypeSynonym :=
  { name := ts.name
    typeArgs := ts.typeArgs
    type := ts.type }

def toCoreLConstr (c : Lambda.LConstr Boole.Visibility) : Lambda.LConstr Core.Visibility :=
  { name := toCoreIdent c.name
    args := c.args.map fun (id, mty) => (toCoreIdent id, mty)
    testerName := c.testerName }

def toCoreLDatatype (dt : Lambda.LDatatype Boole.Visibility) : Lambda.LDatatype Core.Visibility :=
  { name := dt.name
    typeArgs := dt.typeArgs
    constrs := dt.constrs.map toCoreLConstr
    constrs_ne := List.length_map toCoreLConstr ▸ dt.constrs_ne }

def toCoreTypeDecl (td : Boole.TypeDecl) : Core.TypeDecl :=
  match td with
  | .con tc => .con (toCoreTypeConstructor tc)
  | .syn ts => .syn (toCoreTypeSynonym ts)
  | .data ds  => .data (ds.map toCoreLDatatype)

def toCoreAxiom (a : Boole.Axiom) : Core.Axiom :=
  { name := a.name
    e := toCoreExpr a.e }

def toCoreDecl (d : Boole.Decl) : Core.Decl :=
  match d with
  | .var name ty e md => .var (toCoreIdent name) ty (toCoreExpr e) (toCoreMetaData md)
  | .type t md => .type (toCoreTypeDecl t) (toCoreMetaData md)
  | .ax a md => .ax (toCoreAxiom a) (toCoreMetaData md)
  | .distinct l es md => .distinct (toCoreIdent l) (es.map toCoreExpr) (toCoreMetaData md)
  | .proc p md => .proc (toCoreProcedure p) (toCoreMetaData md)
  | .func f md => .func (toCoreFunction f) (toCoreMetaData md)

def toCoreDecls (ds : Boole.Decls) : Core.Decls :=
  ds.map toCoreDecl

def toCoreProgram (program : Boole.Program) : Core.Program :=
  { decls := toCoreDecls program.decls }

def getProgram (p : Strata.Program)
  (ictx : Parser.InputContext) : Boole.Program × Array String :=
  TransM.run ictx (translateProgram p)

def typeCheck (p : Strata.Program) (ictx : Parser.InputContext) (options : Options := Options.default) :
  Except DiagnosticModel Core.Program := do
  let (program, errors) := getProgram p ictx
  if errors.isEmpty then
    Core.typeCheck options (toCoreProgram program)
  else
    panic! s!"DDM Transform Error: {repr errors}"

open Lean.Parser in
def verify
    (env : Strata.Program)
    (ictx : InputContext := Inhabited.default)
    (proceduresToVerify : Option (List String) := none)
    (options : Options := Options.default)
    (moreFns : @Lambda.Factory Boole.BooleLParams := Lambda.Factory.default)
    (tempDir : Option String := .none)
    : IO Core.VCResults := do
  let (program, errors) := Boole.getProgram env ictx
  if errors.isEmpty then
    let runner tempDir :=
      EIO.toIO (fun dm => IO.Error.userError (toString (dm.format (some ictx.fileMap))))
        (Core.verify (toCoreProgram program) tempDir proceduresToVerify options (moreFns.map toCoreFunction))
    match tempDir with
    | .none =>
      IO.FS.withTempDir runner
    | .some p =>
      IO.FS.createDirAll ⟨p⟩
      runner ⟨p⟩
  else
    panic! s!"DDM Transform Error: {repr errors}"

end Strata.Boole
