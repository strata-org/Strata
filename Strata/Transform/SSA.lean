/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase

/-! # SSA (Static Single Assignment) Transformation

Converts Strata Core procedure bodies into SSA form where every variable is
assigned exactly once via `init`. At if-then-else join points, conditional
`init` expressions merge divergent variable versions.

Preconditions: runs after `callElim` and `loopElim`.
SSA is semantics-preserving, so the pipeline phase uses `modelPreserving`.
-/

namespace Core
namespace SSA

open Imperative Lambda

public section

/-- Statistics keys tracked by the SSA transformation. -/
inductive Stats where
  | renamedVars
  | joinPointMerges

#derive_prefixed_toString Stats "SSA"

structure VarInfo where
  ident : Expression.Ident
  ty    : Expression.Ty
  deriving Repr, BEq

abbrev Env := Std.HashMap String VarInfo

structure SSAState where
  counter : Nat := 0
  env : Env := {}
  statistics : Statistics := {}

abbrev SSAM := ExceptT String (StateM SSAState)

def freshIdent (baseName : String) : SSAM Expression.Ident := do
  let st ← get
  let freshName := s!"{baseName}_{st.counter}"
  set { st with counter := st.counter + 1 }
  return ⟨freshName, ()⟩

def bindVar (origName : String) (newIdent : Expression.Ident) (ty : Expression.Ty) : SSAM Unit :=
  modify fun st => { st with env := st.env.insert origName { ident := newIdent, ty := ty } }

def incrStat (key : String) (n : Nat := 1) : SSAM Unit :=
  modify fun st => { st with statistics := st.statistics.increment key n }

def mkFvar (id : Expression.Ident) : Expression.Expr :=
  Lambda.LExpr.fvar ((): ExpressionMetadata) id none

def rewriteExpr (e : Expression.Expr) : SSAM Expression.Expr := do
  let env := (← get).env
  if env.isEmpty then return e
  let sm : Map Expression.Ident Expression.Expr :=
    env.fold (init := Map.empty) fun acc origName info =>
      acc.insert ⟨origName, ()⟩ (mkFvar info.ident)
  return Lambda.LExpr.substFvars e sm

def rewriteExprOrNondet (e : ExprOrNondet Expression) : SSAM (ExprOrNondet Expression) :=
  match e with
  | .det expr => return .det (← rewriteExpr expr)
  | .nondet => return .nondet

def getEnv : SSAM Env := return (← get).env

def setEnv (env : Env) : SSAM Unit :=
  modify fun st => { st with env := env }

/-- Helper to get the identifier from a VarInfo option, with fallback. -/
private def getIdOr (info : Option VarInfo) (fallback : Option VarInfo) (origName : String)
    : Expression.Ident :=
  match info with
  | some i => i.ident
  | none => match fallback with
    | some i => i.ident
    | none => ⟨origName, ()⟩

/-- Helper to get the type from multiple VarInfo options. -/
private def getTyOr (a b c : Option VarInfo) : Expression.Ty :=
  match a with
  | some i => i.ty
  | none => match b with
    | some i => i.ty
    | none => match c with
      | some i => i.ty
      | none => .forAll [] .bool

/-- Check if a variable changed between two environments. -/
private def varChanged (info pre : Option VarInfo) : Bool :=
  match info, pre with
  | some t, some p => t.ident != p.ident
  | some _, none => true
  | none, _ => false

def transformCmd (cmd : Command) : SSAM (List Statement) := do
  match cmd with
  | .cmd (.init name ty rhs imd) =>
    let rhs' ← rewriteExprOrNondet rhs
    let freshId ← freshIdent name.name
    bindVar name.name freshId ty
    incrStat s!"{Stats.renamedVars}"
    return [Statement.init freshId ty rhs' imd]
  | .cmd (.set name (.det expr) smd) =>
    let expr' ← rewriteExpr expr
    match (← get).env.get? name.name with
    | some info =>
      let freshId ← freshIdent name.name
      let some mty := LTy.toMonoType? info.ty
        | throw s!"SSA: type of '{name.name}' is not a monotype"
      bindVar name.name freshId info.ty
      incrStat s!"{Stats.renamedVars}"
      return [Statement.init freshId (.forAll [] mty) (.det expr') smd]
    | none => throw s!"SSA: variable '{name.name}' not found in environment (set)"
  | .cmd (.set name .nondet smd) =>
    match (← get).env.get? name.name with
    | some info =>
      let freshId ← freshIdent name.name
      let some mty := LTy.toMonoType? info.ty
        | throw s!"SSA: type of '{name.name}' is not a monotype"
      bindVar name.name freshId info.ty
      incrStat s!"{Stats.renamedVars}"
      return [Statement.init freshId (.forAll [] mty) .nondet smd]
    | none => throw s!"SSA: variable '{name.name}' not found in environment (havoc)"
  | .cmd (.assert label b amd) => return [Statement.assert label (← rewriteExpr b) amd]
  | .cmd (.assume label b amd) => return [Statement.assume label (← rewriteExpr b) amd]
  | .cmd (.cover label b cmd') => return [Statement.cover label (← rewriteExpr b) cmd']
  | .call _ _ _ => throw "SSA: unexpected call command (callElim should have run first)"

private def collectAllKeys (envs : List Env) : List String :=
  let hs := envs.foldl (fun acc env =>
    env.fold (init := acc) fun acc k _ => acc.insert k)
    (Std.HashSet.emptyWithCapacity (α := String))
  hs.toList

def emitJoinMerges (condVar : Expression.Ident)
    (preEnv thenEnv elseEnv : Env)
    (md : Imperative.MetaData Expression) : SSAM (List Statement) := do
  let allKeys := collectAllKeys [preEnv, thenEnv, elseEnv]
  let mut merges : List Statement := []
  for origName in allKeys do
    let preInfo := preEnv.get? origName
    let thenInfo := thenEnv.get? origName
    let elseInfo := elseEnv.get? origName
    if varChanged thenInfo preInfo || varChanged elseInfo preInfo then
      let thenId := getIdOr thenInfo preInfo origName
      let elseId := getIdOr elseInfo preInfo origName
      let ty := getTyOr thenInfo elseInfo preInfo
      let some mty := LTy.toMonoType? ty
        | throw s!"SSA: type of '{origName}' is not a monotype at join point"
      let freshId ← freshIdent origName
      let iteExpr : Expression.Expr :=
        Lambda.LExpr.ite () (mkFvar condVar) (mkFvar thenId) (mkFvar elseId)
      merges := merges ++ [Statement.init freshId (.forAll [] mty) (.det iteExpr) md]
      bindVar origName freshId ty
      incrStat s!"{Stats.joinPointMerges}"
  return merges

def emitNondetJoinHavocs (preEnv thenEnv elseEnv : Env)
    (md : Imperative.MetaData Expression) : SSAM (List Statement) := do
  let allKeys := collectAllKeys [preEnv, thenEnv, elseEnv]
  let mut havoces : List Statement := []
  for origName in allKeys do
    let preInfo := preEnv.get? origName
    let thenInfo := thenEnv.get? origName
    let elseInfo := elseEnv.get? origName
    if varChanged thenInfo preInfo || varChanged elseInfo preInfo then
      let ty := getTyOr thenInfo elseInfo preInfo
      let some mty := LTy.toMonoType? ty
        | throw s!"SSA: type of '{origName}' is not a monotype at nondet join"
      let freshId ← freshIdent origName
      havoces := havoces ++ [Statement.init freshId (.forAll [] mty) .nondet md]
      bindVar origName freshId ty
      incrStat s!"{Stats.joinPointMerges}"
  return havoces

def initEnvFromProcedure (proc : Procedure) : SSAM Unit := do
  let _ ← (proc.header.inputs : List _).mapM fun (id, mty) =>
    bindVar id.name id (.forAll [] mty)
  let _ ← (proc.header.outputs : List _).mapM fun (id, mty) =>
    bindVar id.name id (.forAll [] mty)

mutual
partial def transformStmt (s : Statement) : SSAM (List Statement) := do
  match s with
  | .cmd cmd => transformCmd cmd
  | .block label stmts md =>
    let stmts' ← transformBlock stmts
    return [Stmt.block label stmts' md]
  | .ite cond thenStmts elseStmts md =>
    match cond with
    | .det condExpr =>
      let condExpr' ← rewriteExpr condExpr
      let condVar ← freshIdent "$ssa_cond"
      let condInit := Statement.init condVar (.forAll [] LMonoTy.bool) (.det condExpr') md
      let preEnv ← getEnv
      let thenStmts' ← transformBlock thenStmts
      let thenEnv ← getEnv
      setEnv preEnv
      let elseStmts' ← transformBlock elseStmts
      let elseEnv ← getEnv
      let merges ← emitJoinMerges condVar preEnv thenEnv elseEnv md
      let iteStmt := Stmt.ite (.det (mkFvar condVar)) thenStmts' elseStmts' md
      return [condInit, iteStmt] ++ merges
    | .nondet =>
      let preEnv ← getEnv
      let thenStmts' ← transformBlock thenStmts
      let thenEnv ← getEnv
      setEnv preEnv
      let elseStmts' ← transformBlock elseStmts
      let elseEnv ← getEnv
      let havoces ← emitNondetJoinHavocs preEnv thenEnv elseEnv md
      return [Stmt.ite .nondet thenStmts' elseStmts' md] ++ havoces
  | .loop _ _ _ _ _ =>
    throw "SSA: unexpected loop statement (loopElim should have run first)"
  | .exit label md => return [Stmt.exit label md]
  | .funcDecl decl md => return [Stmt.funcDecl decl md]
  | .typeDecl tc md => return [Stmt.typeDecl tc md]

partial def transformBlock (stmts : List Statement) : SSAM (List Statement) := do
  let mut result : List Statement := []
  for s in stmts do
    let stmts' ← transformStmt s
    result := result ++ stmts'
  return result
end

def transformProcedure (proc : Procedure) : SSAM Procedure := do
  if proc.body.isEmpty then return proc
  initEnvFromProcedure proc
  let body' ← transformBlock proc.body
  return { proc with body := body' }

def ssaTransform (p : Program) : Except String (Program × Statistics) := do
  let decls ← p.decls.mapM fun d =>
    match d with
    | .proc proc md =>
      let initState : SSAState := {}
      let (result, finalState) := StateT.run (transformProcedure proc) initState
      match result with
      | .ok proc' => .ok (.proc proc' md, finalState.statistics)
      | .error e => .error s!"SSA error in procedure '{proc.header.name}': {e}"
    | other => .ok (other, {})
  let (decls', stats) := decls.foldl (fun (acc, stats) (d, s) =>
    (acc ++ [d], stats.merge s)) ([], {})
  .ok ({ decls := decls' }, stats)

def ssaTransform' (p : Program) : Transform.CoreTransformM (Bool × Program) := do
  match ssaTransform p with
  | .ok (p', stats) =>
    modify fun σ => { σ with statistics := σ.statistics.merge stats }
    return (true, p')
  | .error e => throw e

def ssaPipelinePhase : PipelinePhase where
  transform := ssaTransform'
  phase.name := "SSA"
  phase.getValidation _ := .modelPreserving

end -- public section
end SSA
end Core
