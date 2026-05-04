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
open Core.Transform

public section

/-- Statistics keys tracked by the SSA transformation. -/
inductive Stats where
  | renamedVars
  | joinPointMerges

#derive_prefixed_toString Stats "SSA"

/-- An entry in the SSA environment: the current versioned identifier and its type. -/
structure VarInfo where
  ident : Expression.Ident
  ty    : Expression.Ty
  deriving Repr, BEq

/-- The SSA environment maps original variable names to their current version and type. -/
abbrev Env := Std.HashMap String VarInfo

/-- SSA name prefix for fresh variables. -/
def ssaVarPrefix (id : String) : String := s!"ssa_{id}"

/-- Generate a fresh SSA identifier using the CoreTransformM generator. -/
def genSSAIdent (baseName : String) : CoreTransformM Expression.Ident :=
  genIdent ⟨baseName, ()⟩ ssaVarPrefix

/-- Rewrite free variables in an expression according to the SSA environment. -/
def rewriteExpr (env : Env) (e : Expression.Expr) : Expression.Expr :=
  if env.isEmpty then e
  else
    let sm : Map Expression.Ident Expression.Expr :=
      env.fold (init := Map.empty) fun acc origName info =>
        acc.insert ⟨origName, ()⟩ (createFvar info.ident)
    Lambda.LExpr.substFvars e sm

/-- Rewrite free variables in an `ExprOrNondet`. -/
def rewriteExprOrNondet (env : Env) (e : ExprOrNondet Expression) : ExprOrNondet Expression :=
  match e with
  | .det expr => .det (rewriteExpr env expr)
  | .nondet => .nondet

/-- Helper to get the identifier from a VarInfo option, with fallback. -/
private def getIdOr (info fallback : Option VarInfo) (origName : String)
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

/-- Transform a single command in SSA form. Returns updated env and new statements. -/
def transformCmd (env : Env) (cmd : Command) : CoreTransformM (Env × List Statement) := do
  match cmd with
  | .cmd (.init name ty rhs imd) =>
    let rhs' := rewriteExprOrNondet env rhs
    let freshId ← genSSAIdent name.name
    let env' := env.insert name.name { ident := freshId, ty := ty }
    incrementStat s!"{Stats.renamedVars}"
    return (env', [Statement.init freshId ty rhs' imd])
  | .cmd (.set name (.det expr) smd) =>
    let expr' := rewriteExpr env expr
    match env.get? name.name with
    | some info =>
      let freshId ← genSSAIdent name.name
      let some mty := LTy.toMonoType? info.ty
        | throw s!"SSA: type of '{name.name}' is not a monotype"
      let env' := env.insert name.name { ident := freshId, ty := info.ty }
      incrementStat s!"{Stats.renamedVars}"
      return (env', [Statement.init freshId (.forAll [] mty) (.det expr') smd])
    | none => throw s!"SSA: variable '{name.name}' not found in environment (set)"
  | .cmd (.set name .nondet smd) =>
    match env.get? name.name with
    | some info =>
      let freshId ← genSSAIdent name.name
      let some mty := LTy.toMonoType? info.ty
        | throw s!"SSA: type of '{name.name}' is not a monotype"
      let env' := env.insert name.name { ident := freshId, ty := info.ty }
      incrementStat s!"{Stats.renamedVars}"
      return (env', [Statement.init freshId (.forAll [] mty) .nondet smd])
    | none => throw s!"SSA: variable '{name.name}' not found in environment (havoc)"
  | .cmd (.assert label b amd) =>
    return (env, [Statement.assert label (rewriteExpr env b) amd])
  | .cmd (.assume label b amd) =>
    return (env, [Statement.assume label (rewriteExpr env b) amd])
  | .cmd (.cover label b cmd') =>
    return (env, [Statement.cover label (rewriteExpr env b) cmd'])
  | .call _ _ _ => throw "SSA: unexpected call command (callElim should have run first)"

private def collectAllKeys (envs : List Env) : List String :=
  let hs := envs.foldl (fun acc env =>
    env.fold (init := acc) fun acc k _ => acc.insert k)
    (Std.HashSet.emptyWithCapacity (α := String))
  hs.toList

/-- Emit conditional merge inits at a deterministic join point. -/
def emitJoinMerges (condVar : Expression.Ident)
    (preEnv thenEnv elseEnv : Env)
    (md : Imperative.MetaData Expression) : CoreTransformM (Env × List Statement) := do
  let allKeys := collectAllKeys [preEnv, thenEnv, elseEnv]
  let mut env := thenEnv  -- start from one branch, will be overwritten for changed vars
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
      let freshId ← genSSAIdent origName
      let iteExpr : Expression.Expr :=
        Lambda.LExpr.ite () (createFvar condVar) (createFvar thenId) (createFvar elseId)
      merges := merges ++ [Statement.init freshId (.forAll [] mty) (.det iteExpr) md]
      env := env.insert origName { ident := freshId, ty := ty }
      incrementStat s!"{Stats.joinPointMerges}"
    else
      -- Variable unchanged: keep the pre-branch version
      match preInfo with
      | some info => env := env.insert origName info
      | none => pure ()
  return (env, merges)

/-- Emit havoc inits at a nondet join point. -/
def emitNondetJoinHavocs (preEnv thenEnv elseEnv : Env)
    (md : Imperative.MetaData Expression) : CoreTransformM (Env × List Statement) := do
  let allKeys := collectAllKeys [preEnv, thenEnv, elseEnv]
  let mut env := preEnv
  let mut havoces : List Statement := []
  for origName in allKeys do
    let preInfo := preEnv.get? origName
    let thenInfo := thenEnv.get? origName
    let elseInfo := elseEnv.get? origName
    if varChanged thenInfo preInfo || varChanged elseInfo preInfo then
      let ty := getTyOr thenInfo elseInfo preInfo
      let some mty := LTy.toMonoType? ty
        | throw s!"SSA: type of '{origName}' is not a monotype at nondet join"
      let freshId ← genSSAIdent origName
      havoces := havoces ++ [Statement.init freshId (.forAll [] mty) .nondet md]
      env := env.insert origName { ident := freshId, ty := ty }
      incrementStat s!"{Stats.joinPointMerges}"
  return (env, havoces)

/-- Initialize the SSA environment from a procedure's parameters. -/
def initEnvFromProcedure (proc : Procedure) : Env :=
  let env := (proc.header.inputs : List _).foldl (fun acc (id, mty) =>
    acc.insert id.name { ident := id, ty := .forAll [] mty }) {}
  (proc.header.outputs : List _).foldl (fun acc (id, mty) =>
    acc.insert id.name { ident := id, ty := .forAll [] mty }) env

mutual
partial def transformStmt (env : Env) (s : Statement) : CoreTransformM (Env × List Statement) := do
  match s with
  | .cmd cmd => transformCmd env cmd
  | .block label stmts md =>
    let (env', stmts') ← transformBlock env stmts
    return (env', [Stmt.block label stmts' md])
  | .ite cond thenStmts elseStmts md =>
    match cond with
    | .det condExpr =>
      let condExpr' := rewriteExpr env condExpr
      let condVar ← genSSAIdent "$ssa_cond"
      let condInit := Statement.init condVar (.forAll [] LMonoTy.bool) (.det condExpr') md
      let (thenEnv, thenStmts') ← transformBlock env thenStmts
      let (elseEnv, elseStmts') ← transformBlock env elseStmts
      let (mergedEnv, merges) ← emitJoinMerges condVar env thenEnv elseEnv md
      let iteStmt := Stmt.ite (.det (createFvar condVar)) thenStmts' elseStmts' md
      return (mergedEnv, [condInit, iteStmt] ++ merges)
    | .nondet =>
      let (thenEnv, thenStmts') ← transformBlock env thenStmts
      let (elseEnv, elseStmts') ← transformBlock env elseStmts
      let (mergedEnv, havoces) ← emitNondetJoinHavocs env thenEnv elseEnv md
      return (mergedEnv, [Stmt.ite .nondet thenStmts' elseStmts' md] ++ havoces)
  | .loop _ _ _ _ _ =>
    throw "SSA: unexpected loop statement (loopElim should have run first)"
  | .exit label md => return (env, [Stmt.exit label md])
  | .funcDecl decl md => return (env, [Stmt.funcDecl decl md])
  | .typeDecl tc md => return (env, [Stmt.typeDecl tc md])

partial def transformBlock (env : Env) (stmts : List Statement)
    : CoreTransformM (Env × List Statement) := do
  let mut curEnv := env
  let mut result : List Statement := []
  for s in stmts do
    let (env', stmts') ← transformStmt curEnv s
    curEnv := env'
    result := result ++ stmts'
  return (curEnv, result)
end

/-- Transform a single procedure into SSA form. -/
def transformProcedure (proc : Procedure) : CoreTransformM Procedure := do
  if proc.body.isEmpty then return proc
  let env := initEnvFromProcedure proc
  let (_, body') ← transformBlock env proc.body
  return { proc with body := body' }

/-- SSA transformation on an entire program, using CoreTransformM. -/
def ssaTransform (p : Program) : CoreTransformM (Bool × Program) := do
  let decls ← p.decls.mapM fun d =>
    match d with
    | .proc proc md => return .proc (← transformProcedure proc) md
    | other => return other
  return (true, { decls := decls })

/-- SSA pipeline phase: converts procedure bodies to SSA form.
    SSA is semantics-preserving, so models are preserved. -/
def ssaPipelinePhase : PipelinePhase where
  transform := ssaTransform
  phase.name := "SSA"
  phase.getValidation _ := .modelPreserving

end -- public section
end SSA
end Core
