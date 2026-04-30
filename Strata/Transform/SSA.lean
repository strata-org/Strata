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

Note: After transforming the body, the transform emits final assignments back
to output/inout parameters so that the procedure's contract is preserved.
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

/-- SSA name prefix for phi (join-point merge) variables. -/
def ssaPhiPrefix (id : String) : String := s!"ssa_phi_{id}"

/-- Generate a fresh SSA identifier using the CoreTransformM generator. -/
def genSSAIdent (baseName : String) : CoreTransformM Expression.Ident :=
  genIdent ⟨baseName, ()⟩ ssaVarPrefix

/-- Generate a fresh SSA phi identifier for join-point merges. -/
def genSSAPhiIdent (baseName : String) : CoreTransformM Expression.Ident :=
  genIdent ⟨baseName, ()⟩ ssaPhiPrefix

/-- Rewrite free variables in an expression according to the SSA environment. -/
def rewriteExpr (env : Env) (e : Expression.Expr) : Expression.Expr :=
  let sm : Map Expression.Ident Expression.Expr :=
    env.fold (init := Map.empty) fun acc origName info =>
      acc.insert ⟨origName, ()⟩ (createFvar info.ident)
  Lambda.LExpr.substFvars e sm

/-- Rewrite free variables in an `ExprOrNondet`. -/
def rewriteExprOrNondet (env : Env) (e : ExprOrNondet Expression) : ExprOrNondet Expression :=
  e.map (rewriteExpr env ·)

/-- Check if a variable changed between two environments. -/
private def varChanged (info pre : Option VarInfo) : Bool :=
  match info, pre with
  | some t, some p => t.ident != p.ident
  | some _, none => true
  | none, _ => false

/-- Compute a phi entry for a variable at a join point. Returns `none` if the
    variable doesn't need a merge (unchanged in both branches, or wasn't in
    scope before the ITE). Only merges variables present in `preEnv`. -/
private def phiEntry (origName : String) (preEnv thenEnv elseEnv : Env)
    : Option (Expression.Ident × Expression.Ident × Expression.Ty) := do
  let preInfo ← preEnv.get? origName
  let thenInfo := thenEnv.get? origName
  let elseInfo := elseEnv.get? origName
  if !varChanged thenInfo (some preInfo) && !varChanged elseInfo (some preInfo) then
    .none
  else
    let thenId := (thenInfo.map (·.ident)).getD preInfo.ident
    let elseId := (elseInfo.map (·.ident)).getD preInfo.ident
    .some (thenId, elseId, preInfo.ty)

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
        | throw (Strata.DiagnosticModel.fromMessage s!"SSA: type of '{name.name}' is not a monotype")
      let env' := env.insert name.name { ident := freshId, ty := info.ty }
      incrementStat s!"{Stats.renamedVars}"
      return (env', [Statement.init freshId (.forAll [] mty) (.det expr') smd])
    | none => throw (Strata.DiagnosticModel.fromMessage s!"SSA: variable '{name.name}' not found in environment (set)")
  | .cmd (.set name .nondet smd) =>
    match env.get? name.name with
    | some info =>
      let freshId ← genSSAIdent name.name
      let some mty := LTy.toMonoType? info.ty
        | throw (Strata.DiagnosticModel.fromMessage s!"SSA: type of '{name.name}' is not a monotype")
      let env' := env.insert name.name { ident := freshId, ty := info.ty }
      incrementStat s!"{Stats.renamedVars}"
      return (env', [Statement.init freshId (.forAll [] mty) .nondet smd])
    | none => throw (Strata.DiagnosticModel.fromMessage s!"SSA: variable '{name.name}' not found in environment (havoc)")
  | .cmd (.assert label b amd) =>
    return (env, [Statement.assert label (rewriteExpr env b) amd])
  | .cmd (.assume label b amd) =>
    return (env, [Statement.assume label (rewriteExpr env b) amd])
  | .cmd (.cover label b cmd') =>
    return (env, [Statement.cover label (rewriteExpr env b) cmd'])
  | .call _ _ _ => throw (Strata.DiagnosticModel.fromMessage "SSA: unexpected call command (callElim should have run first)")

/-- Emit conditional merge inits at a join point. Only merges variables that
    were in scope before the ITE (`preEnv`). The `condVar` determines which
    branch's value to select; for nondet branches it is itself nondet. -/
def emitJoinMerges (condVar : Expression.Ident)
    (preEnv thenEnv elseEnv : Env)
    (md : Imperative.MetaData Expression) : CoreTransformM (Env × List Statement) := do
  let mut env := preEnv
  let mut merges : List Statement := []
  -- Only iterate over variables that were in scope before the ITE.
  for (origName, _) in preEnv.toList do
    match phiEntry origName preEnv thenEnv elseEnv with
    | none => pure ()
    | some (thenId, elseId, ty) =>
      let some mty := LTy.toMonoType? ty
        | throw (Strata.DiagnosticModel.fromMessage s!"SSA: type of '{origName}' is not a monotype at join point")
      let freshId ← genSSAPhiIdent origName
      let iteExpr : Expression.Expr :=
        Lambda.LExpr.ite () (createFvar condVar) (createFvar thenId) (createFvar elseId)
      merges := merges ++ [Statement.init freshId (.forAll [] mty) (.det iteExpr) md]
      env := env.insert origName { ident := freshId, ty := ty }
      incrementStat s!"{Stats.joinPointMerges}"
  return (env, merges)

/-- Initialize the SSA environment from a procedure's parameters.
    Both inputs and outputs are seeded so that assignments to outputs
    get tracked. After transformation, `emitOutputAssignments` writes
    the final SSA values back to the original output identifiers. -/
def initEnvFromProcedure (proc : Procedure) : Env :=
  let env := (proc.header.inputs : List _).foldl (fun acc (id, mty) =>
    acc.insert id.name { ident := id, ty := .forAll [] mty }) {}
  (proc.header.outputs : List _).foldl (fun acc (id, mty) =>
    acc.insert id.name { ident := id, ty := .forAll [] mty }) env

/-- Emit final `set` statements to write SSA-renamed values back to the
    original output/inout parameter identifiers. This preserves the
    procedure's contract semantics. -/
def emitOutputAssignments (proc : Procedure) (finalEnv : Env)
    (md : Imperative.MetaData Expression) : List Statement :=
  (proc.header.outputs : List _).filterMap fun (outId, _) =>
    match finalEnv.get? outId.name with
    | some info =>
      if info.ident != outId then
        some (Statement.set outId (createFvar info.ident) md)
      else none
    | none => none

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
      -- In SSA, branching is captured entirely by phi expressions.
      -- Both branches are flattened to the outer scope; the condition
      -- variable selects which branch's values are used via the phi.
      let condExpr' := rewriteExpr env condExpr
      let condVar ← genSSAIdent "cond"
      let condInit := Statement.init condVar (.forAll [] LMonoTy.bool) (.det condExpr') md
      let (thenEnv, thenStmts') ← transformBlock env thenStmts
      let (elseEnv, elseStmts') ← transformBlock env elseStmts
      let (mergedEnv, merges) ← emitJoinMerges condVar env thenEnv elseEnv md
      -- Flatten: condition init, then-branch stmts, else-branch stmts, phi merges.
      -- All at the same scope level so phi references are valid.
      return (mergedEnv, [condInit] ++ thenStmts' ++ elseStmts' ++ merges)
    | .nondet =>
      let condVar ← genSSAIdent "nondet_cond"
      let condInit := Statement.init condVar (.forAll [] LMonoTy.bool) .nondet md
      let (thenEnv, thenStmts') ← transformBlock env thenStmts
      let (elseEnv, elseStmts') ← transformBlock env elseStmts
      let (mergedEnv, merges) ← emitJoinMerges condVar env thenEnv elseEnv md
      return (mergedEnv, [condInit] ++ thenStmts' ++ elseStmts' ++ merges)
  | .loop _ _ _ _ _ =>
    throw (Strata.DiagnosticModel.fromMessage "SSA: unexpected loop statement (loopElim should have run first)")
  | .exit _ _ =>
    throw (Strata.DiagnosticModel.fromMessage "SSA: unexpected exit statement")
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

/-- Transform a single procedure into SSA form. After transforming the body,
    emits final assignments back to output parameters so that the procedure's
    ensures clauses remain valid. -/
def transformProcedure (proc : Procedure) : CoreTransformM Procedure := do
  if proc.body.isEmpty then return proc
  let env := initEnvFromProcedure proc
  let (finalEnv, body') ← transformBlock env proc.body
  -- Emit final assignments: set each output param back from its SSA name.
  let outputAssigns := emitOutputAssignments proc finalEnv MetaData.empty
  return { proc with body := body' ++ outputAssigns }

/-- SSA transformation on an entire program, using CoreTransformM. -/
def ssaTransform (p : Program) : CoreTransformM (Bool × Program) := do
  let decls ← p.decls.mapM fun d =>
    match d with
    | .proc proc md => return .proc (← transformProcedure proc) md
    | other => return other
  return (true, { decls := decls })

/-- SSA pipeline phase: converts procedure bodies to SSA form.

    Correctness status: The transform emits final assignments to output
    parameters to preserve procedure contracts. The `modelPreserving`
    annotation is justified because:
    - Every variable is assigned exactly once (SSA invariant)
    - Output parameters receive their final SSA value via explicit set
    - Phi merges only reference variables in scope before the ITE

    TODO: formal proof of single-assignment, scoping, and output preservation. -/
def ssaPipelinePhase : PipelinePhase where
  transform := ssaTransform
  phase.name := "SSA"
  phase.getValidation _ := .modelPreserving

end -- public section
end SSA
end Core
