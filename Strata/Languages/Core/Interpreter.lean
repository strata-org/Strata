/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core

/-! # Concrete Interpreter for Strata Core Programs

A fuel-based concrete interpreter that executes Strata Core programs by
actually running procedure bodies and iterating loops, rather than
performing symbolic verification.

## Design

- Uses `interpExpr` for expression evaluation (a thin wrapper around `LExpr.eval`).
- Three mutually recursive functions (`interpStmt`, `interpBlock`, `interpCmd`)
  with a shared `fuel : Nat` parameter decremented on each recursive call.
- Returns a structured `StepResult` distinguishing normal completion, exit
  propagation, fuel exhaustion, and stuck states.
-/

namespace Core

open Lambda Imperative Strata
open Std (ToFormat Format format)

/-! ## Helpers -/

/-- Default value based on an optional monotype from the store. -/
private def defaultValueOfMonoTy (ty : Option LMonoTy) : Expression.Expr :=
  match ty with
  | some (.tcons "int" _) => .intConst () 0
  | some (.tcons "bool" _) => .boolConst () false
  | some (.tcons "string" _) => .const () (.strConst "")
  | some (.tcons "real" _) => .const () (.realConst 0)
  | _ => .intConst () 0

/-- Produce a default value for a type. Used for havoc and uninitialized variables. -/
private def defaultValue (ty : Expression.Ty) : Expression.Expr :=
  if h : ty.isMonoType then
    defaultValueOfMonoTy (ty.toMonoType h)
  else .intConst () 0

/-- Insert a variable with a type into the environment. -/
private def insertVar (E : Env) (x : Expression.Ident) (ty : Expression.Ty)
    (v : Expression.Expr) : Env :=
  if h : ty.isMonoType then
    E.insertInContext (x, some (ty.toMonoType h)) v
  else
    E.insertInContext (x, none) v

/-- Update a variable that already exists in the environment. -/
private def updateVar (E : Env) (x : Expression.Ident) (v : Expression.Expr) : Env :=
  let tyOpt := (E.exprEnv.state.find? x).bind (·.fst)
  E.insertInContext (x, tyOpt) v

/-! ## Expression Evaluation -/

/-- Evaluate an expression using the interpreter's environment.

This is the interpreter's own expression evaluator, defined as a separate
function so that we can later prove it consistent with the small-step
`Lambda.Step` relation from `Strata.DL.Lambda.Semantics`.

Currently delegates to `LExpr.eval` with the fuel and state from `Env`.
-/
def interpExpr (E : Env) (e : Expression.Expr) : Expression.Expr :=
  e.eval E.exprEnv.config.fuel E.exprEnv

/-! ## Step Result -/

/-- Result of a single interpreter step. Carries full information about
    why execution stopped. -/
inductive StepResult where
  /-- Normal completion. -/
  | normal (E : Env)
  /-- An `exit` statement propagating upward. -/
  | exiting (label : Option String) (E : Env)
  /-- Fuel exhausted. -/
  | outOfFuel
  /-- Stuck on an unsupported or irreducible construct. -/
  | stuck (msg : String)
  deriving Inhabited

/-- Extract the environment from a successful outcome, or `none`. -/
def StepResult.env? : StepResult → Option Env
  | .normal E => some E
  | .exiting _ E => some E
  | _ => none

/-! ## Interpreter Result -/

/-- Result of interpreting a full program. -/
inductive InterpResult where
  | success (env : Env)
  | assertionFailure (label : String) (expr : Expression.Expr) (env : Env)
  | error (msg : String)
  | fuelExhausted
  | stuck (msg : String)
  deriving Inhabited

instance : ToString InterpResult where
  toString
  | .success _ => "success"
  | .assertionFailure label expr _ => s!"assertion failure: {label}: {format expr}"
  | .error msg => s!"error: {msg}"
  | .fuelExhausted => "fuel exhausted"
  | .stuck msg => s!"stuck: {msg}"

/-! ## Interpreter Core -/

/-- Default fuel for the interpreter. -/
def defaultFuel : Nat := 10000

mutual
/-- Interpret a single command. -/
def interpCmd (fuel : Nat) (E : Env) (c : Command) : StepResult :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
  match c with
  | .cmd (.init x ty e _md) =>
    match e with
    | .det expr => .normal (insertVar E x ty (interpExpr E expr))
    | .nondet => .normal (insertVar E x ty (defaultValue ty))

  | .cmd (.set x e _md) =>
    match e with
    | .det expr => .normal (updateVar E x (interpExpr E expr))
    | .nondet =>
      let tyOpt := (E.exprEnv.state.find? x).bind (·.fst)
      .normal (updateVar E x (defaultValueOfMonoTy tyOpt))

  | .cmd (.assert label expr _md) =>
    let v := interpExpr E expr
    match LExpr.denoteBool v with
    | some true => .normal E
    | some false => .normal { E with error := some (.AssertFail label v) }
    | none => .stuck s!"assert condition did not reduce to bool: {format v}"

  | .cmd (.assume _label expr _md) =>
    let v := interpExpr E expr
    match LExpr.denoteBool v with
    | some true => .normal E
    | some false => .stuck s!"assume condition is false"
    | none => .stuck s!"assume condition did not reduce to bool: {format v}"

  | .cmd (.cover _ _ _) => .normal E

  | .call lhs pname args _md =>
    match Program.Procedure.find? E.program ⟨pname, ()⟩ with
    | none => .stuck s!"procedure '{pname}' not found"
    | some proc =>
      if proc.body.isEmpty then .stuck s!"procedure '{pname}' has no body"
      else
        let argVals := args.map (interpExpr E)
        let formalBindings : List (CoreIdent × (Option LMonoTy × Expression.Expr)) :=
          proc.header.inputs.keys.zip proc.header.inputs.values |>.zip argVals
          |>.map fun ((name, ty), val) => (name, (some ty, val))
        let outputBindings : List (CoreIdent × (Option LMonoTy × Expression.Expr)) :=
          proc.header.outputs.keys.zip proc.header.outputs.values
          |>.map fun (name, ty) => (name, (some ty, LExpr.fvar () name none))
        let callEnv := { E with
          exprEnv := { E.exprEnv with
            state := E.exprEnv.state.push (formalBindings ++ outputBindings) } }
        match interpBlock fuel callEnv proc.body with
        | .outOfFuel => .outOfFuel
        | .stuck msg => .stuck msg
        | .exiting _ callEnv' | .normal callEnv' =>
          match callEnv'.error with
          | some err => .normal { E with error := some err }
          | none =>
            let outputVals := proc.header.outputs.keys.map fun name =>
              (callEnv'.exprEnv.state.findD name (none, LExpr.fvar () name none)).snd
            let modifiedVals := proc.spec.modifies.map fun name =>
              (callEnv'.exprEnv.state.findD name (none, LExpr.fvar () name none)).snd
            let E' := lhs.zip outputVals |>.foldl (fun env (name, val) =>
              updateVar env name val) E
            let E' := proc.spec.modifies.zip modifiedVals |>.foldl (fun env (name, val) =>
              updateVar env name val) E'
            .normal E'

/-- Interpret a block (list of statements). -/
def interpBlock (fuel : Nat) (E : Env) (stmts : Statements) : StepResult :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
  match stmts with
  | [] => .normal E
  | stmt :: rest =>
    match E.error with
    | some _ => .normal E
    | none =>
      match interpStmt fuel E stmt with
      | .outOfFuel => .outOfFuel
      | .stuck msg => .stuck msg
      | .exiting label E' => .exiting label E'
      | .normal E' =>
        match E'.error with
        | some _ => .normal E'
        | none => interpBlock fuel E' rest

/-- Interpret a single statement. -/
def interpStmt (fuel : Nat) (E : Env) (stmt : Statement) : StepResult :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
  match stmt with
  | .cmd c => interpCmd fuel E c

  | .block label stmts _md =>
    let E' := { E with exprEnv := { E.exprEnv with state := E.exprEnv.state.push [] } }
    match interpBlock fuel E' stmts with
    | .outOfFuel => .outOfFuel
    | .stuck msg => .stuck msg
    | .normal E'' =>
      .normal { E'' with exprEnv := { E''.exprEnv with state := E''.exprEnv.state.pop } }
    | .exiting exitLabel E'' =>
      let E'' := { E'' with exprEnv := { E''.exprEnv with state := E''.exprEnv.state.pop } }
      match exitLabel with
      | none => .normal E''
      | some l =>
        if l == label then .normal E''
        else .exiting exitLabel E''

  | .ite cond thenBr elseBr _md =>
    match cond with
    | .nondet => .stuck "nondeterministic ite"
    | .det c =>
      let v := interpExpr E c
      match LExpr.denoteBool v with
      | some true => interpBlock fuel E thenBr
      | some false => interpBlock fuel E elseBr
      | none => interpBlock fuel E elseBr  -- default to else for irreducible guards

  | .loop guard _measure _invariants body _md =>
    match guard with
    | .nondet => .stuck "nondeterministic loop"
    | .det g =>
      let v := interpExpr E g
      match LExpr.denoteBool v with
      | some true =>
        match interpBlock fuel E body with
        | .outOfFuel => .outOfFuel
        | .stuck msg => .stuck msg
        | .exiting label E' => .exiting label E'
        | .normal E' =>
          match E'.error with
          | some _ => .normal E'
          | none => interpStmt fuel E' (.loop (.det g) _measure _invariants body _md)
      | some false => .normal E
      | none => .stuck s!"loop guard did not reduce to bool: {format v}"

  | .funcDecl decl _md =>
    let paramNames := decl.inputs.map (·.1)
    let func : Lambda.LFunc CoreLParams := {
      name := decl.name,
      typeArgs := decl.typeArgs,
      isConstr := decl.isConstr,
      inputs := decl.inputs.map (fun (id, ty) => (id, Lambda.LTy.toMonoTypeUnsafe ty)),
      output := Lambda.LTy.toMonoTypeUnsafe decl.output,
      body := decl.body.map (Statement.captureFreevars E paramNames),
      attr := decl.attr,
      concreteEval := decl.concreteEval,
      axioms := decl.axioms.map (Statement.captureFreevars E paramNames)
    }
    match E.addFactoryFunc func with
    | .ok E' => .normal E'
    | .error _ => .normal E

  | .typeDecl _tc _md => .normal E

  | .exit label _md => .exiting label E

end

/-! ## Program-Level Interpreter -/

/-- Set up the interpreter environment from a type-checked program. -/
def initInterpreterEnv (prog : Program) : Except DiagnosticModel Env := do
  let factory ← Core.Factory.addFactory Lambda.Factory.default
  let datatypes := prog.decls.filterMap fun decl =>
    match decl with
    | .type (.data d) _ => some d
    | _ => none
  let σ ← Lambda.LState.init.addFactory factory
  let E := { Env.init with exprEnv := σ, program := prog }
  E.addDatatypes datatypes

/-- Process top-level declarations (globals, functions, axioms). -/
def processDecls (E : Env) : Env :=
  E.program.decls.foldl (fun E decl =>
    match E.error with
    | some _ => E
    | none =>
    match decl with
    | .var name ty (.det e) _md =>
      insertVar E name ty (interpExpr E e)
    | .var name ty .nondet _md =>
      insertVar E name ty (defaultValue ty)
    | .func f _md =>
      match E.addFactoryFunc f with
      | .ok E' => E'
      | .error _ => E
    | .recFuncBlock fs _md =>
      fs.foldl (fun E f =>
        match E.addFactoryFunc f with
        | .ok E' => E'
        | .error _ => E) E
    | .ax a _md =>
      { E with pathConditions := E.pathConditions.addInNewest [(toString a.name, a.e)] }
    | _ => E
  ) E

/-- Interpret a specific procedure by name from a type-checked program. -/
def interpProcedure (prog : Program) (procName : String)
    (args : List Expression.Expr := [])
    (fuel : Nat := defaultFuel) : InterpResult :=
  match initInterpreterEnv prog with
  | .error e => .error e.message
  | .ok E =>
    let E := processDecls E
    match Program.Procedure.find? prog ⟨procName, ()⟩ with
    | none => .error s!"procedure '{procName}' not found"
    | some proc =>
      if proc.body.isEmpty then .error s!"procedure '{procName}' has no body"
      else
        let argVals := args.map (interpExpr E)
        let formalBindings : List (CoreIdent × (Option LMonoTy × Expression.Expr)) :=
          proc.header.inputs.keys.zip proc.header.inputs.values |>.zip argVals
          |>.map fun ((name, ty), val) => (name, (some ty, val))
        let outputBindings : List (CoreIdent × (Option LMonoTy × Expression.Expr)) :=
          proc.header.outputs.keys.zip proc.header.outputs.values
          |>.map fun (name, ty) => (name, (some ty, LExpr.fvar () name none))
        let E := { E with
          exprEnv := { E.exprEnv with
            state := E.exprEnv.state.push (formalBindings ++ outputBindings) } }
        match interpBlock fuel E proc.body with
        | .outOfFuel => .fuelExhausted
        | .stuck msg => .stuck msg
        | .exiting _ E' | .normal E' =>
          match E'.error with
          | some (.AssertFail label expr) => .assertionFailure label expr E'
          | some _ => .error "evaluation error"
          | none => .success E'

/-- Read the value of a variable from an `InterpResult`. -/
def InterpResult.getValue? (r : InterpResult) (name : String) : Option Expression.Expr :=
  match r with
  | .success E => (E.exprEnv.state.find? ⟨name, ()⟩).map (·.snd)
  | .assertionFailure _ _ E => (E.exprEnv.state.find? ⟨name, ()⟩).map (·.snd)
  | _ => none

end Core
