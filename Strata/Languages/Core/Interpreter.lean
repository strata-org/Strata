/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core

/-! # Concrete Interpreter for Strata Core Programs

Runs the existing partial evaluator in `EvalMode.concrete`, which enables
loop iteration and procedure body execution on top of the standard
symbolic evaluation infrastructure.

See `StatementEval.lean` for the `EvalMode`-aware evaluation logic.
-/

namespace Core

open Lambda Imperative Strata
open Std (ToFormat Format format)

/-! ## Interpreter Result -/

/-- Result of interpreting a full program. -/
inductive InterpResult where
  | success (env : Env)
  | assertionFailure (label : String) (expr : Expression.Expr) (env : Env)
  | error (msg : String)
  | stuck (msg : String)
  deriving Inhabited

instance : ToString InterpResult where
  toString
  | .success _ => "success"
  | .assertionFailure label expr _ => s!"assertion failure: {label}: {format expr}"
  | .error msg => s!"error: {msg}"
  | .stuck msg => s!"stuck: {msg}"

/-! ## Default fuel -/

def defaultFuel : Nat := 100000

/-! ## Program-Level Interpreter -/

/-- Set up the interpreter environment from a type-checked program in concrete mode. -/
def initInterpreterEnv (prog : Program) : Except DiagnosticModel Env := do
  let factory ← Core.Factory.addFactory Lambda.Factory.default
  let datatypes := prog.decls.filterMap fun decl =>
    match decl with
    | .type (.data d) _ => some d
    | _ => none
  let σ ← Lambda.LState.init.addFactory factory
  let E := { Env.init with exprEnv := σ, program := prog, evalMode := .concrete }
  E.addDatatypes datatypes

/-- Process top-level declarations (globals, functions, axioms) without
    running procedure bodies. This mirrors `Program.eval` but skips
    `Procedure.eval` (which sets up verification scaffolding). -/
private def processDecls (E : Env) : Env :=
  let E := { E with pathConditions := E.pathConditions.push [] }
  E.program.decls.foldl (fun E decl =>
    match E.error with
    | some _ => E
    | none =>
    match decl with
    | .var name ty init _md =>
      -- Evaluate global variable initialization
      let ssEs := Statement.eval E [] [(.init name ty init #[])]
      match ssEs with
      | (_, E') :: _ => E'
      | [] => E
    | .type _ _ => E
    | .ax a _ =>
      { E with pathConditions := E.pathConditions.insert (toString a.name) a.e }
    | .distinct _ es _ =>
      { E with distinct := es :: E.distinct }
    | .func f _md =>
      match E.addFactoryFunc f with
      | .ok E' => E'
      | .error _ => E
    | .recFuncBlock fs _md =>
      fs.foldl (fun E f =>
        match E.addFactoryFunc f with
        | .ok E' => E'
        | .error _ => E) E
    | .proc _ _ => E  -- Don't evaluate procedures at declaration time
  ) E

/-- Interpret a specific procedure by name from a type-checked program.
    Uses the existing partial evaluator (`Statement.eval`) with
    `evalMode := .concrete`. -/
def interpProcedure (prog : Program) (procName : String)
    (args : List Expression.Expr := [])
    (fuel : Nat := defaultFuel) : InterpResult :=
  match initInterpreterEnv prog with
  | .error e => .error e.message
  | .ok E =>
    let E := { E with exprEnv := { E.exprEnv with config := { E.exprEnv.config with fuel := fuel } } }
    let E := processDecls E
    match E.error with
    | some e => .stuck s!"{format e}"
    | none =>
    match Program.Procedure.find? prog ⟨procName, ()⟩ with
    | none => .error s!"procedure '{procName}' not found"
    | some proc =>
      if proc.body.isEmpty then .error s!"procedure '{procName}' has no body"
      else
        -- Bind arguments to formals in a new scope
        let argVals := args.map E.exprEval
        let formalBindings : List (CoreIdent × (Option LMonoTy × Expression.Expr)) :=
          proc.header.inputs.keys.zip proc.header.inputs.values |>.zip argVals
          |>.map fun ((name, ty), val) => (name, (some ty, val))
        let outputBindings : List (CoreIdent × (Option LMonoTy × Expression.Expr)) :=
          proc.header.outputs.keys.zip proc.header.outputs.values
          |>.map fun (name, ty) => (name, (some ty, LExpr.fvar () name none))
        let E := { E with
          exprEnv := { E.exprEnv with
            state := E.exprEnv.state.push (List.append formalBindings outputBindings) },
          pathConditions := E.pathConditions.push [] }
        -- Execute the body directly (no precondition/postcondition scaffolding)
        let ssEs := Statement.eval E [] proc.body
        match ssEs with
        | [] => .stuck "procedure body evaluation produced no results"
        | (_, E') :: _ =>
          match E'.error with
          | some (.AssertFail label expr) => .assertionFailure label expr E'
          | some (.OutOfFuel) => .stuck "out of fuel"
          | some e => .stuck s!"{format e}"
          | none => .success E'

/-- Read the value of a variable from an `InterpResult`. -/
def InterpResult.getValue? (r : InterpResult) (name : String) : Option Expression.Expr :=
  match r with
  | .success E => (E.exprEnv.state.find? ⟨name, ()⟩).map (·.snd)
  | .assertionFailure _ _ E => (E.exprEnv.state.find? ⟨name, ()⟩).map (·.snd)
  | _ => none

end Core
