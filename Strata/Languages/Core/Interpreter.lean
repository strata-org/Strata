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

- Reuses `Core.Env` and its `exprEval` for expression evaluation.
- Three mutually recursive functions (`interpStmt`, `interpBlock`, `interpCmd`)
  with a shared `fuel : Nat` parameter decremented on each recursive call.
- Returns `none` on fuel exhaustion or stuck states.

## Differences from the Partial Evaluator (`StatementEval.lean`)

| Aspect | Partial Evaluator | Interpreter |
|--------|------------------|-------------|
| Loops | `panic!` | Iterates with fuel bound |
| Calls | Contract inlining | Body execution |
| `havoc` | Fresh symbolic variable | `none` (stuck) |
| Branching | Explores both paths | Requires concrete condition |
| Result | Symbolic expressions + VCs | Concrete values |

## Intentionally Unsupported

- `havoc` / nondeterministic `init` — returns `none` (stuck)
- Nondeterministic `ite` / `loop` — returns `none`
- `exit` with labels — returns `none`
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
  | fuelExhausted
  deriving Inhabited

instance : ToString InterpResult where
  toString
  | .success _ => "success"
  | .assertionFailure label expr _ => s!"assertion failure: {label}: {format expr}"
  | .error msg => s!"error: {msg}"
  | .fuelExhausted => "fuel exhausted"

/-! ## Helpers -/

/-- Produce a default value for a type. Used for uninitialized variable declarations. -/
private def defaultValue (ty : Expression.Ty) : Expression.Expr :=
  if h : ty.isMonoType then
    match ty.toMonoType h with
    | .tcons "int" _ => .intConst () 0
    | .tcons "bool" _ => .boolConst () false
    | .tcons "string" _ => .const () (.strConst "")
    | .tcons "real" _ => .const () (.realConst 0)
    | _ => .intConst () 0  -- fallback
  else .intConst () 0  -- fallback

/-- Insert a variable with an optional type into the environment. -/
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

/-! ## Interpreter Core -/

/-- Default fuel for the interpreter. Large enough for most programs,
    small enough to avoid excessive computation. -/
def defaultFuel : Nat := 100000

mutual
/-- Interpret a single command. Returns updated `Env` or `none` on stuck/fuel. -/
def interpCmd (fuel : Nat) (E : Env) (c : Command) : Option Env :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
  match c with
  | .cmd (.init x ty e _md) =>
    match e with
    | .det expr =>
      let v := E.exprEval expr
      some (insertVar E x ty v)
    | .nondet =>
      -- Uninitialized variable: use a default value based on type
      let v := defaultValue ty
      some (insertVar E x ty v)

  | .cmd (.set x e _md) =>
    match e with
    | .det expr =>
      let v := E.exprEval expr
      some (updateVar E x v)
    | .nondet => none  -- havoc not supported

  | .cmd (.assert label expr _md) =>
    let v := E.exprEval expr
    match LExpr.denoteBool v with
    | some true => some E
    | some false => some { E with error := some (.AssertFail label v) }
    | none => none  -- condition didn't reduce to bool

  | .cmd (.assume _label expr _md) =>
    let v := E.exprEval expr
    match LExpr.denoteBool v with
    | some true => some E
    | some false => none  -- assumption violated: execution stuck
    | none => none  -- condition didn't reduce to bool

  | .cmd (.cover _ _ _) => some E  -- no-op for concrete execution

  | .call lhs pname args _md =>
    match Program.Procedure.find? E.program ⟨pname, ()⟩ with
    | none => none
    | some proc =>
      if proc.body.isEmpty then none  -- bodyless procedure
      else
        -- Evaluate arguments
        let argVals := args.map E.exprEval
        -- Build formal parameter scope: [(ident, (some ty, val))]
        let formalBindings : List (CoreIdent × (Option LMonoTy × Expression.Expr)) :=
          proc.header.inputs.keys.zip proc.header.inputs.values |>.zip argVals
          |>.map fun ((name, ty), val) => (name, (some ty, val))
        -- Build output variable scope (initialized to fresh fvars)
        let outputBindings : List (CoreIdent × (Option LMonoTy × Expression.Expr)) :=
          proc.header.outputs.keys.zip proc.header.outputs.values
          |>.map fun (name, ty) => (name, (some ty, LExpr.fvar () name none))
        -- Push scope and execute body
        let callEnv := { E with
          exprEnv := { E.exprEnv with
            state := E.exprEnv.state.push (formalBindings ++ outputBindings) } }
        match interpBlock fuel callEnv proc.body with
        | none => none
        | some callEnv' =>
          match callEnv'.error with
          | some err => some { E with error := some err }
          | none =>
            -- Read output values from callee scope
            let outputVals := proc.header.outputs.keys.map fun name =>
              (callEnv'.exprEnv.state.findD name (none, LExpr.fvar () name none)).snd
            -- Read modified globals
            let modifiedVals := proc.spec.modifies.map fun name =>
              (callEnv'.exprEnv.state.findD name (none, LExpr.fvar () name none)).snd
            -- Update caller's LHS and modified globals
            let E' := lhs.zip outputVals |>.foldl (fun env (name, val) =>
              updateVar env name val) E
            let E' := proc.spec.modifies.zip modifiedVals |>.foldl (fun env (name, val) =>
              updateVar env name val) E'
            some E'

/-- Interpret a block (list of statements). -/
def interpBlock (fuel : Nat) (E : Env) (stmts : Statements) : Option Env :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
  match stmts with
  | [] => some E
  | stmt :: rest =>
    match E.error with
    | some _ => some E  -- short-circuit on error
    | none =>
      match interpStmt fuel E stmt with
      | none => none
      | some E' =>
        match E'.error with
        | some _ => some E'
        | none => interpBlock fuel E' rest

/-- Interpret a single statement. -/
def interpStmt (fuel : Nat) (E : Env) (stmt : Statement) : Option Env :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
  match stmt with
  | .cmd c => interpCmd fuel E c

  | .block _label stmts _md =>
    let E' := { E with exprEnv := { E.exprEnv with state := E.exprEnv.state.push [] } }
    match interpBlock fuel E' stmts with
    | none => none
    | some E'' =>
      some { E'' with exprEnv := { E''.exprEnv with state := E''.exprEnv.state.pop } }

  | .ite cond thenBr elseBr _md =>
    match cond with
    | .nondet => none
    | .det c =>
      let v := E.exprEval c
      match LExpr.denoteBool v with
      | some true => interpBlock fuel E thenBr
      | some false => interpBlock fuel E elseBr
      | none => none

  | .loop guard _measure _invariants body _md =>
    match guard with
    | .nondet => none
    | .det g =>
      let v := E.exprEval g
      match LExpr.denoteBool v with
      | some true =>
        match interpBlock fuel E body with
        | none => none
        | some E' =>
          match E'.error with
          | some _ => some E'
          | none => interpStmt fuel E' (.loop (.det g) _measure _invariants body _md)
      | some false => some E
      | none => none

  | .funcDecl decl _md =>
    -- Capture free variables and add function to factory (same as StatementEval)
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
    | .ok E' => some E'
    | .error _ => some E  -- silently skip on error (e.g. duplicate)

  | .typeDecl _tc _md => some E  -- no runtime effect

  | .exit _ _ => none  -- exit not yet supported

end

/-! ## Program-Level Interpreter -/

/-- Set up the interpreter environment from a type-checked program.
    Mirrors `typeCheckAndPartialEval` but doesn't run the partial evaluator. -/
def initInterpreterEnv (prog : Program) : Except DiagnosticModel Env := do
  let factory ← Core.Factory.addFactory Lambda.Factory.default
  let datatypes := prog.decls.filterMap fun decl =>
    match decl with
    | .type (.data d) _ => some d
    | _ => none
  let σ ← Lambda.LState.init.addFactory factory
  let E := { Env.init with exprEnv := σ, program := prog }
  E.addDatatypes datatypes

/-- Process top-level declarations (globals, functions, axioms) to build
    the initial interpreter state. Does not execute procedure bodies. -/
def processDecls (E : Env) : Env :=
  E.program.decls.foldl (fun E decl =>
    match E.error with
    | some _ => E
    | none =>
    match decl with
    | .var name ty (.det e) _md =>
      let v := E.exprEval e
      insertVar E name ty v
    | .var name ty .nondet _md =>
      insertVar E name ty (LExpr.fvar () name none)
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
        -- Evaluate arguments and bind to formals
        let argVals := args.map E.exprEval
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
        | none => .fuelExhausted
        | some E' =>
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
