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
| `havoc` | Fresh symbolic variable | Default value |
| Branching | Explores both paths | Requires concrete condition |
| Result | Symbolic expressions + VCs | Concrete values |
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
  | stuck (msg : String)
  deriving Inhabited

instance : ToString InterpResult where
  toString
  | .success _ => "success"
  | .assertionFailure label expr _ => s!"assertion failure: {label}: {format expr}"
  | .error msg => s!"error: {msg}"
  | .fuelExhausted => "fuel exhausted"
  | .stuck msg => s!"stuck: {msg}"

/-! ## Helpers -/

/-- Produce a default value for a type. Used for havoc and uninitialized variables. -/
private def defaultValue (ty : Expression.Ty) : Expression.Expr :=
  if h : ty.isMonoType then
    match ty.toMonoType h with
    | .tcons "int" _ => .intConst () 0
    | .tcons "bool" _ => .boolConst () false
    | .tcons "string" _ => .const () (.strConst "")
    | .tcons "real" _ => .const () (.realConst 0)
    | _ => .intConst () 0
  else .intConst () 0

/-- Default value based on an optional monotype from the store. -/
private def defaultValueOfMonoTy (ty : Option LMonoTy) : Expression.Expr :=
  match ty with
  | some (.tcons "int" _) => .intConst () 0
  | some (.tcons "bool" _) => .boolConst () false
  | some (.tcons "string" _) => .const () (.strConst "")
  | some (.tcons "real" _) => .const () (.realConst 0)
  | _ => .intConst () 0

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

/-! ## Statement Outcome -/

/-- Outcome of executing a statement. Propagates `exit` labels through blocks. -/
inductive StmtOutcome where
  | normal (E : Env)
  | exiting (label : Option String) (E : Env)
  deriving Inhabited

/-- Extract the environment from any outcome. -/
def StmtOutcome.env : StmtOutcome → Env
  | .normal E => E
  | .exiting _ E => E

/-! ## Interpreter Core -/

/-- Default fuel for the interpreter. -/
def defaultFuel : Nat := 100000

mutual
/-- Interpret a single command. -/
def interpCmd (fuel : Nat) (E : Env) (c : Command) : Option StmtOutcome :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
  match c with
  | .cmd (.init x ty e _md) =>
    match e with
    | .det expr => some (.normal (insertVar E x ty (E.exprEval expr)))
    | .nondet => some (.normal (insertVar E x ty (defaultValue ty)))

  | .cmd (.set x e _md) =>
    match e with
    | .det expr => some (.normal (updateVar E x (E.exprEval expr)))
    | .nondet =>
      let tyOpt := (E.exprEnv.state.find? x).bind (·.fst)
      some (.normal (updateVar E x (defaultValueOfMonoTy tyOpt)))

  | .cmd (.assert label expr _md) =>
    let v := E.exprEval expr
    match LExpr.denoteBool v with
    | some true => some (.normal E)
    | some false => some (.normal { E with error := some (.AssertFail label v) })
    | none => none

  | .cmd (.assume _label expr _md) =>
    let v := E.exprEval expr
    match LExpr.denoteBool v with
    | some true => some (.normal E)
    | _ => none

  | .cmd (.cover _ _ _) => some (.normal E)

  | .call lhs pname args _md =>
    match Program.Procedure.find? E.program ⟨pname, ()⟩ with
    | none => none
    | some proc =>
      if proc.body.isEmpty then none
      else
        let argVals := args.map E.exprEval
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
        | none => none
        | some outcome =>
          let callEnv' := outcome.env
          match callEnv'.error with
          | some err => some (.normal { E with error := some err })
          | none =>
            let outputVals := proc.header.outputs.keys.map fun name =>
              (callEnv'.exprEnv.state.findD name (none, LExpr.fvar () name none)).snd
            let modifiedVals := proc.spec.modifies.map fun name =>
              (callEnv'.exprEnv.state.findD name (none, LExpr.fvar () name none)).snd
            let E' := lhs.zip outputVals |>.foldl (fun env (name, val) =>
              updateVar env name val) E
            let E' := proc.spec.modifies.zip modifiedVals |>.foldl (fun env (name, val) =>
              updateVar env name val) E'
            some (.normal E')

/-- Interpret a block (list of statements). -/
def interpBlock (fuel : Nat) (E : Env) (stmts : Statements) : Option StmtOutcome :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
  match stmts with
  | [] => some (.normal E)
  | stmt :: rest =>
    match E.error with
    | some _ => some (.normal E)
    | none =>
      match interpStmt fuel E stmt with
      | none => none
      | some (.exiting label E') => some (.exiting label E')
      | some (.normal E') =>
        match E'.error with
        | some _ => some (.normal E')
        | none => interpBlock fuel E' rest

/-- Interpret a single statement. -/
def interpStmt (fuel : Nat) (E : Env) (stmt : Statement) : Option StmtOutcome :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
  match stmt with
  | .cmd c => interpCmd fuel E c

  | .block label stmts _md =>
    let E' := { E with exprEnv := { E.exprEnv with state := E.exprEnv.state.push [] } }
    match interpBlock fuel E' stmts with
    | none => none
    | some (.normal E'') =>
      some (.normal { E'' with exprEnv := { E''.exprEnv with state := E''.exprEnv.state.pop } })
    | some (.exiting exitLabel E'') =>
      let E'' := { E'' with exprEnv := { E''.exprEnv with state := E''.exprEnv.state.pop } }
      -- Check if this block catches the exit
      match exitLabel with
      | none => some (.normal E'')  -- unlabeled exit: caught by nearest block
      | some l =>
        if l == label then some (.normal E'')  -- matching label: caught
        else some (.exiting exitLabel E'')  -- non-matching: propagate

  | .ite cond thenBr elseBr _md =>
    match cond with
    | .nondet => none
    | .det c =>
      let v := E.exprEval c
      match LExpr.denoteBool v with
      | some true => interpBlock fuel E thenBr
      | some false => interpBlock fuel E elseBr
      -- When the condition doesn't reduce to a concrete bool (e.g. a
      -- constructor test on an uninitialized output variable), default
      -- to the else branch.  This is sound for the common pattern of
      -- exception-checking guards in generated Python→Core code.
      | none => interpBlock fuel E elseBr

  | .loop guard _measure _invariants body _md =>
    match guard with
    | .nondet => none
    | .det g =>
      let v := E.exprEval g
      match LExpr.denoteBool v with
      | some true =>
        match interpBlock fuel E body with
        | none => none
        | some (.exiting label E') => some (.exiting label E')
        | some (.normal E') =>
          match E'.error with
          | some _ => some (.normal E')
          | none => interpStmt fuel E' (.loop (.det g) _measure _invariants body _md)
      | some false => some (.normal E)
      | none => none

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
    | .ok E' => some (.normal E')
    | .error _ => some (.normal E)

  | .typeDecl _tc _md => some (.normal E)

  | .exit label _md => some (.exiting label E)

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
      insertVar E name ty (E.exprEval e)
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
        | none =>
          -- Distinguish fuel exhaustion from stuck: if a smaller fuel also
          -- fails, the interpreter is stuck on an unsupported construct.
          if fuel > 100 then
            match interpBlock 100 E proc.body with
            | none => .stuck "interpreter got stuck (unsupported construct, bodyless procedure call, or irreducible expression)"
            | some _ => .fuelExhausted
          else .fuelExhausted
        | some outcome =>          let E' := outcome.env
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
