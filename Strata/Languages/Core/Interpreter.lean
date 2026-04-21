/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core
import Strata.Languages.Core.CmdEval

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

/-- Update a variable that already exists in the environment. -/
private def updateVar (E : Env) (x : Expression.Ident) (v : Expression.Expr) : Env :=
  let tyOpt := (E.exprEnv.state.find? x).bind (·.fst)
  E.insertInContext (x, tyOpt) v

/-! ## Step Result -/

/-- Result of a single interpreter step. Carries full information about
    why execution stopped. -/
inductive StepResult where
  /-- Normal completion (although E may have .error set). -/
  | normal (E : Env)
  /-- An `exit` statement propagating upward. -/
  | exiting (label : Option String) (E : Env)
  deriving Inhabited

def stuck (E : Env) (message : String) : Env :=
  { E with error := some (EvalError.Misc message) }

/-! ## Expression Evaluation -/

/-- Walk a post-eval expression looking for a stuck redex: a fully-applied
non-constructor factory function whose arguments are all canonical values.
Such a call *should* have reduced during `eval` but didn't (e.g. missing body
or `concreteEval`). Returns the stuck subexpression if found. -/
def findStuckRedex (F : @Lambda.Factory CoreLParams) : Expression.Expr → Option Expression.Expr
  | .const _ _ | .op _ _ _ | .bvar _ _ | .fvar _ _ _ | .abs _ _ _ _ | .quant _ _ _ _ _ _ => none
  | .eq _m e1 e2 =>
    (findStuckRedex F e1).orElse (fun _ => findStuckRedex F e2)
  | .ite _m c t f =>
    (findStuckRedex F c).orElse (fun _ => (findStuckRedex F t).orElse (fun _ => findStuckRedex F f))
  | e@(.app _m fn arg) =>
    match Factory.callOfLFunc F e false with
    | some (_, args, f) =>
      if !f.isConstr && args.all (LExpr.isCanonicalValue F) then
        some e
      else
        -- Non-stuck call: recurse into fn and arg (structural subterms)
        (findStuckRedex F fn).orElse (fun _ => findStuckRedex F arg)
    | none =>
      (findStuckRedex F fn).orElse (fun _ => findStuckRedex F arg)

/-- Evaluate an expression using the interpreter's environment.

This is the interpreter's own expression evaluator, defined as a separate
function so that we can later prove it consistent with the small-step
`Lambda.Step` relation from `Strata.DL.Lambda.Semantics`.

Currently delegates to `LExpr.eval` with the fuel and state from `Env`.
If the result contains a stuck redex (a fully-applied function that should
have reduced but didn't), returns an error.
-/
def interpExpr (E : Env) (e : Expression.Expr) : Except Env Expression.Expr :=
  let v := e.eval E.exprEnv.config.fuel E.exprEnv
  match findStuckRedex E.factory v with
  | some stuckExpr => .error (stuck E s!"expression contains stuck redex: {format stuckExpr}")
  | none => .ok v

-- TODO: foldlM?
def interpExprList (E : Env) (es : List Expression.Expr) : Except Env (List Expression.Expr) :=
  match es with
  | [] => .ok []
  | e::rest =>
    match interpExpr E e with
    | .error e => .error e
    | .ok v =>
      match interpExprList E rest with
      | .error e => .error e
      | .ok vs => .ok (v::vs)

/-! ## Interpreter Core -/

/-- Default fuel for the interpreter. -/
def defaultFuel : Nat := 10000

mutual
/-- Interpret a single command. -/
def interpCmd (fuel : Nat) (E : Env) (c : Command) : StepResult :=
  match fuel with
  | 0 => .normal { E with error := some EvalError.OutOfFuel }
  | fuel + 1 =>
  match c with
  | .cmd (.init x ty e _md) =>
    match e with
    | .det expr =>
      match interpExpr E expr with
      | .ok v => .normal (CmdEval.update E x ty v)
      | .error sr => .normal sr
    | .nondet => .normal (CmdEval.update E x ty (defaultValue ty))

  | .cmd (.set x e _md) =>
    match e with
    | .det expr =>
      match interpExpr E expr with
      | .ok v => .normal (updateVar E x v)
      | .error sr => .normal sr
    | .nondet =>
      let tyOpt := (E.exprEnv.state.find? x).bind (·.fst)
      .normal (updateVar E x (defaultValueOfMonoTy tyOpt))

  | .cmd (.assert label expr _md) =>
    match interpExpr E expr with
    | .error sr => .normal sr
    | .ok v =>
      match LExpr.denoteBool v with
      | some true => .normal E
      | some false => .normal { E with error := some (.AssertFail label v) }
      | none => .normal (stuck E s!"assert condition did not reduce to bool: {format v}")

  | .cmd (.assume _label expr _md) =>
    match interpExpr E expr with
    | .error sr => .normal sr
    | .ok v =>
      match LExpr.denoteBool v with
      | some true => .normal E
      | some false => .normal (stuck E s!"assume condition is false")
      | none => .normal (stuck E s!"assume condition did not reduce to bool: {format v}")

  | .cmd (.cover _ _ _) => .normal (stuck E "cover not yet supported")

  | .call lhs pname args _md =>
    match Program.Procedure.find? E.program ⟨pname, ()⟩ with
    | none => .normal (stuck E s!"procedure '{pname}' not found")
    | some proc =>
      if proc.body.isEmpty then .normal (stuck E s!"procedure '{pname}' has no body")
      else
        match interpExprList E args with
        | .error e => .normal e
        | .ok argVals =>
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
  | 0 => .normal { E with error := some EvalError.OutOfFuel }
  | fuel + 1 =>
  match stmts with
  | [] => .normal E
  | stmt :: rest =>
    match E.error with
    | some _ => .normal E
    | none =>
      match interpStmt fuel E stmt with
      | .exiting label E' => .exiting label E'
      | .normal E' =>
        match E'.error with
        | some _ => .normal E'
        | none => interpBlock fuel E' rest

/-- Interpret a single statement. -/
def interpStmt (fuel : Nat) (E : Env) (stmt : Statement) : StepResult :=
  match fuel with
  | 0 =>  .normal { E with error := some EvalError.OutOfFuel }
  | fuel + 1 =>
  match stmt with
  | .cmd c => interpCmd fuel E c

  | .block label stmts _md =>
    let E' := { E with exprEnv := { E.exprEnv with state := E.exprEnv.state.push [] } }
    match interpBlock fuel E' stmts with
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
    | .nondet => .normal (stuck E "nondeterministic ite")
    | .det c =>
      match interpExpr E c with
      | .error sr => .normal sr
      | .ok v =>
        match LExpr.denoteBool v with
        | some true => interpBlock fuel E thenBr
        | some false => interpBlock fuel E elseBr
        | none => .normal (stuck E s!"ite condition did not reduce to bool: {format v}")

  | .loop guard _measure _invariants body _md =>
    match guard with
    | .nondet => .normal (stuck E "nondeterministic loop")
    | .det g =>
      match interpExpr E g with
      | .error sr => .normal sr
      | .ok v =>
        match LExpr.denoteBool v with
        | some true =>
          match interpBlock fuel E body with
          | .exiting label E' => .exiting label E'
          | .normal E' =>
            match E'.error with
            | some _ => .normal E'
            | none => interpStmt fuel E' (.loop (.det g) _measure _invariants body _md)
        | some false => .normal E
        | none => .normal (stuck E s!"loop guard did not reduce to bool: {format v}")

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
      match interpExpr E e with
      | .error sr => sr
      | .ok v => CmdEval.update E name ty v
    | .var name ty .nondet _md =>
      CmdEval.update E name ty (defaultValue ty)
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

def diagModel (message : String) : Except DiagnosticModel Env :=
  .error {
    fileRange := FileRange.unknown
    type := DiagnosticType.UserError
    message := message
  }

/-- Interpret a specific procedure by name from a type-checked program. -/
def interpProcedure (prog : Program) (procName : String)
    (args : List Expression.Expr := [])
    (fuel : Nat := defaultFuel) : Except DiagnosticModel Env :=
  match initInterpreterEnv prog with
  | .error e => .error e
  | .ok E =>
    let E := processDecls E
    match Program.Procedure.find? prog ⟨procName, ()⟩ with
    | none => .ok (stuck E s!"procedure '{procName}' not found")
    | some proc =>
      if proc.body.isEmpty then
        .ok (stuck E s!"procedure '{procName}' has no body")
      else
        match interpExprList E args with
        | .error e => .ok e
        | .ok argVals =>
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
          -- TODO: Is it allowed for an exit to propagate right out of a procedure?
          | .exiting _ E' | .normal E' => .ok E'

end Core
