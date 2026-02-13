/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Program
import Strata.Languages.Core.Verifier
import Strata.Languages.Core.Statement
import Strata.Languages.Core.Procedure
import Strata.Languages.Core.Options
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LiftExpressionAssignments
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.ModifiesClauses
import Strata.Languages.Laurel.CorePrelude
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.MetaData
import Strata.DL.Lambda.LExpr
import Strata.Languages.Laurel.LaurelFormat
import Strata.Util.Tactics

open Core (VCResult VCResults)
open Core (intAddOp intSubOp intMulOp intDivOp intModOp intNegOp intLtOp intLeOp intGtOp intGeOp boolAndOp boolOrOp boolNotOp boolImpliesOp)

namespace Strata.Laurel

open Std (Format ToFormat)
open Strata
open Lambda (LMonoTy LTy LExpr)

/-
Translate Laurel HighType to Core Type
-/
def translateType (ty : HighTypeMd) : LMonoTy :=
  match _h : ty.val with
  | .TInt => LMonoTy.int
  | .TBool => LMonoTy.bool
  | .TString => LMonoTy.string
  | .TVoid => LMonoTy.bool -- Using bool as placeholder for void
  | .THeap => Core.mapTy (.tcons "Composite" []) (Core.mapTy (.tcons "Field" []) (.tcons "Box" []))
  | .TTypedField _ => .tcons "Field" []
  | .TSet elementType => Core.mapTy (translateType elementType) LMonoTy.bool
  | .UserDefined _ => .tcons "Composite" []
  | _ => panic s!"unsupported type {ToFormat.format ty}"
termination_by ty.val
decreasing_by cases elementType; term_by_mem

def lookupType (env : TypeEnv) (name : Identifier) : LMonoTy :=
  match env.find? (fun (n, _) => n == name) with
  | some (_, ty) => translateType ty
  | none => panic s!"could not find variable {name} in environment"

def isConstant (constants : List Constant) (name : Identifier) : Bool :=
  constants.any (fun c => c.name == name)

/-- Set of names that are translated to Core functions (not procedures) -/
abbrev FunctionNames := List Identifier

def isCoreFunction (funcNames : FunctionNames) (name : Identifier) : Bool :=
  -- readField, updateField, and Box constructors/destructors are always functions
  name == "readField" || name == "updateField" ||
  name == "BoxInt" || name == "BoxBool" || name == "BoxFloat64" || name == "BoxComposite" ||
  name == "Box..intVal" || name == "Box..boolVal" || name == "Box..float64Val" || name == "Box..compositeVal" ||
  funcNames.contains name

/--
Translate Laurel StmtExpr to Core Expression.

`boundVars` tracks names bound by enclosing Forall/Exists quantifiers (innermost first).
When an Identifier matches a bound name at index `i`, it becomes `bvar i` (de Bruijn index)
instead of `fvar`.
-/
def translateExpr (constants : List Constant) (env : TypeEnv) (expr : StmtExprMd)
    (boundVars : List Identifier := []) : Core.Expression.Expr :=
  match h: expr.val with
  | .LiteralBool b => .const () (.boolConst b)
  | .LiteralInt i => .const () (.intConst i)
  | .LiteralString s => .const () (.strConst s)
  | .Identifier name =>
      -- First check if this name is bound by an enclosing quantifier
      match boundVars.findIdx? (· == name) with
      | some idx =>
          -- Bound variable: use de Bruijn index
          .bvar () idx
      | none =>
          -- Check if this is a constant (field constant) or local variable
          if isConstant constants name then
            let ident := Core.CoreIdent.glob name
            .op () ident none
          else
            let ident := Core.CoreIdent.locl name
            .fvar () ident (some (lookupType env name))
  | .PrimitiveOp op [e] =>
    match op with
    | .Not => .app () boolNotOp (translateExpr constants env e boundVars)
    | .Neg => .app () intNegOp (translateExpr constants env e boundVars)
    | _ => panic! s!"translateExpr: Invalid unary op: {repr op}"
  | .PrimitiveOp op [e1, e2] =>
    let binOp (bop : Core.Expression.Expr): Core.Expression.Expr :=
      LExpr.mkApp () bop [translateExpr constants env e1 boundVars, translateExpr constants env e2 boundVars]
    match op with
    | .Eq => .eq () (translateExpr constants env e1 boundVars) (translateExpr constants env e2 boundVars)
    | .Neq => .app () boolNotOp (.eq () (translateExpr constants env e1 boundVars) (translateExpr constants env e2 boundVars))
    | .And => binOp boolAndOp
    | .Or => binOp boolOrOp
    | .Implies => binOp boolImpliesOp
    | .Add => binOp intAddOp
    | .Sub => binOp intSubOp
    | .Mul => binOp intMulOp
    | .Div => binOp intDivOp
    | .Mod => binOp intModOp
    | .Lt => binOp intLtOp
    | .Leq => binOp intLeOp
    | .Gt => binOp intGtOp
    | .Geq => binOp intGeOp
    | _ => panic! s!"translateExpr: Invalid binary op: {repr op}"
  | .PrimitiveOp op args =>
    panic! s!"translateExpr: PrimitiveOp {repr op} with {args.length} args"
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond := translateExpr constants env cond boundVars
      let bthen := translateExpr constants env thenBranch boundVars
      let belse := match elseBranch with
                  | some e => translateExpr constants env e boundVars
                  | none => .const () (.intConst 0)
      .ite () bcond bthen belse
  | .Assign _ value => translateExpr constants env value boundVars
  | .StaticCall name args =>
      let ident := Core.CoreIdent.unres name
      let fnOp := .op () ident none
      args.foldl (fun acc arg => .app () acc (translateExpr constants env arg boundVars)) fnOp
  | .Block [single] _ => translateExpr constants env single boundVars
  | .Forall name ty body =>
      let coreTy := translateType ty
      let coreBody := translateExpr constants env body (name :: boundVars)
      LExpr.all () (some coreTy) coreBody
  | .Exists name ty body =>
      let coreTy := translateType ty
      let coreBody := translateExpr constants env body (name :: boundVars)
      LExpr.exist () (some coreTy) coreBody
  | .FieldSelect target fieldName =>
      -- Field selects should have been eliminated by heap parameterization
      -- If we see one here, it's an error in the pipeline
      panic! s!"FieldSelect should have been eliminated by heap parameterization: {Std.ToFormat.format target}#{fieldName}"
  | _ => panic! Std.Format.pretty (Std.ToFormat.format expr)
  termination_by expr
  decreasing_by
    all_goals (have := WithMetadata.sizeOf_val_lt expr; term_by_mem)

def getNameFromMd (md : Imperative.MetaData Core.Expression): String :=
  let fileRange := (Imperative.getFileRange md).getD (panic "getNameFromMd bug")
  s!"({fileRange.range.start})"

/--
Translate Laurel StmtExpr to Core Statements
Takes the constants list, type environment, output parameter names, and set of function names
-/
def translateStmt (constants : List Constant) (funcNames : FunctionNames) (env : TypeEnv)
  (outputParams : List Parameter) (stmt : StmtExprMd) : TypeEnv × List Core.Statement :=
  let md := stmt.md
  match h : stmt.val with
  | @StmtExpr.Assert cond =>
      let boogieExpr := translateExpr constants env cond
      (env, [Core.Statement.assert ("assert" ++ getNameFromMd md) boogieExpr md])
  | @StmtExpr.Assume cond =>
      let boogieExpr := translateExpr constants env cond
      (env, [Core.Statement.assume ("assume" ++ getNameFromMd md) boogieExpr md])
  | .Block stmts _ =>
      let (env', stmtsList) := stmts.attach.foldl (fun (e, acc) ⟨s, _hs⟩ =>
        let (e', ss) := translateStmt constants funcNames e outputParams s
        (e', acc ++ ss)) (env, [])
      (env', stmtsList)
  | .LocalVariable name ty initializer =>
      let env' := (name, ty) :: env
      let boogieMonoType := translateType ty
      let boogieType := LTy.forAll [] boogieMonoType
      let ident := Core.CoreIdent.locl name
      match initializer with
      | some (⟨ .StaticCall callee args, callMd⟩) =>
          -- Check if this is a function or a procedure call
          if isCoreFunction funcNames callee then
            -- Translate as expression (function application)
            let boogieExpr := translateExpr constants env (⟨ .StaticCall callee args, callMd ⟩)
            (env', [Core.Statement.init ident boogieType boogieExpr md])
          else
            -- Translate as: var name; call name := callee(args)
            let boogieArgs := args.map (translateExpr constants env)
            let defaultExpr := match ty.val with
                              | .TInt => .const () (.intConst 0)
                              | .TBool => .const () (.boolConst false)
                              | .TString => .const () (.strConst "")
                              | _ => .const () (.intConst 0)
            let initStmt := Core.Statement.init ident boogieType defaultExpr
            let callStmt := Core.Statement.call [ident] callee boogieArgs
            (env', [initStmt, callStmt])
      | some initExpr =>
          let boogieExpr := translateExpr constants env initExpr
          (env', [Core.Statement.init ident boogieType boogieExpr])
      | none =>
          let defaultExpr := match ty.val with
                            | .TInt => .const () (.intConst 0)
                            | .TBool => .const () (.boolConst false)
                            | .TString => .const () (.strConst "")
                            | _ => .const () (.intConst 0)
          (env', [Core.Statement.init ident boogieType defaultExpr])
  | .Assign targets value =>
      match targets with
      | [⟨ .Identifier name, _ ⟩] =>
          let ident := Core.CoreIdent.locl name
          -- Check if RHS is a procedure call (not a function)
          match value.val with
          | .StaticCall callee args =>
              if isCoreFunction funcNames callee then
                -- Functions are translated as expressions
                let boogieExpr := translateExpr constants env value
                (env, [Core.Statement.set ident boogieExpr])
              else
                -- Procedure calls need to be translated as call statements
                let boogieArgs := args.map (translateExpr constants env)
                (env, [Core.Statement.call [ident] callee boogieArgs])
          | _ =>
              let boogieExpr := translateExpr constants env value
              (env, [Core.Statement.set ident boogieExpr])
      | _ =>
          -- Parallel assignment: (var1, var2, ...) := expr
          -- Example use is heap-modifying procedure calls: (result, heap) := f(heap, args)
          match value.val with
          | .StaticCall callee args =>
              let boogieArgs := args.map (translateExpr constants env)
              let lhsIdents := targets.filterMap fun t =>
                match t.val with
                | .Identifier name => some (Core.CoreIdent.locl name)
                | _ => none
              (env, [Core.Statement.call lhsIdents callee boogieArgs value.md])
          | _ =>
              panic "Assignments with multiple target but without a RHS call should not be constructed"
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond := translateExpr constants env cond
      let (_, bthen) := translateStmt constants funcNames env outputParams thenBranch
      let belse := match elseBranch with
                  | some e => (translateStmt constants funcNames env outputParams e).2
                  | none => []
      (env, [Imperative.Stmt.ite bcond bthen belse .empty])
  | .StaticCall name args =>
      -- Check if this is a function or procedure
      if isCoreFunction funcNames name then
        -- Functions as statements have no effect (shouldn't happen in well-formed programs)
        (env, [])
      else
        let boogieArgs := args.map (translateExpr constants env)
        (env, [Core.Statement.call [] name boogieArgs])
  | .Return valueOpt =>
      match valueOpt, outputParams.head? with
      | some value, some outParam =>
          let ident := Core.CoreIdent.locl outParam.name
          let boogieExpr := translateExpr constants env value
          let assignStmt := Core.Statement.set ident boogieExpr
          let noFallThrough := Core.Statement.assume "return" (.const () (.boolConst false)) .empty
          (env, [assignStmt, noFallThrough])
      | none, _ =>
          let noFallThrough := Core.Statement.assume "return" (.const () (.boolConst false)) .empty
          (env, [noFallThrough])
      | some _, none =>
          panic! "Return statement with value but procedure has no output parameters"
  | _ => (env, [])
  termination_by sizeOf stmt
  decreasing_by
    all_goals
      have hlt := WithMetadata.sizeOf_val_lt stmt
      cases stmt; term_by_mem

/--
Translate Laurel Parameter to Core Signature entry
-/
def translateParameterToCore (param : Parameter) : (Core.CoreIdent × LMonoTy) :=
  let ident := Core.CoreIdent.locl param.name
  let ty := translateType param.type
  (ident, ty)

/--
Translate Laurel Procedure to Core Procedure
-/
def translateProcedure (constants : List Constant) (funcNames : FunctionNames) (proc : Procedure) : Core.Procedure :=
  let inputPairs := proc.inputs.map translateParameterToCore
  let inputs := inputPairs

  let outputs := proc.outputs.map translateParameterToCore

  let header : Core.Procedure.Header := {
    name := proc.name
    typeArgs := []
    inputs := inputs
    outputs := outputs
  }
  let initEnv : TypeEnv := proc.inputs.map (fun p => (p.name, p.type)) ++
                           proc.outputs.map (fun p => (p.name, p.type)) ++
                           constants.map (fun c => (c.name, c.type))
  -- Translate precondition if it's not just LiteralBool true
  let preconditions : ListMap Core.CoreLabel Core.Procedure.Check :=
    match proc.precondition with
    | ⟨ .LiteralBool true, _ ⟩ => []
    | precond =>
        let check : Core.Procedure.Check := { expr := translateExpr constants initEnv precond, md := precond.md }
        [("requires", check)]
  -- Translate postconditions for Opaque bodies
  let postconditions : ListMap Core.CoreLabel Core.Procedure.Check :=
    match proc.body with
    | .Opaque postconds _ _ =>
        let (_, result) := postconds.foldl (fun (i, acc) postcond =>
          let label := if postconds.length == 1 then "postcondition" else s!"postcondition_{i}"
          let check : Core.Procedure.Check := { expr := translateExpr constants initEnv postcond, md := postcond.md }
          (i + 1, acc ++ [(label, check)])) (0, [])
        result
    | _ => []
  let modifies : List Core.Expression.Ident := []
  -- For bodyless opaque procedures (no implementation), we use `assume false`
  -- so postcondition asserts are vacuously true. The postconditions are kept in
  -- the spec so they are assumed at call sites via call elimination.
  let body : List Core.Statement :=
    match proc.body with
    | .Transparent bodyExpr => (translateStmt constants funcNames initEnv proc.outputs bodyExpr).2
    | .Opaque _postconds (some impl) _ => (translateStmt constants funcNames initEnv proc.outputs impl).2
    -- because Core does not support procedures without a body, we add an assume false
    | _ => [Core.Statement.assume "no_body" (.const () (.boolConst false)) .empty]
  let spec : Core.Procedure.Spec := {
    modifies,
    preconditions,
    postconditions,
  }
  {
    header := header
    spec := spec
    body := body
  }

def translateConstant (c : Constant) : Core.Decl :=
  match c.type.val with
  | .TTypedField _ =>
      .func {
        name := Core.CoreIdent.glob c.name
        typeArgs := []
        inputs := []
        output := .tcons "Field" []
        body := none
      }
  | _ =>
      let ty := translateType c.type
      .func {
        name := Core.CoreIdent.glob c.name
        typeArgs := []
        inputs := []
        output := ty
        body := none
      }

/--
Check if a StmtExpr is a pure expression (can be used as a Core function body).
Pure expressions don't contain statements like assignments, loops, or local variables.
A Block with a single pure expression is also considered pure.
-/
def isPureExpr(expr: StmtExprMd): Bool :=
  match _h : expr.val with
  | .LiteralBool _ => true
  | .LiteralInt _ => true
  | .LiteralString _ => true
  | .Identifier _ => true
  | .PrimitiveOp _ args => args.attach.all (fun ⟨a, _⟩ => isPureExpr a)
  | .IfThenElse c t none => isPureExpr c && isPureExpr t
  | .IfThenElse c t (some e) => isPureExpr c && isPureExpr t && isPureExpr e
  | .StaticCall _ args => args.attach.all (fun ⟨a, _⟩ => isPureExpr a)
  | .ReferenceEquals e1 e2 => isPureExpr e1 && isPureExpr e2
  | .Block [single] _ => isPureExpr single
  | _ => false
  termination_by sizeOf expr
  decreasing_by all_goals (have := WithMetadata.sizeOf_val_lt expr; term_by_mem)


/--
Check if a procedure can be translated as a Core function.
A procedure can be a function if:
- It has a transparent body that is a pure expression
- It has no precondition (or just `true`)
- It has exactly one output parameter (the return type)
-/
def canBeBoogieFunction (proc : Procedure) : Bool :=
  match proc.body with
  | .Transparent bodyExpr =>
    isPureExpr bodyExpr &&
    (match proc.precondition.val with | .LiteralBool true => true | _ => false) &&
    proc.outputs.length == 1
  | _ => false

/--
Translate a Laurel Procedure to a Core Function (when applicable)
-/
def translateProcedureToFunction (constants : List Constant) (proc : Procedure) : Core.Decl :=
  let inputs := proc.inputs.map translateParameterToCore
  let outputTy := match proc.outputs.head? with
    | some p => translateType p.type
    | none => LMonoTy.int
  let initEnv : TypeEnv := proc.inputs.map (fun p => (p.name, p.type))
  let body := match proc.body with
    | .Transparent bodyExpr => some (translateExpr constants initEnv bodyExpr)
    | _ => none
  .func {
    name := Core.CoreIdent.unres proc.name
    typeArgs := []
    inputs := inputs
    output := outputTy
    body := body
  }

/--
Translate Laurel Program to Core Program
-/
def translate (program : Program) : Except (Array DiagnosticModel) (Core.Program × Array DiagnosticModel) := do
  let program := heapParameterization program
  let (program, modifiesDiags) := modifiesClausesTransform program
  let program := liftExpressionAssignments program
  dbg_trace "===  Program after heapParameterization + modifiesClausesTransform + liftExpressionAssignments ==="
  dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format program)))
  dbg_trace "================================="
  -- Separate procedures that can be functions from those that must be procedures
  let (funcProcs, procProcs) := program.staticProcedures.partition canBeBoogieFunction
  -- Build the set of function names for use during translation
  let funcNames : FunctionNames := funcProcs.map (·.name)
  let procedures := procProcs.map (translateProcedure program.constants funcNames)
  let procDecls := procedures.map (fun p => Core.Decl.proc p .empty)
  let laurelFuncDecls := funcProcs.map (translateProcedureToFunction program.constants)
  let constDecls := program.constants.map translateConstant
  let preludeDecls := corePrelude.decls
  pure ({ decls := preludeDecls ++ constDecls ++ laurelFuncDecls ++ procDecls }, modifiesDiags)

/--
Verify a Laurel program using an SMT solver
-/
def verifyToVcResults (smtsolver : String) (program : Program)
    (options : Options := Options.default)
    (tempDir : Option String := .none)
    : IO (Except (Array DiagnosticModel) VCResults) := do
  let (strataCoreProgram, translateDiags) ← match translate program with
    | .error translateErrorDiags => return .error translateErrorDiags
    | .ok result => pure result

  -- Enable removeIrrelevantAxioms to avoid polluting simple assertions with heap axioms
  let options := { options with removeIrrelevantAxioms := true }
  -- Debug: Print the generated Strata Core program
  dbg_trace "=== Generated Strata Core Program ==="
  dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format strataCoreProgram) 100))
  dbg_trace "================================="
  let runner tempDir :=
    EIO.toIO (fun f => IO.Error.userError (toString f))
        (Core.verify smtsolver strataCoreProgram tempDir .none options)
  let ioResult ← match tempDir with
    | .none => IO.FS.withTempDir runner
    | .some p => IO.FS.createDirAll ⟨p⟩; runner ⟨p⟩
  if translateDiags.isEmpty then
    return .ok ioResult
  else
    return .error (translateDiags ++ ioResult.filterMap toDiagnosticModel)


def verifyToDiagnostics (smtsolver : String) (files: Map Strata.Uri Lean.FileMap) (program : Program): IO (Array Diagnostic) := do
  let results <- verifyToVcResults smtsolver program
  match results with
  | .error errors => return errors.map (fun dm => dm.toDiagnostic files)
  | .ok results => return results.filterMap (fun dm => dm.toDiagnostic files)


def verifyToDiagnosticModels (smtsolver : String) (program : Program): IO (Array DiagnosticModel) := do
  let results <- verifyToVcResults smtsolver program
  match results with
  | .error errors => return errors
  | .ok results => return results.filterMap toDiagnosticModel

end Laurel
