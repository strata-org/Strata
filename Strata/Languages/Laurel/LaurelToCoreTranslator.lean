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
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.MetaData
import Strata.DL.Lambda.LExpr
import Strata.Languages.Laurel.LaurelFormat

open Core (VCResult VCResults)
open Core (intAddOp intSubOp intMulOp intDivOp intModOp intNegOp intLtOp intLeOp intGtOp intGeOp boolAndOp boolOrOp boolNotOp)

namespace Strata.Laurel

open Strata
open Lambda (LMonoTy LTy LExpr)

/-
Translate Laurel HighType to Core Type
-/
def translateType (ty : HighType) : LMonoTy :=
  match ty with
  | .TInt => LMonoTy.int
  | .TBool => LMonoTy.bool
  | .TVoid => LMonoTy.bool -- Using bool as placeholder for void
  | .THeap => .tcons "Heap" []
  | .TTypedField valueType => .tcons "Field" [translateType valueType]
  | .UserDefined _ => .tcons "Composite" []
  | _ => panic s!"unsupported type {repr ty}"

abbrev TypeEnv := List (Identifier × HighType)

def lookupType (env : TypeEnv) (name : Identifier) : LMonoTy :=
  match env.find? (fun (n, _) => n == name) with
  | some (_, ty) => translateType ty
  | none => panic s!"could not find variable {name} in environment"

def isConstant (constants : List Constant) (name : Identifier) : Bool :=
  constants.any (fun c => c.name == name)

/--
Translate Laurel StmtExpr to Core Expression
-/
def translateExpr (constants : List Constant) (env : TypeEnv) (expr : StmtExpr) : Core.Expression.Expr :=
  match h: expr with
  | .LiteralBool b => .const () (.boolConst b)
  | .LiteralInt i => .const () (.intConst i)
  | .Identifier name =>
      -- Check if this is a constant (field constant), global variable, or local variable
      if isConstant constants name then
        -- Constants are global identifiers (functions with no arguments)
        let ident := Core.CoreIdent.glob name
        -- Field constants are declared as functions () → Field T
        -- We just reference them as operations without application
        .op () ident none
      else if name == "$heap" then
        -- Global heap variable
        let ident := Core.CoreIdent.glob name
        .fvar () ident (some (.tcons "Heap" []))
      else
        -- Regular variables are local identifiers
        let ident := Core.CoreIdent.locl name
        .fvar () ident (some (lookupType env name))
  | .PrimitiveOp op [e] =>
    match op with
    | .Not => .app () boolNotOp (translateExpr constants env e)
    | .Neg => .app () intNegOp (translateExpr constants env e)
    | _ => panic! s!"translateExpr: Invalid unary op: {repr op}"
  | .PrimitiveOp op [e1, e2] =>
    let binOp (bop : Core.Expression.Expr): Core.Expression.Expr :=
      LExpr.mkApp () bop [translateExpr constants env e1, translateExpr constants env e2]
    match op with
    | .Eq => .eq () (translateExpr constants env e1) (translateExpr constants env e2)
    | .Neq => .app () boolNotOp (.eq () (translateExpr constants env e1) (translateExpr constants env e2))
    | .And => binOp boolAndOp
    | .Or => binOp boolOrOp
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
      let bcond := translateExpr constants env cond
      let bthen := translateExpr constants env thenBranch
      let belse := match elseBranch with
                  | some e => translateExpr constants env e
                  | none => .const () (.intConst 0)
      .ite () bcond bthen belse
  | .Assign _ value _ => translateExpr constants env value
  | .StaticCall name args =>
      let ident := Core.CoreIdent.glob name
      let fnOp := .op () ident none
      args.foldl (fun acc arg => .app () acc (translateExpr constants env arg)) fnOp
  | .Block [single] _ => translateExpr constants env single
  | .FieldSelect target fieldName =>
      -- Field selects should have been eliminated by heap parameterization
      -- If we see one here, it's an error in the pipeline
      panic! s!"FieldSelect should have been eliminated by heap parameterization: {Std.ToFormat.format target}#{fieldName}"
  | _ => panic! Std.Format.pretty (Std.ToFormat.format expr)
  decreasing_by
  all_goals (simp_wf; try omega)
  rename_i x_in; have := List.sizeOf_lt_of_mem x_in; omega

def getNameFromMd (md : Imperative.MetaData Core.Expression): String :=
  let fileRange := (Imperative.getFileRange md).get!
  s!"({fileRange.range.start})"

/--
Translate Laurel StmtExpr to Core Statements
Takes the constants list, type environment and output parameter names
-/
def translateStmt (constants : List Constant) (env : TypeEnv) (outputParams : List Parameter) (stmt : StmtExpr) : TypeEnv × List Core.Statement :=
  match stmt with
  | @StmtExpr.Assert cond md =>
      let boogieExpr := translateExpr constants env cond
      (env, [Core.Statement.assert ("assert" ++ getNameFromMd md) boogieExpr md])
  | @StmtExpr.Assume cond md =>
      let boogieExpr := translateExpr constants env cond
      (env, [Core.Statement.assume ("assume" ++ getNameFromMd md) boogieExpr md])
  | .Block stmts _ =>
      let (env', stmtsList) := stmts.foldl (fun (e, acc) s =>
        let (e', ss) := translateStmt constants e outputParams s
        (e', acc ++ ss)) (env, [])
      (env', stmtsList)
  | .LocalVariable name ty initializer =>
      let env' := (name, ty) :: env
      let boogieMonoType := translateType ty
      let boogieType := LTy.forAll [] boogieMonoType
      let ident := Core.CoreIdent.locl name
      match initializer with
      | some (.StaticCall callee args) =>
          -- Check if this is a heap function (heapRead/heapStore) or a regular procedure call
          -- Heap functions should be translated as expressions, not call statements
          if callee == "heapRead" || callee == "heapStore" then
            -- Translate as expression (function application)
            let boogieExpr := translateExpr constants env (.StaticCall callee args)
            (env', [Core.Statement.init ident boogieType boogieExpr])
          else
            -- Translate as: var name; call name := callee(args)
            let boogieArgs := args.map (translateExpr constants env)
            let defaultExpr := match ty with
                              | .TInt => .const () (.intConst 0)
                              | .TBool => .const () (.boolConst false)
                              | _ => .const () (.intConst 0)
            let initStmt := Core.Statement.init ident boogieType defaultExpr
            let callStmt := Core.Statement.call [ident] callee boogieArgs
            (env', [initStmt, callStmt])
      | some initExpr =>
          let boogieExpr := translateExpr constants env initExpr
          (env', [Core.Statement.init ident boogieType boogieExpr])
      | none =>
          let defaultExpr := match ty with
                            | .TInt => .const () (.intConst 0)
                            | .TBool => .const () (.boolConst false)
                            | _ => .const () (.intConst 0)
          (env', [Core.Statement.init ident boogieType defaultExpr])
  | .Assign target value _ =>
      match target with
      | .Identifier name =>
          -- Check if this is the global heap variable
          if name == "$heap" then
            let heapIdent := Core.CoreIdent.glob "$heap"
            let boogieExpr := translateExpr constants env value
            (env, [Core.Statement.set heapIdent boogieExpr])
          else
            let ident := Core.CoreIdent.locl name
            let boogieExpr := translateExpr constants env value
            (env, [Core.Statement.set ident boogieExpr])
      | _ => (env, [])
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond := translateExpr constants env cond
      let (_, bthen) := translateStmt constants env outputParams thenBranch
      let belse := match elseBranch with
                  | some e => (translateStmt constants env outputParams e).2
                  | none => []
      (env, [Imperative.Stmt.ite bcond bthen belse .empty])
  | .StaticCall name args =>
      -- Heap functions (heapRead/heapStore) should not appear as standalone statements
      -- Only translate actual procedure calls to call statements
      if name == "heapRead" || name == "heapStore" then
        -- This shouldn't happen in well-formed programs, but handle gracefully
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
def translateProcedure (constants : List Constant) (heapWriters : List Identifier) (proc : Procedure) : Core.Procedure :=
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
    | .LiteralBool true => []
    | precond =>
        let check : Core.Procedure.Check := { expr := translateExpr constants initEnv precond }
        [("requires", check)]
  -- Translate postcondition for Opaque bodies
  let postconditions : ListMap Core.CoreLabel Core.Procedure.Check :=
    match proc.body with
    | .Opaque postcond _ _ =>
        let check : Core.Procedure.Check := { expr := translateExpr constants initEnv postcond }
        [("ensures", check)]
    | _ => []
  let modifies := if heapWriters.contains proc.name then [Core.CoreIdent.glob "$heap"] else []
  let spec : Core.Procedure.Spec := {
    modifies,
    preconditions,
    postconditions,
  }
  let body : List Core.Statement :=
    match proc.body with
    | .Transparent bodyExpr => (translateStmt constants initEnv proc.outputs bodyExpr).2
    | .Opaque _postcond (some impl) _ => (translateStmt constants initEnv proc.outputs impl).2
    | _ => []
  {
    header := header
    spec := spec
    body := body
  }

def heapTypeDecl : Core.Decl := .type (.con { name := "Heap", numargs := 0 })
def fieldTypeDecl : Core.Decl := .type (.con { name := "Field", numargs := 1 })
def compositeTypeDecl : Core.Decl := .type (.con { name := "Composite", numargs := 0 })

def readFunction : Core.Decl :=
  let heapTy := LMonoTy.tcons "Heap" []
  let compTy := LMonoTy.tcons "Composite" []
  let tVar := LMonoTy.ftvar "T"
  let fieldTy := LMonoTy.tcons "Field" [tVar]
  .func {
    name := Core.CoreIdent.glob "heapRead"
    typeArgs := ["T"]
    inputs := [(Core.CoreIdent.locl "heap", heapTy),
               (Core.CoreIdent.locl "obj", compTy),
               (Core.CoreIdent.locl "field", fieldTy)]
    output := tVar
    body := none
  }

def updateFunction : Core.Decl :=
  let heapTy := LMonoTy.tcons "Heap" []
  let compTy := LMonoTy.tcons "Composite" []
  let tVar := LMonoTy.ftvar "T"
  let fieldTy := LMonoTy.tcons "Field" [tVar]
  .func {
    name := Core.CoreIdent.glob "heapStore"
    typeArgs := ["T"]
    inputs := [(Core.CoreIdent.locl "heap", heapTy),
               (Core.CoreIdent.locl "obj", compTy),
               (Core.CoreIdent.locl "field", fieldTy),
               (Core.CoreIdent.locl "val", tVar)]
    output := heapTy
    body := none
  }

-- Axiom 1: read-over-write-same
-- forall h, r, f, v :: read(store(h, r, f, v), r, f) == v
def readUpdateSameAxiom : Core.Decl :=
  let heapTy := LMonoTy.tcons "Heap" []
  let compTy := LMonoTy.tcons "Composite" []
  let fieldTy := LMonoTy.tcons "Field" [LMonoTy.int]
  -- Quantifier order (outer to inner): int (v), Field int (f), Composite (r), Heap (h)
  -- So: h is bvar 0, r is bvar 1, f is bvar 2, v is bvar 3
  let h := LExpr.bvar () 0
  let r := LExpr.bvar () 1
  let f := LExpr.bvar () 2
  let v := LExpr.bvar () 3
  let storeOp := LExpr.op () (Core.CoreIdent.glob "heapStore") none
  let readOp := LExpr.op () (Core.CoreIdent.glob "heapRead") none
  let storeExpr := LExpr.mkApp () storeOp [h, r, f, v]
  let readExpr := LExpr.mkApp () readOp [storeExpr, r, f]
  let eqBody := LExpr.eq () readExpr v
  let body := LExpr.all () (some LMonoTy.int) <|
              LExpr.all () (some fieldTy) <|
              LExpr.all () (some compTy) <|
              LExpr.all () (some heapTy) eqBody
  .ax { name := "read_over_write_same", e := body }

-- Axiom 2: read-over-write-diff
-- forall h, r1, r2, f1, f2, v ::
--   (r1 != r2 || f1 != f2) ==> read(store(h, r1, f1, v), r2, f2) == read(h, r2, f2)
def readUpdateDiffAxiom : Core.Decl :=
  let heapTy := LMonoTy.tcons "Heap" []
  let compTy := LMonoTy.tcons "Composite" []
  let fieldTy := LMonoTy.tcons "Field" [LMonoTy.int]
  -- Quantifier order (outer to inner): int (v), Field (f2), Field (f1), Composite (r2), Composite (r1), Heap (h)
  -- So: h is bvar 0, r1 is bvar 1, r2 is bvar 2, f1 is bvar 3, f2 is bvar 4, v is bvar 5
  let h := LExpr.bvar () 0
  let r1 := LExpr.bvar () 1
  let r2 := LExpr.bvar () 2
  let f1 := LExpr.bvar () 3
  let f2 := LExpr.bvar () 4
  let v := LExpr.bvar () 5
  let storeOp := LExpr.op () (Core.CoreIdent.glob "heapStore") none
  let readOp := LExpr.op () (Core.CoreIdent.glob "heapRead") none
  let storeExpr := LExpr.mkApp () storeOp [h, r1, f1, v]
  let readAfterStore := LExpr.mkApp () readOp [storeExpr, r2, f2]
  let readOriginal := LExpr.mkApp () readOp [h, r2, f2]
  let refsDiff := LExpr.app () boolNotOp (LExpr.eq () r1 r2)
  let fieldsDiff := LExpr.app () boolNotOp (LExpr.eq () f1 f2)
  let precond := LExpr.app () (LExpr.app () boolOrOp refsDiff) fieldsDiff
  let conclusion := LExpr.eq () readAfterStore readOriginal
  let implBody := LExpr.app () (LExpr.app () Core.boolImpliesOp precond) conclusion
  let body := LExpr.all () (some LMonoTy.int) <|
              LExpr.all () (some fieldTy) <|
              LExpr.all () (some fieldTy) <|
              LExpr.all () (some compTy) <|
              LExpr.all () (some compTy) <|
              LExpr.all () (some heapTy) implBody
  .ax { name := "read_over_write_diff", e := body }

def translateConstant (c : Constant) : Core.Decl :=
  match c.type with
  | .TTypedField valueType =>
      -- Field constants with known type: () → Field <valueType>
      let valueTy := translateType valueType
      .func {
        name := Core.CoreIdent.glob c.name
        typeArgs := []
        inputs := []
        output := .tcons "Field" [valueTy]
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
def isPureExpr : StmtExpr → Bool
  | .LiteralBool _ => true
  | .LiteralInt _ => true
  | .Identifier _ => true
  | .PrimitiveOp _ args => args.attach.all (fun ⟨a, _⟩ => isPureExpr a)
  | .IfThenElse c t none => isPureExpr c && isPureExpr t
  | .IfThenElse c t (some e) => isPureExpr c && isPureExpr t && isPureExpr e
  | .StaticCall _ args => args.attach.all (fun ⟨a, _⟩ => isPureExpr a)
  | .ReferenceEquals e1 e2 => isPureExpr e1 && isPureExpr e2
  | .Block [single] _ => isPureExpr single
  | _ => false
termination_by e => sizeOf e

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
    (match proc.precondition with | .LiteralBool true => true | _ => false) &&
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
    name := Core.CoreIdent.glob proc.name
    typeArgs := []
    inputs := inputs
    output := outputTy
    body := body
  }

/--
Translate Laurel Program to Core Program
-/
def translate (program : Program) : Except (Array DiagnosticModel) Core.Program := do
  let sequencedProgram ← liftExpressionAssignments program
  let (heapProgram, heapWriters) := heapParameterization sequencedProgram
  dbg_trace "===  Program after heapParameterization==="
  dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format heapProgram)))
  dbg_trace "================================="
  -- Separate procedures that can be functions from those that must be procedures
  let (funcProcs, procProcs) := heapProgram.staticProcedures.partition canBeBoogieFunction
  let procedures := procProcs.map (translateProcedure heapProgram.constants heapWriters)
  let procDecls := procedures.map (fun p => Core.Decl.proc p .empty)
  let laurelFuncDecls := funcProcs.map (translateProcedureToFunction heapProgram.constants)
  let constDecls := heapProgram.constants.map translateConstant
  let typeDecls := [heapTypeDecl, fieldTypeDecl, compositeTypeDecl]
  let funcDecls := [readFunction, updateFunction]
  let axiomDecls := [readUpdateSameAxiom, readUpdateDiffAxiom]
  -- Add global heap variable declaration with a free variable as initializer
  let heapTy := LMonoTy.tcons "Heap" []
  let heapInitVar := LExpr.fvar () (Core.CoreIdent.glob "$heap_init") (some heapTy)
  let heapVarDecl := Core.Decl.var
    (Core.CoreIdent.glob "$heap")
    (LTy.forAll [] heapTy)
    heapInitVar
    .empty
  return { decls := typeDecls ++ funcDecls ++ axiomDecls ++ [heapVarDecl] ++ constDecls ++ laurelFuncDecls ++ procDecls }

/--
Verify a Laurel program using an SMT solver
-/
def verifyToVcResults (smtsolver : String) (program : Program)
    (options : Options := Options.default)
    (tempDir : Option String := .none)
    : IO (Except (Array DiagnosticModel) VCResults) := do
  let strataCoreProgramExcept := translate program
    -- Enable removeIrrelevantAxioms to avoid polluting simple assertions with heap axioms
  let options := { options with removeIrrelevantAxioms := true }
  -- Debug: Print the generated Strata Core program
  match strataCoreProgramExcept with
    | .error e => return .error e
    | .ok strataCoreProgram =>
      dbg_trace "=== Generated Strata Core Program ==="
      dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format strataCoreProgram)))
      dbg_trace "================================="

      let runner tempDir :=
        EIO.toIO (fun f => IO.Error.userError (toString f))
            (Core.verify smtsolver strataCoreProgram tempDir .none options)
      let ioResult ← match tempDir with
      | .none =>
        IO.FS.withTempDir runner
      | .some p =>
        IO.FS.createDirAll ⟨p⟩
        runner ⟨p⟩
      return .ok ioResult


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
