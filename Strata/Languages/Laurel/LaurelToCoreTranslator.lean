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
  | .TVoid => LMonoTy.bool
  | .THeap => .tcons "Heap" []
  | .TField => .tcons "Field" [LMonoTy.int]  -- For now, all fields hold int
  | .UserDefined _ => .tcons "Composite" []
  | _ => panic s!"unsupported type {repr ty}"

abbrev TypeEnv := List (Identifier × HighType)

def lookupType (env : TypeEnv) (name : Identifier) : LMonoTy :=
  match env.find? (fun (n, _) => n == name) with
  | some (_, ty) => translateType ty
  | none => LMonoTy.int  -- fallback

/--
Translate Laurel StmtExpr to Core Expression
-/
def translateExpr (env : TypeEnv) (expr : StmtExpr) : Core.Expression.Expr :=
  match h: expr with
  | .LiteralBool b => .const () (.boolConst b)
  | .LiteralInt i => .const () (.intConst i)
  | .Identifier name =>
      let ident := Core.CoreIdent.locl name
      .fvar () ident (some (lookupType env name))
  | .PrimitiveOp op [e] =>
    match op with
    | .Not => .app () boolNotOp (translateExpr env e)
    | .Neg => .app () intNegOp (translateExpr env e)
    | _ => panic! s!"translateExpr: Invalid unary op: {repr op}"
  | .PrimitiveOp op [e1, e2] =>
    let binOp (bop : Core.Expression.Expr): Core.Expression.Expr :=
      LExpr.mkApp () bop [translateExpr env e1, translateExpr env e2]
    match op with
    | .Eq => .eq () (translateExpr env e1) (translateExpr env e2)
    | .Neq => .app () boolNotOp (.eq () (translateExpr env e1) (translateExpr env e2))
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
      let bcond := translateExpr env cond
      let bthen := translateExpr env thenBranch
      let belse := match elseBranch with
                  | some e => translateExpr env e
                  | none => .const () (.intConst 0)
      .ite () bcond bthen belse
  | .Assign _ value _ => translateExpr env value
  | .StaticCall name args =>
      let ident := Core.CoreIdent.glob name
      let fnOp := .op () ident none
      args.foldl (fun acc arg => .app () acc (translateExpr env arg)) fnOp
  | .ReferenceEquals e1 e2 =>
      .eq () (translateExpr env e1) (translateExpr env e2)
  | .Block [single] _ => translateExpr env single
  | _ => panic! Std.Format.pretty (Std.ToFormat.format expr)
  decreasing_by
  all_goals (simp_wf; try omega)
  rename_i x_in; have := List.sizeOf_lt_of_mem x_in; omega

def getNameFromMd (md : Imperative.MetaData Core.Expression): String :=
  let fileRange := (Imperative.getFileRange md).get!
  s!"({fileRange.range.start})"

/--
Translate Laurel StmtExpr to Core Statements
Takes the type environment and output parameter names
-/
def translateStmt (env : TypeEnv) (outputParams : List Parameter) (stmt : StmtExpr) : TypeEnv × List Core.Statement :=
  match stmt with
  | @StmtExpr.Assert cond md =>
      let boogieExpr := translateExpr env cond
      (env, [Core.Statement.assert ("assert" ++ getNameFromMd md) boogieExpr md])
  | @StmtExpr.Assume cond md =>
      let boogieExpr := translateExpr env cond
      (env, [Core.Statement.assume ("assume" ++ getNameFromMd md) boogieExpr md])
  | .Block stmts _ =>
      let (env', stmtsList) := stmts.foldl (fun (e, acc) s =>
        let (e', ss) := translateStmt e outputParams s
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
            let boogieExpr := translateExpr env (.StaticCall callee args)
            (env', [Core.Statement.init ident boogieType boogieExpr])
          else
            -- Translate as: var name; call name := callee(args)
            let boogieArgs := args.map (translateExpr env)
            let defaultExpr := match ty with
                              | .TInt => .const () (.intConst 0)
                              | .TBool => .const () (.boolConst false)
                              | _ => .const () (.intConst 0)
            let initStmt := Core.Statement.init ident boogieType defaultExpr
            let callStmt := Core.Statement.call [ident] callee boogieArgs
            (env', [initStmt, callStmt])
      | some initExpr =>
          let boogieExpr := translateExpr env initExpr
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
          let ident := Core.CoreIdent.locl name
          let boogieExpr := translateExpr env value
          (env, [Core.Statement.set ident boogieExpr])
      | _ => (env, [])
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond := translateExpr env cond
      let (_, bthen) := translateStmt env outputParams thenBranch
      let belse := match elseBranch with
                  | some e => (translateStmt env outputParams e).2
                  | none => []
      (env, [Imperative.Stmt.ite bcond bthen belse .empty])
  | .While cond invOpt _decOpt body =>
      let condExpr := translateExpr env cond
      let invExpr := invOpt.map (translateExpr env)
      let (_, bodyStmts) := translateStmt env outputParams body
      (env, [Imperative.Stmt.loop condExpr none invExpr bodyStmts .empty])
  | .StaticCall name args =>
      -- Heap functions (heapRead/heapStore) should not appear as standalone statements
      -- Only translate actual procedure calls to call statements
      if name == "heapRead" || name == "heapStore" then
        -- This shouldn't happen in well-formed programs, but handle gracefully
        (env, [])
      else
        let boogieArgs := args.map (translateExpr env)
        (env, [Core.Statement.call [] name boogieArgs])
  | .Return valueOpt =>
      match valueOpt, outputParams.head? with
      | some value, some outParam =>
          let ident := Core.CoreIdent.locl outParam.name
          let boogieExpr := translateExpr env value
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
def translateProcedure (constants : List Constant) (proc : Procedure) : Core.Procedure :=
  -- Check if this procedure has a heap parameter (first input named "heap")
  let hasHeapParam := proc.inputs.any (fun p => p.name == "heap" && p.type == .THeap)
  -- Rename heap input to heap_in if present
  let renamedInputs := proc.inputs.map (fun p =>
    if p.name == "heap" && p.type == .THeap then { p with name := "heap_in" } else p)
  let inputPairs := renamedInputs.map translateParameterToCore
  let inputs := inputPairs
  let header : Core.Procedure.Header := {
    name := proc.name
    typeArgs := []
    inputs := inputs
    outputs := proc.outputs.map translateParameterToCore
  }
  let initEnv : TypeEnv := proc.inputs.map (fun p => (p.name, p.type)) ++
                           proc.outputs.map (fun p => (p.name, p.type)) ++
                           constants.map (fun c => (c.name, c.type))
  -- Translate preconditions
  let preconditions : ListMap Core.CoreLabel Core.Procedure.Check :=
    proc.preconditions.mapIdx fun i precond =>
      let check : Core.Procedure.Check := { expr := translateExpr initEnv precond }
      (s!"{proc.name}_pre_{i}", check)
  -- Translate postconditions for Opaque bodies
  let postconditions : ListMap Core.CoreLabel Core.Procedure.Check :=
    match proc.body with
    | .Opaque posts _ _ _ =>
        posts.mapIdx fun i postcond =>
          let check : Core.Procedure.Check := { expr := translateExpr initEnv postcond }
          (s!"{proc.name}_post_{i}", check)
    | _ => []
  let spec : Core.Procedure.Spec := {
    modifies := []
    preconditions := preconditions
    postconditions := postconditions
  }
  -- If we have a heap parameter, add initialization: var heap := heap_in
  let heapInit : List Core.Statement :=
    if hasHeapParam then
      let heapTy := LMonoTy.tcons "Heap" []
      let heapType := LTy.forAll [] heapTy
      let heapIdent := Core.CoreIdent.locl "heap"
      let heapInExpr := LExpr.fvar () (Core.CoreIdent.locl "heap_in") (some heapTy)
      [Core.Statement.init heapIdent heapType heapInExpr]
    else []
  let body : List Core.Statement :=
    match proc.body with
    | .Transparent bodyExpr => heapInit ++ (translateStmt initEnv proc.outputs bodyExpr).2
    | .Opaque _posts (some impl) _ _ => heapInit ++ (translateStmt initEnv proc.outputs impl).2
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

-- Axiom: forall h, o, f, v :: heapRead(heapStore(h, o, f, v), o, f) == v
-- Using int for field values since Core doesn't support polymorphism in axioms
def readUpdateSameAxiom : Core.Decl :=
  let heapTy := LMonoTy.tcons "Heap" []
  let compTy := LMonoTy.tcons "Composite" []
  let fieldTy := LMonoTy.tcons "Field" [LMonoTy.int]
  -- Build: heapRead(heapStore(h, o, f, v), o, f) == v using de Bruijn indices
  -- Quantifier order (outer to inner): int (v), Field int (f), Composite (o), Heap (h)
  -- So: h is bvar 0, o is bvar 1, f is bvar 2, v is bvar 3
  let h := LExpr.bvar () 0
  let o := LExpr.bvar () 1
  let f := LExpr.bvar () 2
  let v := LExpr.bvar () 3
  let updateOp := LExpr.op () (Core.CoreIdent.glob "heapStore") none
  let readOp := LExpr.op () (Core.CoreIdent.glob "heapRead") none
  let updateExpr := LExpr.mkApp () updateOp [h, o, f, v]
  let readExpr := LExpr.mkApp () readOp [updateExpr, o, f]
  let eqBody := LExpr.eq () readExpr v
  -- Wrap in foralls: forall v:int, f:Field int, o:Composite, h:Heap
  let body := LExpr.all () (some LMonoTy.int) <|
              LExpr.all () (some fieldTy) <|
              LExpr.all () (some compTy) <|
              LExpr.all () (some heapTy) eqBody
  .ax { name := "heapRead_heapStore_same", e := body }

-- Axiom: forall h, o1, o2, f, v :: o1 != o2 ==> heapRead(heapStore(h, o1, f, v), o2, f) == heapRead(h, o2, f)
-- Using int for field values since Core doesn't support polymorphism in axioms
def readUpdateDiffObjAxiom : Core.Decl :=
  let heapTy := LMonoTy.tcons "Heap" []
  let compTy := LMonoTy.tcons "Composite" []
  let fieldTy := LMonoTy.tcons "Field" [LMonoTy.int]
  -- Quantifier order (outer to inner): int (v), Field int (f), Composite (o2), Composite (o1), Heap (h)
  -- So: h is bvar 0, o1 is bvar 1, o2 is bvar 2, f is bvar 3, v is bvar 4
  let h := LExpr.bvar () 0
  let o1 := LExpr.bvar () 1
  let o2 := LExpr.bvar () 2
  let f := LExpr.bvar () 3
  let v := LExpr.bvar () 4
  let updateOp := LExpr.op () (Core.CoreIdent.glob "heapStore") none
  let readOp := LExpr.op () (Core.CoreIdent.glob "heapRead") none
  let updateExpr := LExpr.mkApp () updateOp [h, o1, f, v]
  let lhs := LExpr.mkApp () readOp [updateExpr, o2, f]
  let rhs := LExpr.mkApp () readOp [h, o2, f]
  let neq := LExpr.app () boolNotOp (LExpr.eq () o1 o2)
  let implBody := LExpr.app () (LExpr.app () Core.boolImpliesOp neq) (LExpr.eq () lhs rhs)
  let body := LExpr.all () (some LMonoTy.int) <|
              LExpr.all () (some fieldTy) <|
              LExpr.all () (some compTy) <|
              LExpr.all () (some compTy) <|
              LExpr.all () (some heapTy) implBody
  .ax { name := "heapRead_heapStore_diff_obj", e := body }

def translateConstant (c : Constant) : Core.Decl :=
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
    proc.preconditions.isEmpty &&
    proc.outputs.length == 1
  | _ => false

/--
Translate a Laurel Procedure to a Core Function (when applicable)
-/
def translateProcedureToFunction (proc : Procedure) : Core.Decl :=
  let inputs := proc.inputs.map translateParameterToCore
  let outputTy := match proc.outputs.head? with
    | some p => translateType p.type
    | none => LMonoTy.int
  let initEnv : TypeEnv := proc.inputs.map (fun p => (p.name, p.type))
  let body := match proc.body with
    | .Transparent bodyExpr => some (translateExpr initEnv bodyExpr)
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
  let heapProgram := heapParameterization sequencedProgram
  -- Separate procedures that can be functions from those that must be procedures
  let (funcProcs, procProcs) := heapProgram.staticProcedures.partition canBeBoogieFunction
  let procedures := procProcs.map (translateProcedure heapProgram.constants)
  let procDecls := procedures.map (fun p => Core.Decl.proc p .empty)
  let laurelFuncDecls := funcProcs.map translateProcedureToFunction
  let constDecls := heapProgram.constants.map translateConstant
  let typeDecls := [heapTypeDecl, fieldTypeDecl, compositeTypeDecl]
  let funcDecls := [readFunction, updateFunction]
  let axiomDecls := [readUpdateSameAxiom, readUpdateDiffObjAxiom]
  return { decls := typeDecls ++ funcDecls ++ axiomDecls ++ constDecls ++ laurelFuncDecls ++ procDecls }

/--
Verify a Laurel program using an SMT solver
-/
def verifyToVcResults (smtsolver : String) (program : Program)
    (options : Options := Options.default)
    (tempDir : Option String := .none)
    : IO (Except (Array DiagnosticModel) VCResults) := do
  let boogieProgramExcept := translate program
    -- Enable removeIrrelevantAxioms to avoid polluting simple assertions with heap axioms
  let options := { options with removeIrrelevantAxioms := true }
  -- Debug: Print the generated Core program
  match boogieProgramExcept with
    | .error e => return .error e
    | .ok boogieProgram =>
      dbg_trace "=== Generated Core Program ==="
      dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format boogieProgram)))
      dbg_trace "================================="

      let runner tempDir :=
        EIO.toIO (fun f => IO.Error.userError (toString f))
            (Core.verify smtsolver boogieProgram tempDir options)
      let ioResult <- match tempDir with
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
