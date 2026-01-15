/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Program
import Strata.Languages.Boogie.Verifier
import Strata.Languages.Boogie.Statement
import Strata.Languages.Boogie.Procedure
import Strata.Languages.Boogie.Options
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LiftExpressionAssignments
import Strata.Languages.Laurel.HeapParameterization
import Strata.DL.Imperative.Stmt
import Strata.DL.Lambda.LExpr
import Strata.Languages.Laurel.LaurelFormat

open Boogie (VCResult VCResults)
open Boogie (intAddOp intSubOp intMulOp intDivOp intModOp intNegOp intLtOp intLeOp intGtOp intGeOp boolAndOp boolOrOp boolNotOp)

namespace Strata.Laurel

open Strata
open Lambda (LMonoTy LTy LExpr)

/-
Translate Laurel HighType to Boogie Type
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
Translate Laurel StmtExpr to Boogie Expression
-/
def translateExpr (env : TypeEnv) (expr : StmtExpr) : Boogie.Expression.Expr :=
  match h: expr with
  | .LiteralBool b => .const () (.boolConst b)
  | .LiteralInt i => .const () (.intConst i)
  | .Identifier name =>
      let ident := Boogie.BoogieIdent.locl name
      .fvar () ident (some (lookupType env name))
  | .PrimitiveOp op [e] =>
    match op with
    | .Not => .app () boolNotOp (translateExpr env e)
    | .Neg => .app () intNegOp (translateExpr env e)
    | _ => panic! s!"translateExpr: Invalid unary op: {repr op}"
  | .PrimitiveOp op [e1, e2] =>
    let binOp (bop : Boogie.Expression.Expr): Boogie.Expression.Expr :=
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
      let ident := Boogie.BoogieIdent.glob name
      let fnOp := .op () ident none
      args.foldl (fun acc arg => .app () acc (translateExpr env arg)) fnOp
  | _ => panic! Std.Format.pretty (Std.ToFormat.format expr)
  decreasing_by
  all_goals (simp_wf; try omega)
  rename_i x_in; have := List.sizeOf_lt_of_mem x_in; omega

/--
Translate Laurel StmtExpr to Boogie Statements
Takes the type environment and output parameter names
-/
def translateStmt (env : TypeEnv) (outputParams : List Parameter) (stmt : StmtExpr) : TypeEnv × List Boogie.Statement :=
  match stmt with
  | @StmtExpr.Assert cond md =>
      let boogieExpr := translateExpr env cond
      (env, [Boogie.Statement.assert "assert" boogieExpr md])
  | @StmtExpr.Assume cond md =>
      let boogieExpr := translateExpr env cond
      (env, [Boogie.Statement.assume "assume" boogieExpr md])
  | .Block stmts _ =>
      let (env', stmtsList) := stmts.foldl (fun (e, acc) s =>
        let (e', ss) := translateStmt e outputParams s
        (e', acc ++ ss)) (env, [])
      (env', stmtsList)
  | .LocalVariable name ty initializer =>
      let env' := (name, ty) :: env
      let boogieMonoType := translateType ty
      let boogieType := LTy.forAll [] boogieMonoType
      let ident := Boogie.BoogieIdent.locl name
      match initializer with
      | some initExpr =>
          let boogieExpr := translateExpr env initExpr
          (env', [Boogie.Statement.init ident boogieType boogieExpr])
      | none =>
          let defaultExpr := match ty with
                            | .TInt => .const () (.intConst 0)
                            | .TBool => .const () (.boolConst false)
                            | _ => .const () (.intConst 0)
          (env', [Boogie.Statement.init ident boogieType defaultExpr])
  | .Assign target value _ =>
      match target with
      | .Identifier name =>
          let ident := Boogie.BoogieIdent.locl name
          let boogieExpr := translateExpr env value
          (env, [Boogie.Statement.set ident boogieExpr])
      | _ => (env, [])
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond := translateExpr env cond
      let (_, bthen) := translateStmt env outputParams thenBranch
      let belse := match elseBranch with
                  | some e => (translateStmt env outputParams e).2
                  | none => []
      (env, [Imperative.Stmt.ite bcond bthen belse .empty])
  | .StaticCall name args =>
      let boogieArgs := args.map (translateExpr env)
      (env, [Boogie.Statement.call [] name boogieArgs])
  | .Return valueOpt =>
      match valueOpt, outputParams.head? with
      | some value, some outParam =>
          let ident := Boogie.BoogieIdent.locl outParam.name
          let boogieExpr := translateExpr env value
          let assignStmt := Boogie.Statement.set ident boogieExpr
          let noFallThrough := Boogie.Statement.assume "return" (.const () (.boolConst false)) .empty
          (env, [assignStmt, noFallThrough])
      | none, _ =>
          let noFallThrough := Boogie.Statement.assume "return" (.const () (.boolConst false)) .empty
          (env, [noFallThrough])
      | some _, none =>
          panic! "Return statement with value but procedure has no output parameters"
  | _ => (env, [])

/--
Translate Laurel Parameter to Boogie Signature entry
-/
def translateParameterToBoogie (param : Parameter) : (Boogie.BoogieIdent × LMonoTy) :=
  let ident := Boogie.BoogieIdent.locl param.name
  let ty := translateType param.type
  (ident, ty)

/--
Translate Laurel Procedure to Boogie Procedure
-/
def translateProcedure (constants : List Constant) (proc : Procedure) : Boogie.Procedure :=
  let inputPairs := proc.inputs.map translateParameterToBoogie
  let inputs := inputPairs
  let header : Boogie.Procedure.Header := {
    name := proc.name
    typeArgs := []
    inputs := inputs
    outputs := proc.outputs.map translateParameterToBoogie
  }
  let spec : Boogie.Procedure.Spec := {
    modifies := []
    preconditions := []
    postconditions := []
  }
  let initEnv : TypeEnv := proc.inputs.map (fun p => (p.name, p.type)) ++
                           proc.outputs.map (fun p => (p.name, p.type)) ++
                           constants.map (fun c => (c.name, c.type))
  let body : List Boogie.Statement :=
    match proc.body with
    | .Transparent bodyExpr => (translateStmt initEnv proc.outputs bodyExpr).2
    | _ => []
  {
    header := header
    spec := spec
    body := body
  }

def heapTypeDecl : Boogie.Decl := .type (.con { name := "Heap", numargs := 0 })
def fieldTypeDecl : Boogie.Decl := .type (.con { name := "Field", numargs := 1 })
def compositeTypeDecl : Boogie.Decl := .type (.con { name := "Composite", numargs := 0 })

def readFunction : Boogie.Decl :=
  let heapTy := LMonoTy.tcons "Heap" []
  let compTy := LMonoTy.tcons "Composite" []
  let tVar := LMonoTy.ftvar "T"
  let fieldTy := LMonoTy.tcons "Field" [tVar]
  .func {
    name := Boogie.BoogieIdent.glob "read"
    typeArgs := ["T"]
    inputs := [(Boogie.BoogieIdent.locl "heap", heapTy),
               (Boogie.BoogieIdent.locl "obj", compTy),
               (Boogie.BoogieIdent.locl "field", fieldTy)]
    output := tVar
    body := none
  }

def translateConstant (c : Constant) : Boogie.Decl :=
  let ty := translateType c.type
  .func {
    name := Boogie.BoogieIdent.glob c.name
    typeArgs := []
    inputs := []
    output := ty
    body := none
  }

/--
Translate Laurel Program to Boogie Program
-/
def translate (program : Program) : Except (Array DiagnosticModel) Boogie.Program := do
  let sequencedProgram ← liftExpressionAssignments program
  let heapProgram := heapParameterization sequencedProgram
  dbg_trace "=== Heap parameterized Program ==="
  dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format heapProgram)))
  dbg_trace "=================================="
  let procedures := heapProgram.staticProcedures.map (translateProcedure heapProgram.constants)
  let procDecls := procedures.map (fun p => Boogie.Decl.proc p .empty)
  let constDecls := heapProgram.constants.map translateConstant
  let typeDecls := [heapTypeDecl, fieldTypeDecl, compositeTypeDecl]
  let funcDecls := [readFunction]
  return { decls := typeDecls ++ funcDecls ++ constDecls ++ procDecls }

/--
Verify a Laurel program using an SMT solver
-/
def verifyToVcResults (smtsolver : String) (program : Program)
    (options : Options := Options.default) : IO (Except (Array DiagnosticModel) VCResults) := do
  let boogieProgramExcept := translate program
  -- Debug: Print the generated Boogie program
  match boogieProgramExcept with
    | .error e => return .error e
    | .ok boogieProgram =>
      dbg_trace "=== Generated Boogie Program ==="
      dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format boogieProgram)))
      dbg_trace "================================="
      let ioResult <- EIO.toIO (fun f => IO.Error.userError (toString f))
          (Boogie.verify smtsolver boogieProgram options)
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
