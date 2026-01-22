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
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.MetaData
import Strata.DL.Lambda.LExpr
import Strata.Languages.Laurel.LaurelFormat

namespace Laurel

open Core (VCResult VCResults)
open Strata

open Core (intAddOp intSubOp intMulOp intDivOp intModOp intNegOp intLtOp intLeOp intGtOp intGeOp boolAndOp boolOrOp boolNotOp)
open Lambda (LMonoTy LTy LExpr)

/-
Translate Laurel HighType to Core Type
-/
def translateType (ty : HighType) : LMonoTy :=
  match ty with
  | .TInt => LMonoTy.int
  | .TBool => LMonoTy.bool
  | .TVoid => LMonoTy.bool  -- Using bool as placeholder for void
  | _ => panic s!"unsupported type {repr ty}"

/--
Translate Laurel StmtExpr to Core Expression
-/
def translateExpr (expr : StmtExpr) : Core.Expression.Expr :=
  match h: expr with
  | .LiteralBool b => .const () (.boolConst b)
  | .LiteralInt i => .const () (.intConst i)
  | .Identifier name =>
      let ident := Core.CoreIdent.locl name
      .fvar () ident (some LMonoTy.int)  -- Default to int type
  | .PrimitiveOp op [e] =>
    match op with
    | .Not => .app () boolNotOp (translateExpr e)
    | .Neg => .app () intNegOp (translateExpr e)
    | _ => panic! s!"translateExpr: Invalid unary op: {repr op}"
  | .PrimitiveOp op [e1, e2] =>
    let binOp (bop : Core.Expression.Expr): Core.Expression.Expr :=
      LExpr.mkApp () bop [translateExpr e1, translateExpr e2]
    match op with
    | .Eq => .eq () (translateExpr e1) (translateExpr e2)
    | .Neq => .app () boolNotOp (.eq () (translateExpr e1) (translateExpr e2))
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
      let bcond := translateExpr cond
      let bthen := translateExpr thenBranch
      let belse := match elseBranch with
                  | some e => translateExpr e
                  | none => .const () (.intConst 0)
      .ite () bcond bthen belse
  | .Assign _ value => translateExpr value  -- For expressions, just translate the value
  | .StaticCall name args =>
      -- Create function call as an op application
      let ident := Core.CoreIdent.glob name
      let fnOp := .op () ident (some LMonoTy.int)  -- Assume int return type
      args.foldl (fun acc arg => .app () acc (translateExpr arg)) fnOp
  | _ => panic! Std.Format.pretty (Std.ToFormat.format expr)
  decreasing_by
  all_goals (simp_wf; try omega)
  rename_i x_in; have := List.sizeOf_lt_of_mem x_in; omega

def getNameFromMd (md : Imperative.MetaData Core.Expression): String :=
  let fileRange := (Imperative.getFileRange md).get!
  s!"({fileRange.range.start})"

/--
Translate Laurel StmtExpr to Core Statements
Takes the list of output parameter names to handle return statements correctly
-/
def translateStmt (outputParams : List Parameter) (stmt : StmtExpr) : List Core.Statement :=
  match stmt with
  | @StmtExpr.Assert cond md =>
      let coreExpr := translateExpr cond
      [Core.Statement.assert ("assert" ++ getNameFromMd md) coreExpr md]
  | @StmtExpr.Assume cond md =>
      let coreExpr := translateExpr cond
      [Core.Statement.assume ("assume" ++ getNameFromMd md) coreExpr md]
  | .Block stmts _ =>
      stmts.flatMap (translateStmt outputParams)
  | .LocalVariable name ty initializer =>
      let coreMonoType := translateType ty
      let coreType := LTy.forAll [] coreMonoType
      let ident := Core.CoreIdent.locl name
      match initializer with
      | some initExpr =>
          let coreExpr := translateExpr initExpr
          [Core.Statement.init ident coreType coreExpr]
      | none =>
          -- Initialize with default value
          let defaultExpr := match ty with
                            | .TInt => .const () (.intConst 0)
                            | .TBool => .const () (.boolConst false)
                            | _ => .const () (.intConst 0)
          [Core.Statement.init ident coreType defaultExpr]
  | .Assign target value =>
      match target with
      | .Identifier name =>
          let ident := Core.CoreIdent.locl name
          let coreExpr := translateExpr value
          [Core.Statement.set ident coreExpr]
      | _ => []  -- Can only assign to simple identifiers
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond := translateExpr cond
      let bthen := translateStmt outputParams thenBranch
      let belse := match elseBranch with
                  | some e => translateStmt outputParams e
                  | none => []
      -- Use Core's if-then-else construct
      [Imperative.Stmt.ite bcond bthen belse .empty]
  | .StaticCall name args =>
      let coreArgs := args.map translateExpr
      [Core.Statement.call [] name coreArgs]
  | .Return valueOpt =>
      -- In Core, returns are done by assigning to output parameters
      match valueOpt, outputParams.head? with
      | some value, some outParam =>
          -- Assign to the first output parameter, then assume false for no fallthrough
          let ident := Core.CoreIdent.locl outParam.name
          let coreExpr := translateExpr value
          let assignStmt := Core.Statement.set ident coreExpr
          let noFallThrough := Core.Statement.assume "return" (.const () (.boolConst false)) .empty
          [assignStmt, noFallThrough]
      | none, _ =>
          -- Return with no value - just indicate no fallthrough
          let noFallThrough := Core.Statement.assume "return" (.const () (.boolConst false)) .empty
          [noFallThrough]
      | some _, none =>
          -- Error: trying to return a value but no output parameters
          panic! "Return statement with value but procedure has no output parameters"
  | _ => panic! Std.Format.pretty (Std.ToFormat.format stmt)

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
def translateProcedure (proc : Procedure) : Core.Procedure :=
  -- Translate input parameters
  let inputPairs := proc.inputs.map translateParameterToCore
  let inputs := inputPairs

  let header : Core.Procedure.Header := {
    name := proc.name
    typeArgs := []
    inputs := inputs
    outputs := proc.outputs.map translateParameterToCore
  }
  let spec : Core.Procedure.Spec := {
    modifies := []
    preconditions := []
    postconditions := []
  }
  let body : List Core.Statement :=
    match proc.body with
    | .Transparent bodyExpr => translateStmt proc.outputs bodyExpr
    | _ => []  -- TODO: handle Opaque and Abstract bodies
  {
    header := header
    spec := spec
    body := body
  }

/--
Translate Laurel Program to Core Program
-/
def translate (program : Program) : Core.Program :=
  -- First, sequence all assignments (move them out of expression positions)
  let sequencedProgram := liftExpressionAssignments program
  dbg_trace "=== Sequenced program Program ==="
  dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format sequencedProgram)))
  dbg_trace "================================="
  -- Then translate to Core
  let procedures := sequencedProgram.staticProcedures.map translateProcedure
  let decls := procedures.map (fun p => Core.Decl.proc p .empty)
  { decls := decls }

/--
Verify a Laurel program using an SMT solver
-/
def verifyToVcResults (smtsolver : String) (program : Program)
    (options : Options := Options.default) : IO VCResults := do
  let coreProgram := translate program
  -- Debug: Print the generated Core program
  dbg_trace "=== Generated Core.Program ==="
  dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format coreProgram)))
  dbg_trace "================================="
  IO.FS.withTempDir (fun tempDir =>
    EIO.toIO (fun f => IO.Error.userError (toString f))
      (Core.verify smtsolver coreProgram tempDir options))

def verifyToDiagnostics (smtsolver : String) (files: Map Strata.Uri Lean.FileMap) (program : Program): IO (Array Diagnostic) := do
  let results <- verifyToVcResults smtsolver program
  return results.filterMap (toDiagnostic files)

def verifyToDiagnosticModels (smtsolver : String) (program : Program): IO (Array DiagnosticModel) := do
  let results <- verifyToVcResults smtsolver program
  return results.filterMap toDiagnosticModel

end Laurel
