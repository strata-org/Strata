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
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.MetaData
import Strata.DL.Lambda.LExpr
import Strata.Languages.Laurel.LaurelFormat

namespace Laurel

open Boogie (VCResult VCResults)
open Strata

open Boogie (intAddOp intSubOp intMulOp intDivOp intModOp intNegOp intLtOp intLeOp intGtOp intGeOp boolAndOp boolOrOp boolNotOp)
open Lambda (LMonoTy LTy LExpr)

/-
Translate Laurel HighType to Boogie Type
-/
def translateType (ty : HighType) : LMonoTy :=
  match ty with
  | .TInt => LMonoTy.int
  | .TBool => LMonoTy.bool
  | .TVoid => LMonoTy.bool  -- Using bool as placeholder for void
  | _ => panic s!"unsupported type {repr ty}"

/--
Translate Laurel StmtExpr to Boogie Expression
-/
def translateExpr (expr : StmtExpr) : Boogie.Expression.Expr :=
  match h: expr with
  | .LiteralBool b => .const () (.boolConst b)
  | .LiteralInt i => .const () (.intConst i)
  | .Identifier name =>
      let ident := Boogie.BoogieIdent.locl name
      .fvar () ident (some LMonoTy.int)  -- Default to int type
  | .PrimitiveOp op [e] =>
    match op with
    | .Not => .app () boolNotOp (translateExpr e)
    | .Neg => .app () intNegOp (translateExpr e)
    | _ => panic! s!"translateExpr: Invalid unary op: {repr op}"
  | .PrimitiveOp op [e1, e2] =>
    let binOp (bop : Boogie.Expression.Expr): Boogie.Expression.Expr :=
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
      let ident := Boogie.BoogieIdent.glob name
      let fnOp := .op () ident (some LMonoTy.int)  -- Assume int return type
      args.foldl (fun acc arg => .app () acc (translateExpr arg)) fnOp
  | _ => panic! Std.Format.pretty (Std.ToFormat.format expr)
  decreasing_by
  all_goals (simp_wf; try omega)
  rename_i x_in; have := List.sizeOf_lt_of_mem x_in; omega

def getNameFromMd (md : Imperative.MetaData Boogie.Expression): String :=
  let fileRange := (Imperative.getFileRange md).get!
  s!"({fileRange.start.column},{fileRange.start.line})"

/--
Translate Laurel StmtExpr to Boogie Statements
Takes the list of output parameter names to handle return statements correctly
-/
def translateStmt (outputParams : List Parameter) (stmt : StmtExpr) : List Boogie.Statement :=
  match stmt with
  | @StmtExpr.Assert cond md =>
      let boogieExpr := translateExpr cond
      [Boogie.Statement.assert ("assert" ++ getNameFromMd md) boogieExpr md]
  | @StmtExpr.Assume cond md =>
      let boogieExpr := translateExpr cond
      [Boogie.Statement.assume ("assume" ++ getNameFromMd md) boogieExpr md]
  | .Block stmts _ =>
      stmts.flatMap (translateStmt outputParams)
  | .LocalVariable name ty initializer =>
      let boogieMonoType := translateType ty
      let boogieType := LTy.forAll [] boogieMonoType
      let ident := Boogie.BoogieIdent.locl name
      match initializer with
      | some initExpr =>
          let boogieExpr := translateExpr initExpr
          [Boogie.Statement.init ident boogieType boogieExpr]
      | none =>
          -- Initialize with default value
          let defaultExpr := match ty with
                            | .TInt => .const () (.intConst 0)
                            | .TBool => .const () (.boolConst false)
                            | _ => .const () (.intConst 0)
          [Boogie.Statement.init ident boogieType defaultExpr]
  | .Assign target value =>
      match target with
      | .Identifier name =>
          let ident := Boogie.BoogieIdent.locl name
          let boogieExpr := translateExpr value
          [Boogie.Statement.set ident boogieExpr]
      | _ => []  -- Can only assign to simple identifiers
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond := translateExpr cond
      let bthen := translateStmt outputParams thenBranch
      let belse := match elseBranch with
                  | some e => translateStmt outputParams e
                  | none => []
      -- Use Boogie's if-then-else construct
      [Imperative.Stmt.ite bcond bthen belse .empty]
  | .StaticCall name args =>
      let boogieArgs := args.map translateExpr
      [Boogie.Statement.call [] name boogieArgs]
  | .Return valueOpt =>
      -- In Boogie, returns are done by assigning to output parameters
      match valueOpt, outputParams.head? with
      | some value, some outParam =>
          -- Assign to the first output parameter, then assume false for no fallthrough
          let ident := Boogie.BoogieIdent.locl outParam.name
          let boogieExpr := translateExpr value
          let assignStmt := Boogie.Statement.set ident boogieExpr
          let noFallThrough := Boogie.Statement.assume "return" (.const () (.boolConst false)) .empty
          [assignStmt, noFallThrough]
      | none, _ =>
          -- Return with no value - just indicate no fallthrough
          let noFallThrough := Boogie.Statement.assume "return" (.const () (.boolConst false)) .empty
          [noFallThrough]
      | some _, none =>
          -- Error: trying to return a value but no output parameters
          panic! "Return statement with value but procedure has no output parameters"
  | _ => panic! Std.Format.pretty (Std.ToFormat.format stmt)

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
def translateProcedure (proc : Procedure) : Boogie.Procedure :=
  -- Translate input parameters
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
  let body : List Boogie.Statement :=
    match proc.body with
    | .Transparent bodyExpr => translateStmt proc.outputs bodyExpr
    | _ => []  -- TODO: handle Opaque and Abstract bodies
  {
    header := header
    spec := spec
    body := body
  }

/--
Translate Laurel Program to Boogie Program
-/
def translate (program : Program) : Boogie.Program :=
  -- First, sequence all assignments (move them out of expression positions)
  let sequencedProgram := liftExpressionAssignments program
  dbg_trace "=== Sequenced program Program ==="
  dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format sequencedProgram)))
  dbg_trace "================================="
  -- Then translate to Boogie
  let procedures := sequencedProgram.staticProcedures.map translateProcedure
  let decls := procedures.map (fun p => Boogie.Decl.proc p .empty)
  { decls := decls }

/--
Verify a Laurel program using an SMT solver
-/
def verifyToVcResults (smtsolver : String) (program : Program)
    (options : Options := Options.default) : IO VCResults := do
  let boogieProgram := translate program
  -- Debug: Print the generated Boogie program
  dbg_trace "=== Generated Boogie Program ==="
  dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format boogieProgram)))
  dbg_trace "================================="
  EIO.toIO (fun f => IO.Error.userError (toString f))
      (Boogie.verify smtsolver boogieProgram options)

def verifyToDiagnostics (smtsolver : String) (program : Program): IO (Array Diagnostic)  := do
  let results <- verifyToVcResults smtsolver program
  return results.filterMap toDiagnostic

end Laurel
