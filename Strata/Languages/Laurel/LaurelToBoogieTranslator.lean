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
import Strata.Languages.Laurel.SequenceAssignments

namespace Laurel

open Boogie (VCResult VCResults)
open Strata

open Boogie (intAddOp)
open Lambda (LMonoTy LTy)

/-
Translate Laurel HighType to Boogie Type
-/
def translateType (ty : HighType) : LMonoTy :=
  match ty with
  | .TInt => LMonoTy.int
  | .TBool => LMonoTy.bool
  | .TVoid => LMonoTy.bool  -- Using bool as placeholder for void
  | _ => LMonoTy.int  -- Default to int for other types

/-
Translate Laurel StmtExpr to Boogie Expression
-/
partial def translateExpr (expr : StmtExpr) : Boogie.Expression.Expr :=
  match expr with
  | .LiteralBool b => .const () (.boolConst b)
  | .LiteralInt i => .const () (.intConst i)
  | .Identifier name =>
      let ident := Boogie.BoogieIdent.locl name
      .fvar () ident (some LMonoTy.int)  -- Default to int type
  | .PrimitiveOp .Add args =>
      match args with
      | [e1, e2] =>
          let be1 := translateExpr e1
          let be2 := translateExpr e2
          .app () (.app () intAddOp be1) be2
      | e1 :: e2 :: _ =>  -- More than 2 args
          let be1 := translateExpr e1
          let be2 := translateExpr e2
          .app () (.app () intAddOp be1) be2
      | [_] | [] => .const () (.intConst 0)  -- Error cases
  | .PrimitiveOp .Eq args =>
      match args with
      | [e1, e2] =>
          let be1 := translateExpr e1
          let be2 := translateExpr e2
          .eq () be1 be2
      | e1 :: e2 :: _ =>  -- More than 2 args
          let be1 := translateExpr e1
          let be2 := translateExpr e2
          .eq () be1 be2
      | [_] | [] => .const () (.boolConst false)  -- Error cases
  | .PrimitiveOp .Neq args =>
      match args with
      | [e1, e2] =>
          let be1 := translateExpr e1
          let be2 := translateExpr e2
          -- Negate equality
          .app () (.op () (Boogie.BoogieIdent.glob "Bool.Not") (some LMonoTy.bool)) (.eq () be1 be2)
      | e1 :: e2 :: _ =>  -- More than 2 args
          let be1 := translateExpr e1
          let be2 := translateExpr e2
          .app () (.op () (Boogie.BoogieIdent.glob "Bool.Not") (some LMonoTy.bool)) (.eq () be1 be2)
      | [_] | [] => .const () (.boolConst false)  -- Error cases
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
  | _ => .const () (.intConst 0)  -- Default for unhandled cases

/-
Translate Laurel StmtExpr to Boogie Statements
-/
partial def translateStmt (stmt : StmtExpr) : List Boogie.Statement :=
  match stmt with
  | @StmtExpr.Assert cond md =>
      let boogieExpr := translateExpr cond
      [Boogie.Statement.assert "assert" boogieExpr md]
  | @StmtExpr.Assume cond md =>
      let boogieExpr := translateExpr cond
      [Boogie.Statement.assume "assume" boogieExpr md]
  | .Block stmts _ =>
      stmts.flatMap translateStmt
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
      let bthen := translateStmt thenBranch
      let belse := match elseBranch with
                  | some e => translateStmt e
                  | none => []
      -- Boogie doesn't have if-else statements directly, we need to use havoc + assume
      -- For now, just translate branches and add conditional assumes
      let thenStmts := (Boogie.Statement.assume "then" bcond) :: bthen
      let elseStmts := match elseBranch with
                      | some _ =>
                          let notCond := .app () (.op () (Boogie.BoogieIdent.glob "Bool.Not") (some LMonoTy.bool)) bcond
                          (Boogie.Statement.assume "else" notCond) :: belse
                      | none => []
      thenStmts ++ elseStmts
  | .StaticCall name args =>
      let boogieArgs := args.map translateExpr
      [Boogie.Statement.call [] name boogieArgs]
  | _ => []  -- Default for unhandled cases

/-
Translate Laurel Parameter to Boogie Signature entry
-/
def translateParameterToBoogie (param : Parameter) : (Boogie.BoogieIdent × LMonoTy) :=
  let ident := Boogie.BoogieIdent.locl param.name
  let ty := translateType param.type
  (ident, ty)

/-
Translate Laurel Procedure to Boogie Procedure
-/
def translateProcedure (proc : Procedure) : Boogie.Procedure :=
  -- Translate input parameters
  let inputPairs := proc.inputs.map translateParameterToBoogie
  let inputs := inputPairs

  -- Translate output type
  let outputs :=
    match proc.output with
    | .TVoid => []  -- No return value
    | _ =>
        let retTy := translateType proc.output
        let retIdent := Boogie.BoogieIdent.locl "result"
        [(retIdent, retTy)]

  let header : Boogie.Procedure.Header := {
    name := proc.name
    typeArgs := []
    inputs := inputs
    outputs := outputs
  }
  let spec : Boogie.Procedure.Spec := {
    modifies := []
    preconditions := []
    postconditions := []
  }
  let body : List Boogie.Statement :=
    match proc.body with
    | .Transparent bodyExpr => translateStmt bodyExpr
    | _ => []  -- TODO: handle Opaque and Abstract bodies
  {
    header := header
    spec := spec
    body := body
  }

/-
Translate Laurel Program to Boogie Program
-/
def translate (program : Program) : Boogie.Program :=
  -- First, sequence all assignments (move them out of expression positions)
  let sequencedProgram := sequenceProgram program
  -- Then translate to Boogie
  let procedures := sequencedProgram.staticProcedures.map translateProcedure
  let decls := procedures.map (fun p => Boogie.Decl.proc p .empty)
  { decls := decls }

/-
Verify a Laurel program using an SMT solver
-/
def verifyToVcResults (smtsolver : String) (program : Program)
    (options : Options := Options.default) : IO VCResults := do
  let boogieProgram := translate program
  EIO.toIO (fun f => IO.Error.userError (toString f))
      (Boogie.verify smtsolver boogieProgram options)

def verifyToDiagnostics (smtsolver : String) (program : Program): IO (Array Diagnostic)  := do
  let results <- verifyToVcResults smtsolver program
  return results.filterMap toDiagnostic

end Laurel
