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

namespace Laurel

open Boogie (VCResult VCResults)
open Strata

/-
Translate Laurel StmtExpr to Boogie Expression
-/
partial def translateExpr (expr : StmtExpr) : Boogie.Expression.Expr :=
  match expr with
  | .LiteralBool true => .boolConst () true
  | .LiteralBool false => .boolConst () false
  | _ => .boolConst () true  -- TODO: handle other expressions

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
  | _ => []  -- TODO: handle other statements

/-
Translate Laurel Procedure to Boogie Procedure
-/
def translateProcedure (proc : Procedure) : Boogie.Procedure :=
  let header : Boogie.Procedure.Header := {
    name := proc.name
    typeArgs := []
    inputs := []
    outputs := []
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
  let procedures := program.staticProcedures.map translateProcedure
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
