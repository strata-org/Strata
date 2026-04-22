/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Core.Statement

/-!
# Remove Unused Variables

A Core-to-Core transformation that removes `init` statements for variables
that are never referenced in subsequent statements. This is useful as a
pre-processing step before CoreSMT verification, where unused variables
with non-SMT types would cause errors.
-/

namespace Strata.Core.CoreSMT

open Imperative
open Lambda

/-- Collect all free variable names referenced in an expression. -/
partial def collectExprVarNames : Core.Expression.Expr → List String
  | .fvar _ name _ => [name.name]
  | .eq _ e1 e2 => collectExprVarNames e1 ++ collectExprVarNames e2
  | .ite _ c t e => collectExprVarNames c ++ collectExprVarNames t ++ collectExprVarNames e
  | .quant _ _ _ _ tr b => collectExprVarNames tr ++ collectExprVarNames b
  | .app _ fn arg => collectExprVarNames fn ++ collectExprVarNames arg
  | .abs _ _ _ body => collectExprVarNames body
  | _ => []

/-- Collect all variable names referenced in a command (excluding the defined variable). -/
def collectCmdUsedVarNames : Core.Command → List String
  | .cmd (.assume _ e _) => collectExprVarNames e
  | .cmd (.assert _ e _) => collectExprVarNames e
  | .cmd (.cover _ e _) => collectExprVarNames e
  | .cmd (.init _ _ (.det e) _) => collectExprVarNames e
  | .cmd (.init _ _ .nondet _) => []
  | .cmd (.set _ (.det e) _) => collectExprVarNames e
  | .cmd (.set _ .nondet _) => []
  | .call _ args _ => args.flatMap (fun a => match a with | .inArg e => collectExprVarNames e | _ => [])

mutual
/-- Collect all variable names referenced in a statement. -/
partial def collectStmtUsedVarNames : Core.Statement → List String
  | .cmd c => collectCmdUsedVarNames c
  | .block _ stmts _ => collectStmtsUsedVarNames stmts
  | .funcDecl decl _ =>
    match decl.body with
    | some e => collectExprVarNames e
    | none => []
  | .typeDecl _ _ => []
  | .ite cond thenB elseB _ =>
    (match cond with | .det e => collectExprVarNames e | .nondet => []) ++
    collectStmtsUsedVarNames thenB ++ collectStmtsUsedVarNames elseB
  | .loop guard _ _ body _ =>
    (match guard with | .det e => collectExprVarNames e | .nondet => []) ++
    collectStmtsUsedVarNames body
  | .exit _ _ => []

/-- Collect all variable names referenced in a list of statements. -/
partial def collectStmtsUsedVarNames : Core.Statements → List String
  | [] => []
  | s :: ss => collectStmtUsedVarNames s ++ collectStmtsUsedVarNames ss
end

mutual
/-- Remove unused init statements from a statement. -/
partial def removeUnusedVarsStmt : Core.Statement → Core.Statement
  | .block _label stmts _md => .ite .nondet (removeUnusedVarsStmts stmts) [] .empty
  | .ite cond thenB elseB md =>
    .ite cond (removeUnusedVarsStmts thenB) (removeUnusedVarsStmts elseB) md
  | .loop guard measure invs body md =>
    .loop guard measure invs (removeUnusedVarsStmts body) md
  | s => s

/-- Remove unused init statements from a list of statements.
    An init is unused if the variable name doesn't appear in any subsequent statement. -/
partial def removeUnusedVarsStmts : Core.Statements → Core.Statements
  | [] => []
  | s :: rest =>
    let rest' := removeUnusedVarsStmts rest
    match s with
    | .cmd (.cmd (.init name _ _ _)) =>
      if (collectStmtsUsedVarNames rest').contains name.name then
        removeUnusedVarsStmt s :: rest'
      else
        rest'
    | _ => removeUnusedVarsStmt s :: rest'
end

end Strata.Core.CoreSMT
