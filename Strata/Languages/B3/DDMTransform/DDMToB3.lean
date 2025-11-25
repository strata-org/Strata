/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Expression
import Strata.Languages.B3.Stmt
import Strata.Languages.B3.DDMTransform.Parse

/-!
# DDM to B3 Converter

This module converts DDM AST types back to B3 AST types for parsing and analysis.
This is the reverse of B3ToDDM and is used to convert parsed DDM syntax back into
B3's native AST representation.
-/

namespace B3

open Strata
open Strata.B3DDM

-- Inhabited instances needed for partial definitions
instance : Inhabited (Expression B3.defaultExprParams) where
  default := .literal () (.boolConst false)

instance : Inhabited (Pattern B3.defaultExprParams) where
  default := .pattern () []

instance : Inhabited (Stmt B3.defaultStmtParams) where
  default := .returnStmt ()

instance : Inhabited (CallArg B3.defaultStmtParams) where
  default := .expr (.literal () (.boolConst false))

---------------------------------------------------------------------
-- Expression and Pattern Conversion
---------------------------------------------------------------------

mutual
  /-- Convert DDM Expression to B3 Expression -/
  partial def Expression.fromDDM : B3DDM.Expression Unit → Expression B3.defaultExprParams
    | .natLit _ n => .literal () (.intConst (Int.ofNat n.val))
    | .strLit _ s => .literal () (.strConst s.val)
    | .btrue _ => .literal () (.boolConst true)
    | .bfalse _ => .literal () (.boolConst false)
    | .id _ name => .id () { name := name.val, metadata := .none }
    | .not _ arg => .unaryOp () .not (Expression.fromDDM arg)
    | .neg _ arg => .unaryOp () .neg (Expression.fromDDM arg)
    | .iff _ lhs rhs => .binaryOp () .iff (Expression.fromDDM lhs) (Expression.fromDDM rhs)
    | .implies _ lhs rhs => .binaryOp () .implies (Expression.fromDDM lhs) (Expression.fromDDM rhs)
    | .impliedBy _ lhs rhs => .binaryOp () .impliedBy (Expression.fromDDM lhs) (Expression.fromDDM rhs)
    | .and _ lhs rhs => .binaryOp () .and (Expression.fromDDM lhs) (Expression.fromDDM rhs)
    | .or _ lhs rhs => .binaryOp () .or (Expression.fromDDM lhs) (Expression.fromDDM rhs)
    | .equal _ lhs rhs => .binaryOp () .eq (Expression.fromDDM lhs) (Expression.fromDDM rhs)
    | .not_equal _ lhs rhs => .binaryOp () .neq (Expression.fromDDM lhs) (Expression.fromDDM rhs)
    | .lt _ lhs rhs => .binaryOp () .lt (Expression.fromDDM lhs) (Expression.fromDDM rhs)
    | .le _ lhs rhs => .binaryOp () .le (Expression.fromDDM lhs) (Expression.fromDDM rhs)
    | .ge _ lhs rhs => .binaryOp () .ge (Expression.fromDDM lhs) (Expression.fromDDM rhs)
    | .gt _ lhs rhs => .binaryOp () .gt (Expression.fromDDM lhs) (Expression.fromDDM rhs)
    | .add _ lhs rhs => .binaryOp () .add (Expression.fromDDM lhs) (Expression.fromDDM rhs)
    | .sub _ lhs rhs => .binaryOp () .sub (Expression.fromDDM lhs) (Expression.fromDDM rhs)
    | .mul _ lhs rhs => .binaryOp () .mul (Expression.fromDDM lhs) (Expression.fromDDM rhs)
    | .div _ lhs rhs => .binaryOp () .div (Expression.fromDDM lhs) (Expression.fromDDM rhs)
    | .mod _ lhs rhs => .binaryOp () .mod (Expression.fromDDM lhs) (Expression.fromDDM rhs)
    | .functionCall _ fn args => .functionCall () { name := fn.val, metadata := .none } (args.val.toList.map Expression.fromDDM)
    | .labeledExpr _ label expr => .labeledExpr () label.val (Expression.fromDDM expr)
    | .letExpr _ var value body => .letExpr () { name := var.val, metadata := .none } (Expression.fromDDM value) (Expression.fromDDM body)
    | .ite _ cond thenExpr elseExpr => .ite () (Expression.fromDDM cond) (Expression.fromDDM thenExpr) (Expression.fromDDM elseExpr)
    | .forall_expr_no_patterns _ var ty body =>
        .quantifierExpr () .forall { name := var.val, metadata := .none } ty.val [] (Expression.fromDDM body)
    | .forall_expr _ var ty patterns body =>
        let patternsB3 := patternsFromDDM patterns
        .quantifierExpr () .forall { name := var.val, metadata := .none } ty.val patternsB3 (Expression.fromDDM body)
    | .exists_expr_no_patterns _ var ty body =>
        .quantifierExpr () .exists { name := var.val, metadata := .none } ty.val [] (Expression.fromDDM body)
    | .exists_expr _ var ty patterns body =>
        let patternsB3 := patternsFromDDM patterns
        .quantifierExpr () .exists { name := var.val, metadata := .none } ty.val patternsB3 (Expression.fromDDM body)
    | .paren _ expr => Expression.fromDDM expr

  /-- Helper to convert DDM Patterns to B3 Pattern list -/
  private partial def patternsFromDDM : B3DDM.Patterns Unit → List (Pattern B3.defaultExprParams)
    | .patterns_single _ p => [patternFromDDM p]
    | .patterns_cons _ p ps => patternFromDDM p :: patternsFromDDM ps

  /-- Convert DDM Pattern to B3 Pattern -/
  private partial def patternFromDDM : B3DDM.Pattern Unit → Pattern B3.defaultExprParams
    | .pattern _ expr => .pattern () [Expression.fromDDM expr]
end

---------------------------------------------------------------------
-- Statement Conversion
---------------------------------------------------------------------

mutual
  /-- Convert DDM CallArg to B3 CallArg -/
  partial def CallArg.fromDDM : B3DDM.CallArg Unit → CallArg B3.defaultStmtParams
    | .call_arg_expr _ e => .expr (Expression.fromDDM e)
    | .call_arg_out _ id => .out { name := id.val, metadata := .none }
    | .call_arg_inout _ id => .inout { name := id.val, metadata := .none }

  /-- Helper to convert DDM ChoiceBranches to B3 Statement list -/
  private partial def choiceBranchesFromDDM : B3DDM.ChoiceBranches Unit → List (Stmt B3.defaultStmtParams)
    | .choiceAtom _ b => [choiceBranchFromDDM b]
    | .choicePush _ bs b => choiceBranchesFromDDM bs ++ [choiceBranchFromDDM b]

  /-- Helper to convert DDM ChoiceBranch to B3 Statement -/
  private partial def choiceBranchFromDDM : B3DDM.ChoiceBranch Unit → Stmt B3.defaultStmtParams
    | .choice_branch _ s => Stmt.fromDDM s

  /-- Convert DDM Statement to B3 Statement -/
  partial def Stmt.fromDDM : B3DDM.Statement Unit → Stmt B3.defaultStmtParams
  | .var_decl_full _ name ty autoinv init =>
      .varDecl () { name := name.val, metadata := .none } (some ty.val) (some (Expression.fromDDM autoinv)) (some (Expression.fromDDM init))
  | .var_decl_with_autoinv _ name ty autoinv =>
      .varDecl () { name := name.val, metadata := .none } (some ty.val) (some (Expression.fromDDM autoinv)) none
  | .var_decl_with_init _ name ty init =>
      .varDecl () { name := name.val, metadata := .none } (some ty.val) none (some (Expression.fromDDM init))
  | .var_decl_typed _ name ty =>
      .varDecl () { name := name.val, metadata := .none } (some ty.val) none none
  | .var_decl_inferred _ name init =>
      .varDecl () { name := name.val, metadata := .none } none none (some (Expression.fromDDM init))
  | .val_decl _ name ty init =>
      -- val_decl maps to varDecl in B3 (B3 doesn't distinguish var/val at AST level)
      .varDecl () { name := name.val, metadata := .none } (some ty.val) none (some (Expression.fromDDM init))
  | .val_decl_inferred _ name init =>
      -- val_decl_inferred maps to varDecl in B3
      .varDecl () { name := name.val, metadata := .none } none none (some (Expression.fromDDM init))
  | .assign _ lhs rhs => .assign () { name := lhs.val, metadata := .none } (Expression.fromDDM rhs)
  | .block _ stmts => .blockStmt () (stmts.val.toList.map Stmt.fromDDM)
  | .call_statement _ procName args => .call () procName.val (args.val.toList.map CallArg.fromDDM)
  | .check _ expr => .check () (Expression.fromDDM expr)
  | .assume _ expr => .assume () (Expression.fromDDM expr)
  | .reach _ expr => .reach () (Expression.fromDDM expr)
  | .assert _ expr => .assert () (Expression.fromDDM expr)
  | .aForall_statement _ var ty body => .aForall () { name := var.val, metadata := .none } ty.val (Stmt.fromDDM body)
  | .choose_statement _ branches => .choose () (choiceBranchesFromDDM branches)
  | .if_statement _ cond thenB elseB =>
      match elseB with
      | .else_some _ e => .ifStmt () (Expression.fromDDM cond) (Stmt.fromDDM thenB) (some (Stmt.fromDDM e))
      | .else_none _ => .ifStmt () (Expression.fromDDM cond) (Stmt.fromDDM thenB) none
  | .if_case_statement _ cases =>
      let casesB3 := cases.val.toList.map fun case =>
        match case with
        | .if_case_branch _ cond body => (Expression.fromDDM cond, Stmt.fromDDM body)
      .ifCase () casesB3
  | .loop_statement _ invariants body =>
      let invsB3 := invariants.val.toList.map fun inv =>
        match inv with
        | .invariant _ e => Expression.fromDDM e
      .loop () invsB3 (Stmt.fromDDM body)
  | .labeled_statement _ label stmt => .labeledStmt () label.val (Stmt.fromDDM stmt)
  | .exit_statement _ label =>
      match label.val with
      | some l => .exit () (some l.val)
      | none => .exit () none
  | .return_statement _ => .returnStmt ()
  | .probe _ label => .probe () label.val
end

end B3
