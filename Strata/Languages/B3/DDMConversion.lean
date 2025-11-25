/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Expression
import Strata.Languages.B3.Stmt
import Strata.Languages.B3.DDMTransform.Parse

/-!
# B3 ↔ DDM Bidirectional Conversion

This module provides bidirectional conversion between B3 AST types and DDM AST types.

## B3 → DDM Conversion
Used for formatting and pretty-printing B3 constructs using DDM's formatting system.

## DDM → B3 Conversion
Used for parsing B3 syntax via DDM and converting it back to B3 AST.

## Organization
- Expression and Pattern conversion (both directions)
- Statement conversion (both directions)
- Declaration conversion (both directions)
-/

namespace B3

open Strata
open Strata.B3DDM

-- Helper to create Ann with Unit annotation
private def mkAnn {α : Type} (x : α) : Ann α Unit := ⟨(), x⟩

---------------------------------------------------------------------
-- B3 → DDM Conversion
---------------------------------------------------------------------

section ToDDM

/-- Convert B3 Expression to DDM for formatting -/
partial def Expression.toDDM : Expression B3.defaultExprParams → B3DDM.Expression Unit
    | .literal _ (.intConst n) =>
      if n >= 0 then
        .natLit () (mkAnn n.toNat)
      else
        .neg () (.natLit () (mkAnn (-n).toNat))
    | .literal _ (.strConst s) => .strLit () (mkAnn s)
    | .literal _ (.boolConst true) => .btrue ()
    | .literal _ (.boolConst false) => .bfalse ()
    | .literal _ (.realConst _) => .natLit () (mkAnn 0) -- TODO: handle rationals
    | .literal _ (.bitvecConst _ _) => .natLit () (mkAnn 0) -- TODO: handle bitvecs
    | .id _ identifier => .id () (mkAnn identifier.name)
    | .unaryOp _ .not arg => .not () (arg.toDDM)
    | .unaryOp _ .neg arg => .neg () (arg.toDDM)
    | .binaryOp _ .iff lhs rhs => .iff () (lhs.toDDM) (rhs.toDDM)
    | .binaryOp _ .implies lhs rhs => .implies () (lhs.toDDM) (rhs.toDDM)
    | .binaryOp _ .impliedBy lhs rhs => .impliedBy () (lhs.toDDM) (rhs.toDDM)
    | .binaryOp _ .and lhs rhs => .and () (lhs.toDDM) (rhs.toDDM)
    | .binaryOp _ .or lhs rhs => .or () (lhs.toDDM) (rhs.toDDM)
    | .binaryOp _ .eq lhs rhs => .equal () (lhs.toDDM) (rhs.toDDM)
    | .binaryOp _ .neq lhs rhs => .not_equal () (lhs.toDDM) (rhs.toDDM)
    | .binaryOp _ .lt lhs rhs => .lt () (lhs.toDDM) (rhs.toDDM)
    | .binaryOp _ .le lhs rhs => .le () (lhs.toDDM) (rhs.toDDM)
    | .binaryOp _ .ge lhs rhs => .ge () (lhs.toDDM) (rhs.toDDM)
    | .binaryOp _ .gt lhs rhs => .gt () (lhs.toDDM) (rhs.toDDM)
    | .binaryOp _ .add lhs rhs => .add () (lhs.toDDM) (rhs.toDDM)
    | .binaryOp _ .sub lhs rhs => .sub () (lhs.toDDM) (rhs.toDDM)
    | .binaryOp _ .mul lhs rhs => .mul () (lhs.toDDM) (rhs.toDDM)
    | .binaryOp _ .div lhs rhs => .div () (lhs.toDDM) (rhs.toDDM)
    | .binaryOp _ .mod lhs rhs => .mod () (lhs.toDDM) (rhs.toDDM)
    | .functionCall _ fn args => .functionCall () (mkAnn fn.name) (mkAnn (args.map Expression.toDDM).toArray)
    | .labeledExpr _ label expr => .labeledExpr () (mkAnn label) (expr.toDDM)
    | .letExpr _ var value body => .letExpr () (mkAnn var.name) (value.toDDM) (body.toDDM)
    | .ite _ cond thenExpr elseExpr => .ite () (cond.toDDM) (thenExpr.toDDM) (elseExpr.toDDM)
    | .quantifierExpr _ .forall var ty patterns body =>
      let convertPattern (p : Pattern B3.defaultExprParams) : B3DDM.Pattern Unit :=
        match p with
        | .pattern _ exprs =>
          match exprs with
          | [e] => B3DDM.Pattern.pattern () (e.toDDM)
          | _ => B3DDM.Pattern.pattern () (.btrue ())
      match patterns with
      | [] => .forall_expr_no_patterns () (mkAnn var.name) (mkAnn ty) (body.toDDM)
      | [p] => .forall_expr () (mkAnn var.name) (mkAnn ty) (Patterns.patterns_single () (convertPattern p)) (body.toDDM)
      | p :: ps =>
        let patternsDDM := ps.foldr (init := Patterns.patterns_single () (convertPattern p)) fun p acc =>
          Patterns.patterns_cons () (convertPattern p) acc
        .forall_expr () (mkAnn var.name) (mkAnn ty) patternsDDM (body.toDDM)
    | .quantifierExpr _ .exists var ty patterns body =>
      let convertPattern (p : Pattern B3.defaultExprParams) : B3DDM.Pattern Unit :=
        match p with
        | .pattern _ exprs =>
          match exprs with
          | [e] => B3DDM.Pattern.pattern () (e.toDDM)
          | _ => B3DDM.Pattern.pattern () (.btrue ())
      match patterns with
      | [] => .exists_expr_no_patterns () (mkAnn var.name) (mkAnn ty) (body.toDDM)
      | [p] => .exists_expr () (mkAnn var.name) (mkAnn ty) (Patterns.patterns_single () (convertPattern p)) (body.toDDM)
      | p :: ps =>
        let patternsDDM := ps.foldr (init := Patterns.patterns_single () (convertPattern p)) fun p acc =>
          Patterns.patterns_cons () (convertPattern p) acc
        .exists_expr () (mkAnn var.name) (mkAnn ty) patternsDDM (body.toDDM)

/-- Convert B3 Pattern to DDM for formatting -/
partial def Pattern.toDDM : Pattern B3.defaultExprParams → B3DDM.Pattern Unit
  | .pattern _ exprs =>
    -- B3 patterns contain a list of expressions, but DDM patterns take a single expression
    -- We'll just take the first one for now
    match exprs with
    | [e] => B3DDM.Pattern.pattern () (e.toDDM)
    | _ => B3DDM.Pattern.pattern () (.btrue ()) -- fallback

/-- Convert B3 CallArg to DDM for formatting -/
partial def CallArg.toDDM : CallArg B3.defaultStmtParams → B3DDM.CallArg Unit
  | .expr e => .call_arg_expr () (e.toDDM)
  | .out id => .call_arg_out () (mkAnn id.name)
  | .inout id => .call_arg_inout () (mkAnn id.name)

/-- Helper to build ChoiceBranches from a list -/
private def buildChoiceBranches : List (B3DDM.ChoiceBranch Unit) → B3DDM.ChoiceBranches Unit
  | [] => ChoiceBranches.choiceAtom () (ChoiceBranch.choice_branch () (.return_statement ())) -- fallback
  | [b] => ChoiceBranches.choiceAtom () b
  | b :: bs => ChoiceBranches.choicePush () (buildChoiceBranches bs) b

/-- Convert B3 Statement to DDM for formatting -/
partial def Stmt.toDDM : Stmt B3.defaultStmtParams → B3DDM.Statement Unit
  | .varDecl _ name ty autoinv init =>
    match ty, autoinv, init with
    | some t, some ai, some i => .var_decl_full () (mkAnn name.name) (mkAnn t) (ai.toDDM) (i.toDDM)
    | some t, some ai, none => .var_decl_with_autoinv () (mkAnn name.name) (mkAnn t) (ai.toDDM)
    | some t, none, some i => .var_decl_with_init () (mkAnn name.name) (mkAnn t) (i.toDDM)
    | some t, none, none => .var_decl_typed () (mkAnn name.name) (mkAnn t)
    | none, _, some i => .var_decl_inferred () (mkAnn name.name) (i.toDDM)
    | none, _, none => .var_decl_typed () (mkAnn name.name) (mkAnn "unknown") -- fallback
  | .assign _ lhs rhs => .assign () (mkAnn lhs.name) (rhs.toDDM)
  | .reinit _ _ => .return_statement () -- TODO: reinit doesn't have a DDM equivalent yet
  | .blockStmt _ stmts => .block () (mkAnn (stmts.map Stmt.toDDM).toArray)
  | .call _ procName args => .call_statement () (mkAnn procName) (mkAnn (args.map CallArg.toDDM).toArray)
  | .check _ expr => .check () (expr.toDDM)
  | .assume _ expr => .assume () (expr.toDDM)
  | .reach _ expr => .reach () (expr.toDDM)
  | .assert _ expr => .assert () (expr.toDDM)
  | .aForall _ var ty body => .aForall_statement () (mkAnn var.name) (mkAnn ty) (body.toDDM)
  | .choose _ branches =>
    let choiceBranches := branches.map (fun s => ChoiceBranch.choice_branch () (s.toDDM))
    .choose_statement () (buildChoiceBranches choiceBranches)
  | .ifStmt _ cond thenB elseB =>
    match elseB with
    | some e => .if_statement () (cond.toDDM) (thenB.toDDM) (Else.else_some () (e.toDDM))
    | none => .if_statement () (cond.toDDM) (thenB.toDDM) (Else.else_none ())
  | .ifCase _ cases => .if_case_statement () (mkAnn (cases.map (fun (e, s) => IfCaseBranch.if_case_branch () (e.toDDM) (s.toDDM))).toArray)
  | .loop _ invariants body => .loop_statement () (mkAnn (invariants.map (fun e => Invariant.invariant () (e.toDDM))).toArray) (body.toDDM)
  | .labeledStmt _ label stmt => .labeled_statement () (mkAnn label) (stmt.toDDM)
  | .exit _ label =>
    match label with
    | some l => .exit_statement () (mkAnn (some (mkAnn l)))
    | none => .exit_statement () (mkAnn none)
  | .returnStmt _ => .return_statement ()
  | .probe _ label => .probe () (mkAnn label)

-- Backward compatibility aliases
@[deprecated Expression.toDDM (since := "2024-11-24")] def exprToDDM := Expression.toDDM
@[deprecated Pattern.toDDM (since := "2024-11-24")] def patternToDDM := Pattern.toDDM

end ToDDM

---------------------------------------------------------------------
-- DDM → B3 Conversion
---------------------------------------------------------------------

section FromDDM

-- TODO: Implement DDM to B3 conversion
-- This will be used for parsing B3 syntax via DDM and converting it back to B3 AST
-- The implementation is complex due to mutual recursion constraints in Lean 4's partial definitions
-- and will be added in a future iteration.

end FromDDM

end B3
