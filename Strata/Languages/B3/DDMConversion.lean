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

## B3AST → B3CST Conversion
Converts abstract syntax (de Bruijn indices) to concrete syntax (named identifiers).
Used for formatting and pretty-printing B3 constructs using DDM's formatting system.

## B3CST → B3AST Conversion
Converts concrete syntax (named identifiers) to abstract syntax (de Bruijn indices).
Used for parsing B3 syntax via DDM and converting it back to B3 AST.

## Context Management
A list of variable names is maintained to convert between indices and names.
-/

namespace B3

open Strata
open Strata.B3CST
open Strata.B3AST

private def mkAnn {α : Type} (x : α) : Ann α Unit := ⟨(), x⟩

---------------------------------------------------------------------
-- B3AST → B3CST Conversion (Abstract to Concrete)
---------------------------------------------------------------------

section ToCST

structure ToCSTContext where
  vars : List String

namespace ToCSTContext

def lookup (ctx : ToCSTContext) (idx : Nat): String :=
  match ctx.vars[idx]? with
  | .some name =>
    if name == "" then s!"@{idx}" else
    -- We need to resolve ambiguities
    let rec go (vars: List String) (pastIndex: Nat) (idx: Nat): String :=
      let default := fun _: Unit => if pastIndex == 0 then
          name  -- No ambiguity
        else
          s!"name@{pastIndex}"
      if idx == 0 then
        default ()
      else
        match vars with
        | [] => default ()
        | otherName :: tail =>
          if name == otherName then
            go tail (pastIndex + 1) (idx - 1)
          else
            go tail pastIndex (idx - 1)

    go ctx.vars 0 idx
  | .none =>
    s!"@{idx}"

def push (ctx : ToCSTContext) (name : String) : ToCSTContext :=
  { vars := name :: ctx.vars }

def empty : ToCSTContext := { vars := [] }

end ToCSTContext

mutual

partial def binaryOpToCST : B3AST.BinaryOp Unit →
    (B3CST.Expression Unit → B3CST.Expression Unit → B3CST.Expression Unit)
  | .iff _ => B3CST.Expression.iff ()
  | .implies _ => B3CST.Expression.implies ()
  | .impliedBy _ => B3CST.Expression.impliedBy ()
  | .and _ => B3CST.Expression.and ()
  | .or _ => B3CST.Expression.or ()
  | .eq _ => B3CST.Expression.equal ()
  | .neq _ => B3CST.Expression.not_equal ()
  | .lt _ => B3CST.Expression.lt ()
  | .le _ => B3CST.Expression.le ()
  | .ge _ => B3CST.Expression.ge ()
  | .gt _ => B3CST.Expression.gt ()
  | .add _ => B3CST.Expression.add ()
  | .sub _ => B3CST.Expression.sub ()
  | .mul _ => B3CST.Expression.mul ()
  | .div _ => B3CST.Expression.div ()
  | .mod _ => B3CST.Expression.mod ()

partial def unaryOpToCST : B3AST.UnaryOp Unit →
    (B3CST.Expression Unit → B3CST.Expression Unit)
  | .not _ => B3CST.Expression.not ()
  | .neg _ => B3CST.Expression.neg ()

partial def literalToCST : B3AST.Literal Unit → B3CST.Expression Unit
  | .intLit _ n => B3CST.Expression.natLit () n
  | .boolLit _ b => match b with | ⟨_, true⟩ => B3CST.Expression.btrue () | ⟨_, false⟩ => B3CST.Expression.bfalse ()
  | .stringLit _ s => B3CST.Expression.strLit () s

partial def expressionToCST (ctx : ToCSTContext) : B3.Expression → B3CST.Expression Unit
  | .literal _ lit =>
      literalToCST lit
  | .id _ idx =>
      B3CST.Expression.id () (mkAnn (ctx.lookup idx.val))
  | .ite _ cond thn els =>
      B3CST.Expression.ite () (expressionToCST ctx cond) (expressionToCST ctx thn) (expressionToCST ctx els)
  | .binaryOp _ op lhs rhs =>
      (binaryOpToCST op) (expressionToCST ctx lhs) (expressionToCST ctx rhs)
  | .unaryOp _ op arg =>
      (unaryOpToCST op) (expressionToCST ctx arg)
  | .functionCall _ fnName args =>
      B3CST.Expression.functionCall () fnName (mkAnn (args.val.map (expressionToCST ctx)))
  | .labeledExpr _ label expr =>
      B3CST.Expression.labeledExpr () label (expressionToCST ctx expr)
  | .letExpr _ var value body =>
      let ctx' := ctx.push var.val
      B3CST.Expression.letExpr () var (expressionToCST ctx value) (expressionToCST ctx' body)
  | .quantifierExpr _ qkind var ty patterns body =>
      let ctx' := ctx.push var.val
      let convertPattern (p : B3.Pattern) : B3CST.Pattern Unit :=
        match p with
        | .pattern _ exprs =>
            match exprs.val.toList with
            | [e] => B3CST.Pattern.pattern () (expressionToCST ctx' e)
            | _ => B3CST.Pattern.pattern () (B3CST.Expression.btrue ())
      let patternsDDM := match patterns.val.toList with
        | [] => none
        | [p] => some (Patterns.patterns_single () (convertPattern p))
        | p :: ps =>
            some (ps.foldl (init := Patterns.patterns_single () (convertPattern p)) fun acc p =>
              Patterns.patterns_cons () (convertPattern p) acc)
      match qkind with
      | .forall _ =>
          match patternsDDM with
          | none => B3CST.Expression.forall_expr_no_patterns () var ty (expressionToCST ctx' body)
          | some pats => B3CST.Expression.forall_expr () var ty pats (expressionToCST ctx' body)
      | .exists _ =>
          match patternsDDM with
          | none => B3CST.Expression.exists_expr_no_patterns () var ty (expressionToCST ctx' body)
          | some pats => B3CST.Expression.exists_expr () var ty pats (expressionToCST ctx' body)

partial def callArgToCST (ctx : ToCSTContext) : B3.CallArg → B3CST.CallArg Unit
  | .callArgExpr _ e => B3CST.CallArg.call_arg_expr () (expressionToCST ctx e)
  | .callArgOut _ id => B3CST.CallArg.call_arg_out () (mkAnn id.val)
  | .callArgInout _ id => B3CST.CallArg.call_arg_inout () (mkAnn id.val)

partial def buildChoiceBranches : List (B3CST.ChoiceBranch Unit) → B3CST.ChoiceBranches Unit
  | [] => ChoiceBranches.choiceAtom () (ChoiceBranch.choice_branch () (B3CST.Statement.return_statement ()))
  | [b] => ChoiceBranches.choiceAtom () b
  | b :: bs => ChoiceBranches.choicePush () (buildChoiceBranches bs) b

partial def stmtToCST (ctx : ToCSTContext) : B3.Stmt → B3CST.Statement Unit
  | .varDecl _ name ty autoinv init =>
    let ctx' := ctx.push name.val
    match ty.val, autoinv.val, init.val with
    | some t, some ai, some i => B3CST.Statement.var_decl_full () (mkAnn name.val) (mkAnn t.val) (expressionToCST ctx ai) (expressionToCST ctx' i)
    | some t, some ai, none => B3CST.Statement.var_decl_with_autoinv () (mkAnn name.val) (mkAnn t.val) (expressionToCST ctx ai)
    | some t, none, some i => B3CST.Statement.var_decl_with_init () (mkAnn name.val) (mkAnn t.val) (expressionToCST ctx' i)
    | some t, none, none => B3CST.Statement.var_decl_typed () (mkAnn name.val) (mkAnn t.val)
    | none, _, some i => B3CST.Statement.var_decl_inferred () (mkAnn name.val) (expressionToCST ctx' i)
    | none, _, none => B3CST.Statement.var_decl_typed () (mkAnn name.val) (mkAnn "unknown")
  | .assign _ lhs rhs => B3CST.Statement.assign () (mkAnn (ctx.lookup lhs.val)) (expressionToCST ctx rhs)
  | .reinit _ idx => B3CST.Statement.reinit_statement () (mkAnn (ctx.lookup idx.val))
  | .blockStmt _ stmts =>
      let (stmts', _) := stmts.val.toList.foldl (fun (acc, ctx) stmt =>
        let stmt' := stmtToCST ctx stmt
        let ctx' := match stmt with
          | .varDecl _ name _ _ _ => ctx.push name.val
          | _ => ctx
        (acc ++ [stmt'], ctx')
      ) ([], ctx)
      B3CST.Statement.block () (mkAnn stmts'.toArray)
  | .call _ procName args => B3CST.Statement.call_statement () (mkAnn procName.val) (mkAnn (args.val.toList.map (callArgToCST ctx)).toArray)
  | .check _ expr => B3CST.Statement.check () (expressionToCST ctx expr)
  | .assume _ expr => B3CST.Statement.assume () (expressionToCST ctx expr)
  | .reach _ expr => B3CST.Statement.reach () (expressionToCST ctx expr)
  | .assert _ expr => B3CST.Statement.assert () (expressionToCST ctx expr)
  | .aForall _ var ty body =>
      let ctx' := ctx.push var.val
      B3CST.Statement.aForall_statement () (mkAnn var.val) (mkAnn ty.val) (stmtToCST ctx' body)
  | .choose _ branches =>
      let choiceBranches := branches.val.toList.map (fun s => ChoiceBranch.choice_branch () (stmtToCST ctx s))
      B3CST.Statement.choose_statement () (buildChoiceBranches choiceBranches)
  | .ifStmt _ cond thenB elseB =>
      match elseB.val with
      | some e => B3CST.Statement.if_statement () (expressionToCST ctx cond) (stmtToCST ctx thenB) (Else.else_some () (stmtToCST ctx e))
      | none => B3CST.Statement.if_statement () (expressionToCST ctx cond) (stmtToCST ctx thenB) (Else.else_none ())
  | .ifCase _ cases =>
      B3CST.Statement.if_case_statement () (mkAnn (cases.val.toList.map (fun c =>
        match c with
        | .oneIfCase _ cond body => IfCaseBranch.if_case_branch () (expressionToCST ctx cond) (stmtToCST ctx body)
      )).toArray)
  | .loop _ invariants body =>
      B3CST.Statement.loop_statement () (mkAnn (invariants.val.toList.map (fun e => Invariant.invariant () (expressionToCST ctx e))).toArray) (stmtToCST ctx body)
  | .labeledStmt _ label stmt => B3CST.Statement.labeled_statement () (mkAnn label.val) (stmtToCST ctx stmt)
  | .exit _ label =>
      match label.val with
      | some l => B3CST.Statement.exit_statement () (mkAnn (some (mkAnn l.val)))
      | none => B3CST.Statement.exit_statement () (mkAnn none)
  | .returnStmt _ => B3CST.Statement.return_statement ()
  | .probe _ label => B3CST.Statement.probe () (mkAnn label.val)

end

end ToCST

---------------------------------------------------------------------
-- B3CST → B3AST Conversion (Concrete to Abstract)
---------------------------------------------------------------------

section FromDDM

structure FromDDMContext where
  vars : List String

namespace FromDDMContext

def lookup (ctx : FromDDMContext) (name : String) : Nat :=
  ctx.vars.findIdx? (· == name) |>.getD ctx.vars.length

def push (ctx : FromDDMContext) (name : String) : FromDDMContext :=
  { vars := name :: ctx.vars }

def empty : FromDDMContext := { vars := [] }

end FromDDMContext

mutual

partial def binaryOpFromDDM : (B3CST.Expression Unit → B3CST.Expression Unit → B3CST.Expression Unit) → B3AST.BinaryOp Unit
  | _ => .add ()

partial def expressionFromDDM (ctx : FromDDMContext) : B3CST.Expression Unit → B3.Expression
  | .natLit _ n => .literal () (.intLit () ⟨(), n.val⟩)
  | .strLit _ s => .literal () (.stringLit () ⟨(), s.val⟩)
  | .btrue _ => .literal () (.boolLit () ⟨(), true⟩)
  | .bfalse _ => .literal () (.boolLit () ⟨(), false⟩)
  | .id _ name => .id () ⟨(), ctx.lookup name.val⟩
  | .not _ arg => .unaryOp () (.not ()) (expressionFromDDM ctx arg)
  | .neg _ arg => .unaryOp () (.neg ()) (expressionFromDDM ctx arg)
  | .iff _ lhs rhs => .binaryOp () (.iff ()) (expressionFromDDM ctx lhs) (expressionFromDDM ctx rhs)
  | .implies _ lhs rhs => .binaryOp () (.implies ()) (expressionFromDDM ctx lhs) (expressionFromDDM ctx rhs)
  | .impliedBy _ lhs rhs => .binaryOp () (.impliedBy ()) (expressionFromDDM ctx lhs) (expressionFromDDM ctx rhs)
  | .and _ lhs rhs => .binaryOp () (.and ()) (expressionFromDDM ctx lhs) (expressionFromDDM ctx rhs)
  | .or _ lhs rhs => .binaryOp () (.or ()) (expressionFromDDM ctx lhs) (expressionFromDDM ctx rhs)
  | .equal _ lhs rhs => .binaryOp () (.eq ()) (expressionFromDDM ctx lhs) (expressionFromDDM ctx rhs)
  | .not_equal _ lhs rhs => .binaryOp () (.neq ()) (expressionFromDDM ctx lhs) (expressionFromDDM ctx rhs)
  | .lt _ lhs rhs => .binaryOp () (.lt ()) (expressionFromDDM ctx lhs) (expressionFromDDM ctx rhs)
  | .le _ lhs rhs => .binaryOp () (.le ()) (expressionFromDDM ctx lhs) (expressionFromDDM ctx rhs)
  | .ge _ lhs rhs => .binaryOp () (.ge ()) (expressionFromDDM ctx lhs) (expressionFromDDM ctx rhs)
  | .gt _ lhs rhs => .binaryOp () (.gt ()) (expressionFromDDM ctx lhs) (expressionFromDDM ctx rhs)
  | .add _ lhs rhs => .binaryOp () (.add ()) (expressionFromDDM ctx lhs) (expressionFromDDM ctx rhs)
  | .sub _ lhs rhs => .binaryOp () (.sub ()) (expressionFromDDM ctx lhs) (expressionFromDDM ctx rhs)
  | .mul _ lhs rhs => .binaryOp () (.mul ()) (expressionFromDDM ctx lhs) (expressionFromDDM ctx rhs)
  | .div _ lhs rhs => .binaryOp () (.div ()) (expressionFromDDM ctx lhs) (expressionFromDDM ctx rhs)
  | .mod _ lhs rhs => .binaryOp () (.mod ()) (expressionFromDDM ctx lhs) (expressionFromDDM ctx rhs)
  | .functionCall _ fn args => .functionCall () ⟨(), fn.val⟩ ⟨(), args.val.map (expressionFromDDM ctx)⟩
  | .labeledExpr _ label expr => .labeledExpr () ⟨(), label.val⟩ (expressionFromDDM ctx expr)
  | .letExpr _ var value body =>
      let ctx' := ctx.push var.val
      .letExpr () ⟨(), var.val⟩ (expressionFromDDM ctx value) (expressionFromDDM ctx' body)
  | .ite _ cond thenExpr elseExpr => .ite () (expressionFromDDM ctx cond) (expressionFromDDM ctx thenExpr) (expressionFromDDM ctx elseExpr)
  | .forall_expr_no_patterns _ var ty body =>
      let ctx' := ctx.push var.val
      .quantifierExpr () (.forall ()) ⟨(), var.val⟩ ⟨(), ty.val⟩ ⟨(), #[]⟩ (expressionFromDDM ctx' body)
  | .forall_expr _ var ty patterns body =>
      let ctx' := ctx.push var.val
      let convertPattern (p : B3CST.Pattern Unit) : B3.Pattern :=
        match p with
        | .pattern _ expr => .pattern () ⟨(), #[expressionFromDDM ctx' expr]⟩
      let patternsArray := patternsToArray patterns |>.map convertPattern
      .quantifierExpr () (.forall ()) ⟨(), var.val⟩ ⟨(), ty.val⟩ ⟨(), patternsArray⟩ (expressionFromDDM ctx' body)
  | .exists_expr_no_patterns _ var ty body =>
      let ctx' := ctx.push var.val
      .quantifierExpr () (.exists ()) ⟨(), var.val⟩ ⟨(), ty.val⟩ ⟨(), #[]⟩ (expressionFromDDM ctx' body)
  | .exists_expr _ var ty patterns body =>
      let ctx' := ctx.push var.val
      let convertPattern (p : B3CST.Pattern Unit) : B3.Pattern :=
        match p with
        | .pattern _ expr => .pattern () ⟨(), #[expressionFromDDM ctx' expr]⟩
      let patternsArray := patternsToArray patterns |>.map convertPattern
      .quantifierExpr () (.exists ()) ⟨(), var.val⟩ ⟨(), ty.val⟩ ⟨(), patternsArray⟩ (expressionFromDDM ctx' body)
  | .paren _ expr => expressionFromDDM ctx expr

partial def patternsToArray : B3CST.Patterns Unit → Array (B3CST.Pattern Unit)
  | .patterns_single _ p => #[p]
  | .patterns_cons _ p ps => patternsToArray ps |>.push p

end

end FromDDM

-- Add convenience methods to Expression
namespace Expression

def fromDDM (e : B3CST.Expression Unit) : B3.Expression :=
  expressionFromDDM FromDDMContext.empty e

def toDDM (e : B3.Expression) : B3CST.Expression Unit :=
  expressionToCST ToCSTContext.empty e

end Expression

-- Add conversion functions for statements
namespace Stmt

mutual

partial def fromDDM (s : B3CST.Statement Unit) : B3.Stmt :=
  stmtFromDDM FromDDMContext.empty s

partial def stmtFromDDM (ctx : FromDDMContext) : B3CST.Statement Unit → B3.Stmt
  | .var_decl_full _ name ty autoinv init =>
      let ctx' := ctx.push name.val
      .varDecl () (mkAnn name.val) (mkAnn (some (mkAnn ty.val))) (mkAnn (some (expressionFromDDM ctx autoinv))) (mkAnn (some (expressionFromDDM ctx' init)))
  | .var_decl_with_autoinv _ name ty autoinv =>
      .varDecl () (mkAnn name.val) (mkAnn (some (mkAnn ty.val))) (mkAnn (some (expressionFromDDM ctx autoinv))) (mkAnn none)
  | .var_decl_with_init _ name ty init =>
      let ctx' := ctx.push name.val
      .varDecl () (mkAnn name.val) (mkAnn (some (mkAnn ty.val))) (mkAnn none) (mkAnn (some (expressionFromDDM ctx' init)))
  | .var_decl_typed _ name ty =>
      .varDecl () (mkAnn name.val) (mkAnn (some (mkAnn ty.val))) (mkAnn none) (mkAnn none)
  | .var_decl_inferred _ name init =>
      let ctx' := ctx.push name.val
      .varDecl () (mkAnn name.val) (mkAnn none) (mkAnn none) (mkAnn (some (expressionFromDDM ctx' init)))
  | .val_decl _ name ty init =>
      let ctx' := ctx.push name.val
      .varDecl () (mkAnn name.val) (mkAnn (some (mkAnn ty.val))) (mkAnn none) (mkAnn (some (expressionFromDDM ctx' init)))
  | .val_decl_inferred _ name init =>
      let ctx' := ctx.push name.val
      .varDecl () (mkAnn name.val) (mkAnn none) (mkAnn none) (mkAnn (some (expressionFromDDM ctx' init)))
  | .assign _ lhs rhs =>
      .assign () (mkAnn (ctx.lookup lhs.val)) (expressionFromDDM ctx rhs)
  | .reinit_statement _ v =>
      .reinit () (mkAnn (ctx.lookup v.val))
  | .check _ expr =>
      .check () (expressionFromDDM ctx expr)
  | .assume _ expr =>
      .assume () (expressionFromDDM ctx expr)
  | .reach _ expr =>
      .reach () (expressionFromDDM ctx expr)
  | .assert _ expr =>
      .assert () (expressionFromDDM ctx expr)
  | .return_statement _ =>
      .returnStmt ()
  | .block _ stmts =>
      let (stmts', _) := stmts.val.toList.foldl (fun (acc, ctx) stmt =>
        let stmt' := stmtFromDDM ctx stmt
        let ctx' := match stmt with
          | .var_decl_full _ name _ _ _ => ctx.push name.val
          | .var_decl_with_autoinv _ name _ _ => ctx.push name.val
          | .var_decl_with_init _ name _ _ => ctx.push name.val
          | .var_decl_typed _ name _ => ctx.push name.val
          | .var_decl_inferred _ name _ => ctx.push name.val
          | .val_decl _ name _ _ => ctx.push name.val
          | .val_decl_inferred _ name _ => ctx.push name.val
          | _ => ctx
        (acc ++ [stmt'], ctx')
      ) ([], ctx)
      .blockStmt () (mkAnn stmts'.toArray)
  | .if_statement _ cond thenB elseB =>
      let elseBranch := match elseB with
        | .else_none _ => mkAnn none
        | .else_some _ stmt => mkAnn (some (stmtFromDDM ctx stmt))
      .ifStmt () (expressionFromDDM ctx cond) (stmtFromDDM ctx thenB) elseBranch
  | .loop_statement _ invs body =>
      let invariants := invs.val.toList.map fun inv =>
        match inv with
        | .invariant _ expr => expressionFromDDM ctx expr
      .loop () (mkAnn invariants.toArray) (stmtFromDDM ctx body)
  | .exit_statement _ label =>
      .exit () (mkAnn (label.val.map (fun l => mkAnn l.val)))
  | .labeled_statement _ label stmt =>
      .labeledStmt () (mkAnn label.val) (stmtFromDDM ctx stmt)
  | .probe _ label =>
      .probe () (mkAnn label.val)
  | .aForall_statement _ var ty body =>
      let ctx' := ctx.push var.val
      .aForall () (mkAnn var.val) (mkAnn ty.val) (stmtFromDDM ctx' body)
  | .choose_statement _ branches =>
      .choose () (mkAnn (choiceBranchesToList branches |>.map (stmtFromDDM ctx)).toArray)
  | .if_case_statement _ cases =>
      .ifCase () (mkAnn (cases.val.toList.map fun case =>
        match case with
        | .if_case_branch _ cond stmt => .oneIfCase () (expressionFromDDM ctx cond) (stmtFromDDM ctx stmt)).toArray)
  | .call_statement _ procName args =>
      .call () (mkAnn procName.val) (mkAnn (args.val.toList.map (callArgFromDDM ctx)).toArray)

partial def callArgFromDDM (ctx : FromDDMContext) : B3CST.CallArg Unit → B3.CallArg
  | .call_arg_expr _ expr => .callArgExpr () (expressionFromDDM ctx expr)
  | .call_arg_out _ id => .callArgOut () (mkAnn id.val)
  | .call_arg_inout _ id => .callArgInout () (mkAnn id.val)

partial def choiceBranchesToList : B3CST.ChoiceBranches Unit → List (B3CST.Statement Unit)
  | .choiceAtom _ branch =>
      match branch with
      | .choice_branch _ stmt => [stmt]
  | .choicePush _ branches branch =>
      match branch with
      | .choice_branch _ stmt => stmt :: choiceBranchesToList branches

end

def toDDM (s : B3.Stmt) : B3CST.Statement Unit :=
  stmtToCST ToCSTContext.empty s

end Stmt

end B3
