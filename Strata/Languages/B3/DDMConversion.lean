/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Expression
import Strata.Languages.B3.Stmt
import Strata.Languages.B3.Decl
import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.DefinitionAST

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

-- Helper to preserve annotations when converting
private def preserveAnn {α β : Type} (ann : β) (x : α) : Ann α β := ⟨ann, x⟩

-- Helper to map over Ann while preserving the annotation
private def mapAnn {α β γ : Type} (f : α → β) (a : Ann α γ) : Ann β γ := ⟨a.ann, f a.val⟩

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
      let elseCST := mkAnn (elseB.val.map (fun e => Else.else_some () (stmtToCST ctx e)))
      B3CST.Statement.if_statement () (expressionToCST ctx cond) (stmtToCST ctx thenB) elseCST
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
      let elseBranch := mkAnn (elseB.val.map (fun e => match e with | .else_some _ stmt => stmtFromDDM ctx stmt))
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

---------------------------------------------------------------------
-- Declaration Conversion
---------------------------------------------------------------------

section DeclConversion

def paramModeToCST : B3.ParamMode → Ann (Option (B3CST.PParamMode Unit)) Unit
  | .paramModeIn _ => mkAnn none
  | .paramModeOut _ => mkAnn (some (B3CST.PParamMode.pmode_out ()))
  | .paramModeInout _ => mkAnn (some (B3CST.PParamMode.pmode_inout ()))

def paramModeFromCST : Ann (Option (B3CST.PParamMode Unit)) Unit → B3.ParamMode
  | ⟨_, none⟩ => .paramModeIn ()
  | ⟨_, some (.pmode_out _)⟩ => .paramModeOut ()
  | ⟨_, some (.pmode_inout _)⟩ => .paramModeInout ()

def fParameterToCST (_ctx : ToCSTContext) : B3.FParameter → B3CST.FParam Unit
  | .fParameter _ injective name ty =>
      let inj := mkAnn (if injective.val then some (B3CST.Injective.injective_some ()) else none)
      B3CST.FParam.fparam () inj (mkAnn name.val) (mkAnn ty.val)

def fParameterFromCST : B3CST.FParam Unit → B3.FParameter
  | .fparam _ injective name ty =>
      let inj := match injective.val with
        | some (.injective_some _) => true
        | none => false
      .fParameter () (mkAnn inj) (mkAnn name.val) (mkAnn ty.val)

def pParameterToCST (ctx : ToCSTContext) : B3.PParameter → B3CST.PParam Unit
  | .pParameter _ mode name ty autoinv =>
      match autoinv.val with
      | some ai => B3CST.PParam.pparam_with_autoinv () (paramModeToCST mode) (mkAnn name.val) (mkAnn ty.val) (expressionToCST ctx ai)
      | none => B3CST.PParam.pparam () (paramModeToCST mode) (mkAnn name.val) (mkAnn ty.val)

def pParameterFromCST (ctx : FromDDMContext) : B3CST.PParam Unit → B3.PParameter
  | .pparam _ mode name ty =>
      .pParameter () (paramModeFromCST mode) (mkAnn name.val) (mkAnn ty.val) (mkAnn none)
  | .pparam_with_autoinv _ mode name ty autoinv =>
      .pParameter () (paramModeFromCST mode) (mkAnn name.val) (mkAnn ty.val) (mkAnn (some (expressionFromDDM ctx autoinv)))

def specToCST (ctx : ToCSTContext) : B3.Spec → B3CST.Spec Unit
  | .specRequires _ expr => B3CST.Spec.spec_requires () (expressionToCST ctx expr)
  | .specEnsures _ expr => B3CST.Spec.spec_ensures () (expressionToCST ctx expr)

def specFromCST (ctx : FromDDMContext) : B3CST.Spec Unit → B3.Spec
  | .spec_requires _ expr => .specRequires () (expressionFromDDM ctx expr)
  | .spec_ensures _ expr => .specEnsures () (expressionFromDDM ctx expr)

def fparamsToList : Ann (Array (B3CST.FParam Unit)) Unit → List (B3CST.FParam Unit)
  | ⟨_, arr⟩ => arr.toList

def declToCST (ctx : ToCSTContext) : B3.Decl → B3CST.Decl Unit
  | .typeDecl _ name =>
      B3CST.Decl.type_decl () (mkAnn name.val)
  | .tagger _ name forType =>
      B3CST.Decl.tagger_decl () (mkAnn name.val) (mkAnn forType.val)
  | .function _ name params resultType tag body =>
      let paramsCST := mkAnn (params.val.toList.map (fParameterToCST ctx)).toArray
      let tagClause := mkAnn (tag.val.map (fun t => B3CST.TagClause.tag_some () (mkAnn t.val)))
      let bodyCST := mkAnn (body.val.map (fun b => match b with
        | .functionBody _ whens expr =>
            let whensCST := whens.val.toList.map (fun w => match w with | .when _ e => B3CST.WhenClause.when_clause () (expressionToCST ctx e))
            B3CST.FunctionBody.function_body_some () (mkAnn whensCST.toArray) (expressionToCST ctx expr)))
      B3CST.Decl.function_decl () (mkAnn name.val) paramsCST (mkAnn resultType.val) tagClause bodyCST
  | .axiom _ explains expr =>
      let explainsCST := mkAnn (explains.val.toList.map (fun id => mkAnn id.val)).toArray
      if explains.val.isEmpty then
        B3CST.Decl.axiom_decl () (B3CST.AxiomBody.axiom () (expressionToCST ctx expr))
      else
        B3CST.Decl.axiom_decl () (B3CST.AxiomBody.explain_axiom () explainsCST (expressionToCST ctx expr))
  | .procedure _ name params specs body =>
      let paramNames := params.val.toList.map (fun p => match p with | .pParameter _ _ n _ _ => n.val)
      let ctx' := paramNames.foldl (fun acc n => acc.push n) ctx
      let paramsCST := mkAnn (params.val.toList.map (pParameterToCST ctx)).toArray
      let specsCST := specs.val.toList.map (specToCST ctx')
      let bodyCST := mkAnn (body.val.map (fun s => B3CST.ProcBody.proc_body_some () (stmtToCST ctx' s)))
      B3CST.Decl.procedure_decl () (mkAnn name.val) paramsCST (mkAnn specsCST.toArray) bodyCST

def declFromCST (ctx : FromDDMContext) : B3CST.Decl Unit → B3.Decl
  | .type_decl _ name =>
      .typeDecl () (mkAnn name.val)
  | .tagger_decl _ name forType =>
      .tagger () (mkAnn name.val) (mkAnn forType.val)
  | .function_decl _ name params resultType tag body =>
      let paramsAST := fparamsToList params |>.map fParameterFromCST
      let tagAST := tag.val.map (fun t => match t with | .tag_some _ id => mkAnn id.val)
      let bodyAST := mkAnn (body.val.map (fun b => match b with
        | .function_body_some _ whens expr =>
            let whensAST := whens.val.toList.map (fun w => match w with | .when_clause _ e => B3AST.When.when () (expressionFromDDM ctx e))
            B3AST.FunctionBody.functionBody () (mkAnn whensAST.toArray) (expressionFromDDM ctx expr)))
      .function () (mkAnn name.val) (mkAnn paramsAST.toArray) (mkAnn resultType.val) (mkAnn tagAST) bodyAST
  | .axiom_decl _ axiomBody =>
      match axiomBody with
      | .axiom _ expr =>
          .axiom () (mkAnn #[]) (expressionFromDDM ctx expr)
      | .explain_axiom _ names expr =>
          let namesAST := names.val.toList.map (fun n => mkAnn n.val)
          .axiom () (mkAnn namesAST.toArray) (expressionFromDDM ctx expr)
  | .procedure_decl _ name params specs body =>
      let paramsAST := params.val.toList.map (pParameterFromCST ctx)
      let paramNames := paramsAST.map (fun p => match p with | .pParameter _ _ n _ _ => n.val)
      let ctx' := paramNames.foldl (fun acc n => acc.push n) ctx
      let specsAST := specs.val.toList.map (specFromCST ctx')
      let bodyAST := mkAnn (body.val.map (fun b => match b with | .proc_body_some _ s => Stmt.stmtFromDDM ctx' s))
      .procedure () (mkAnn name.val) (mkAnn paramsAST.toArray) (mkAnn specsAST.toArray) bodyAST

end DeclConversion

namespace Decl

def toDDM (d : B3.Decl) : B3CST.Decl Unit :=
  declToCST ToCSTContext.empty d

def fromDDM (d : B3CST.Decl Unit) : B3.Decl :=
  declFromCST FromDDMContext.empty d

end Decl

---------------------------------------------------------------------
-- Annotation-Preserving Conversions (B3CST SourceRange ↔ B3AST SourceRange)
---------------------------------------------------------------------

section AnnotationPreserving

structure ToCSTContextSR where
  vars : List String

namespace ToCSTContextSR

def lookup (ctx : ToCSTContextSR) (idx : Nat): String :=
  match ctx.vars[idx]? with
  | .some name =>
    if name == "" then s!"@{idx}" else
    let rec go (vars: List String) (pastIndex: Nat) (idx: Nat): String :=
      let default := fun _: Unit => if pastIndex == 0 then name else s!"name@{pastIndex}"
      if idx == 0 then default ()
      else
        match vars with
        | [] => default ()
        | otherName :: tail =>
          if name == otherName then go tail (pastIndex + 1) (idx - 1)
          else go tail pastIndex (idx - 1)
    go ctx.vars 0 idx
  | .none => s!"@{idx}"

def push (ctx : ToCSTContextSR) (name : String) : ToCSTContextSR :=
  { vars := name :: ctx.vars }

def empty : ToCSTContextSR := { vars := [] }

end ToCSTContextSR

structure FromDDMContextSR where
  vars : List String

namespace FromDDMContextSR

def lookup (ctx : FromDDMContextSR) (name : String) : Nat :=
  ctx.vars.findIdx? (· == name) |>.getD ctx.vars.length

def push (ctx : FromDDMContextSR) (name : String) : FromDDMContextSR :=
  { vars := name :: ctx.vars }

def empty : FromDDMContextSR := { vars := [] }

end FromDDMContextSR

/-!
## Annotation-Preserving Conversions

These functions preserve SourceRange annotations when converting between B3CST and B3AST.
They duplicate the Unit-based conversions but thread SourceRange through all recursive calls.
-/

mutual

partial def literalToCSTSR (ann : SourceRange) : B3AST.Literal SourceRange → B3CST.Expression SourceRange
  | .intLit _ n => B3CST.Expression.natLit ann (preserveAnn ann n.val)
  | .boolLit _ b => match b with
    | ⟨_, true⟩ => B3CST.Expression.btrue ann
    | ⟨_, false⟩ => B3CST.Expression.bfalse ann
  | .stringLit _ s => B3CST.Expression.strLit ann (preserveAnn ann s.val)

partial def expressionToCSTSR (ctx : ToCSTContextSR) : Strata.B3AST.Expression SourceRange → B3CST.Expression SourceRange
  | .literal ann lit => literalToCSTSR ann lit
  | .id ann idx => B3CST.Expression.id ann (preserveAnn ann (ctx.lookup idx.val))
  | .ite ann cond thn els => B3CST.Expression.ite ann (expressionToCSTSR ctx cond) (expressionToCSTSR ctx thn) (expressionToCSTSR ctx els)
  | .binaryOp ann op lhs rhs =>
      let ctor := match op with
        | .iff _ => B3CST.Expression.iff
        | .implies _ => B3CST.Expression.implies
        | .impliedBy _ => B3CST.Expression.impliedBy
        | .and _ => B3CST.Expression.and
        | .or _ => B3CST.Expression.or
        | .eq _ => B3CST.Expression.equal
        | .neq _ => B3CST.Expression.not_equal
        | .lt _ => B3CST.Expression.lt
        | .le _ => B3CST.Expression.le
        | .ge _ => B3CST.Expression.ge
        | .gt _ => B3CST.Expression.gt
        | .add _ => B3CST.Expression.add
        | .sub _ => B3CST.Expression.sub
        | .mul _ => B3CST.Expression.mul
        | .div _ => B3CST.Expression.div
        | .mod _ => B3CST.Expression.mod
      ctor ann (expressionToCSTSR ctx lhs) (expressionToCSTSR ctx rhs)
  | .unaryOp ann op arg =>
      let ctor := match op with
        | .not _ => B3CST.Expression.not
        | .neg _ => B3CST.Expression.neg
      ctor ann (expressionToCSTSR ctx arg)
  | .functionCall ann fnName args => B3CST.Expression.functionCall ann (preserveAnn ann fnName.val) (preserveAnn ann (args.val.map (expressionToCSTSR ctx)))
  | .labeledExpr ann label expr => B3CST.Expression.labeledExpr ann (preserveAnn ann label.val) (expressionToCSTSR ctx expr)
  | .letExpr ann var value body =>
      let ctx' := ctx.push var.val
      B3CST.Expression.letExpr ann (preserveAnn ann var.val) (expressionToCSTSR ctx value) (expressionToCSTSR ctx' body)
  | .quantifierExpr ann qkind var ty patterns body =>
      let ctx' := ctx.push var.val
      let convertPattern (p : Strata.B3AST.Pattern SourceRange) : B3CST.Pattern SourceRange :=
        match p with
        | .pattern pann exprs =>
            match exprs.val.toList with
            | [e] => B3CST.Pattern.pattern pann (expressionToCSTSR ctx' e)
            | _ => B3CST.Pattern.pattern pann (B3CST.Expression.btrue pann)
      let patternsDDM := match patterns.val.toList with
        | [] => none
        | [p] => some (Patterns.patterns_single ann (convertPattern p))
        | p :: ps =>
            some (ps.foldl (init := Patterns.patterns_single ann (convertPattern p)) fun acc p =>
              Patterns.patterns_cons ann (convertPattern p) acc)
      match qkind with
      | .forall _ =>
          match patternsDDM with
          | none => B3CST.Expression.forall_expr_no_patterns ann (preserveAnn ann var.val) (preserveAnn ann ty.val) (expressionToCSTSR ctx' body)
          | some pats => B3CST.Expression.forall_expr ann (preserveAnn ann var.val) (preserveAnn ann ty.val) pats (expressionToCSTSR ctx' body)
      | .exists _ =>
          match patternsDDM with
          | none => B3CST.Expression.exists_expr_no_patterns ann (preserveAnn ann var.val) (preserveAnn ann ty.val) (expressionToCSTSR ctx' body)
          | some pats => B3CST.Expression.exists_expr ann (preserveAnn ann var.val) (preserveAnn ann ty.val) pats (expressionToCSTSR ctx' body)

partial def patternsToArraySR : B3CST.Patterns SourceRange → Array (B3CST.Pattern SourceRange)
  | .patterns_single _ p => #[p]
  | .patterns_cons _ p ps => patternsToArraySR ps |>.push p

partial def expressionFromDDMSR (ctx : FromDDMContextSR) : B3CST.Expression SourceRange → Strata.B3AST.Expression SourceRange
  | .natLit ann n => .literal ann (.intLit ann (preserveAnn ann n.val))
  | .strLit ann s => .literal ann (.stringLit ann (preserveAnn ann s.val))
  | .btrue ann => .literal ann (.boolLit ann (preserveAnn ann true))
  | .bfalse ann => .literal ann (.boolLit ann (preserveAnn ann false))
  | .id ann name => .id ann (preserveAnn ann (ctx.lookup name.val))
  | .not ann arg => .unaryOp ann (.not ann) (expressionFromDDMSR ctx arg)
  | .neg ann arg => .unaryOp ann (.neg ann) (expressionFromDDMSR ctx arg)
  | .iff ann lhs rhs => .binaryOp ann (.iff ann) (expressionFromDDMSR ctx lhs) (expressionFromDDMSR ctx rhs)
  | .implies ann lhs rhs => .binaryOp ann (.implies ann) (expressionFromDDMSR ctx lhs) (expressionFromDDMSR ctx rhs)
  | .impliedBy ann lhs rhs => .binaryOp ann (.impliedBy ann) (expressionFromDDMSR ctx lhs) (expressionFromDDMSR ctx rhs)
  | .and ann lhs rhs => .binaryOp ann (.and ann) (expressionFromDDMSR ctx lhs) (expressionFromDDMSR ctx rhs)
  | .or ann lhs rhs => .binaryOp ann (.or ann) (expressionFromDDMSR ctx lhs) (expressionFromDDMSR ctx rhs)
  | .equal ann lhs rhs => .binaryOp ann (.eq ann) (expressionFromDDMSR ctx lhs) (expressionFromDDMSR ctx rhs)
  | .not_equal ann lhs rhs => .binaryOp ann (.neq ann) (expressionFromDDMSR ctx lhs) (expressionFromDDMSR ctx rhs)
  | .lt ann lhs rhs => .binaryOp ann (.lt ann) (expressionFromDDMSR ctx lhs) (expressionFromDDMSR ctx rhs)
  | .le ann lhs rhs => .binaryOp ann (.le ann) (expressionFromDDMSR ctx lhs) (expressionFromDDMSR ctx rhs)
  | .ge ann lhs rhs => .binaryOp ann (.ge ann) (expressionFromDDMSR ctx lhs) (expressionFromDDMSR ctx rhs)
  | .gt ann lhs rhs => .binaryOp ann (.gt ann) (expressionFromDDMSR ctx lhs) (expressionFromDDMSR ctx rhs)
  | .add ann lhs rhs => .binaryOp ann (.add ann) (expressionFromDDMSR ctx lhs) (expressionFromDDMSR ctx rhs)
  | .sub ann lhs rhs => .binaryOp ann (.sub ann) (expressionFromDDMSR ctx lhs) (expressionFromDDMSR ctx rhs)
  | .mul ann lhs rhs => .binaryOp ann (.mul ann) (expressionFromDDMSR ctx lhs) (expressionFromDDMSR ctx rhs)
  | .div ann lhs rhs => .binaryOp ann (.div ann) (expressionFromDDMSR ctx lhs) (expressionFromDDMSR ctx rhs)
  | .mod ann lhs rhs => .binaryOp ann (.mod ann) (expressionFromDDMSR ctx lhs) (expressionFromDDMSR ctx rhs)
  | .functionCall ann fn args => .functionCall ann (preserveAnn ann fn.val) (preserveAnn ann (args.val.map (expressionFromDDMSR ctx)))
  | .labeledExpr ann label expr => .labeledExpr ann (preserveAnn ann label.val) (expressionFromDDMSR ctx expr)
  | .letExpr ann var value body =>
      let ctx' := ctx.push var.val
      .letExpr ann (preserveAnn ann var.val) (expressionFromDDMSR ctx value) (expressionFromDDMSR ctx' body)
  | .ite ann cond thenExpr elseExpr => .ite ann (expressionFromDDMSR ctx cond) (expressionFromDDMSR ctx thenExpr) (expressionFromDDMSR ctx elseExpr)
  | .forall_expr_no_patterns ann var ty body =>
      let ctx' := ctx.push var.val
      .quantifierExpr ann (.forall ann) (preserveAnn ann var.val) (preserveAnn ann ty.val) (preserveAnn ann #[]) (expressionFromDDMSR ctx' body)
  | .forall_expr ann var ty patterns body =>
      let ctx' := ctx.push var.val
      let convertPattern (p : B3CST.Pattern SourceRange) : Strata.B3AST.Pattern SourceRange :=
        match p with
        | .pattern pann expr => .pattern pann (preserveAnn pann #[expressionFromDDMSR ctx' expr])
      let patternsArray := patternsToArraySR patterns |>.map convertPattern
      .quantifierExpr ann (.forall ann) (preserveAnn ann var.val) (preserveAnn ann ty.val) (preserveAnn ann patternsArray) (expressionFromDDMSR ctx' body)
  | .exists_expr_no_patterns ann var ty body =>
      let ctx' := ctx.push var.val
      .quantifierExpr ann (.exists ann) (preserveAnn ann var.val) (preserveAnn ann ty.val) (preserveAnn ann #[]) (expressionFromDDMSR ctx' body)
  | .exists_expr ann var ty patterns body =>
      let ctx' := ctx.push var.val
      let convertPattern (p : B3CST.Pattern SourceRange) : Strata.B3AST.Pattern SourceRange :=
        match p with
        | .pattern pann expr => .pattern pann (preserveAnn pann #[expressionFromDDMSR ctx' expr])
      let patternsArray := patternsToArraySR patterns |>.map convertPattern
      .quantifierExpr ann (.exists ann) (preserveAnn ann var.val) (preserveAnn ann ty.val) (preserveAnn ann patternsArray) (expressionFromDDMSR ctx' body)
  | .paren _ expr => expressionFromDDMSR ctx expr

end

namespace Expression

def fromDDMWithAnnotations (e : B3CST.Expression SourceRange) : Strata.B3AST.Expression SourceRange :=
  expressionFromDDMSR FromDDMContextSR.empty e

def toDDMWithAnnotations (e : Strata.B3AST.Expression SourceRange) : B3CST.Expression SourceRange :=
  expressionToCSTSR ToCSTContextSR.empty e

end Expression

namespace Stmt

-- TODO: Implement annotation-preserving statement conversions
def fromDDMWithAnnotations (s : B3CST.Statement SourceRange) : Strata.B3AST.Statement SourceRange :=
  sorry

def toDDMWithAnnotations (s : Strata.B3AST.Statement SourceRange) : B3CST.Statement SourceRange :=
  sorry

end Stmt

namespace Decl

-- TODO: Implement annotation-preserving declaration conversions
def fromDDMWithAnnotations (d : B3CST.Decl SourceRange) : Strata.B3AST.Decl SourceRange :=
  sorry

def toDDMWithAnnotations (d : Strata.B3AST.Decl SourceRange) : B3CST.Decl SourceRange :=
  sorry

end Decl

end AnnotationPreserving

end B3
