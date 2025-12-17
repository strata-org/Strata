/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

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

/--
Typeclass for creating annotations when converting CST → AST.
Methods are named specifically for where they're used. Each should be used exactly once.
-/
class B3AnnFromCST (α : Type) where
  /-- Used in: literal cases (.natLit, .strLit, .btrue, .bfalse) for .literal wrapper -/
  annForLiteral : α → α
  /-- Used in: literal cases for the specific literal type (.intLit, .stringLit, .boolLit) -/
  annForLiteralType : α → α
  /-- Used in: literal cases for Ann wrapping the value -/
  annForLiteralValue : α → α
  /-- Used in: .id case for .id wrapper -/
  annForId : α → α
  /-- Used in: .id case for Ann wrapping the looked-up index -/
  annForIdValue : α → α
  /-- Used in: unary op cases (.not, .neg) for .unaryOp wrapper -/
  annForUnaryOp : α → α
  /-- Used in: unary op cases for the op type (.not, .neg) -/
  annForUnaryOpType : α → α
  /-- Used in: binary op cases for .binaryOp wrapper -/
  annForBinaryOp : α → α
  /-- Used in: binary op cases for the op type -/
  annForBinaryOpType : α → α
  /-- Used in: .functionCall for wrapper -/
  annForFunctionCall : α → α
  /-- Used in: .functionCall for Ann wrapping function name -/
  annForFunctionCallName : α → α
  /-- Used in: .functionCall for Ann wrapping args array -/
  annForFunctionCallArgs : α → α
  /-- Used in: .labeledExpr for wrapper -/
  annForLabeledExpr : α → α
  /-- Used in: .labeledExpr for Ann wrapping label -/
  annForLabeledExprLabel : α → α
  /-- Used in: .letExpr for wrapper -/
  annForLetExpr : α → α
  /-- Used in: .letExpr for Ann wrapping var name -/
  annForLetExprVar : α → α
  /-- Used in: .ite for wrapper -/
  annForIte : α → α
  /-- Used in: quantifier cases for .quantifierExpr wrapper -/
  annForQuantifierExpr : α → α
  /-- Used in: quantifier cases for quantifier kind (.forall, .exists) -/
  annForQuantifierKind : α → α
  /-- Used in: quantifier cases for Ann wrapping var name -/
  annForQuantifierVar : α → α
  /-- Used in: quantifier cases for Ann wrapping type -/
  annForQuantifierType : α → α
  /-- Used in: quantifier cases for Ann wrapping patterns array -/
  annForQuantifierPatterns : α → α
  /-- Used in: pattern case for .pattern wrapper -/
  annForPattern : α → α
  /-- Used in: pattern case for Ann wrapping expressions array -/
  annForPatternExprs : α → α

instance : B3AnnFromCST Unit where
  annForLiteral _ := ()
  annForLiteralType _ := ()
  annForLiteralValue _ := ()
  annForId _ := ()
  annForIdValue _ := ()
  annForUnaryOp _ := ()
  annForUnaryOpType _ := ()
  annForBinaryOp _ := ()
  annForBinaryOpType _ := ()
  annForFunctionCall _ := ()
  annForFunctionCallName _ := ()
  annForFunctionCallArgs _ := ()
  annForLabeledExpr _ := ()
  annForLabeledExprLabel _ := ()
  annForLetExpr _ := ()
  annForLetExprVar _ := ()
  annForIte _ := ()
  annForQuantifierExpr _ := ()
  annForQuantifierKind _ := ()
  annForQuantifierVar _ := ()
  annForQuantifierType _ := ()
  annForQuantifierPatterns _ := ()
  annForPattern _ := ()
  annForPatternExprs _ := ()

instance : B3AnnFromCST M where
  annForLiteral := id
  annForLiteralType := id
  annForLiteralValue := id
  annForId := id
  annForIdValue := id
  annForUnaryOp := id
  annForUnaryOpType := id
  annForBinaryOp := id
  annForBinaryOpType := id
  annForFunctionCall := id
  annForFunctionCallName := id
  annForFunctionCallArgs := id
  annForLabeledExpr := id
  annForLabeledExprLabel := id
  annForLetExpr := id
  annForLetExprVar := id
  annForIte := id
  annForQuantifierExpr := id
  annForQuantifierKind := id
  annForQuantifierVar := id
  annForQuantifierType := id
  annForQuantifierPatterns := id
  annForPattern := id
  annForPatternExprs := id

-- Helpers for common Ann operations
private def mkAnn {α M: Type} (m: M) (x : α) : Ann α M := ⟨m, x⟩
private def mapAnn {α β M : Type} (f : α → β) (a : Ann α M) : Ann β M := mkAnn a.ann (f a.val)

---------------------------------------------------------------------
-- B3AST → B3CST Conversion (Abstract to Concrete)
---------------------------------------------------------------------

section ToCST

structure ToCSTContext where
  vars : List String

namespace ToCSTContext

def lookup (ctx : ToCSTContext) (idx : Nat): String × Bool :=
  match ctx.vars[idx]? with
  | .some name =>
    if name == "" then (s!"@{idx}", false) else
    -- Determine if this is an old value: first occurrence with shadowing
    let isOld :=
      -- Check if there's a later occurrence (lower index) with the same name
      ctx.vars.take idx |>.any (· == name)
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

    (go ctx.vars 0 idx, isOld)
  | .none =>
    (s!"@{idx}", false)

def push (ctx : ToCSTContext) (name : String) : ToCSTContext :=
  { vars := name :: ctx.vars }

def empty : ToCSTContext := { vars := [] }

end ToCSTContext

mutual

partial def binaryOpToCST [Inhabited (B3CST.Expression M)] : B3AST.BinaryOp M →
    (M → B3CST.Expression M → B3CST.Expression M → B3CST.Expression M)
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

partial def unaryOpToCST [Inhabited (B3CST.Expression M)] : B3AST.UnaryOp M →
    (M → B3CST.Expression M → B3CST.Expression M)
  | .not _ => B3CST.Expression.not
  | .neg _ => B3CST.Expression.neg

partial def literalToCST [Inhabited (B3CST.Expression M)] : B3AST.Literal M → B3CST.Expression M
  | .intLit m n => B3CST.Expression.natLit m (mkAnn m n)
  | .boolLit m b => if b then B3CST.Expression.btrue m else B3CST.Expression.bfalse m
  | .stringLit m s => B3CST.Expression.strLit m (mkAnn m s)

partial def expressionToCST [Inhabited (B3CST.Expression M)] (ctx : ToCSTContext) : B3AST.Expression M → B3CST.Expression M
  | .literal _m lit =>
      literalToCST lit
  | .id m idx =>
      let (name, isOld) := ctx.lookup idx
      if isOld then
        B3CST.Expression.old_id m (mkAnn m name)
      else
        B3CST.Expression.id m (mkAnn m name)
  | .ite m cond thn els =>
      B3CST.Expression.ite m (expressionToCST ctx cond) (expressionToCST ctx thn) (expressionToCST ctx els)
  | .binaryOp m op lhs rhs =>
      (binaryOpToCST op) m (expressionToCST ctx lhs) (expressionToCST ctx rhs)
  | .unaryOp m op arg =>
      (unaryOpToCST op) m (expressionToCST ctx arg)
  | .functionCall m fnName args =>
      B3CST.Expression.functionCall m (mapAnn (fun x => x) fnName) (mapAnn (fun arr => arr.map (expressionToCST ctx)) args)
  | .labeledExpr m label expr =>
      B3CST.Expression.labeledExpr m (mapAnn (fun x => x) label) (expressionToCST ctx expr)
  | .letExpr m var value body =>
      let ctx' := ctx.push var.val
      B3CST.Expression.letExpr m (mapAnn (fun x => x) var) (expressionToCST ctx value) (expressionToCST ctx' body)
  | .quantifierExpr m qkind var ty patterns body =>
      let ctx' := ctx.push var.val
      let convertPattern (p : Strata.B3AST.Pattern M) : B3CST.Pattern M :=
        match p with
        | .pattern pm exprs =>
            let exprsCST := exprs.val.map (expressionToCST ctx')
            B3CST.Pattern.pattern pm (mkAnn pm exprsCST)
      let patternsDDM := match patterns.val.toList with
        | [] => none
        | [p] => some (Patterns.patterns_single m (convertPattern p))
        | p :: ps =>
            some (ps.foldl (init := Patterns.patterns_single m (convertPattern p)) fun acc p =>
              Patterns.patterns_cons m (convertPattern p) acc)
      match qkind with
      | .forall _qm =>
          match patternsDDM with
          | none => B3CST.Expression.forall_expr_no_patterns m (mapAnn (fun x => x) var) (mapAnn (fun x => x) ty) (expressionToCST ctx' body)
          | some pats => B3CST.Expression.forall_expr m (mapAnn (fun x => x) var) (mapAnn (fun x => x) ty) pats (expressionToCST ctx' body)
      | .exists _qm =>
          match patternsDDM with
          | none => B3CST.Expression.exists_expr_no_patterns m (mapAnn (fun x => x) var) (mapAnn (fun x => x) ty) (expressionToCST ctx' body)
          | some pats => B3CST.Expression.exists_expr m (mapAnn (fun x => x) var) (mapAnn (fun x => x) ty) pats (expressionToCST ctx' body)

partial def callArgToCST [Inhabited M] (ctx : ToCSTContext) : Strata.B3AST.CallArg M → B3CST.CallArg M
  | .callArgExpr m e => B3CST.CallArg.call_arg_expr m (expressionToCST ctx e)
  | .callArgOut m id => B3CST.CallArg.call_arg_out m (mapAnn (fun x => x) id)
  | .callArgInout m id => B3CST.CallArg.call_arg_inout m (mapAnn (fun x => x) id)

partial def buildChoiceBranches [Inhabited M] : M → List (B3CST.ChoiceBranch M) → B3CST.ChoiceBranches M
  | m, [] => ChoiceBranches.choiceAtom m (ChoiceBranch.choice_branch m (B3CST.Statement.return_statement m))
  | m, [b] => ChoiceBranches.choiceAtom m b
  | m, b :: bs => ChoiceBranches.choicePush m (buildChoiceBranches m bs) b

partial def stmtToCST [Inhabited M] (ctx : ToCSTContext) : Strata.B3AST.Statement M → B3CST.Statement M
  | .varDecl m name ty autoinv init =>
    let ctx' := ctx.push name.val
    match ty.val, autoinv.val, init.val with
    | some t, some ai, some i => B3CST.Statement.var_decl_full m (mapAnn (fun x => x) name) (mkAnn m t.val) (expressionToCST ctx ai) (expressionToCST ctx' i)
    | some t, some ai, none => B3CST.Statement.var_decl_with_autoinv m (mapAnn (fun x => x) name) (mkAnn m t.val) (expressionToCST ctx ai)
    | some t, none, some i => B3CST.Statement.var_decl_with_init m (mapAnn (fun x => x) name) (mkAnn m t.val) (expressionToCST ctx' i)
    | some t, none, none => B3CST.Statement.var_decl_typed m (mapAnn (fun x => x) name) (mkAnn m t.val)
    | none, _, some i => B3CST.Statement.var_decl_inferred m (mapAnn (fun x => x) name) (expressionToCST ctx' i)
    | none, _, none => B3CST.Statement.var_decl_typed m (mapAnn (fun x => x) name) (mkAnn m "unknown")
  | .assign m lhs rhs => B3CST.Statement.assign m (mkAnn m (ctx.lookup lhs.val).1) (expressionToCST ctx rhs)
  | .reinit m idx => B3CST.Statement.reinit_statement m (mkAnn m (ctx.lookup idx.val).1)
  | .blockStmt m stmts =>
      let (stmts', _) := stmts.val.toList.foldl (fun (acc, ctx) stmt =>
        let stmt' := stmtToCST ctx stmt
        let ctx' := match stmt with
          | .varDecl _ name _ _ _ => ctx.push name.val
          | _ => ctx
        (acc ++ [stmt'], ctx')
      ) ([], ctx)
      B3CST.Statement.block m (mkAnn m stmts'.toArray)
  | .call m procName args => B3CST.Statement.call_statement m (mapAnn (fun x => x) procName) (mapAnn (fun arr => arr.toList.map (callArgToCST ctx) |>.toArray) args)
  | .check m expr => B3CST.Statement.check m (expressionToCST ctx expr)
  | .assume m expr => B3CST.Statement.assume m (expressionToCST ctx expr)
  | .reach m expr => B3CST.Statement.reach m (expressionToCST ctx expr)
  | .assert m expr => B3CST.Statement.assert m (expressionToCST ctx expr)
  | .aForall m var ty body =>
      let ctx' := ctx.push var.val
      B3CST.Statement.aForall_statement m (mapAnn (fun x => x) var) (mapAnn (fun x => x) ty) (stmtToCST ctx' body)
  | .choose m branches =>
      let choiceBranches := branches.val.toList.map (fun s => ChoiceBranch.choice_branch m (stmtToCST ctx s))
      B3CST.Statement.choose_statement m (buildChoiceBranches m choiceBranches)
  | .ifStmt m cond thenB elseB =>
      let elseCST := mapAnn (fun opt => opt.map (fun e => Else.else_some m (stmtToCST ctx e))) elseB
      B3CST.Statement.if_statement m (expressionToCST ctx cond) (stmtToCST ctx thenB) elseCST
  | .ifCase m cases =>
      B3CST.Statement.if_case_statement m (mapAnn (fun arr => arr.toList.map (fun c =>
        match c with
        | .oneIfCase cm cond body => IfCaseBranch.if_case_branch cm (expressionToCST ctx cond) (stmtToCST ctx body)) |>.toArray) cases)
  | .loop m invariants body =>
      B3CST.Statement.loop_statement m (mapAnn (fun arr => arr.toList.map (fun e => Invariant.invariant m (expressionToCST ctx e)) |>.toArray) invariants) (stmtToCST ctx body)
  | .labeledStmt m label stmt => B3CST.Statement.labeled_statement m (mapAnn (fun x => x) label) (stmtToCST ctx stmt)
  | .exit m label =>
      B3CST.Statement.exit_statement m (mapAnn (fun opt => opt.map (fun l => mkAnn m l.val)) label)
  | .returnStmt m => B3CST.Statement.return_statement m
  | .probe m label => B3CST.Statement.probe m (mapAnn (fun x => x) label)

end

end ToCST

---------------------------------------------------------------------
-- B3CST → B3AST Conversion (Concrete to Abstract)
---------------------------------------------------------------------

section FromCST

structure FromCSTContext where
  vars : List String

namespace FromCSTContext

def lookup (ctx : FromCSTContext) (name : String) : Nat :=
  ctx.vars.findIdx? (· == name) |>.getD ctx.vars.length

def lookupLast (ctx : FromCSTContext) (name : String) : Nat :=
  -- Find the last occurrence by searching from the end
  let rec findLast (vars : List String) (idx : Nat) : Option Nat :=
    match vars with
    | [] => none
    | v :: vs =>
        match findLast vs (idx + 1) with
        | some found => some found
        | none => if v == name then some idx else none
  findLast ctx.vars 0 |>.getD ctx.vars.length

def push (ctx : FromCSTContext) (name : String) : FromCSTContext :=
  { vars := name :: ctx.vars }

def empty : FromCSTContext := { vars := [] }

end FromCSTContext

partial def patternsToArray [Inhabited M] : B3CST.Patterns M → Array (B3CST.Pattern M)
  | .patterns_single _ p => #[p]
  | .patterns_cons _ p ps => patternsToArray ps |>.push p

partial def expressionFromCST [Inhabited M] [B3AnnFromCST M] (ctx : FromCSTContext) : B3CST.Expression M → Strata.B3AST.Expression M
  | .natLit ann n => .literal (B3AnnFromCST.annForLiteral ann) (.intLit (B3AnnFromCST.annForLiteralType ann) n.val)
  | .strLit ann s => .literal (B3AnnFromCST.annForLiteral ann) (.stringLit (B3AnnFromCST.annForLiteralType ann) s.val)
  | .btrue ann => .literal (B3AnnFromCST.annForLiteral ann) (.boolLit (B3AnnFromCST.annForLiteralType ann) true)
  | .bfalse ann => .literal (B3AnnFromCST.annForLiteral ann) (.boolLit (B3AnnFromCST.annForLiteralType ann) false)
  | .id ann name => .id (B3AnnFromCST.annForId ann) (ctx.lookup name.val)
  | .old_id ann name => .id (B3AnnFromCST.annForId ann) (ctx.lookupLast name.val)
  | .not ann arg => .unaryOp (B3AnnFromCST.annForUnaryOp ann) (.not (B3AnnFromCST.annForUnaryOpType ann)) (expressionFromCST ctx arg)
  | .neg ann arg => .unaryOp (B3AnnFromCST.annForUnaryOp ann) (.neg (B3AnnFromCST.annForUnaryOpType ann)) (expressionFromCST ctx arg)
  | .iff ann lhs rhs => .binaryOp (B3AnnFromCST.annForBinaryOp ann) (.iff (B3AnnFromCST.annForBinaryOpType ann)) (expressionFromCST ctx lhs) (expressionFromCST ctx rhs)
  | .implies ann lhs rhs => .binaryOp (B3AnnFromCST.annForBinaryOp ann) (.implies (B3AnnFromCST.annForBinaryOpType ann)) (expressionFromCST ctx lhs) (expressionFromCST ctx rhs)
  | .impliedBy ann lhs rhs => .binaryOp (B3AnnFromCST.annForBinaryOp ann) (.impliedBy (B3AnnFromCST.annForBinaryOpType ann)) (expressionFromCST ctx lhs) (expressionFromCST ctx rhs)
  | .and ann lhs rhs => .binaryOp (B3AnnFromCST.annForBinaryOp ann) (.and (B3AnnFromCST.annForBinaryOpType ann)) (expressionFromCST ctx lhs) (expressionFromCST ctx rhs)
  | .or ann lhs rhs => .binaryOp (B3AnnFromCST.annForBinaryOp ann) (.or (B3AnnFromCST.annForBinaryOpType ann)) (expressionFromCST ctx lhs) (expressionFromCST ctx rhs)
  | .equal ann lhs rhs => .binaryOp (B3AnnFromCST.annForBinaryOp ann) (.eq (B3AnnFromCST.annForBinaryOpType ann)) (expressionFromCST ctx lhs) (expressionFromCST ctx rhs)
  | .not_equal ann lhs rhs => .binaryOp (B3AnnFromCST.annForBinaryOp ann) (.neq (B3AnnFromCST.annForBinaryOpType ann)) (expressionFromCST ctx lhs) (expressionFromCST ctx rhs)
  | .lt ann lhs rhs => .binaryOp (B3AnnFromCST.annForBinaryOp ann) (.lt (B3AnnFromCST.annForBinaryOpType ann)) (expressionFromCST ctx lhs) (expressionFromCST ctx rhs)
  | .le ann lhs rhs => .binaryOp (B3AnnFromCST.annForBinaryOp ann) (.le (B3AnnFromCST.annForBinaryOpType ann)) (expressionFromCST ctx lhs) (expressionFromCST ctx rhs)
  | .ge ann lhs rhs => .binaryOp (B3AnnFromCST.annForBinaryOp ann) (.ge (B3AnnFromCST.annForBinaryOpType ann)) (expressionFromCST ctx lhs) (expressionFromCST ctx rhs)
  | .gt ann lhs rhs => .binaryOp (B3AnnFromCST.annForBinaryOp ann) (.gt (B3AnnFromCST.annForBinaryOpType ann)) (expressionFromCST ctx lhs) (expressionFromCST ctx rhs)
  | .add ann lhs rhs => .binaryOp (B3AnnFromCST.annForBinaryOp ann) (.add (B3AnnFromCST.annForBinaryOpType ann)) (expressionFromCST ctx lhs) (expressionFromCST ctx rhs)
  | .sub ann lhs rhs => .binaryOp (B3AnnFromCST.annForBinaryOp ann) (.sub (B3AnnFromCST.annForBinaryOpType ann)) (expressionFromCST ctx lhs) (expressionFromCST ctx rhs)
  | .mul ann lhs rhs => .binaryOp (B3AnnFromCST.annForBinaryOp ann) (.mul (B3AnnFromCST.annForBinaryOpType ann)) (expressionFromCST ctx lhs) (expressionFromCST ctx rhs)
  | .div ann lhs rhs => .binaryOp (B3AnnFromCST.annForBinaryOp ann) (.div (B3AnnFromCST.annForBinaryOpType ann)) (expressionFromCST ctx lhs) (expressionFromCST ctx rhs)
  | .mod ann lhs rhs => .binaryOp (B3AnnFromCST.annForBinaryOp ann) (.mod (B3AnnFromCST.annForBinaryOpType ann)) (expressionFromCST ctx lhs) (expressionFromCST ctx rhs)
  | .functionCall ann fn args => .functionCall (B3AnnFromCST.annForFunctionCall ann) ⟨B3AnnFromCST.annForFunctionCallName ann, fn.val⟩ ⟨B3AnnFromCST.annForFunctionCallArgs ann, args.val.map (expressionFromCST ctx)⟩
  | .labeledExpr ann label expr => .labeledExpr (B3AnnFromCST.annForLabeledExpr ann) ⟨B3AnnFromCST.annForLabeledExprLabel ann, label.val⟩ (expressionFromCST ctx expr)
  | .letExpr ann var value body =>
      let ctx' := ctx.push var.val
      .letExpr (B3AnnFromCST.annForLetExpr ann) ⟨B3AnnFromCST.annForLetExprVar ann, var.val⟩ (expressionFromCST ctx value) (expressionFromCST ctx' body)
  | .ite ann cond thenExpr elseExpr => .ite (B3AnnFromCST.annForIte ann) (expressionFromCST ctx cond) (expressionFromCST ctx thenExpr) (expressionFromCST ctx elseExpr)
  | .forall_expr_no_patterns ann var ty body =>
      let ctx' := ctx.push var.val
      .quantifierExpr (B3AnnFromCST.annForQuantifierExpr ann) (.forall (B3AnnFromCST.annForQuantifierKind ann)) ⟨B3AnnFromCST.annForQuantifierVar ann, var.val⟩ ⟨B3AnnFromCST.annForQuantifierType ann, ty.val⟩ ⟨B3AnnFromCST.annForQuantifierPatterns ann, #[]⟩ (expressionFromCST ctx' body)
  | .forall_expr ann var ty patterns body =>
      let ctx' := ctx.push var.val
      let convertPattern (p : B3CST.Pattern M) : Strata.B3AST.Pattern M :=
        match p with
        | .pattern pann exprs => .pattern (B3AnnFromCST.annForPattern pann) ⟨B3AnnFromCST.annForPatternExprs pann, exprs.val.map (expressionFromCST ctx')⟩
      let patternsArray := patternsToArray patterns |>.map convertPattern
      .quantifierExpr (B3AnnFromCST.annForQuantifierExpr ann) (.forall (B3AnnFromCST.annForQuantifierKind ann)) ⟨B3AnnFromCST.annForQuantifierVar ann, var.val⟩ ⟨B3AnnFromCST.annForQuantifierType ann, ty.val⟩ ⟨B3AnnFromCST.annForQuantifierPatterns ann, patternsArray⟩ (expressionFromCST ctx' body)
  | .exists_expr_no_patterns ann var ty body =>
      let ctx' := ctx.push var.val
      .quantifierExpr (B3AnnFromCST.annForQuantifierExpr ann) (.exists (B3AnnFromCST.annForQuantifierKind ann)) ⟨B3AnnFromCST.annForQuantifierVar ann, var.val⟩ ⟨B3AnnFromCST.annForQuantifierType ann, ty.val⟩ ⟨B3AnnFromCST.annForQuantifierPatterns ann, #[]⟩ (expressionFromCST ctx' body)
  | .exists_expr ann var ty patterns body =>
      let ctx' := ctx.push var.val
      let convertPattern (p : B3CST.Pattern M) : Strata.B3AST.Pattern M :=
        match p with
        | .pattern pann exprs => .pattern (B3AnnFromCST.annForPattern pann) ⟨B3AnnFromCST.annForPatternExprs pann, exprs.val.map (expressionFromCST ctx')⟩
      let patternsArray := patternsToArray patterns |>.map convertPattern
      .quantifierExpr (B3AnnFromCST.annForQuantifierExpr ann) (.exists (B3AnnFromCST.annForQuantifierKind ann)) ⟨B3AnnFromCST.annForQuantifierVar ann, var.val⟩ ⟨B3AnnFromCST.annForQuantifierType ann, ty.val⟩ ⟨B3AnnFromCST.annForQuantifierPatterns ann, patternsArray⟩ (expressionFromCST ctx' body)
  | .paren _ expr => expressionFromCST ctx expr

partial def callArgFromCST [Inhabited M] [B3AnnFromCST M] (ctx : FromCSTContext) : B3CST.CallArg M → Strata.B3AST.CallArg M
  | .call_arg_expr m expr => .callArgExpr m (expressionFromCST ctx expr)
  | .call_arg_out m id => .callArgOut m (mapAnn (fun x => x) id)
  | .call_arg_inout m id => .callArgInout m (mapAnn (fun x => x) id)

partial def choiceBranchesToList [Inhabited M] : B3CST.ChoiceBranches M → List (B3CST.Statement M)
  | .choiceAtom _ branch =>
      match branch with
      | .choice_branch _ stmt => [stmt]
  | .choicePush _ branches branch =>
      match branch with
      | .choice_branch _ stmt => stmt :: choiceBranchesToList branches

partial def stmtFromCST [Inhabited M] [B3AnnFromCST M] (ctx : FromCSTContext) : B3CST.Statement M → Strata.B3AST.Statement M
  | .var_decl_full m name ty autoinv init =>
      let ctx' := ctx.push name.val
      .varDecl m (mapAnn (fun x => x) name) (mapAnn (fun t => some (mkAnn m t)) ty) (mkAnn m (some (expressionFromCST ctx autoinv))) (mkAnn m (some (expressionFromCST ctx' init)))
  | .var_decl_with_autoinv m name ty autoinv =>
      .varDecl m (mapAnn (fun x => x) name) (mapAnn (fun t => some (mkAnn m t)) ty) (mkAnn m (some (expressionFromCST ctx autoinv))) (mkAnn m none)
  | .var_decl_with_init m name ty init =>
      let ctx' := ctx.push name.val
      .varDecl m (mapAnn (fun x => x) name) (mapAnn (fun t => some (mkAnn m t)) ty) (mkAnn m none) (mkAnn m (some (expressionFromCST ctx' init)))
  | .var_decl_typed m name ty =>
      .varDecl m (mapAnn (fun x => x) name) (mapAnn (fun t => some (mkAnn m t)) ty) (mkAnn m none) (mkAnn m none)
  | .var_decl_inferred m name init =>
      let ctx' := ctx.push name.val
      .varDecl m (mapAnn (fun x => x) name) (mkAnn m none) (mkAnn m none) (mkAnn m (some (expressionFromCST ctx' init)))
  | .val_decl m name ty init =>
      let ctx' := ctx.push name.val
      .varDecl m (mapAnn (fun x => x) name) (mapAnn (fun t => some (mkAnn m t)) ty) (mkAnn m none) (mkAnn m (some (expressionFromCST ctx' init)))
  | .val_decl_inferred m name init =>
      let ctx' := ctx.push name.val
      .varDecl m (mapAnn (fun x => x) name) (mkAnn m none) (mkAnn m none) (mkAnn m (some (expressionFromCST ctx' init)))
  | .assign m lhs rhs =>
      .assign m (mkAnn m (ctx.lookup lhs.val)) (expressionFromCST ctx rhs)
  | .reinit_statement m v =>
      .reinit m (mkAnn m (ctx.lookup v.val))
  | .check m expr =>
      .check m (expressionFromCST ctx expr)
  | .assume m expr =>
      .assume m (expressionFromCST ctx expr)
  | .reach m expr =>
      .reach m (expressionFromCST ctx expr)
  | .assert m expr =>
      .assert m (expressionFromCST ctx expr)
  | .return_statement m =>
      .returnStmt m
  | .block m stmts =>
      let (stmts', _) := stmts.val.toList.foldl (fun (acc, ctx) stmt =>
        let stmt' := stmtFromCST ctx stmt
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
      .blockStmt m (mkAnn m stmts'.toArray)
  | .if_statement m cond thenB elseB =>
      let elseBranch := mapAnn (fun opt => opt.map (fun e => match e with | .else_some _ stmt => stmtFromCST ctx stmt)) elseB
      .ifStmt m (expressionFromCST ctx cond) (stmtFromCST ctx thenB) elseBranch
  | .loop_statement m invs body =>
      let invariants := invs.val.toList.map fun inv =>
        match inv with
        | .invariant _ expr => expressionFromCST ctx expr
      .loop m (mkAnn m invariants.toArray) (stmtFromCST ctx body)
  | .exit_statement m label =>
      .exit m (mapAnn (fun opt => opt.map (fun l => mkAnn m l.val)) label)
  | .labeled_statement m label stmt =>
      .labeledStmt m (mapAnn (fun x => x) label) (stmtFromCST ctx stmt)
  | .probe m label =>
      .probe m (mapAnn (fun x => x) label)
  | .aForall_statement m var ty body =>
      let ctx' := ctx.push var.val
      .aForall m (mapAnn (fun x => x) var) (mapAnn (fun x => x) ty) (stmtFromCST ctx' body)
  | .choose_statement m branches =>
      .choose m (mkAnn m (choiceBranchesToList branches |>.map (stmtFromCST ctx)).toArray)
  | .if_case_statement m cases =>
      .ifCase m (mapAnn (fun arr => arr.toList.map (fun case =>
        match case with
        | .if_case_branch cm cond stmt => .oneIfCase cm (expressionFromCST ctx cond) (stmtFromCST ctx stmt)) |>.toArray) cases)
  | .call_statement m procName args =>
      .call m (mapAnn (fun x => x) procName) (mapAnn (fun arr => arr.toList.map (callArgFromCST ctx) |>.toArray) args)

def paramModeFromCST [Inhabited M] : Ann (Option (B3CST.PParamMode M)) M → Strata.B3AST.ParamMode M
  | ⟨m, none⟩ => .paramModeIn m
  | ⟨m, some (.pmode_out _)⟩ => .paramModeOut m
  | ⟨m, some (.pmode_inout _)⟩ => .paramModeInout m

def fParameterFromCST [Inhabited M] : B3CST.FParam M → Strata.B3AST.FParameter M
  | .fparam m injective name ty =>
      let inj := match injective.val with
        | some (.injective_some _) => true
        | none => false
      .fParameter m (mkAnn m inj) (mapAnn (fun x => x) name) (mapAnn (fun x => x) ty)

def pParameterFromCST [Inhabited M] [B3AnnFromCST M] (ctx : FromCSTContext) : B3CST.PParam M → Strata.B3AST.PParameter M
  | .pparam m mode name ty =>
      .pParameter m (paramModeFromCST mode) (mapAnn (fun x => x) name) (mapAnn (fun x => x) ty) (mkAnn m none)
  | .pparam_with_autoinv m mode name ty autoinv =>
      .pParameter m (paramModeFromCST mode) (mapAnn (fun x => x) name) (mapAnn (fun x => x) ty) (mkAnn m (some (expressionFromCST ctx autoinv)))

def specFromCST [Inhabited M] [B3AnnFromCST M] (ctx : FromCSTContext) : B3CST.Spec M → Strata.B3AST.Spec M
  | .spec_requires m expr => .specRequires m (expressionFromCST ctx expr)
  | .spec_ensures m expr => .specEnsures m (expressionFromCST ctx expr)

def fparamsToList : Ann (Array (B3CST.FParam M)) M → List (B3CST.FParam M)
  | ⟨_, arr⟩ => arr.toList

def declFromCST [Inhabited M] [B3AnnFromCST M] (ctx : FromCSTContext) : B3CST.Decl M → Strata.B3AST.Decl M
  | .type_decl m name =>
      .typeDecl m (mapAnn (fun x => x) name)
  | .tagger_decl m name forType =>
      .tagger m (mapAnn (fun x => x) name) (mapAnn (fun x => x) forType)
  | .function_decl m name params resultType tag body =>
      let paramsAST := fparamsToList params |>.map fParameterFromCST
      let paramNames := paramsAST.map (fun p => match p with | .fParameter _ _ n _ => n.val)
      let ctx' := paramNames.foldl (fun acc n => acc.push n) ctx
      let tagAST := tag.val.map (fun t => match t with | .tag_some _ id => mkAnn m id.val)
      let bodyAST := mapAnn (fun opt => opt.map (fun b => match b with
        | .function_body_some bm whens expr =>
            let whensAST := whens.val.toList.map (fun w => match w with | .when_clause wm e => B3AST.When.when wm (expressionFromCST ctx' e))
            B3AST.FunctionBody.functionBody bm (mkAnn bm whensAST.toArray) (expressionFromCST ctx' expr))) body
      .function m (mapAnn (fun x => x) name) (mkAnn m paramsAST.toArray) (mapAnn (fun x => x) resultType) (mkAnn m tagAST) bodyAST
  | .axiom_decl m axiomBody =>
      match axiomBody with
      | .axiom _ expr =>
          .axiom m (mkAnn m #[]) (expressionFromCST ctx expr)
      | .explain_axiom _ names expr =>
          let namesAST := names.val.toList.map (fun n => mkAnn m n.val)
          .axiom m (mkAnn m namesAST.toArray) (expressionFromCST ctx expr)
  | .procedure_decl m name params specs body =>
      -- Build context for parameters: inout parameters need two entries (old and current)
      let ctx' := params.val.toList.foldl (fun acc p =>
        let (pname, mode) := match p with
          | .pparam _ mode n _ => (n.val, mode.val)
          | .pparam_with_autoinv _ mode n _ _ => (n.val, mode.val)
        match mode with
        | some (.pmode_inout _) => acc.push pname |>.push pname  -- Push twice: old value, then current value
        | _ => acc.push pname  -- Push once for in/out parameters
      ) ctx
      -- Now convert all parameters with the full context (so autoinv can reference all params)
      let paramsAST := params.val.toList.map (pParameterFromCST ctx')
      let specsAST := specs.val.toList.map (specFromCST ctx')
      let bodyAST := mapAnn (fun opt => opt.map (fun b => match b with | .proc_body_some _ s => stmtFromCST ctx' s)) body
      .procedure m (mapAnn (fun x => x) name) (mkAnn m paramsAST.toArray) (mkAnn m specsAST.toArray) bodyAST

end FromCST

end B3
