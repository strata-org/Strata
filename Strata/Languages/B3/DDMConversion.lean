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
  inProcedure : Bool := false

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

-- Check if a variable at index idx is shadowed (has a later occurrence with same name)
-- This is now computed in lookup, but kept for compatibility
def isShadowed (ctx : ToCSTContext) (idx : Nat) : Bool :=
  (ctx.lookup idx).2

def push (ctx : ToCSTContext) (name : String) : ToCSTContext :=
  { vars := name :: ctx.vars, inProcedure := ctx.inProcedure }

def enterProcedure (ctx : ToCSTContext) : ToCSTContext :=
  { ctx with inProcedure := true }

def empty : ToCSTContext := { vars := [], inProcedure := false }

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

---------------------------------------------------------------------
-- Annotation-Preserving Conversions (B3CST M ↔ B3AST M)
---------------------------------------------------------------------

section AnnotationPreserving

structure ToCSTContextSR where
  vars : List String

namespace ToCSTContextSR

def lookup (ctx : ToCSTContextSR) (idx : Nat): String × Bool :=
  match ctx.vars[idx]? with
  | .some name =>
    if name == "" then (s!"@{idx}", false) else
    -- Determine if this is an old value: first occurrence with shadowing
    let isOld := ctx.vars.take idx |>.any (· == name)
    let rec go (vars: List String) (pastIndex: Nat) (idx: Nat): String :=
      let default := fun _: Unit => if pastIndex == 0 then name else s!"name@{pastIndex}"
      if idx == 0 then default ()
      else
        match vars with
        | [] => default ()
        | otherName :: tail =>
          if name == otherName then go tail (pastIndex + 1) (idx - 1)
          else go tail pastIndex (idx - 1)
    (go ctx.vars 0 idx, isOld)
  | .none => (s!"@{idx}", false)

def push (ctx : ToCSTContextSR) (name : String) : ToCSTContextSR :=
  { vars := name :: ctx.vars }

def empty : ToCSTContextSR := { vars := [] }

end ToCSTContextSR

structure FromCSTContextSR where
  vars : List String

namespace FromCSTContextSR

def lookup (ctx : FromCSTContextSR) (name : String) : Nat :=
  ctx.vars.findIdx? (· == name) |>.getD ctx.vars.length

def lookupLast (ctx : FromCSTContextSR) (name : String) : Nat :=
  -- Find the last occurrence by searching from the end
  let rec findLast (vars : List String) (idx : Nat) : Option Nat :=
    match vars with
    | [] => none
    | v :: vs =>
        match findLast vs (idx + 1) with
        | some found => some found
        | none => if v == name then some idx else none
  findLast ctx.vars 0 |>.getD ctx.vars.length

def push (ctx : FromCSTContextSR) (name : String) : FromCSTContextSR :=
  { vars := name :: ctx.vars }

def empty : FromCSTContextSR := { vars := [] }

end FromCSTContextSR

/-!
## Annotation-Preserving Conversions

These functions preserve M annotations when converting between B3CST and B3AST.
They duplicate the Unit-based conversions but thread M through all recursive calls.
-/

mutual

partial def literalToCSTSR [Inhabited $ Strata.B3CST.Expression M] (ann : M) : B3AST.Literal M → B3CST.Expression M
  | .intLit _ n => B3CST.Expression.natLit ann (mkAnn ann n)
  | .boolLit _ b => if b then B3CST.Expression.btrue ann else B3CST.Expression.bfalse ann
  | .stringLit _ s => B3CST.Expression.strLit ann (mkAnn ann s)

partial def expressionToCSTSR [Inhabited $ Strata.B3CST.Expression M] (ctx : ToCSTContextSR) : Strata.B3AST.Expression M → B3CST.Expression M
  | .literal ann lit => literalToCSTSR ann lit
  | .id ann idx =>
      let (name, isOld) := ctx.lookup idx
      if isOld then
        B3CST.Expression.old_id ann (mkAnn ann name)
      else
        B3CST.Expression.id ann (mkAnn ann name)
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
  | .functionCall ann fnName args => B3CST.Expression.functionCall ann (mkAnn ann fnName.val) (mkAnn ann (args.val.map (expressionToCSTSR ctx)))
  | .labeledExpr ann label expr => B3CST.Expression.labeledExpr ann (mkAnn ann label.val) (expressionToCSTSR ctx expr)
  | .letExpr ann var value body =>
      let ctx' := ctx.push var.val
      B3CST.Expression.letExpr ann (mkAnn ann var.val) (expressionToCSTSR ctx value) (expressionToCSTSR ctx' body)
  | .quantifierExpr ann qkind var ty patterns body =>
      let ctx' := ctx.push var.val
      let convertPattern (p : Strata.B3AST.Pattern M) : B3CST.Pattern M :=
        match p with
        | .pattern pann exprs =>
            let exprsCST := exprs.val.map (expressionToCSTSR ctx')
            B3CST.Pattern.pattern pann (mkAnn pann exprsCST)
      let patternsDDM := match patterns.val.toList with
        | [] => none
        | [p] => some (Patterns.patterns_single ann (convertPattern p))
        | p :: ps =>
            some (ps.foldl (init := Patterns.patterns_single ann (convertPattern p)) fun acc p =>
              Patterns.patterns_cons ann (convertPattern p) acc)
      match qkind with
      | .forall _ =>
          match patternsDDM with
          | none => B3CST.Expression.forall_expr_no_patterns ann (mkAnn ann var.val) (mkAnn ann ty.val) (expressionToCSTSR ctx' body)
          | some pats => B3CST.Expression.forall_expr ann (mkAnn ann var.val) (mkAnn ann ty.val) pats (expressionToCSTSR ctx' body)
      | .exists _ =>
          match patternsDDM with
          | none => B3CST.Expression.exists_expr_no_patterns ann (mkAnn ann var.val) (mkAnn ann ty.val) (expressionToCSTSR ctx' body)
          | some pats => B3CST.Expression.exists_expr ann (mkAnn ann var.val) (mkAnn ann ty.val) pats (expressionToCSTSR ctx' body)

partial def patternsToArraySR [Inhabited $ Strata.B3AST.Expression M] : B3CST.Patterns M → Array (B3CST.Pattern M)
  | .patterns_single _ p => #[p]
  | .patterns_cons _ p ps => patternsToArraySR ps |>.push p

partial def expressionFromCSTSR [Inhabited $ Strata.B3AST.Expression M] (ctx : FromCSTContextSR) : B3CST.Expression M → Strata.B3AST.Expression M
  | .natLit ann n => .literal ann (.intLit ann n.val)
  | .strLit ann s => .literal ann (.stringLit ann s.val)
  | .btrue ann => .literal ann (.boolLit ann true)
  | .bfalse ann => .literal ann (.boolLit ann false)
  | .id ann name => .id ann (ctx.lookup name.val)
  | .old_id ann name => .id ann (ctx.lookupLast name.val)
  | .not ann arg => .unaryOp ann (.not ann) (expressionFromCSTSR ctx arg)
  | .neg ann arg => .unaryOp ann (.neg ann) (expressionFromCSTSR ctx arg)
  | .iff ann lhs rhs => .binaryOp ann (.iff ann) (expressionFromCSTSR ctx lhs) (expressionFromCSTSR ctx rhs)
  | .implies ann lhs rhs => .binaryOp ann (.implies ann) (expressionFromCSTSR ctx lhs) (expressionFromCSTSR ctx rhs)
  | .impliedBy ann lhs rhs => .binaryOp ann (.impliedBy ann) (expressionFromCSTSR ctx lhs) (expressionFromCSTSR ctx rhs)
  | .and ann lhs rhs => .binaryOp ann (.and ann) (expressionFromCSTSR ctx lhs) (expressionFromCSTSR ctx rhs)
  | .or ann lhs rhs => .binaryOp ann (.or ann) (expressionFromCSTSR ctx lhs) (expressionFromCSTSR ctx rhs)
  | .equal ann lhs rhs => .binaryOp ann (.eq ann) (expressionFromCSTSR ctx lhs) (expressionFromCSTSR ctx rhs)
  | .not_equal ann lhs rhs => .binaryOp ann (.neq ann) (expressionFromCSTSR ctx lhs) (expressionFromCSTSR ctx rhs)
  | .lt ann lhs rhs => .binaryOp ann (.lt ann) (expressionFromCSTSR ctx lhs) (expressionFromCSTSR ctx rhs)
  | .le ann lhs rhs => .binaryOp ann (.le ann) (expressionFromCSTSR ctx lhs) (expressionFromCSTSR ctx rhs)
  | .ge ann lhs rhs => .binaryOp ann (.ge ann) (expressionFromCSTSR ctx lhs) (expressionFromCSTSR ctx rhs)
  | .gt ann lhs rhs => .binaryOp ann (.gt ann) (expressionFromCSTSR ctx lhs) (expressionFromCSTSR ctx rhs)
  | .add ann lhs rhs => .binaryOp ann (.add ann) (expressionFromCSTSR ctx lhs) (expressionFromCSTSR ctx rhs)
  | .sub ann lhs rhs => .binaryOp ann (.sub ann) (expressionFromCSTSR ctx lhs) (expressionFromCSTSR ctx rhs)
  | .mul ann lhs rhs => .binaryOp ann (.mul ann) (expressionFromCSTSR ctx lhs) (expressionFromCSTSR ctx rhs)
  | .div ann lhs rhs => .binaryOp ann (.div ann) (expressionFromCSTSR ctx lhs) (expressionFromCSTSR ctx rhs)
  | .mod ann lhs rhs => .binaryOp ann (.mod ann) (expressionFromCSTSR ctx lhs) (expressionFromCSTSR ctx rhs)
  | .functionCall ann fn args => .functionCall ann (mkAnn ann fn.val) (mkAnn ann (args.val.map (expressionFromCSTSR ctx)))
  | .labeledExpr ann label expr => .labeledExpr ann (mkAnn ann label.val) (expressionFromCSTSR ctx expr)
  | .letExpr ann var value body =>
      let ctx' := ctx.push var.val
      .letExpr ann (mkAnn ann var.val) (expressionFromCSTSR ctx value) (expressionFromCSTSR ctx' body)
  | .ite ann cond thenExpr elseExpr => .ite ann (expressionFromCSTSR ctx cond) (expressionFromCSTSR ctx thenExpr) (expressionFromCSTSR ctx elseExpr)
  | .forall_expr_no_patterns ann var ty body =>
      let ctx' := ctx.push var.val
      .quantifierExpr ann (.forall ann) (mkAnn ann var.val) (mkAnn ann ty.val) (mkAnn ann #[]) (expressionFromCSTSR ctx' body)
  | .forall_expr ann var ty patterns body =>
      let ctx' := ctx.push var.val
      let convertPattern (p : B3CST.Pattern M) : Strata.B3AST.Pattern M :=
        match p with
        | .pattern pann exprs => .pattern pann (mkAnn pann (exprs.val.map (expressionFromCSTSR ctx')))
      let patternsArray := patternsToArraySR patterns |>.map convertPattern
      .quantifierExpr ann (.forall ann) (mkAnn ann var.val) (mkAnn ann ty.val) (mkAnn ann patternsArray) (expressionFromCSTSR ctx' body)
  | .exists_expr_no_patterns ann var ty body =>
      let ctx' := ctx.push var.val
      .quantifierExpr ann (.exists ann) (mkAnn ann var.val) (mkAnn ann ty.val) (mkAnn ann #[]) (expressionFromCSTSR ctx' body)
  | .exists_expr ann var ty patterns body =>
      let ctx' := ctx.push var.val
      let convertPattern (p : B3CST.Pattern M) : Strata.B3AST.Pattern M :=
        match p with
        | .pattern pann exprs => .pattern pann (mkAnn pann (exprs.val.map (expressionFromCSTSR ctx')))
      let patternsArray := patternsToArraySR patterns |>.map convertPattern
      .quantifierExpr ann (.exists ann) (mkAnn ann var.val) (mkAnn ann ty.val) (mkAnn ann patternsArray) (expressionFromCSTSR ctx' body)
  | .paren _ expr => expressionFromCSTSR ctx expr

end

namespace Expression

def toAST [Inhabited $ Strata.B3AST.Expression M] (e : B3CST.Expression M) : Strata.B3AST.Expression M :=
  expressionFromCSTSR FromCSTContextSR.empty e

def toCST [Inhabited $ Strata.B3CST.Expression M] (e : Strata.B3AST.Expression M) : B3CST.Expression M :=
  expressionToCSTSR ToCSTContextSR.empty e

end Expression

namespace Stmt

mutual

partial def callArgToCSTSR [Inhabited $ B3CST.Expression M] [Inhabited $ B3CST.Statement M] (ctx : ToCSTContextSR) : Strata.B3AST.CallArg M → B3CST.CallArg M
  | .callArgExpr m e => B3CST.CallArg.call_arg_expr m (expressionToCSTSR ctx e)
  | .callArgOut m id => B3CST.CallArg.call_arg_out m (mkAnn m id.val)
  | .callArgInout m id => B3CST.CallArg.call_arg_inout m (mkAnn m id.val)

partial def buildChoiceBranchesSR : M → List (B3CST.ChoiceBranch M) → B3CST.ChoiceBranches M
  | m, [] => ChoiceBranches.choiceAtom m (ChoiceBranch.choice_branch m (B3CST.Statement.return_statement m))
  | m, [b] => ChoiceBranches.choiceAtom m b
  | m, b :: bs => ChoiceBranches.choicePush m (buildChoiceBranchesSR m bs) b

partial def stmtToCSTSR [Inhabited (B3CST.Expression M)] [Inhabited $ B3CST.Statement M] (ctx : ToCSTContextSR) : Strata.B3AST.Statement M → B3CST.Statement M
  | .varDecl m name ty autoinv init =>
    let ctx' := ctx.push name.val
    match ty.val, autoinv.val, init.val with
    | some t, some ai, some i => B3CST.Statement.var_decl_full m (mkAnn m name.val) (mkAnn m t.val) (expressionToCSTSR ctx ai) (expressionToCSTSR ctx' i)
    | some t, some ai, none => B3CST.Statement.var_decl_with_autoinv m (mkAnn m name.val) (mkAnn m t.val) (expressionToCSTSR ctx ai)
    | some t, none, some i => B3CST.Statement.var_decl_with_init m (mkAnn m name.val) (mkAnn m t.val) (expressionToCSTSR ctx' i)
    | some t, none, none => B3CST.Statement.var_decl_typed m (mkAnn m name.val) (mkAnn m t.val)
    | none, _, some i => B3CST.Statement.var_decl_inferred m (mkAnn m name.val) (expressionToCSTSR ctx' i)
    | none, _, none => B3CST.Statement.var_decl_typed m (mkAnn m name.val) (mkAnn m "unknown")
  | .assign m lhs rhs => B3CST.Statement.assign m (mkAnn m (ctx.lookup lhs.val).fst) (expressionToCSTSR ctx rhs)
  | .reinit m idx => B3CST.Statement.reinit_statement m (mkAnn m (ctx.lookup idx.val).fst)
  | .blockStmt m stmts =>
      let (stmts', _) := stmts.val.toList.foldl (fun (acc, ctx) stmt =>
        let stmt' := stmtToCSTSR ctx stmt
        let ctx' := match stmt with
          | .varDecl _ name _ _ _ => ctx.push name.val
          | _ => ctx
        (acc ++ [stmt'], ctx')
      ) ([], ctx)
      B3CST.Statement.block m (mkAnn m stmts'.toArray)
  | .call m procName args => B3CST.Statement.call_statement m (mkAnn m procName.val) (mkAnn m (args.val.toList.map (callArgToCSTSR ctx) |>.toArray))
  | .check m expr => B3CST.Statement.check m (expressionToCSTSR ctx expr)
  | .assume m expr => B3CST.Statement.assume m (expressionToCSTSR ctx expr)
  | .reach m expr => B3CST.Statement.reach m (expressionToCSTSR ctx expr)
  | .assert m expr => B3CST.Statement.assert m (expressionToCSTSR ctx expr)
  | .aForall m var ty body =>
      let ctx' := ctx.push var.val
      B3CST.Statement.aForall_statement m (mkAnn m var.val) (mkAnn m ty.val) (stmtToCSTSR ctx' body)
  | .choose m branches =>
      let choiceBranches := branches.val.toList.map (fun s => ChoiceBranch.choice_branch m (stmtToCSTSR ctx s))
      B3CST.Statement.choose_statement m (buildChoiceBranchesSR m choiceBranches)
  | .ifStmt m cond thenB elseB =>
      let elseCST := mapAnn (fun opt => opt.map (fun e => Else.else_some m (stmtToCSTSR ctx e))) elseB
      B3CST.Statement.if_statement m (expressionToCSTSR ctx cond) (stmtToCSTSR ctx thenB) elseCST
  | .ifCase m cases =>
      B3CST.Statement.if_case_statement m (mkAnn m (cases.val.toList.map (fun c =>
        match c with
        | .oneIfCase cm cond body => IfCaseBranch.if_case_branch cm (expressionToCSTSR ctx cond) (stmtToCSTSR ctx body)) |>.toArray))
  | .loop m invariants body =>
      B3CST.Statement.loop_statement m (mkAnn m (invariants.val.toList.map (fun e => Invariant.invariant m (expressionToCSTSR ctx e)) |>.toArray)) (stmtToCSTSR ctx body)
  | .labeledStmt m label stmt => B3CST.Statement.labeled_statement m (mkAnn m label.val) (stmtToCSTSR ctx stmt)
  | .exit m label =>
      B3CST.Statement.exit_statement m (mapAnn (fun opt => opt.map (fun l => mkAnn m l.val)) label)
  | .returnStmt m => B3CST.Statement.return_statement m
  | .probe m label => B3CST.Statement.probe m (mkAnn m label.val)

partial def callArgFromCSTSR [Inhabited (B3AST.Expression M)] (ctx : FromCSTContextSR) : B3CST.CallArg M → Strata.B3AST.CallArg M
  | .call_arg_expr m expr => .callArgExpr m (expressionFromCSTSR ctx expr)
  | .call_arg_out m id => .callArgOut m (mkAnn m id.val)
  | .call_arg_inout m id => .callArgInout m (mkAnn m id.val)

partial def choiceBranchesToListSR : B3CST.ChoiceBranches M → List (B3CST.Statement M)
  | .choiceAtom _ branch =>
      match branch with
      | .choice_branch _ stmt => [stmt]
  | .choicePush _ branches branch =>
      match branch with
      | .choice_branch _ stmt => stmt :: choiceBranchesToListSR branches

partial def stmtFromCSTSR [Inhabited $ B3AST.Expression M] [Inhabited $ B3AST.Statement M] (ctx : FromCSTContextSR) : B3CST.Statement M → Strata.B3AST.Statement M
  | .var_decl_full m name ty autoinv init =>
      let ctx' := ctx.push name.val
      .varDecl m (mkAnn m name.val) (mkAnn m (some (mkAnn m ty.val))) (mkAnn m (some (expressionFromCSTSR ctx autoinv))) (mkAnn m (some (expressionFromCSTSR ctx' init)))
  | .var_decl_with_autoinv m name ty autoinv =>
      .varDecl m (mkAnn m name.val) (mkAnn m (some (mkAnn m ty.val))) (mkAnn m (some (expressionFromCSTSR ctx autoinv))) (mkAnn m none)
  | .var_decl_with_init m name ty init =>
      let ctx' := ctx.push name.val
      .varDecl m (mkAnn m name.val) (mkAnn m (some (mkAnn m ty.val))) (mkAnn m none) (mkAnn m (some (expressionFromCSTSR ctx' init)))
  | .var_decl_typed m name ty =>
      .varDecl m (mkAnn m name.val) (mkAnn m (some (mkAnn m ty.val))) (mkAnn m none) (mkAnn m none)
  | .var_decl_inferred m name init =>
      let ctx' := ctx.push name.val
      .varDecl m (mkAnn m name.val) (mkAnn m none) (mkAnn m none) (mkAnn m (some (expressionFromCSTSR ctx' init)))
  | .val_decl m name ty init =>
      let ctx' := ctx.push name.val
      .varDecl m (mkAnn m name.val) (mkAnn m (some (mkAnn m ty.val))) (mkAnn m none) (mkAnn m (some (expressionFromCSTSR ctx' init)))
  | .val_decl_inferred m name init =>
      let ctx' := ctx.push name.val
      .varDecl m (mkAnn m name.val) (mkAnn m none) (mkAnn m none) (mkAnn m (some (expressionFromCSTSR ctx' init)))
  | .assign m lhs rhs =>
      .assign m (mkAnn m (ctx.lookup lhs.val)) (expressionFromCSTSR ctx rhs)
  | .reinit_statement m v =>
      .reinit m (mkAnn m (ctx.lookup v.val))
  | .check m expr =>
      .check m (expressionFromCSTSR ctx expr)
  | .assume m expr =>
      .assume m (expressionFromCSTSR ctx expr)
  | .reach m expr =>
      .reach m (expressionFromCSTSR ctx expr)
  | .assert m expr =>
      .assert m (expressionFromCSTSR ctx expr)
  | .return_statement m =>
      .returnStmt m
  | .block m stmts =>
      let (stmts', _) := stmts.val.toList.foldl (fun (acc, ctx) stmt =>
        let stmt' := stmtFromCSTSR ctx stmt
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
      let elseBranch := mapAnn (fun opt => opt.map (fun e => match e with | .else_some _ stmt => stmtFromCSTSR ctx stmt)) elseB
      .ifStmt m (expressionFromCSTSR ctx cond) (stmtFromCSTSR ctx thenB) elseBranch
  | .loop_statement m invs body =>
      let invariants := invs.val.toList.map fun inv =>
        match inv with
        | .invariant _ expr => expressionFromCSTSR ctx expr
      .loop m (mkAnn m invariants.toArray) (stmtFromCSTSR ctx body)
  | .exit_statement m label =>
      .exit m (mapAnn (fun opt => opt.map (fun l => mkAnn m l.val)) label)
  | .labeled_statement m label stmt =>
      .labeledStmt m (mkAnn m label.val) (stmtFromCSTSR ctx stmt)
  | .probe m label =>
      .probe m (mkAnn m label.val)
  | .aForall_statement m var ty body =>
      let ctx' := ctx.push var.val
      .aForall m (mkAnn m var.val) (mkAnn m ty.val) (stmtFromCSTSR ctx' body)
  | .choose_statement m branches =>
      .choose m (mkAnn m (choiceBranchesToListSR branches |>.map (stmtFromCSTSR ctx)).toArray)
  | .if_case_statement m cases =>
      .ifCase m (mkAnn m (cases.val.toList.map (fun case =>
        match case with
        | .if_case_branch cm cond stmt => .oneIfCase cm (expressionFromCSTSR ctx cond) (stmtFromCSTSR ctx stmt)) |>.toArray))
  | .call_statement m procName args =>
      .call m (mkAnn m procName.val) (mkAnn m (args.val.toList.map (callArgFromCSTSR ctx) |>.toArray))

end

def toAST   [Inhabited $ B3AST.Expression M] [Inhabited $ B3AST.Statement M] (s : B3CST.Statement M) : Strata.B3AST.Statement M :=
  stmtFromCSTSR FromCSTContextSR.empty s

def toCST [Inhabited $ B3CST.Expression M] [Inhabited $ B3CST.Statement M] (s : Strata.B3AST.Statement M) : B3CST.Statement M :=
  stmtToCSTSR ToCSTContextSR.empty s

end Stmt

namespace Decl

mutual

partial def fParameterToCSTSR (_ctx : ToCSTContextSR) : Strata.B3AST.FParameter M → B3CST.FParam M
  | .fParameter m injective name ty =>
      let inj := mapAnn (fun b => if b then some (B3CST.Injective.injective_some m) else none) injective
      B3CST.FParam.fparam m inj (mkAnn m name.val) (mkAnn m ty.val)

partial def pParameterToCSTSR [Inhabited $ B3CST.Expression M] (ctx : ToCSTContextSR) : Strata.B3AST.PParameter M → B3CST.PParam M
  | .pParameter m mode name ty autoinv =>
      let modeCST := match mode with
        | .paramModeIn _ => mkAnn m none
        | .paramModeOut _ => mkAnn m (some (B3CST.PParamMode.pmode_out m))
        | .paramModeInout _ => mkAnn m (some (B3CST.PParamMode.pmode_inout m))
      match autoinv.val with
      | some ai => B3CST.PParam.pparam_with_autoinv m modeCST (mkAnn m name.val) (mkAnn m ty.val) (expressionToCSTSR ctx ai)
      | none => B3CST.PParam.pparam m modeCST (mkAnn m name.val) (mkAnn m ty.val)

partial def specToCSTSR [Inhabited $ B3CST.Expression M] (ctx : ToCSTContextSR) : Strata.B3AST.Spec M → B3CST.Spec M
  | .specRequires m expr => B3CST.Spec.spec_requires m (expressionToCSTSR ctx expr)
  | .specEnsures m expr => B3CST.Spec.spec_ensures m (expressionToCSTSR ctx expr)

partial def declToCSTSR [Inhabited $ B3CST.Expression M] [Inhabited $ B3CST.Statement M]  (ctx : ToCSTContextSR) : Strata.B3AST.Decl M → B3CST.Decl M
  | .typeDecl m name =>
      B3CST.Decl.type_decl m (mkAnn m name.val)
  | .tagger m name forType =>
      B3CST.Decl.tagger_decl m (mkAnn m name.val) (mkAnn m forType.val)
  | .function m name params resultType tag body =>
      let paramNames := params.val.toList.map (fun p => match p with | .fParameter _ _ n _ => n.val)
      let ctx' := paramNames.foldl (fun acc n => acc.push n) ctx
      let paramsCST := mkAnn m (params.val.toList.map (fParameterToCSTSR ctx) |>.toArray)
      let tagClause := mapAnn (fun opt => opt.map (fun t => B3CST.TagClause.tag_some m (mkAnn m t.val))) tag
      let bodyCST := mapAnn (fun opt => opt.map (fun b => match b with
        | .functionBody bm whens expr =>
            let whensCST := whens.val.toList.map (fun w => match w with | .when wm e => B3CST.WhenClause.when_clause wm (expressionToCSTSR ctx' e))
            B3CST.FunctionBody.function_body_some bm (mkAnn bm whensCST.toArray) (expressionToCSTSR ctx' expr))) body
      B3CST.Decl.function_decl m (mkAnn m name.val) paramsCST (mkAnn m resultType.val) tagClause bodyCST
  | .axiom m explains expr =>
      let explainsCST := mkAnn m (explains.val.toList.map (fun id => mkAnn m id.val) |>.toArray)
      if explains.val.isEmpty then
        B3CST.Decl.axiom_decl m (B3CST.AxiomBody.axiom m (expressionToCSTSR ctx expr))
      else
        B3CST.Decl.axiom_decl m (B3CST.AxiomBody.explain_axiom m explainsCST (expressionToCSTSR ctx expr))
  | .procedure m name params specs body =>
      -- Build context: inout parameters need two entries (old and current)
      let ctx' := params.val.toList.foldl (fun acc p =>
        match p with
        | .pParameter _ mode pname _ _ =>
          match mode with
          | .paramModeInout _ => acc.push s!"old {pname.val}" |>.push pname.val  -- Push "old x" then "x"
          | _ => acc.push pname.val
      ) ctx
      let paramsCST := mkAnn m (params.val.toList.map (pParameterToCSTSR ctx') |>.toArray)
      let specsCST := specs.val.toList.map (specToCSTSR ctx')
      let bodyCST := mapAnn (fun opt => opt.map (fun s => B3CST.ProcBody.proc_body_some m (Stmt.stmtToCSTSR ctx' s))) body
      B3CST.Decl.procedure_decl m (mkAnn m name.val) paramsCST (mkAnn m specsCST.toArray) bodyCST

partial def fParameterFromCSTSR : B3CST.FParam M → Strata.B3AST.FParameter M
  | .fparam m injective name ty =>
      let inj := match injective.val with
        | some (.injective_some _) => true
        | none => false
      .fParameter m (mkAnn m inj) (mkAnn m name.val) (mkAnn m ty.val)

partial def pParameterFromCSTSR [Inhabited $ B3AST.Expression M] (ctx : FromCSTContextSR) : B3CST.PParam M → Strata.B3AST.PParameter M
  | .pparam m mode name ty =>
      let modeAST := match mode.val with
        | none => Strata.B3AST.ParamMode.paramModeIn m
        | some (.pmode_out _) => Strata.B3AST.ParamMode.paramModeOut m
        | some (.pmode_inout _) => Strata.B3AST.ParamMode.paramModeInout m
      .pParameter m modeAST (mkAnn m name.val) (mkAnn m ty.val) (mkAnn m none)
  | .pparam_with_autoinv m mode name ty autoinv =>
      let modeAST := match mode.val with
        | none => Strata.B3AST.ParamMode.paramModeIn m
        | some (.pmode_out _) => Strata.B3AST.ParamMode.paramModeOut m
        | some (.pmode_inout _) => Strata.B3AST.ParamMode.paramModeInout m
      .pParameter m modeAST (mkAnn m name.val) (mkAnn m ty.val) (mkAnn m (some (expressionFromCSTSR ctx autoinv)))

partial def specFromCSTSR [Inhabited $ B3AST.Expression M] (ctx : FromCSTContextSR) : B3CST.Spec M → Strata.B3AST.Spec M
  | .spec_requires m expr => .specRequires m (expressionFromCSTSR ctx expr)
  | .spec_ensures m expr => .specEnsures m (expressionFromCSTSR ctx expr)

partial def fparamsToListSR : Ann (Array (B3CST.FParam M)) M → List (B3CST.FParam M)
  | ⟨_, arr⟩ => arr.toList

partial def declFromCSTSR [Inhabited $ B3AST.Expression M] [Inhabited $ B3AST.Statement M]  (ctx : FromCSTContextSR) : B3CST.Decl M → Strata.B3AST.Decl M
  | .type_decl m name =>
      .typeDecl m (mkAnn m name.val)
  | .tagger_decl m name forType =>
      .tagger m (mkAnn m name.val) (mkAnn m forType.val)
  | .function_decl m name params resultType tag body =>
      let paramsAST := fparamsToListSR params |>.map fParameterFromCSTSR
      let paramNames := paramsAST.map (fun p => match p with | .fParameter _ _ n _ => n.val)
      let ctx' := paramNames.foldl (fun acc n => acc.push n) ctx
      let tagAST := tag.val.map (fun t => match t with | .tag_some _ id => mkAnn m id.val)
      let bodyAST := mapAnn (fun opt => opt.map (fun b => match b with
        | .function_body_some bm whens expr =>
            let whensAST := whens.val.toList.map (fun w => match w with | .when_clause wm e => B3AST.When.when wm (expressionFromCSTSR ctx' e))
            B3AST.FunctionBody.functionBody bm (mkAnn bm whensAST.toArray) (expressionFromCSTSR ctx' expr))) body
      .function m (mkAnn m name.val) (mkAnn m paramsAST.toArray) (mkAnn m resultType.val) (mkAnn m tagAST) bodyAST
  | .axiom_decl m axiomBody =>
      match axiomBody with
      | .axiom _ expr =>
          .axiom m (mkAnn m #[]) (expressionFromCSTSR ctx expr)
      | .explain_axiom _ names expr =>
          let namesAST := names.val.toList.map (fun n => mkAnn m n.val)
          .axiom m (mkAnn m namesAST.toArray) (expressionFromCSTSR ctx expr)
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
      let paramsAST := params.val.toList.map (pParameterFromCSTSR ctx')
      let specsAST := specs.val.toList.map (specFromCSTSR ctx')
      let bodyAST := mapAnn (fun opt => opt.map (fun b => match b with | .proc_body_some _ s => Stmt.stmtFromCSTSR ctx' s)) body
      .procedure m (mkAnn m name.val) (mkAnn m paramsAST.toArray) (mkAnn m specsAST.toArray) bodyAST

end

def toAST [Inhabited $ B3AST.Expression M] [Inhabited $ B3AST.Statement M]  (d : B3CST.Decl M) : Strata.B3AST.Decl M :=
  declFromCSTSR FromCSTContextSR.empty d

def toCST [Inhabited $ B3CST.Expression M] [Inhabited $ B3CST.Statement M]  (d : Strata.B3AST.Decl M) : B3CST.Decl M :=
  declToCSTSR ToCSTContextSR.empty d

end Decl

namespace Program

partial def programFromCSTSR [Inhabited $ B3AST.Expression M] [Inhabited $ B3AST.Statement M] (ctx : FromCSTContextSR) : B3CST.Program M → Strata.B3AST.Program M
  | .program m decls => .program m (mkAnn m (decls.val.toList.map (Decl.declFromCSTSR ctx) |>.toArray))

partial def programToCSTSR [Inhabited $ B3CST.Expression M] [Inhabited $ B3CST.Statement M] (ctx : ToCSTContextSR) : Strata.B3AST.Program M → B3CST.Program M
  | .program m decls => .program m (mkAnn m (decls.val.toList.map (Decl.declToCSTSR ctx) |>.toArray))

def toAST [Inhabited $ B3AST.Expression M] [Inhabited $ B3AST.Statement M] (p : B3CST.Program M) : Strata.B3AST.Program M :=
  programFromCSTSR FromCSTContextSR.empty p

def toCST [Inhabited $ B3CST.Expression M] [Inhabited $ B3CST.Statement M] (p : Strata.B3AST.Program M) : B3CST.Program M :=
  programToCSTSR ToCSTContextSR.empty p

end Program

end AnnotationPreserving

end B3
