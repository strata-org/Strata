/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.Parse
import Strata.Languages.B3.DDMTransform.Translate
import Strata.Languages.B3.DDMConversion

namespace B3

open Std (Format)
open Strata
open Strata.B3CST

/--
info: inductive Strata.B3CST.Expression : Type → Type
number of parameters: 1
constructors:
Strata.B3CST.Expression.not : {α : Type} → α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.natLit : {α : Type} → α → Ann Nat α → B3CST.Expression α
Strata.B3CST.Expression.strLit : {α : Type} → α → Ann String α → B3CST.Expression α
Strata.B3CST.Expression.btrue : {α : Type} → α → B3CST.Expression α
Strata.B3CST.Expression.bfalse : {α : Type} → α → B3CST.Expression α
Strata.B3CST.Expression.id : {α : Type} → α → Ann String α → B3CST.Expression α
Strata.B3CST.Expression.letExpr : {α : Type} →
  α → Ann String α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.labeledExpr : {α : Type} → α → Ann String α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.ite : {α : Type} →
  α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.iff : {α : Type} → α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.implies : {α : Type} → α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.impliedBy : {α : Type} → α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.and : {α : Type} → α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.or : {α : Type} → α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.equal : {α : Type} → α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.not_equal : {α : Type} → α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.le : {α : Type} → α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.lt : {α : Type} → α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.ge : {α : Type} → α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.gt : {α : Type} → α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.neg : {α : Type} → α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.add : {α : Type} → α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.sub : {α : Type} → α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.mul : {α : Type} → α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.div : {α : Type} → α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.mod : {α : Type} → α → B3CST.Expression α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.paren : {α : Type} → α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.functionCall : {α : Type} →
  α → Ann String α → Ann (Array (B3CST.Expression α)) α → B3CST.Expression α
Strata.B3CST.Expression.forall_expr_no_patterns : {α : Type} →
  α → Ann String α → Ann String α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.forall_expr : {α : Type} →
  α → Ann String α → Ann String α → Patterns α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.exists_expr_no_patterns : {α : Type} →
  α → Ann String α → Ann String α → B3CST.Expression α → B3CST.Expression α
Strata.B3CST.Expression.exists_expr : {α : Type} →
  α → Ann String α → Ann String α → Patterns α → B3CST.Expression α → B3CST.Expression α
-/
#guard_msgs in
#print B3CST.Expression

/--
info: inductive Strata.B3CST.Pattern : Type → Type
number of parameters: 1
constructors:
Strata.B3CST.Pattern.pattern : {α : Type} → α → B3CST.Expression α → B3CST.Pattern α
-/
#guard_msgs in
#print B3CST.Pattern

/--
info: inductive Strata.B3CST.Patterns : Type → Type
number of parameters: 1
constructors:
Strata.B3CST.Patterns.patterns_cons : {α : Type} → α → B3CST.Pattern α → Patterns α → Patterns α
Strata.B3CST.Patterns.patterns_single : {α : Type} → α → B3CST.Pattern α → Patterns α
-/
#guard_msgs in
#print B3CST.Patterns

-- Helpers to convert Unit annotations to SourceRange
mutual
  partial def exprFUnitToSourceRange : ExprF Unit → ExprF SourceRange
    | .bvar () idx => .bvar default idx
    | .fvar () idx => .fvar default idx
    | .fn () f => .fn default f
    | .app () f a => .app default (exprFUnitToSourceRange f) (argFUnitToSourceRange a)

  partial def argFUnitToSourceRange : ArgF Unit → ArgF SourceRange
    | .op op => .op { op with ann := default, args := op.args.map argFUnitToSourceRange }
    | .expr e => .expr (exprFUnitToSourceRange e)
    | .type t => .type (typeExprFUnitToSourceRange t)
    | .cat c => .cat (syntaxCatFUnitToSourceRange c)
    | .ident () x => .ident default x
    | .num () x => .num default x
    | .decimal () v => .decimal default v
    | .strlit () s => .strlit default s
    | .bytes () v => .bytes default v
    | .bool () b => .bool default b
    | .option () ma => .option default (ma.map argFUnitToSourceRange)
    | .seq () entries => .seq default (entries.map argFUnitToSourceRange)
    | .commaSepList () entries => .commaSepList default (entries.map argFUnitToSourceRange)

  partial def typeExprFUnitToSourceRange : TypeExprF Unit → TypeExprF SourceRange
    | .ident () tp a => .ident default tp (a.map typeExprFUnitToSourceRange)
    | .bvar () idx => .bvar default idx
    | .fvar () idx a => .fvar default idx (a.map typeExprFUnitToSourceRange)
    | .arrow () a r => .arrow default (typeExprFUnitToSourceRange a) (typeExprFUnitToSourceRange r)

  partial def syntaxCatFUnitToSourceRange : SyntaxCatF Unit → SyntaxCatF SourceRange
    | ⟨(), name, args⟩ => ⟨default, name, args.map syntaxCatFUnitToSourceRange⟩
end

-- Create a minimal B3 program to get the dialect context
def b3Program : Program := #strata program B3CST; #end

-- Helper to strip SourceRange annotations and replace with Unit
mutual
  partial def stripAnnotations : B3CST.Expression SourceRange → B3CST.Expression Unit
    | .natLit _ n => .natLit () ⟨(), n.val⟩
    | .strLit _ s => .strLit () ⟨(), s.val⟩
    | .btrue _ => .btrue ()
    | .bfalse _ => .bfalse ()
    | .id _ name => .id () ⟨(), name.val⟩
    | .not _ arg => .not () (stripAnnotations arg)
    | .neg _ arg => .neg () (stripAnnotations arg)
    | .iff _ lhs rhs => .iff () (stripAnnotations lhs) (stripAnnotations rhs)
    | .implies _ lhs rhs => .implies () (stripAnnotations lhs) (stripAnnotations rhs)
    | .impliedBy _ lhs rhs => .impliedBy () (stripAnnotations lhs) (stripAnnotations rhs)
    | .and _ lhs rhs => .and () (stripAnnotations lhs) (stripAnnotations rhs)
    | .or _ lhs rhs => .or () (stripAnnotations lhs) (stripAnnotations rhs)
    | .equal _ lhs rhs => .equal () (stripAnnotations lhs) (stripAnnotations rhs)
    | .not_equal _ lhs rhs => .not_equal () (stripAnnotations lhs) (stripAnnotations rhs)
    | .lt _ lhs rhs => .lt () (stripAnnotations lhs) (stripAnnotations rhs)
    | .le _ lhs rhs => .le () (stripAnnotations lhs) (stripAnnotations rhs)
    | .ge _ lhs rhs => .ge () (stripAnnotations lhs) (stripAnnotations rhs)
    | .gt _ lhs rhs => .gt () (stripAnnotations lhs) (stripAnnotations rhs)
    | .add _ lhs rhs => .add () (stripAnnotations lhs) (stripAnnotations rhs)
    | .sub _ lhs rhs => .sub () (stripAnnotations lhs) (stripAnnotations rhs)
    | .mul _ lhs rhs => .mul () (stripAnnotations lhs) (stripAnnotations rhs)
    | .div _ lhs rhs => .div () (stripAnnotations lhs) (stripAnnotations rhs)
    | .mod _ lhs rhs => .mod () (stripAnnotations lhs) (stripAnnotations rhs)
    | .functionCall _ fn args => .functionCall () ⟨(), fn.val⟩ ⟨(), args.val.map stripAnnotations⟩
    | .labeledExpr _ label expr => .labeledExpr () ⟨(), label.val⟩ (stripAnnotations expr)
    | .letExpr _ var value body => .letExpr () ⟨(), var.val⟩ (stripAnnotations value) (stripAnnotations body)
    | .ite _ cond thenExpr elseExpr => .ite () (stripAnnotations cond) (stripAnnotations thenExpr) (stripAnnotations elseExpr)
    | .forall_expr_no_patterns _ var ty body => .forall_expr_no_patterns () ⟨(), var.val⟩ ⟨(), ty.val⟩ (stripAnnotations body)
    | .forall_expr _ var ty patterns body => .forall_expr () ⟨(), var.val⟩ ⟨(), ty.val⟩ (stripPatternsAnnotations patterns) (stripAnnotations body)
    | .exists_expr_no_patterns _ var ty body => .exists_expr_no_patterns () ⟨(), var.val⟩ ⟨(), ty.val⟩ (stripAnnotations body)
    | .exists_expr _ var ty patterns body => .exists_expr () ⟨(), var.val⟩ ⟨(), ty.val⟩ (stripPatternsAnnotations patterns) (stripAnnotations body)
    | .paren _ expr => .paren () (stripAnnotations expr)

  partial def stripPatternAnnotations : B3CST.Pattern SourceRange → B3CST.Pattern Unit
    | .pattern _ expr => .pattern () (stripAnnotations expr)

  partial def stripPatternsAnnotations : B3CST.Patterns SourceRange → B3CST.Patterns Unit
    | .patterns_single _ p => .patterns_single () (stripPatternAnnotations p)
    | .patterns_cons _ p ps => .patterns_cons () (stripPatternAnnotations p) (stripPatternsAnnotations ps)
end

-- Helper to convert OperationF Unit to OperationF SourceRange
def operationFUnitToSourceRange (op : OperationF Unit) : OperationF SourceRange :=
  { op with ann := default, args := op.args.map argFUnitToSourceRange }

end B3
