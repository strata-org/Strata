/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.DefinitionAST
import Strata.Languages.B3.DDMConversion

namespace B3

open Std (Format)
open Strata
open Strata.B3CST

/--
info: inductive Strata.B3CST.Expression : Type → Type
number of parameters: 1
constructors:
Strata.B3CST.Expression.not : {α : Type} → α → Expression α → Expression α
Strata.B3CST.Expression.natLit : {α : Type} → α → Ann Nat α → Expression α
Strata.B3CST.Expression.strLit : {α : Type} → α → Ann String α → Expression α
Strata.B3CST.Expression.btrue : {α : Type} → α → Expression α
Strata.B3CST.Expression.bfalse : {α : Type} → α → Expression α
Strata.B3CST.Expression.old_id : {α : Type} → α → Ann String α → Expression α
Strata.B3CST.Expression.id : {α : Type} → α → Ann String α → Expression α
Strata.B3CST.Expression.letExpr : {α : Type} → α → Ann String α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.labeledExpr : {α : Type} → α → Ann String α → Expression α → Expression α
Strata.B3CST.Expression.ite : {α : Type} → α → Expression α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.iff : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.implies : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.impliedBy : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.and : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.or : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.equal : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.not_equal : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.le : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.lt : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.ge : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.gt : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.neg : {α : Type} → α → Expression α → Expression α
Strata.B3CST.Expression.add : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.sub : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.mul : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.div : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.mod : {α : Type} → α → Expression α → Expression α → Expression α
Strata.B3CST.Expression.paren : {α : Type} → α → Expression α → Expression α
Strata.B3CST.Expression.functionCall : {α : Type} → α → Ann String α → Ann (Array (Expression α)) α → Expression α
Strata.B3CST.Expression.forall_expr_no_patterns : {α : Type} →
  α → Ann String α → Ann String α → Expression α → Expression α
Strata.B3CST.Expression.forall_expr : {α : Type} →
  α → Ann String α → Ann String α → Patterns α → Expression α → Expression α
Strata.B3CST.Expression.exists_expr_no_patterns : {α : Type} →
  α → Ann String α → Ann String α → Expression α → Expression α
Strata.B3CST.Expression.exists_expr : {α : Type} →
  α → Ann String α → Ann String α → Patterns α → Expression α → Expression α
-/
#guard_msgs in
#print B3CST.Expression

/--
info: inductive Strata.B3AST.Expression : Type → Type
number of parameters: 1
constructors:
Strata.B3AST.Expression.literal : {α : Type} → α → B3AST.Literal α → B3AST.Expression α
Strata.B3AST.Expression.id : {α : Type} → α → Ann Nat α → B3AST.Expression α
Strata.B3AST.Expression.ite : {α : Type} →
  α → B3AST.Expression α → B3AST.Expression α → B3AST.Expression α → B3AST.Expression α
Strata.B3AST.Expression.binaryOp : {α : Type} →
  α → B3AST.BinaryOp α → B3AST.Expression α → B3AST.Expression α → B3AST.Expression α
Strata.B3AST.Expression.unaryOp : {α : Type} → α → B3AST.UnaryOp α → B3AST.Expression α → B3AST.Expression α
Strata.B3AST.Expression.functionCall : {α : Type} →
  α → Ann String α → Ann (Array (B3AST.Expression α)) α → B3AST.Expression α
Strata.B3AST.Expression.labeledExpr : {α : Type} → α → Ann String α → B3AST.Expression α → B3AST.Expression α
Strata.B3AST.Expression.letExpr : {α : Type} →
  α → Ann String α → B3AST.Expression α → B3AST.Expression α → B3AST.Expression α
Strata.B3AST.Expression.quantifierExpr : {α : Type} →
  α →
    B3AST.QuantifierKind α →
      Ann String α → Ann String α → Ann (Array (B3AST.Pattern α)) α → B3AST.Expression α → B3AST.Expression α
-/
#guard_msgs in
#print B3AST.Expression

/--
info: inductive Strata.B3CST.Pattern : Type → Type
number of parameters: 1
constructors:
Strata.B3CST.Pattern.pattern : {α : Type} → α → Expression α → Pattern α
-/
#guard_msgs in
#print B3CST.Pattern

/--
info: inductive Strata.B3CST.Patterns : Type → Type
number of parameters: 1
constructors:
Strata.B3CST.Patterns.patterns_cons : {α : Type} → α → Pattern α → Patterns α → Patterns α
Strata.B3CST.Patterns.patterns_single : {α : Type} → α → Pattern α → Patterns α
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

-- Helper to convert OperationF Unit to OperationF SourceRange
def operationFUnitToSourceRange (op : OperationF Unit) : OperationF SourceRange :=
  { op with ann := default, args := op.args.map argFUnitToSourceRange }

end B3
