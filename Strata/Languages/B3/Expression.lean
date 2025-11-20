/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.Lambda
import Strata.Languages.B3.Identifiers

namespace B3
open Std (ToFormat Format format)

/--
Type parameters for B3 Expression.
-/
structure ExprParams : Type 1 where
  Metadata : Type
  IDMeta : Type

abbrev ExprParams.Identifier (P : ExprParams) : Type := Lambda.Identifier P.IDMeta

/--
B3 Binary operators
-/
inductive BinaryOp where
  | iff        -- "<==>"
  | implies    -- "==>"
  | impliedBy  -- "<=="
  | and        -- "&&"
  | or         -- "||"
  | eq         -- "=="
  | neq        -- "!="
  | lt         -- "<"
  | le         -- "<="
  | ge         -- ">="
  | gt         -- ">"
  | add        -- "+"
  | sub        -- "-"
  | mul        -- "*"
  | div        -- "div"
  | mod        -- "mod"
deriving Repr, DecidableEq

def BinaryOp.toString : BinaryOp → String
  | .iff => "<==>"
  | .implies => "==>"
  | .impliedBy => "<=="
  | .and => "&&"
  | .or => "||"
  | .eq => "=="
  | .neq => "!="
  | .lt => "<"
  | .le => "<="
  | .ge => ">="
  | .gt => ">"
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "div"
  | .mod => "mod"

/-- Precedence levels for binary operators (higher = tighter binding) -/
def BinaryOp.precedence : BinaryOp → Nat
  | .iff => 1
  | .implies => 2
  | .impliedBy => 2
  | .or => 3
  | .and => 4
  | .eq => 5
  | .neq => 5
  | .lt => 5
  | .le => 5
  | .ge => 5
  | .gt => 5
  | .add => 6
  | .sub => 6
  | .mul => 7
  | .div => 7
  | .mod => 7

instance : ToString BinaryOp where
  toString := BinaryOp.toString

instance : ToFormat BinaryOp where
  format op := op.toString

/--
B3 Unary operators
-/
inductive UnaryOp where
  | not  -- "!"
  | neg  -- "-"
deriving Repr, DecidableEq

def UnaryOp.toString : UnaryOp → String
  | .not => "!"
  | .neg => "-"

instance : ToString UnaryOp where
  toString := UnaryOp.toString

instance : ToFormat UnaryOp where
  format op := op.toString

/--
B3 Quantifier kind
-/
inductive QuantifierKind where
  | forall
  | exists
deriving Repr, DecidableEq

def QuantifierKind.toString : QuantifierKind → String
  | .forall => "forall"
  | .exists => "exists"

instance : ToString QuantifierKind where
  toString := QuantifierKind.toString

instance : ToFormat QuantifierKind where
  format q := q.toString

-- B3 Expression and Pattern - mutually inductive types.
mutual

/--
B3 Expression type - a proper tree structure parameterized by ExprParams.
-/
inductive Expression (P : ExprParams) : Type where
  | literal        (md : P.Metadata) (val : Lambda.LConst)
  | id             (md : P.Metadata) (name : P.Identifier)
  | ite            (md : P.Metadata) (cond : Expression P) (thenExpr : Expression P) (elseExpr : Expression P)
  | binaryOp       (md : P.Metadata) (op : BinaryOp) (lhs : Expression P) (rhs : Expression P)
  | unaryOp        (md : P.Metadata) (op : UnaryOp) (arg : Expression P)
  | functionCall   (md : P.Metadata) (fn : P.Identifier) (args : List (Expression P))
  | labeledExpr    (md : P.Metadata) (label : String) (expr : Expression P)
  | letExpr        (md : P.Metadata) (var : P.Identifier) (value : Expression P) (body : Expression P)
  | quantifierExpr (md : P.Metadata) (quantifier : QuantifierKind) (var : P.Identifier) (ty : String) (patterns : List (Pattern P)) (body : Expression P)

/--
B3 Pattern for quantifier triggers.
-/
inductive Pattern (P : ExprParams) : Type where
  | pattern (md : P.Metadata) (exprs : List (Expression P))

end

mutual
def Pattern.sizeOf : Pattern P → Nat
  | .pattern _ exprs => 1 + Expression.sizeOfList exprs

def Expression.sizeOf : Expression P → Nat
  | .literal _ _ => 1
  | .id _ _ => 1
  | .ite _ cond thenE elseE => 1 + cond.sizeOf + thenE.sizeOf + elseE.sizeOf
  | .binaryOp _ _ lhs rhs => 1 + lhs.sizeOf + rhs.sizeOf
  | .unaryOp _ _ arg => 1 + arg.sizeOf
  | .functionCall _ _ args => 1 + Expression.sizeOfList args
  | .labeledExpr _ _ e => 1 + e.sizeOf
  | .letExpr _ _ value body => 1 + value.sizeOf + body.sizeOf
  | .quantifierExpr _ _ _ _ patterns body => 1 + Pattern.sizeOfList patterns + body.sizeOf

def Expression.sizeOfList : List (Expression P) → Nat
  | [] => 0
  | e :: es => e.sizeOf + Expression.sizeOfList es

def Pattern.sizeOfList : List (Pattern P) → Nat
  | [] => 0
  | p :: ps => p.sizeOf + Pattern.sizeOfList ps

end

instance : SizeOf (Expression P) where
  sizeOf := Expression.sizeOf

instance : SizeOf (Pattern P) where
  sizeOf := Pattern.sizeOf

mutual
/-- Format with optional parentheses based on parent precedence -/
partial def Expression.formatWithPrec [ToFormat P.Metadata] [ToFormat P.Identifier] (parentPrec : Nat) : Expression P → Format
  | .literal _ val => f!"{val}"
  | .id _ name => ToFormat.format name
  | .ite _ cond thenE elseE => f!"if {Format.nest 2 (cond.formatWithPrec 0)} then {Format.nest 2 (thenE.formatWithPrec 0)} else {Format.nest 2 (elseE.formatWithPrec 0)}"
  | .binaryOp _ op lhs rhs =>
    let prec := op.precedence
    let lhsStr := Format.nest 2 (lhs.formatWithPrec prec)
    let rhsStr := Format.nest 2 (rhs.formatWithPrec (prec + 1))
    let inner := f!"{lhsStr} {op} {rhsStr}"
    if parentPrec > prec then f!"({inner})" else inner
  | .unaryOp _ op arg =>
    let argStr := Format.nest 2 (arg.formatWithPrec 100)
    f!"{op}{argStr}"
  | .functionCall _ fn args =>
    let argStrs := Format.joinSep (args.map (Expression.formatWithPrec 0)) ", "
    f!"{ToFormat.format fn}({argStrs})"
  | .labeledExpr _ label expr => f!"{label}: {expr.formatWithPrec 0}"
  | .letExpr _ var value body =>
    f!"val {ToFormat.format var} := {Format.nest 2 (value.formatWithPrec 0)}{Format.line}{body.formatWithPrec 0}"
  | .quantifierExpr _ q var ty patterns body =>
    let patternsFormatted := patterns.foldl (fun acc p => f!"{acc} {Pattern.format p},") Format.nil
    f!"{q} {ToFormat.format var} : {ty}{Format.nest 2 $ patternsFormatted} {Format.nest 2 $ body.formatWithPrec 0}"

partial def Expression.format [ToFormat P.Metadata] [ToFormat P.Identifier] : Expression P → Format :=
  Expression.formatWithPrec 0

partial def Pattern.format [ToFormat P.Metadata] [ToFormat P.Identifier] : Pattern P → Format
  | .pattern _ exprs =>
    let exprStrs := Format.joinSep (exprs.map Expression.format) " "
    f!"pattern {exprStrs}"
end

instance [ToFormat P.Metadata] [ToFormat P.Identifier] : ToFormat (Expression P) where
  format := Expression.format

instance [ToFormat P.Metadata] [ToFormat P.Identifier] : ToFormat (Pattern P) where
  format := Pattern.format

/-- Default ExprParams with Unit metadata and B3IdentifierMetadata -/
def defaultExprParams : ExprParams := {
  Metadata := Unit
  IDMeta := B3IdentifierMetadata
}

/-- B3 Expression with default parameters -/
abbrev B3Expression := Expression defaultExprParams

/-- B3 Pattern with default parameters -/
abbrev B3Pattern := Pattern defaultExprParams

-- ToFormat instances for default parameters
instance : Std.ToFormat Unit where
  format _ := ""

instance : Std.ToFormat B3IdentifierMetadata where
  format _ := ""

instance : Std.ToFormat (Lambda.Identifier B3IdentifierMetadata) where
  format id := id.name

instance : Std.ToFormat defaultExprParams.Metadata := inferInstanceAs (Std.ToFormat Unit)
instance : Std.ToFormat defaultExprParams.Identifier := inferInstanceAs (Std.ToFormat (Lambda.Identifier B3IdentifierMetadata))

end B3
