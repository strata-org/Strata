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
deriving DecidableEq

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

instance : Repr BinaryOp where
  reprPrec op _ := match op with
    | .iff => ".iff"
    | .implies => ".implies"
    | .impliedBy => ".impliedBy"
    | .and => ".and"
    | .or => ".or"
    | .eq => ".eq"
    | .neq => ".neq"
    | .lt => ".lt"
    | .le => ".le"
    | .ge => ".ge"
    | .gt => ".gt"
    | .add => ".add"
    | .sub => ".sub"
    | .mul => ".mul"
    | .div => ".div"
    | .mod => ".mod"

/--
B3 Unary operators
-/
inductive UnaryOp where
  | not  -- "!"
  | neg  -- "-"
deriving DecidableEq

def UnaryOp.toString : UnaryOp → String
  | .not => "!"
  | .neg => "-"

instance : ToString UnaryOp where
  toString := UnaryOp.toString

instance : ToFormat UnaryOp where
  format op := op.toString

instance : Repr UnaryOp where
  reprPrec op _ := match op with
    | .not => ".not"
    | .neg => ".neg"

/--
B3 Quantifier kind
-/
inductive QuantifierKind where
  | forall
  | exists
deriving DecidableEq

def QuantifierKind.toString : QuantifierKind → String
  | .forall => "forall"
  | .exists => "exists"

instance : ToString QuantifierKind where
  toString := QuantifierKind.toString

instance : ToFormat QuantifierKind where
  format q := q.toString

instance : Repr QuantifierKind where
  reprPrec q _ := match q with
    | .forall => ".forall"
    | .exists => ".exists"

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

---------------------------------------------------------------------
-- Repr Instances
---------------------------------------------------------------------

mutual
partial def Expression.repr [Repr P.Metadata] [Repr P.Identifier] : Expression P → String
  | .literal md val => s!".literal {reprArg md} {reprArg val}"
  | .id md name => s!".id {reprArg md} {reprArg name}"
  | .ite md cond thenE elseE => s!".ite {reprArg md} ({cond.repr}) ({thenE.repr}) ({elseE.repr})"
  | .binaryOp md op lhs rhs => s!".binaryOp {reprArg md} {reprArg op} ({lhs.repr}) ({rhs.repr})"
  | .unaryOp md op arg => s!".unaryOp {reprArg md} {reprArg op} ({arg.repr})"
  | .functionCall md fn args =>
      let argsRepr := "[" ++ String.intercalate ", " (args.map Expression.repr) ++ "]"
      s!".functionCall {reprArg md} {reprArg fn} {argsRepr}"
  | .labeledExpr md label expr => s!".labeledExpr {reprArg md} {reprArg label} ({expr.repr})"
  | .letExpr md var value body => s!".letExpr {reprArg md} {reprArg var} ({value.repr}) ({body.repr})"
  | .quantifierExpr md q var ty patterns body =>
      let patternsRepr := "[" ++ String.intercalate ", " (patterns.map Pattern.repr) ++ "]"
      ".quantifierExpr " ++ toString (reprArg md) ++ " " ++ toString (reprArg q) ++ " " ++ toString (reprArg var) ++ " " ++ toString (reprArg ty) ++ " " ++ patternsRepr ++ " (" ++ body.repr ++ ")"

partial def Pattern.repr [Repr P.Metadata] [Repr P.Identifier] : Pattern P → String
  | .pattern md exprs =>
      let exprsRepr := "[" ++ String.intercalate ", " (exprs.map Expression.repr) ++ "]"
      ".pattern " ++ toString (reprArg md) ++ " " ++ exprsRepr
end

instance [Repr P.Metadata] [Repr P.Identifier] : Repr (Expression P) where
  reprPrec e _ := Expression.repr e

instance [Repr P.Metadata] [Repr P.Identifier] : Repr (Pattern P) where
  reprPrec p _ := Pattern.repr p

/-- Default ExprParams with Unit metadata and B3IdentifierMetadata -/
abbrev defaultExprParams : ExprParams := {
  Metadata := Unit
  IDMeta := B3IdentifierMetadata
}

/-- B3 Expression with default parameters -/
abbrev B3Expression := Expression defaultExprParams

instance : Repr (B3Expression) where
  reprPrec e _ := Expression.repr e

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
