/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel

/-! # Laurel StmtExpr Builders

Concise helpers for constructing `StmtExprMd` values, reducing boilerplate
in the Python-to-Laurel translator and other Laurel code generators.

Each builder takes optional `source` and `md` parameters so callers can
attach source locations when available.

## Type-safe builders (`Typed` namespace)

The `Typed` sub-namespace provides phantom-typed wrappers (`TypedExpr tp`)
that enforce type correctness at Lean compile time. These should be
preferred for new code; the untyped builders remain for backward
compatibility and for statement-level constructs that don't have a
meaningful expression type.
-/

namespace Strata.Laurel

public section

/-- Default metadata with unknown file range. -/
def defaultMd : MetaData := .empty

/-- Build a StmtExprMd from a StmtExpr with optional source and metadata. -/
@[inline] def mkNode (e : StmtExpr) (source : Option FileRange := none)
    (md : MetaData := defaultMd) : StmtExprMd :=
  { val := e, source := source, md := md }

/-- A Laurel `StmtExprMd` tagged with its `HighType`. -/
structure TypedExpr (tp : HighType) where
  expr : StmtExprMd

/-- Allow typed expressions to be used wherever StmtExprMd is expected. -/
instance : CoeOut (TypedExpr tp) StmtExprMd where
  coe e := e.expr

/-! ## Untyped builders (return StmtExprMd) -/

def litInt (n : Int) (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.LiteralInt n) source md
def litStr (s : String) (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.LiteralString s) source md
def litBool (b : Bool) (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.LiteralBool b) source md
def ident (name : String) (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.Identifier name) source md
def fieldSelect (obj : StmtExprMd) (field : String) (source : Option FileRange := none)
    (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.FieldSelect obj field) source md
def call (name : String) (args : List StmtExprMd) (source : Option FileRange := none)
    (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.StaticCall name args) source md
def primOp (op : Operation) (args : List StmtExprMd) (source : Option FileRange := none)
    (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.PrimitiveOp op args) source md
def localVar (name : String) (ty : HighTypeMd) (init : Option StmtExprMd := none)
    (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.LocalVariable name ty init) source md
def assign (targets : List StmtExprMd) (value : StmtExprMd)
    (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.Assign targets value) source md
def assert_ (cond : TypedExpr .TBool) (summary : Option String := none)
    (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.Assert { condition := cond.expr, summary }) source md
def assume_ (cond : TypedExpr .TBool) (source : Option FileRange := none)
    (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.Assume cond.expr) source md
def block (stmts : List StmtExprMd) (label : Option String := none)
    (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.Block stmts label) source md
def ifThenElse (cond : TypedExpr .TBool) (thenBranch : StmtExprMd)
    (elseBranch : Option StmtExprMd := none) (source : Option FileRange := none)
    (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.IfThenElse cond.expr thenBranch elseBranch) source md
def exit_ (label : String) (source : Option FileRange := none)
    (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.Exit label) source md
def return_ (value : Option StmtExprMd := none) (source : Option FileRange := none)
    (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.Return value) source md
def new_ (className : Identifier) (source : Option FileRange := none)
    (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.New className) source md
def hole (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode .Hole source md
def nondetHole (ty : Option HighTypeMd := none) (source : Option FileRange := none)
    (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.Hole false ty) source md
def while_ (cond : StmtExprMd) (invs : List StmtExprMd := [])
    (dec : Option StmtExprMd := none) (body : StmtExprMd)
    (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.While cond invs dec body) source md

/-! ## Type-safe builders -/

namespace Typed

/-- Typed literal int. -/
def litInt (n : Int) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr .TInt :=
  ⟨mkNode (.LiteralInt n) source md⟩
/-- Typed literal string. -/
def litStr (s : String) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr .TString :=
  ⟨mkNode (.LiteralString s) source md⟩
/-- Typed literal bool. -/
def litBool (b : Bool) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr .TBool :=
  ⟨mkNode (.LiteralBool b) source md⟩
/-- Typed identifier. -/
def ident (name : String) (tp : HighType) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr tp :=
  ⟨mkNode (.Identifier name) source md⟩
/-- Typed static call. -/
def call (name : String) (args : List StmtExprMd) (tp : HighType)
    (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr tp :=
  ⟨mkNode (.StaticCall name args) source md⟩
/-- Boolean negation. -/
def not (x : TypedExpr .TBool) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .Not [x.expr]) source md⟩
/-- Boolean and. -/
def and (x y : TypedExpr .TBool) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .And [x.expr, y.expr]) source md⟩
/-- Boolean or. -/
def or (x y : TypedExpr .TBool) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .Or [x.expr, y.expr]) source md⟩
/-- Boolean implies. -/
def implies (x y : TypedExpr .TBool) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .Implies [x.expr, y.expr]) source md⟩
/-- Equality. -/
def eq (x y : TypedExpr tp) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .Eq [x.expr, y.expr]) source md⟩
/-- Less than. -/
def lt (x y : StmtExprMd) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .Lt [x, y]) source md⟩
/-- Less than or equal. -/
def leq (x y : StmtExprMd) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .Leq [x, y]) source md⟩
/-- Greater than or equal. -/
def geq (x y : StmtExprMd) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .Geq [x, y]) source md⟩
/-- Greater than. -/
def gt (x y : StmtExprMd) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .Gt [x, y]) source md⟩
/-- Integer addition. -/
def add (x y : StmtExprMd) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr .TInt :=
  ⟨mkNode (.PrimitiveOp .Add [x, y]) source md⟩
/-- Integer subtraction. -/
def sub (x y : StmtExprMd) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr .TInt :=
  ⟨mkNode (.PrimitiveOp .Sub [x, y]) source md⟩
/-- String concatenation. -/
def strConcat (x y : StmtExprMd) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr .TString :=
  ⟨mkNode (.PrimitiveOp .StrConcat [x, y]) source md⟩
/-- If-then-else (expression, returns typed value). -/
def ite (cond : TypedExpr .TBool) (t e : TypedExpr tp) (source : Option FileRange := none) (md : MetaData := defaultMd) : TypedExpr tp :=
  ⟨mkNode (.IfThenElse cond.expr t.expr (some e.expr)) source md⟩

end Typed

end -- public section
end Strata.Laurel
