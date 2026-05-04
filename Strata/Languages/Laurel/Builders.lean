/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel

/-! # Laurel StmtExpr Builders

Concise helpers for constructing `StmtExprMd` values, reducing boilerplate
in the Python-to-Laurel translator and other Laurel code generators.

Each builder takes an optional `source` parameter so callers can
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


/-- Build a StmtExprMd from a StmtExpr with optional source. -/
@[inline] def mkNode (e : StmtExpr) (source : Option FileRange := none)
    : StmtExprMd :=
  { val := e, source := source }

/-- A Laurel `StmtExprMd` tagged with its `HighType`. -/
structure TypedExpr (tp : HighType) where
  expr : StmtExprMd

/-- Allow typed expressions to be used wherever StmtExprMd is expected. -/
instance : CoeOut (TypedExpr tp) StmtExprMd where
  coe e := e.expr

/-! ## Untyped builders (return StmtExprMd) -/

def litInt (n : Int) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.LiteralInt n) source
def litStr (s : String) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.LiteralString s) source
def litBool (b : Bool) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.LiteralBool b) source
def ident (name : String) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.Identifier name) source
def fieldSelect (obj : StmtExprMd) (field : String) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.FieldSelect obj field) source
def call (name : String) (args : List StmtExprMd) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.StaticCall name args) source
def primOp (op : Operation) (args : List StmtExprMd) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.PrimitiveOp op args) source
def localVar (name : String) (ty : HighTypeMd) (init : Option StmtExprMd := none)
    (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.LocalVariable name ty init) source
def assign (targets : List StmtExprMd) (value : StmtExprMd)
    (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.Assign targets value) source
def assert_ (cond : TypedExpr .TBool) (summary : Option String := none)
    (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.Assert { condition := cond.expr, summary }) source
def assume_ (cond : TypedExpr .TBool) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.Assume cond.expr) source
def block (stmts : List StmtExprMd) (label : Option String := none)
    (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.Block stmts label) source
def ifThenElse (cond : TypedExpr .TBool) (thenBranch : StmtExprMd)
    (elseBranch : Option StmtExprMd := none) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.IfThenElse cond.expr thenBranch elseBranch) source
def exit_ (label : String) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.Exit label) source
def return_ (value : Option StmtExprMd := none) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.Return value) source
def new_ (className : Identifier) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.New className) source
def hole (source : Option FileRange := none) : StmtExprMd :=
  mkNode .Hole source
def nondetHole (ty : Option HighTypeMd := none) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.Hole false ty) source
def while_ (cond : StmtExprMd) (invs : List StmtExprMd := [])
    (dec : Option StmtExprMd := none) (body : StmtExprMd)
    (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.While cond invs dec body) source

/-! ## Type-safe builders -/

namespace Typed

/-- Typed literal int. -/
def litInt (n : Int) (source : Option FileRange := none) : TypedExpr .TInt :=
  ⟨mkNode (.LiteralInt n) source⟩
/-- Typed literal string. -/
def litStr (s : String) (source : Option FileRange := none) : TypedExpr .TString :=
  ⟨mkNode (.LiteralString s) source⟩
/-- Typed literal bool. -/
def litBool (b : Bool) (source : Option FileRange := none) : TypedExpr .TBool :=
  ⟨mkNode (.LiteralBool b) source⟩
/-- Typed identifier. -/
def ident (name : String) (tp : HighType) (source : Option FileRange := none) : TypedExpr tp :=
  ⟨mkNode (.Identifier name) source⟩
/-- Typed static call. -/
def call (name : String) (args : List StmtExprMd) (tp : HighType)
    (source : Option FileRange := none) : TypedExpr tp :=
  ⟨mkNode (.StaticCall name args) source⟩
/-- Boolean negation. -/
def not (x : TypedExpr .TBool) (source : Option FileRange := none) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .Not [x.expr]) source⟩
/-- Boolean and. -/
def and (x y : TypedExpr .TBool) (source : Option FileRange := none) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .And [x.expr, y.expr]) source⟩
/-- Boolean or. -/
def or (x y : TypedExpr .TBool) (source : Option FileRange := none) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .Or [x.expr, y.expr]) source⟩
/-- Boolean implies. -/
def implies (x y : TypedExpr .TBool) (source : Option FileRange := none) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .Implies [x.expr, y.expr]) source⟩
/-- Equality. -/
def eq (x y : TypedExpr tp) (source : Option FileRange := none) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .Eq [x.expr, y.expr]) source⟩
/-- Less than. -/
def lt (x y : StmtExprMd) (source : Option FileRange := none) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .Lt [x, y]) source⟩
/-- Less than or equal. -/
def leq (x y : StmtExprMd) (source : Option FileRange := none) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .Leq [x, y]) source⟩
/-- Greater than or equal. -/
def geq (x y : StmtExprMd) (source : Option FileRange := none) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .Geq [x, y]) source⟩
/-- Greater than. -/
def gt (x y : StmtExprMd) (source : Option FileRange := none) : TypedExpr .TBool :=
  ⟨mkNode (.PrimitiveOp .Gt [x, y]) source⟩
/-- Integer addition. -/
def add (x y : StmtExprMd) (source : Option FileRange := none) : TypedExpr .TInt :=
  ⟨mkNode (.PrimitiveOp .Add [x, y]) source⟩
/-- Integer subtraction. -/
def sub (x y : StmtExprMd) (source : Option FileRange := none) : TypedExpr .TInt :=
  ⟨mkNode (.PrimitiveOp .Sub [x, y]) source⟩
/-- String concatenation. -/
def strConcat (x y : StmtExprMd) (source : Option FileRange := none) : TypedExpr .TString :=
  ⟨mkNode (.PrimitiveOp .StrConcat [x, y]) source⟩
/-- If-then-else (expression, returns typed value). -/
def ite (cond : TypedExpr .TBool) (t e : TypedExpr tp) (source : Option FileRange := none) : TypedExpr tp :=
  ⟨mkNode (.IfThenElse cond.expr t.expr (some e.expr)) source⟩

end Typed

end -- public section
end Strata.Laurel
