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

## Type-safe conditions (`TypedExpr` and `Typed` namespace)

The `TypedExpr tp` phantom-typed wrapper lets `assert_`, `assume_`, and
`ifThenElse` enforce — at Lean compile time — that their condition has
type `TBool`. The `CoeOut` instance below lets a `TypedExpr tp` flow
into any context expecting an untyped `StmtExprMd` (e.g. `while_`).

Only the typed factory used by current consumers (`Typed.call`) lives
here; further typed combinators should be added when their first caller
arrives.
-/

namespace Strata.Laurel

public section


/-- Build a StmtExprMd from a StmtExpr with optional source. -/
@[inline] def mkNode (e : StmtExpr) (source : Option FileRange := none)
    : StmtExprMd :=
  { val := e, source := source }

/-- Build a VariableMd from a Variable with optional source. -/
@[inline] def mkVarNode (v : Variable) (source : Option FileRange := none)
    : VariableMd :=
  { val := v, source := source }

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
def litDecimal (d : Decimal) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.LiteralDecimal d) source
def ident (name : Identifier) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.Var (.Local name)) source
def fieldSelect (obj : StmtExprMd) (field : Identifier) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.Var (.Field obj field)) source
def call (name : String) (args : List StmtExprMd) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.StaticCall name args) source
def primOp (op : Operation) (args : List StmtExprMd) (source : Option FileRange := none) : StmtExprMd :=
  mkNode (.PrimitiveOp op args) source
def localVar (name : Identifier) (ty : HighTypeMd) (init : Option StmtExprMd := none)
    (source : Option FileRange := none) : StmtExprMd :=
  match init with
  | some i => mkNode (.Assign [mkVarNode (.Declare ⟨name, ty⟩)] i) source
  | none => mkNode (.Var (.Declare ⟨name, ty⟩)) source
def assign (targets : List VariableMd) (value : StmtExprMd)
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

/-- Helper to create a VariableMd for a local variable reference. -/
def freeVar (name : Identifier) (source : Option FileRange := none) : VariableMd :=
  mkVarNode (.Local name) source

/-- Helper to create a VariableMd for a field access. -/
def fieldVar (obj : StmtExprMd) (field : Identifier) (source : Option FileRange := none) : VariableMd :=
  mkVarNode (.Field obj field) source

/-! ## Typed factories

Only the typed factory consumed by current call sites lives here.
Add more entries when their first caller arrives. -/

namespace Typed

/-- Typed static call. -/
def call (name : String) (args : List StmtExprMd) (tp : HighType)
    (source : Option FileRange := none) : TypedExpr tp :=
  ⟨mkNode (.StaticCall name args) source⟩

end Typed

end -- public section
end Strata.Laurel
