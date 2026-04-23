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
-/

namespace Strata.Laurel

public section

/-- Default metadata with unknown file range. -/
def defaultMd : MetaData :=
  #[⟨Imperative.MetaData.fileRange, .fileRange FileRange.unknown⟩]

/-- Build a StmtExprMd from a StmtExpr with optional source and metadata. -/
@[inline] def mkNode (e : StmtExpr) (source : Option FileRange := none)
    (md : MetaData := defaultMd) : StmtExprMd :=
  { val := e, source := source, md := md }

/-! ## Literals -/

def litInt (n : Int) (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.LiteralInt n) source md
def litStr (s : String) (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.LiteralString s) source md
def litBool (b : Bool) (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.LiteralBool b) source md

/-! ## Identifiers and field access -/

def ident (name : String) (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.Identifier name) source md
def fieldSelect (obj : StmtExprMd) (field : String) (source : Option FileRange := none)
    (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.FieldSelect obj field) source md

/-! ## Calls -/

def call (name : String) (args : List StmtExprMd) (source : Option FileRange := none)
    (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.StaticCall name args) source md

/-! ## Statements -/

def localVar (name : String) (ty : HighTypeMd) (init : Option StmtExprMd := none)
    (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.LocalVariable name ty init) source md

def assign (targets : List StmtExprMd) (value : StmtExprMd)
    (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.Assign targets value) source md

def assert_ (cond : StmtExprMd) (summary : Option String := none)
    (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.Assert { condition := cond, summary }) source md

def assume_ (cond : StmtExprMd) (source : Option FileRange := none)
    (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.Assume cond) source md

def block (stmts : List StmtExprMd) (label : Option String := none)
    (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.Block stmts label) source md

def ifThenElse (cond thenBranch : StmtExprMd) (elseBranch : Option StmtExprMd := none)
    (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.IfThenElse cond thenBranch elseBranch) source md

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

/-! ## Primitive operations -/

def primOp (op : Operation) (args : List StmtExprMd) (source : Option FileRange := none)
    (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.PrimitiveOp op args) source md

/-- While loop. -/
def while_ (cond : StmtExprMd) (invs : List StmtExprMd := [])
    (dec : Option StmtExprMd := none) (body : StmtExprMd)
    (source : Option FileRange := none) (md : MetaData := defaultMd) : StmtExprMd :=
  mkNode (.While cond invs dec body) source md

end -- public section
end Strata.Laurel
