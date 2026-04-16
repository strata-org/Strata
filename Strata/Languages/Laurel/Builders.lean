/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel

/-! # Laurel StmtExpr Builders

Concise helpers for constructing `StmtExprMd` values, reducing boilerplate
in the Python-to-Laurel translator and other Laurel code generators.
-/

namespace Strata.Laurel

public section

private def defaultMd : MetaData :=
  #[⟨Imperative.MetaData.fileRange, .fileRange FileRange.unknown⟩]

/-! ## Core constructors -/

/-- Create a `StmtExprMd` with default metadata (unknown file range). -/
def withDefaultMd (e : StmtExpr) : StmtExprMd := ⟨e, defaultMd⟩


/-! ## Literals -/

def litInt (n : Int) : StmtExprMd := withDefaultMd (.LiteralInt n)
def litIntMd (n : Int) (md : MetaData) : StmtExprMd := ⟨.LiteralInt n, md⟩
def litStr (s : String) : StmtExprMd := withDefaultMd (.LiteralString s)
def litStrMd (s : String) (md : MetaData) : StmtExprMd := ⟨.LiteralString s, md⟩
def litBool (b : Bool) : StmtExprMd := withDefaultMd (.LiteralBool b)
def litBoolMd (b : Bool) (md : MetaData) : StmtExprMd := ⟨.LiteralBool b, md⟩

/-! ## Identifiers and field access -/

def ident (name : String) : StmtExprMd := withDefaultMd (.Identifier name)
def identMd (name : String) (md : MetaData) : StmtExprMd := ⟨.Identifier name, md⟩
def fieldSelect (obj : StmtExprMd) (field : String) : StmtExprMd :=
  withDefaultMd (.FieldSelect obj field)
def fieldSelectMd (obj : StmtExprMd) (field : String) (md : MetaData) : StmtExprMd :=
  ⟨.FieldSelect obj field, md⟩

/-! ## Calls -/

/-- Static function call: `name(args...)` -/
def call (name : String) (args : List StmtExprMd) : StmtExprMd :=
  withDefaultMd (.StaticCall name args)

/-- Static function call with metadata. -/
def callMd (name : String) (args : List StmtExprMd) (md : MetaData) : StmtExprMd :=
  ⟨.StaticCall name args, md⟩

/-! ## Statements -/

/-- Variable declaration: `var name : type := init` -/
def localVar (name : String) (ty : HighTypeMd) (init : Option StmtExprMd := none) : StmtExprMd :=
  withDefaultMd (.LocalVariable name ty init)

/-- Variable declaration with metadata. -/
def localVarMd (name : String) (ty : HighTypeMd) (init : Option StmtExprMd := none)
    (md : MetaData) : StmtExprMd :=
  ⟨.LocalVariable name ty init, md⟩

/-- Assignment: `targets := value` -/
def assign (targets : List StmtExprMd) (value : StmtExprMd) : StmtExprMd :=
  withDefaultMd (.Assign targets value)

/-- Assignment with metadata. -/
def assignMd (targets : List StmtExprMd) (value : StmtExprMd)
    (md : MetaData) : StmtExprMd :=
  ⟨.Assign targets value, md⟩

/-- Assert statement. -/
def assert_ (cond : StmtExprMd) : StmtExprMd := withDefaultMd (.Assert cond)

/-- Assert with metadata. -/
def assertMd (cond : StmtExprMd) (md : MetaData) : StmtExprMd :=
  ⟨.Assert cond, md⟩

/-- Assume statement. -/
def assume_ (cond : StmtExprMd) : StmtExprMd := withDefaultMd (.Assume cond)

/-- Assume with metadata. -/
def assumeMd (cond : StmtExprMd) (md : MetaData) : StmtExprMd :=
  ⟨.Assume cond, md⟩

/-- Block of statements. -/
def block (stmts : List StmtExprMd) (label : Option String := none) : StmtExprMd :=
  withDefaultMd (.Block stmts label)

/-- Block with metadata. -/
def blockMd (stmts : List StmtExprMd) (label : Option String)
    (md : MetaData) : StmtExprMd :=
  ⟨.Block stmts label, md⟩

/-- If-then-else expression. -/
def ifThenElse (cond thenBranch : StmtExprMd)
    (elseBranch : Option StmtExprMd := none) : StmtExprMd :=
  withDefaultMd (.IfThenElse cond thenBranch elseBranch)

/-- If-then-else with metadata. -/
def ifThenElseMd (cond thenBranch : StmtExprMd)
    (elseBranch : Option StmtExprMd := none)
    (md : MetaData) : StmtExprMd :=
  ⟨.IfThenElse cond thenBranch elseBranch, md⟩

/-- Exit/return statement. -/
def exit_ (label : String) : StmtExprMd := withDefaultMd (.Exit label)

/-- New (constructor) expression. -/
def new_ (className : Identifier) : StmtExprMd := withDefaultMd (.New className)

/-- Hole (unknown/unsupported expression). -/
def hole : StmtExprMd := withDefaultMd .Hole

/-! ## Primitive operations -/

def primOp (op : Operation) (args : List StmtExprMd) : StmtExprMd :=
  withDefaultMd (.PrimitiveOp op args)

end -- public section
end Strata.Laurel
