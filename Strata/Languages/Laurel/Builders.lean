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
def stmtExpr (e : StmtExpr) : StmtExprMd := ⟨e, defaultMd⟩

/-- Create a `StmtExprMd` with explicit metadata. -/
def stmtExprMd (e : StmtExpr) (md : MetaData) : StmtExprMd := ⟨e, md⟩

/-! ## Literals -/

def litInt (n : Int) : StmtExprMd := stmtExpr (.LiteralInt n)
def litStr (s : String) : StmtExprMd := stmtExpr (.LiteralString s)
def litBool (b : Bool) : StmtExprMd := stmtExpr (.LiteralBool b)

/-! ## Identifiers and field access -/

def ident (name : String) : StmtExprMd := stmtExpr (.Identifier name)
def fieldSelect (obj : StmtExprMd) (field : String) : StmtExprMd :=
  stmtExpr (.FieldSelect obj field)

/-! ## Calls -/

/-- Static function call: `name(args...)` -/
def call (name : String) (args : List StmtExprMd) : StmtExprMd :=
  stmtExpr (.StaticCall name args)

/-- Static function call with metadata. -/
def callMd (name : String) (args : List StmtExprMd) (md : MetaData) : StmtExprMd :=
  stmtExprMd (.StaticCall name args) md

/-! ## Statements -/

/-- Variable declaration: `var name : type := init` -/
def localVar (name : String) (ty : HighTypeMd) (init : Option StmtExprMd := none) : StmtExprMd :=
  stmtExpr (.LocalVariable name ty init)

/-- Variable declaration with metadata. -/
def localVarMd (name : String) (ty : HighTypeMd) (init : Option StmtExprMd := none)
    (md : MetaData) : StmtExprMd :=
  stmtExprMd (.LocalVariable name ty init) md

/-- Assignment: `targets := value` -/
def assign (targets : List StmtExprMd) (value : StmtExprMd) : StmtExprMd :=
  stmtExpr (.Assign targets value)

/-- Assignment with metadata. -/
def assignMd (targets : List StmtExprMd) (value : StmtExprMd)
    (md : MetaData) : StmtExprMd :=
  stmtExprMd (.Assign targets value) md

/-- Assert statement. -/
def assert_ (cond : StmtExprMd) : StmtExprMd := stmtExpr (.Assert cond)

/-- Assert with metadata. -/
def assertMd (cond : StmtExprMd) (md : MetaData) : StmtExprMd :=
  stmtExprMd (.Assert cond) md

/-- Assume statement. -/
def assume_ (cond : StmtExprMd) : StmtExprMd := stmtExpr (.Assume cond)

/-- Assume with metadata. -/
def assumeMd (cond : StmtExprMd) (md : MetaData) : StmtExprMd :=
  stmtExprMd (.Assume cond) md

/-- Block of statements. -/
def block (stmts : List StmtExprMd) (label : Option String := none) : StmtExprMd :=
  stmtExpr (.Block stmts label)

/-- Block with metadata. -/
def blockMd (stmts : List StmtExprMd) (label : Option String)
    (md : MetaData) : StmtExprMd :=
  stmtExprMd (.Block stmts label) md

/-- If-then-else expression. -/
def ifThenElse (cond thenBranch : StmtExprMd)
    (elseBranch : Option StmtExprMd := none) : StmtExprMd :=
  stmtExpr (.IfThenElse cond thenBranch elseBranch)

/-- If-then-else with metadata. -/
def ifThenElseMd (cond thenBranch : StmtExprMd)
    (elseBranch : Option StmtExprMd := none)
    (md : MetaData) : StmtExprMd :=
  stmtExprMd (.IfThenElse cond thenBranch elseBranch) md

/-- Exit/return statement. -/
def exit_ (label : String) : StmtExprMd := stmtExpr (.Exit label)

/-- New (constructor) expression. -/
def new_ (className : Identifier) : StmtExprMd := stmtExpr (.New className)

/-- Hole (unknown/unsupported expression). -/
def hole : StmtExprMd := stmtExpr .Hole

/-! ## Primitive operations -/

def primOp (op : Operation) (args : List StmtExprMd) : StmtExprMd :=
  stmtExpr (.PrimitiveOp op args)

end -- public section
end Strata.Laurel
