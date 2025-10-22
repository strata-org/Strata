/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Expr
import Strata.Backends.CBMC.GOTO.SourceLocation

namespace CProverGOTO
open Std (ToFormat Format format)

-------------------------------------------------------------------------------

namespace Code

namespace Identifier
/-
Ref.:
cbmc/src/util/std_code.h
cbmc/src/goto-programs/goto_program.h
https://diffblue.github.io/cbmc/classcodet.html
-/

inductive Assignment where
  /-- `code_assignt` -/
  | assign
  /-- `code_declt` -/
  | decl
  /-- `code_deadt` -/
  | dead
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Assignment where
  format a := match a with
    | .assign => "assign" | .decl => "decl" | .dead => "dead"

inductive ControlFlow where
  /-- `code_gotot` -/
  | goto (destination : String)
  /-- `code_labelt` -/
  | label (labelName : String)
  /-- `code_skipt` -/
  | skip
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat ControlFlow where
  format cf := match cf with
    | .goto dest => f!"goto {dest}"
    | .label name => f!"label {name}"
    | .skip => f!"skip"

inductive Assertion where
  /-- `code_assumet` -/
  | assume
  /-- `code_assertt` -/
  | assert
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Assertion where
  format a := match a with
    | .assume => "assume" | .assert => "assert"

inductive Function where
  /-- `code_function_callt` -/
  | functionCall
  /-- `code_returnt` -/
  | return
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Function where
  format f := match f with
    | .functionCall => "function_call" | .return => "return"

inductive Block where
  | block
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Block where
  format b := match b with
     | .block => "block"


end Identifier

inductive Identifier where
  | assignment (a : Identifier.Assignment)
  | controlFlow (cf : Identifier.ControlFlow)
  | assertion (a : Identifier.Assertion)
  | function (f : Identifier.Function)
  | block (b : Identifier.Block)
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Identifier where
  format i := match i with
    | .controlFlow cf => f!"{cf}"
    | .assignment a => f!"{a}"
    | .assertion a => f!"{a}"
    | .function f => f!"{f}"
    | .block b => f!"{b}"

end Code

-------------------------------------------------------------------------------

/--
GOTO [Code](https://diffblue.github.io/cbmc/classcodet.html)
-/
structure Code where
  /--
  The interpretation of `Code` depends on the `id` field.
  CBMC pre-defines some code IDs in `util/irep_ids.def`.
  -/
  id         : Code.Identifier
  operands   : List Expr := []
  sourceLoc  : SourceLocation := .nil
  /--
  Named fields for code statements that need additional data.
  -/
  namedFields : List (String × String) := []
  /--
  Nested code statements for compound statements like blocks.
  -/
  statements : List Code := []
  deriving Repr, Inhabited

partial def Code.beq (x y : Code) : Bool :=
  x.id == y.id && x.sourceLoc == y.sourceLoc &&
  x.namedFields == y.namedFields &&
  goExpr x.operands y.operands &&
  goCode x.statements y.statements
  where
    goExpr xs ys :=
      match xs, ys with
      | [], [] => true
      | _, [] | [], _ => false
      | x :: xrest, y :: yrest =>
        x == y && goExpr xrest yrest
    goCode xs ys :=
      match xs, ys with
      | [], [] => true
      | _, [] | [], _ => false
      | x :: xrest, y :: yrest =>
        Code.beq x y && goCode xrest yrest

instance : BEq Code where
  beq := Code.beq

partial def formatCode (c : Code) : Format :=
  let operands := c.operands.map (fun o => format o)
  let operands := Format.joinSep operands " "
  let statements := c.statements.map (fun s => formatCode s)
  let statements := Format.joinSep statements "; "

  let base := if operands.isEmpty then
    f!"{c.id}"
  else
    f!"({c.id} {operands})"

  if statements.isEmpty then
    base
  else
    f!"{base} {statements}"

instance : ToFormat Code where
  format c := formatCode c

/-- Get a named field from the code statement. -/
def Code.getNamedField (c : Code) (name : String) : Option String :=
  c.namedFields.find? (fun (n, _) => n == name) |>.map (·.2)

/-- Set a named field in the code statement. -/
def Code.setNamedField (c : Code) (name : String) (value : String) : Code :=
  { c with namedFields := (name, value) :: c.namedFields.filter (fun (n, _) => n != name) }

namespace Code

/-- Assignment statement -/
def assign (lhs rhs : Expr) : Code :=
  { id := .assignment .assign, operands := [lhs, rhs] }

/-- Assume statement -/
def assume (condition : Expr) : Code :=
  { id := .assertion .assume, operands := [condition] }

/-- Assert statement -/
def assert (condition : Expr) : Code :=
  { id := .assertion .assert, operands := [condition] }

/-- Declaration statement -/
def decl (symbol : Expr) : Code :=
  { id := .assignment .decl, operands := [symbol] }

/-- Dead statement -/
def dead (symbol : Expr) : Code :=
  { id := .assignment .dead, operands := [symbol] }

/-- Goto statement -/
def goto (destination : String) : Code :=
  { id := .controlFlow (.goto destination) }

/-- Label statement -/
def label (labelName : String) : Code :=
  { id := .controlFlow (.label labelName) }

/-- Block statement -/
def block (statements : List Code) : Code :=
  { id := .block .block, statements := statements }

/-- Skip statement -/
def skip : Code :=
  { id := .controlFlow .skip }

/--
Return statement
FIXME: Is this analogous to `SET_RETURN_VALUE`? -/
def set_return_value (symbol : Expr) : Code :=
  { id := .function .return, operands := [symbol] }

end Code

-------------------------------------------------------------------------------
