/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Type
import Strata.Backends.CBMC.GOTO.SourceLocation

namespace CProverGOTO
open Std (ToFormat Format format)

-------------------------------------------------------------------------------
namespace Expr

namespace Identifier
/-
Ref.:
cbmc/src/util/irep_ids.h
cbmc/src/util/irep_ids.def
-/

inductive Nullary where
  /-- `symbol_exprt` -/
  | symbol (name : String)
  /-- `constant_exprt` -/
  | constant (value : String)
  /-- `nondet_symbol_exprt` -/
  | nondet (name : String)
  /-- `nil_exprt` -/
  | nil
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Nullary where
  format n := match n with
    | .symbol name => name
    | .constant value => value
    | .nondet name => f!"nondet({name})"
    | .nil => "nil"

inductive Unary where
  /-- `unary_minus_exprt` -/
  | UnaryMinus
  /-- `unary_plus_exprt` -/
  | UnaryPlus
  /-- `not_exprt` -/
  | Not
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Unary where
  format u := match u with
    | .UnaryMinus => "-"
    | .UnaryPlus => "+"
    | .Not => "not"

/--
Representation of identifiers specific to binary expressions,
[binary_exprt](https://diffblue.github.io/cbmc/classbinary__exprt.html).
-/
inductive Binary where
  /-- `div_exprt` -/
  | Div
  /-- `mod_exprt` -/
  | Mod
  /-- `shl_exprt` -/
  | Shl
  /-- `ashr_exprt` -/
  | Ashr
  /-- `lshr_exprt` -/
  | Lshr
  /-- `plus_overflow_exprt` -/
  | PlusOverflow
  | Gt | Lt | Ge | Le | Equal | NotEqual
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Binary where
  format b := match b with
    | .Div => "div"
    | .Mod => "mod"
    | .Shl => "shl"
    | .Ashr => "ashr"
    | .Lshr => "lshr"
    | .PlusOverflow => "overflow-+"
    | .Gt => ">"
    | .Lt => "<"
    | .Ge => ">="
    | .Le => "<="
    | .Equal => "="
    | .NotEqual => "!="

inductive Ternary where
  /-- `if_exprt` -/
  | ite
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Ternary where
  format t := match t with
    | .ite => "if"

inductive Multiary where
  /-- `and_exprt` -/
  | And
  /-- `or_exprt` -/
  | Or
  /-- `mult_exprt` -/
  | Mult
  /-- `plus_exprt` -/
  | Plus
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Multiary where
  format m := match m with
    | .And => "and"
    | .Or => "or"
    | .Mult => "*"
    | .Plus => "+"

inductive SideEffect where
  /-- `side_effect_expr_nondett` -/
  | Nondet
  /-- `side_effect_expr_assignt` -/
  | Assign
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat SideEffect where
  format s := match s with
    | .Nondet => "nondet"
    | .Assign => "assign"

end Identifier

inductive Identifier where
  | nullary (n : Identifier.Nullary)
  | unary (u : Identifier.Unary)
  | binary (b : Identifier.Binary)
  | ternary (t : Identifier.Ternary)
  | multiary (m : Identifier.Multiary)
  | side_effect (s : Identifier.SideEffect)
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Identifier where
  format i := match i with
    | .nullary n => f!"{n}"
    | .unary u => f!"{u}"
    | .binary b => f!"{b}"
    | .ternary t => f!"{t}"
    | .multiary m => f!"{m}"
    | .side_effect s => f!"{s}"

end Expr
-------------------------------------------------------------------------------

/--
GOTO [Expressions](https://diffblue.github.io/cbmc/classexprt.html)

For now, we have primarily focused on `expr_protectedt` class.

We will also confine ourselves to expressions that can appear at the lowest
level of CProver IRs -- i.e., GOTO assembly instructions.
-/
structure Expr where
  /--
  The interpretation of `Expr` depends on the `id` field.
  CBMC pre-defines some IDs here: `util/irep_ids.def`.
  -/
  id         : Expr.Identifier
  type       : Ty
  operands   : List Expr := []
  sourceLoc  : SourceLocation := .nil
  /--
  Named fields for expressions that need additional data (e.g.,
  `side_effect_exprt` has a `statement` field).
  -/
  namedFields : List (String × Expr) := []
  deriving Repr, Inhabited

def Expr.beq (x y : Expr) : Bool :=
  x.id == y.id && x.type == y.type && x.sourceLoc == y.sourceLoc &&
  go x.operands y.operands
  termination_by (SizeOf.sizeOf x)
  decreasing_by cases x; simp_wf; omega
  where go xs ys :=
  match xs, ys with
  | [], [] => true
  | _, [] | [], _ => false
  | x :: xrest, y :: yrest =>
    Expr.beq x y && go xrest yrest
  termination_by (SizeOf.sizeOf xs)

instance : BEq Expr where
  beq := Expr.beq

def formatExpr (e : Expr) : Format :=
  match e.id, _: e.operands with
  | .nullary n, [] => f!"({n} : {e.type})"
  | .unary u, [op] => f!"(({u}{formatExpr op}) : {e.type})"
  | .binary b, [left, right] => f!"(({formatExpr left} {b} {formatExpr right}) : {e.type})"
  | .ternary .ite, [cond, then_expr, else_expr] => f!"(({formatExpr cond} ? {formatExpr then_expr} : {formatExpr else_expr}) : {e.type})"
  | .multiary m, ops =>
    let formatted := ops.map formatExpr
    f!"(({Format.joinSep formatted f!" {m} "}) : {e.type})"
  | .side_effect s, ops =>
    let formatted := ops.map formatExpr
    let operands := Format.joinSep formatted f!" "
    if operands.isEmpty then f!"({s} : {e.type})" else f!"(({s} {operands}) : {e.type})"
  | id, ops =>
    let formatted := ops.map formatExpr
    let operands := Format.joinSep formatted f!" "
    if operands.isEmpty then f!"({id} : {e.type})" else f!"(({id} {operands}) : {e.type})"
  termination_by (SizeOf.sizeOf e)
  decreasing_by
    all_goals (cases e; simp_all; subst_vars; try omega)
    all_goals (rename_i x_in; have := List.sizeOf_lt_of_mem x_in; omega)

instance : ToFormat Expr where
  format e := formatExpr e

def Expr.true : Expr :=
  { id := (.nullary $ .constant "true"), type := .Boolean }

/-- Get a named field from the expression. -/
def Expr.getNamedField (e : Expr) (name : String) : Option Expr :=
  e.namedFields.find? (fun (n, _) => n == name) |>.map (·.2)

/-- Set a named field in the expression. -/
def Expr.setNamedField (e : Expr) (name : String) (value : Expr) : Expr :=
  { e with namedFields := (name, value) :: e.namedFields.filter (fun (n, _) => n != name) }

namespace Expr

/-- Symbol expression -/
def symbol (name : String) (type : Ty) : Expr :=
  { id := .nullary (.symbol name), type := type }

/-- Constant expression -/
def constant (value : String) (type : Ty) : Expr :=
  { id := .nullary (.constant value), type := type }

/-- Nondet expression -/
def nondet (name : String) (type : Ty) : Expr :=
  { id := .nullary (.nondet name), type := type }

/-- Unary minus -/
def neg (operand : Expr) : Expr :=
  { id := .unary .UnaryMinus, type := operand.type, operands := [operand] }

/-- Logical not -/
def not (operand : Expr) : Expr :=
  { id := .unary .Not, type := operand.type, operands := [operand] }

/-- Overflow-+ -/
def plus_overflow (left right : Expr) : Expr :=
  { id := .binary .PlusOverflow, type := Ty.Boolean, operands := [left, right] }

/-- Division -/
def div (left right : Expr) : Expr :=
  { id := .binary .Div, type := left.type, operands := [left, right] }

/-- Modulo -/
def mod (left right : Expr) : Expr :=
  { id := .binary .Mod, type := left.type, operands := [left, right] }

/-- Greater than -/
def gt (left right : Expr) : Expr :=
  { id := .binary .Gt, type := Ty.Boolean, operands := [left, right] }

/-- Less than -/
def lt (left right : Expr) : Expr :=
  { id := .binary .Lt, type := Ty.Boolean, operands := [left, right] }

/-- Equal -/
def eq (left right : Expr) : Expr :=
  { id := .binary .Equal, type := Ty.Boolean, operands := [left, right] }

/-- Addition -/
def add (operands : List Expr) : Expr :=
  match operands with
  | [] => { id := .nullary (.constant "0"), type := Ty.Integer }
  | [x] => x
  | x :: _ => { id := .multiary .Plus, type := x.type, operands := operands }

/-- Multiplication -/
def mul (operands : List Expr) : Expr :=
  match operands with
  | [] => { id := .nullary (.constant "1"), type := Ty.Integer }
  | [x] => x
  | x :: _ => { id := .multiary .Mult, type := x.type, operands := operands }

/-- Logical and -/
def and (operands : List Expr) : Expr :=
  match operands with
  | [] => Expr.true
  | [x] => x
  | _ => { id := .multiary .And, type := Ty.Boolean, operands := operands }

/-- Logical or -/
def or (operands : List Expr) : Expr :=
  match operands with
  | [] => { id := .nullary (.constant "false"), type := Ty.Boolean }
  | [x] => x
  | _ => { id := .multiary .Or, type := Ty.Boolean, operands := operands }

/-- If-then-else -/
def ite (cond then_expr else_expr : Expr) : Expr :=
  { id := .ternary .ite, type := then_expr.type, operands := [cond, then_expr, else_expr] }

/-- Non-deterministic side effects -/
def side_effect_nondet (namedFields : List (String × Expr)) : Expr :=
  { id := .side_effect .Nondet, type := .Empty, namedFields := namedFields }

end Expr

-------------------------------------------------------------------------------
