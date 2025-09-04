/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.CProver.Type

namespace GotoIR
open Std (ToFormat Format format)

-- (TODO) Implement Expr/Code.toIRep.

-------------------------------------------------------------------------------
namespace Expr

namespace Identifier
/-
Ref.:
cbmc/src/util/irep_ids.h
cbmc/src/util/irep_ids.def
-/

/--
Representation of identifiers specific to binary expressions
[ref](https://diffblue.github.io/cbmc/classbinary__exprt.html).
E.g., `Plus` below corresponds to IRep ID `ID_plus`, and so on.
-/
inductive Binary where
  | Plus
  | Minus
  | Equal
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Binary where
  format b := match b with
    | .Plus => "+"
    | .Minus => "-"
    | .Equal => "=="

/--
Data structure for representing an arbitrary statement in a program. This is
analogous to CBMC's `codet`.
-/
inductive Code where
  | Assert
  | Assign
  | Assume
  | Block
  | Break
  | Continue
  | Dead
  | Decl
  | Goto
  | Label
  | Return
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Code where
  format c := match c with
    | .Assert => "Assert"
    | .Assign => "Assign"
    | .Assume => "Assume"
    | .Block => "Block"
    | .Break => "Break"
    | .Continue => "Continue"
    | .Dead => "Dead"
    | .Decl => "Decl"
    | .Goto => "Goto"
    | .Label => "Label"
    | .Return => "Return"

end Identifier

inductive Identifier where
  /--
  `symbol name`: The `name` corresponds to the field set by function
  `set_identifier` of `symbol_exprt`.
  -/
  | symbol (name : String)
  /--
    `constant value`: The `value` corresponds to the field set by function
    `set_value` of `constant_exprt`.
  -/
  | constant (value : String)
  /--
  `nondet`: This corresponds to `side_effect_expr_nondett`.
  -/
  | nondet
  | code (c : Identifier.Code)
  | bin (b : Identifier.Binary)
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Identifier where
  format i :=
    match i with
    | .symbol name => name
    | .constant value => value
    | .nondet => "nondet"
    | .code c => f!"{c}"
    | .bin b => f!"{b}"

end Expr
-------------------------------------------------------------------------------

/--
GOTO [Expressions](https://diffblue.github.io/cbmc/classexprt.html)
-/
structure Expr where
  /--
  The interpretation of `Expr` depends on the `id` field (also sometimes called
  the `data` field?).
  CBMC pre-defines some IDs here: `util/irep_ids.def`.
  -/
  id       : Expr.Identifier
  type     : Ty
  operands : List Expr := []
  -- TODO: Source Location
  deriving Repr, Inhabited

partial def Expr.BEq (x y : Expr) : Bool :=
  x.id == y.id && x.type == y.type &&
  go x.operands y.operands
  where go xs ys :=
  match xs, ys with
  | [], [] => true
  | _, [] | [], _ => false
  | x :: xrest, y :: yrest =>
    Expr.BEq x y && go xrest yrest

partial def formatExpr (e : Expr) : Format :=
  let operands := e.operands.map (fun o => formatExpr o)
  let operands := Format.joinSep operands f!" "
  if operands.isEmpty then
    f!"({e.id} : {e.type})"
  else
  f!"(({e.id} {operands}) : {e.type})"

instance : ToFormat Expr where
  format e := formatExpr e

def true_expr : Expr :=
  { id := .constant "true", type := .Boolean }

-------------------------------------------------------------------------------

section Examples

private def s_expr : Expr :=
  {
    id := .symbol "s",
    type := .BitVector (.UnsignedBV 32)
  }

private def one_expr : Expr :=
  {
    id := .constant "1",
    type := .BitVector (.UnsignedBV 32),
  }

-- s + 1  (bv32)
private def add_expr : Expr :=
  {
    id := .bin .Plus,
    type := .BitVector (.UnsignedBV 32),
    operands := [s_expr, one_expr]
  }

/-- info: ((+ (s : unsignedbv[32]) (1 : unsignedbv[32])) : unsignedbv[32]) -/
#guard_msgs in
#eval format add_expr

-- DECL s : bv32
private def decl_code : Expr :=
  {
    id := .code .Decl,
    type := .BitVector (.UnsignedBV 32),
    operands := [s_expr]
  }

/-- info: ((Decl (s : unsignedbv[32])) : unsignedbv[32]) -/
#guard_msgs in
#eval format decl_code

end Examples

-------------------------------------------------------------------------------

end GotoIR
