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
  | Plus | Minus
  | Equal
  deriving Repr, Inhabited, DecidableEq

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

-- DECL s : bv32
private def decl_code : Expr :=
  {
    id := .code .Decl,
    type := .BitVector (.UnsignedBV 32),
    operands := [s_expr]
  }

end Examples

-------------------------------------------------------------------------------

end GotoIR
