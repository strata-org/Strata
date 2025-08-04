/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Imperative.PureExpr

namespace Imperative

---------------------------------------------------------------------

/-! ## MetaData

The Imperative dialect has a mechanism to store metadata in each of its
constructs. Metadata can be used to track both syntactic facts obtained during
translation from the source program to this dialect (e.g., line and column
numbers), or semantic facts derived during analyses (e.g., global variables
implicitly modified by a language construct).
-/

open Std (ToFormat Format format)

variable {Identifier : Type} [DecidableEq Identifier] [ToFormat Identifier] [Inhabited Identifier]

/-- A metadata field.

For now, we only track the variables modified by a construct, but we will expand
this in the future.
-/
inductive MetaDataElem.Field (P : PureExpr) where
  | var (v : P.Ident)
  | label (l : String)

instance [BEq P.Ident] : BEq (MetaDataElem.Field P) where
  beq f1 f2 :=
    match f1, f2 with
    | .var v1, .var v2 => v1 == v2
    | .label l1, .label l2 => l1 == l2
    | _, _ => false

instance [ToFormat P.Ident] : ToFormat (MetaDataElem.Field P) where
  format f := match f with | .var v => f!"var {v}" | .label l => f!"[{l}]"

/-- A metadata value. -/
inductive MetaDataElem.Value (P : PureExpr) where
  | expr (e : P.Expr)
  | msg (s : String)

instance [ToFormat P.Expr] : ToFormat (MetaDataElem.Value P) where
  format f := match f with | .expr e => f!"{e}" | .msg s => f!"{s}"

/-- A metadata element -/
structure MetaDataElem (P : PureExpr) where
  fld   : MetaDataElem.Field P
  value : MetaDataElem.Value P

/-- Metadata is an array of tagged elements. -/
abbrev MetaData (P : PureExpr) := Array (MetaDataElem P)

def MetaData.empty {P : PureExpr} : MetaData P := #[]

/-- Push a new metadata element. -/
def MetaData.pushElem {P : PureExpr}
    (md : MetaData P) (fld : MetaDataElem.Field P) (value : MetaDataElem.Value P) : MetaData P :=
  md.push { fld, value }

/-- Remove the first metadata element with tag `fld`. -/
def MetaData.eraseElem {P : PureExpr} [BEq P.Ident]
    (md : MetaData P) (fld : MetaDataElem.Field P) : MetaData P :=
  md.eraseP (fun e => e.fld == fld)

instance [ToFormat (MetaDataElem.Field P)] [ToFormat (MetaDataElem.Value P)] :
    ToFormat (MetaDataElem P) where
  format m := f!"<{m.fld}: {m.value}>"

instance [ToFormat (MetaDataElem P)] : ToFormat (MetaData P) where
  format md := if md.isEmpty then f!"" else f!"{md} "

---------------------------------------------------------------------

end Imperative
