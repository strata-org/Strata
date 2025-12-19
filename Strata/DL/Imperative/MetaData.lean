/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.PureExpr
import Strata.DL.Util.DecidableEq
import Lean.Data.Position

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
open Lean (Position)

variable {Identifier : Type} [DecidableEq Identifier] [ToFormat Identifier] [Inhabited Identifier]

/-- A metadata field, which can be either a variable or an arbitrary string label.

For now, we only track the variables modified by a construct, but we will expand
this in the future.
-/
inductive MetaDataElem.Field (P : PureExpr) where
  /-- Metadata indexed by a Strata variable. -/
  | var (v : P.Ident)
  /-- Metadata indexed by an arbitrary label. -/
  | label (l : String)

@[grind]
def MetaDataElem.Field.beq [BEq P.Ident] (f1 f2 : MetaDataElem.Field P) :=
  match f1, f2 with
  | .var v1, .var v2 => v1 == v2
  | .label l1, .label l2 => l1 == l2
  | _, _ => false

instance [BEq P.Ident] : BEq (MetaDataElem.Field P) where
  beq f1 f2 := f1.beq f2

theorem MetaDataElem.Field.beq_eq {P : PureExpr} [DecidableEq P.Ident]
  (f1 f2 : MetaDataElem.Field P) : MetaDataElem.Field.beq f1 f2 = true ↔ f1 = f2 := by
  solve_beq f1 f2

instance [DecidableEq P.Ident] : DecidableEq (MetaDataElem.Field P) :=
  beq_eq_DecidableEq MetaDataElem.Field.beq MetaDataElem.Field.beq_eq

instance [ToFormat P.Ident] : ToFormat (MetaDataElem.Field P) where
  format f := match f with | .var v => f!"var {v}" | .label l => f!"[{l}]"

instance [Repr P.Ident] : Repr (MetaDataElem.Field P) where
  reprPrec f prec :=
    let res :=
      match f with
      | .var v => f!"MetaDataElem.Field.var {repr v}"
      | .label s => f!"MetaDataElem.Field.label {s}"
    Repr.addAppParen res prec

inductive Uri where
  | file (path: String)
  deriving DecidableEq

instance : ToFormat Uri where
 format fr := match fr with | .file path => path

structure FileRange where
  file: Uri
  start: Lean.Position
  ending: Lean.Position
  deriving DecidableEq

instance : ToFormat FileRange where
 format fr := f!"{fr.file}:{fr.start}-{fr.ending}"

/-- A metadata value, which can be either an expression, a message, or a fileRange -/
inductive MetaDataElem.Value (P : PureExpr) where
  /-- Metadata value in the form of a structured expression. -/
  | expr (e : P.Expr)
  /-- Metadata value in the form of an arbitrary string. -/
  | msg (s : String)
  /-- Metadata value in the form of a fileRange. -/
  | fileRange (r: FileRange)


instance [ToFormat P.Expr] : ToFormat (MetaDataElem.Value P) where
  format f := match f with | .expr e => f!"{e}" | .msg s => f!"{s}" | .fileRange r => f!"{r}"

instance [Repr P.Expr] : Repr (MetaDataElem.Value P) where
  reprPrec v prec :=
    let res :=
      match v with
      | .expr e => f!"MetaDataElem.Value.expr {reprPrec e prec}"
      | .msg s => f!"MetaDataElem.Value.msg {s}"
      | .fileRange fr => f!"MetaDataElem.Value.fileRange {fr}"
    Repr.addAppParen res prec

def MetaDataElem.Value.beq [BEq P.Expr] (v1 v2 : MetaDataElem.Value P) :=
  match v1, v2 with
  | .expr e1, .expr e2 => e1 == e2
  | .msg m1, .msg m2 => m1 == m2
  | .fileRange r1, .fileRange r2 => r1 == r2
  | _, _ => false

instance [BEq P.Expr] : BEq (MetaDataElem.Value P) where
  beq v1 v2 := v1.beq v2

-- TODO: this is exactly the same proof as MetaDataElem.Field.beq_eq. Is there
-- some existing automation we could use?
theorem MetaDataElem.Value.beq_eq {P : PureExpr} [DecidableEq P.Expr]
  (v1 v2 : MetaDataElem.Value P) : MetaDataElem.Value.beq v1 v2 = true ↔ v1 = v2 := by
  constructor <;> intro h
  case mp =>
    -- Soundness: beq = true → e1 = e2
    unfold beq at h; induction v1 generalizing v2 <;> (cases v2 <;> grind)
  case mpr =>
    -- Completeness: e1 = e2 → beq = true
    rw[h]; induction v2 generalizing v1 <;> simp only [MetaDataElem.Value.beq] <;> grind

instance [DecidableEq P.Expr] : DecidableEq (MetaDataElem.Value P) :=
  beq_eq_DecidableEq MetaDataElem.Value.beq MetaDataElem.Value.beq_eq

/-- A metadata element -/
structure MetaDataElem (P : PureExpr) where
  /-- The field or key used to identify the metadata. -/
  fld   : MetaDataElem.Field P
  /-- The value of the metadata. -/
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

/-- Retrieve the first metadata element with tag `fld`. -/
def MetaData.findElem {P : PureExpr} [BEq P.Ident]
    (md : MetaData P) (fld : MetaDataElem.Field P) : Option (MetaDataElem P) :=
    md.find? (λ e => e.fld == fld)

def MetaDataElem.beq {P : PureExpr} [DecidableEq P.Ident] [DecidableEq P.Expr]
  (e1 e2 : MetaDataElem P) : Bool := e1.fld.beq e2.fld && e1.value.beq e2.value

theorem MetaDataElem.beq_eq {P : PureExpr} [DecidableEq P.Ident] [DecidableEq P.Expr]
  (e1 e2 : MetaDataElem P) : MetaDataElem.beq e1 e2 = true ↔ e1 = e2 := by
  unfold MetaDataElem.beq
  constructor <;> (cases e1 ; cases e2 ; grind [MetaDataElem.Field.beq_eq, MetaDataElem.Value.beq_eq])

instance [DecidableEq P.Ident] [DecidableEq P.Expr] : DecidableEq (MetaDataElem P) :=
  beq_eq_DecidableEq MetaDataElem.beq MetaDataElem.beq_eq

instance [ToFormat (MetaDataElem.Field P)] [ToFormat (MetaDataElem.Value P)] :
    ToFormat (MetaDataElem P) where
  format m := f!"<{m.fld}: {m.value}>"

instance [ToFormat (MetaDataElem P)] : ToFormat (MetaData P) where
  format md := if md.isEmpty then f!"" else f!"{md} "

instance [Repr P.Expr] [Repr P.Ident] : Repr (MetaDataElem P) where
  reprPrec e prec :=
    Repr.addAppParen (f!"fld := {repr e.fld}, value := {repr e.value}") prec

---------------------------------------------------------------------

/-! ### Common metadata fields -/

def MetaData.fileRange : MetaDataElem.Field P := .label "fileRange"

end Imperative
