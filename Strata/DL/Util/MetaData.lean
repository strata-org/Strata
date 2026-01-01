/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Util.DecidableEq
import Lean.Data.Position

namespace MetaData

---------------------------------------------------------------------

/-! ## MetaData

Metadata can be used to track both syntactic facts obtained during
translation from the source program to this dialect (e.g., line and column
numbers), or semantic facts derived during analyses (e.g., global variables
implicitly modified by a language construct).
-/

open Std (ToFormat Format format)
open Lean (Position)

---------------------------------------------------------------------

/--
A metadata field, which can be either a variable or an arbitrary string
label.
-/
inductive MetaDataElem.Field (Identifier : Type) where
  /-- Metadata indexed by a Strata variable. -/
  | var (v : Identifier)
  /-- Metadata indexed by an arbitrary label. -/
  | label (l : String)
  deriving Inhabited

@[grind]
def MetaDataElem.Field.beq {Identifier} [BEq Identifier] (f1 f2 : MetaDataElem.Field Identifier) :=
  match f1, f2 with
  | .var v1, .var v2 => v1 == v2
  | .label l1, .label l2 => l1 == l2
  | _, _ => false

instance {Identifier} [BEq Identifier] : BEq (MetaDataElem.Field Identifier) where
  beq f1 f2 := f1.beq f2

theorem MetaDataElem.Field.beq_eq {Identifier : Type} [DecidableEq Identifier]
  (f1 f2 : MetaDataElem.Field Identifier) : MetaDataElem.Field.beq f1 f2 = true ↔ f1 = f2 := by
  solve_beq f1 f2

instance {Identifier} [DecidableEq Identifier] : DecidableEq (MetaDataElem.Field Identifier) :=
  beq_eq_DecidableEq MetaDataElem.Field.beq MetaDataElem.Field.beq_eq

instance {Identifier} [ToFormat Identifier] : ToFormat (MetaDataElem.Field Identifier) where
  format f := match f with | .var v => f!"var {v}" | .label l => f!"[{l}]"

instance {Identifier} [Repr Identifier] : Repr (MetaDataElem.Field Identifier) where
  reprPrec f prec :=
    let res :=
      match f with
      | .var v => f!"MetaDataElem.Field.var {repr v}"
      | .label s => f!"MetaDataElem.Field.label {s}"
    Repr.addAppParen res prec

---------------------------------------------------------------------

inductive Uri where
  | file (path: String)
  deriving DecidableEq, Inhabited

instance : ToFormat Uri where
 format fr := match fr with | .file path => path

structure FileRange where
  file: Uri
  start: Lean.Position
  ending: Lean.Position
  deriving DecidableEq, Inhabited

instance : ToFormat FileRange where
 format fr := f!"{fr.file}:{fr.start}-{fr.ending}"

/-- A metadata value, which can be either an expression, a message, or a fileRange -/
inductive MetaDataElem.Value (Expr : Type) where
  /-- Metadata value in the form of a structured expression. -/
  | expr (e : Expr)
  /-- Metadata value in the form of an arbitrary string. -/
  | msg (s : String)
  /-- Metadata value in the form of a fileRange. -/
  | fileRange (r: FileRange)
  deriving Inhabited

instance {Expr} [ToFormat Expr] : ToFormat (MetaDataElem.Value Expr) where
  format f := match f with | .expr e => f!"{e}" | .msg s => f!"{s}" | .fileRange r => f!"{r}"

instance {Expr} [Repr Expr] : Repr (MetaDataElem.Value Expr) where
  reprPrec v prec :=
    let res :=
      match v with
      | .expr e => f!"MetaDataElem.Value.expr {reprPrec e prec}"
      | .msg s => f!"MetaDataElem.Value.msg {s}"
      | .fileRange fr => f!"MetaDataElem.Value.fileRange {fr}"
    Repr.addAppParen res prec

def MetaDataElem.Value.beq {Expr} [BEq Expr] (v1 v2 : MetaDataElem.Value Expr) :=
  match v1, v2 with
  | .expr e1, .expr e2 => e1 == e2
  | .msg m1, .msg m2 => m1 == m2
  | .fileRange r1, .fileRange r2 => r1 == r2
  | _, _ => false

instance {Expr} [BEq Expr] : BEq (MetaDataElem.Value Expr) where
  beq v1 v2 := v1.beq v2

-- TODO: this is exactly the same proof as MetaDataElem.Field.beq_eq. Is there
-- some existing automation we could use?
theorem MetaDataElem.Value.beq_eq {Expr} [DecidableEq Expr]
  (v1 v2 : MetaDataElem.Value Expr) : MetaDataElem.Value.beq v1 v2 = true ↔ v1 = v2 := by
  constructor <;> intro h
  case mp =>
    -- Soundness: beq = true → e1 = e2
    unfold beq at h; induction v1 generalizing v2 <;> (cases v2 <;> grind)
  case mpr =>
    -- Completeness: e1 = e2 → beq = true
    rw[h]; induction v2 generalizing v1 <;> simp only [MetaDataElem.Value.beq] <;> grind

instance {Expr} [DecidableEq Expr] : DecidableEq (MetaDataElem.Value Expr) :=
  beq_eq_DecidableEq MetaDataElem.Value.beq MetaDataElem.Value.beq_eq

---------------------------------------------------------------------

structure MetaDataParams where
  Identifier : Type
  Expr : Type
  deriving Inhabited, Repr

/-- A metadata element -/
structure MetaDataElem (P : MetaDataParams) where
  /-- The field or key used to identify the metadata. -/
  fld   : MetaDataElem.Field P.Identifier
  /-- The value of the metadata. -/
  value : MetaDataElem.Value P.Expr
  deriving Inhabited

/-- Metadata is an array of tagged elements. -/
abbrev MetaData (P : MetaDataParams) := Array (MetaDataElem P)

def MetaData.empty {P} : MetaData P := #[]

/-- Push a new metadata element. -/
def MetaData.pushElem {P}
    (md : MetaData P) (fld : MetaDataElem.Field P.Identifier)
    (value : MetaDataElem.Value P.Expr) : MetaData P :=
  md.push { fld, value }

/-- Remove the first metadata element with tag `fld`. -/
def MetaData.eraseElem {P} [BEq P.Identifier]
    (md : MetaData P) (fld : MetaDataElem.Field P.Identifier) : MetaData P :=
  md.eraseP (fun e => e.fld == fld)

/-- Retrieve the first metadata element with tag `fld`. -/
def MetaData.findElem {P} [BEq (MetaDataElem.Field P.Identifier)]
    (md : MetaData P) (fld : MetaDataElem.Field P.Identifier) :
    Option (MetaDataElem P) :=
    md.find? (λ e => e.fld == fld)

def MetaDataElem.beq {P} [BEq P.Identifier] [DecidableEq P.Expr]
  (e1 e2 : MetaDataElem P) : Bool := e1.fld.beq e2.fld && e1.value.beq e2.value

theorem MetaDataElem.beq_eq {P} [DecidableEq P.Identifier] [DecidableEq P.Expr]
  (e1 e2 : MetaDataElem P) : MetaDataElem.beq e1 e2 = true ↔ e1 = e2 := by
  unfold MetaDataElem.beq
  constructor <;> (cases e1 ; cases e2 ; grind [MetaDataElem.Field.beq_eq, MetaDataElem.Value.beq_eq])

instance {P} [DecidableEq P.Identifier] [DecidableEq P.Expr] : DecidableEq (MetaDataElem P) :=
  beq_eq_DecidableEq MetaDataElem.beq MetaDataElem.beq_eq

instance {P} [ToFormat (MetaDataElem.Field P.Identifier)] [ToFormat (MetaDataElem.Value P.Expr)] :
    ToFormat (MetaDataElem P) where
  format m := f!"<{m.fld}: {m.value}>"

instance {P} [ToFormat (MetaDataElem P)] : ToFormat (MetaData P) where
  format md := if md.isEmpty then f!"" else f!"{md} "

instance {P} [Repr P.Expr] [Repr P.Identifier] : Repr (MetaDataElem P) where
  reprPrec e prec :=
    Repr.addAppParen (f!"fld := {repr e.fld}, value := {repr e.value}") prec

---------------------------------------------------------------------

/-! ### Common metadata fields -/

def fileRange {P} : MetaDataElem.Field P := .label "fileRange"

def formatFileRange? {P} [BEq P.Identifier] (md : MetaData P) (includeEnd? : Bool := false) :
    Option Std.Format := do
  let fileRangeElem ← md.findElem MetaData.fileRange
  match fileRangeElem.value with
  | .fileRange m =>
    let baseName := match m.file with
                    | .file path => (path.splitToList (· == '/')).getLast!
    if includeEnd? then
      if m.start.line == m.ending.line then
        return f!"{baseName}({m.start.line}, ({m.start.column}-{m.ending.column}))"
      else
        return f!"{baseName}(({m.start.line}, {m.start.column})-({m.ending.line}, {m.ending.column}))"
    else -- don't include the end position.
      return f!"{baseName}({m.start.line}, {m.start.column})"
  | _ => none

def formatFileRangeD {P} [BEq P.Identifier] (md : MetaData P) (includeEnd? : Bool := false)
    : Std.Format :=
  match formatFileRange? md includeEnd? with
  | .none => "<no position info>"
  | .some str => s!"{str}"

end MetaData

---------------------------------------------------------------------
