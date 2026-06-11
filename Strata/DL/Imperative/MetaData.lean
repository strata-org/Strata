/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.PureExpr
public import Strata.DL.Util.DecidableEq
public import Strata.Util.Provenance

namespace Imperative
open Strata (DiagnosticModel DiagnosticType FileRange Provenance Uri SourceRange)

public section

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

/-- A metadata value, which can be either an expression, a message, a switch, or a provenance. -/
inductive MetaDataElem.Value (P : PureExpr) where
  /-- Metadata value in the form of a structured expression. -/
  | expr (e : P.Expr)
  /-- Metadata value in the form of an arbitrary string. -/
  | msg (s : String)
  /-- Metadata value in the form of a boolean switch. -/
  | switch (b : Bool)
  /-- Metadata value in the form of a provenance (source location or synthesized origin). -/
  | provenance (p : Provenance)

instance [ToFormat P.Expr] : ToFormat (MetaDataElem.Value P) where
  format f := match f with
              | .expr e => f!"{e}"
              | .msg s => f!"{s}"
              | .switch b => f!"{b}"
              | .provenance p => f!"{p}"

instance [Repr P.Expr] : Repr (MetaDataElem.Value P) where
  reprPrec v prec :=
    let res :=
      match v with
      | .expr e => f!".expr {reprPrec e prec}"
      | .msg s => f!".msg {s}"
      | .switch b => f!".switch {repr b}"
      | .provenance p => f!".provenance {repr p}"
    Repr.addAppParen res prec

def MetaDataElem.Value.beq [BEq P.Expr] (v1 v2 : MetaDataElem.Value P) :=
  match v1, v2 with
  | .expr e1, .expr e2 => e1 == e2
  | .msg m1, .msg m2 => m1 == m2
  | .switch b1, .switch b2 => b1 == b2
  | .provenance p1, .provenance p2 => p1 == p2
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
@[expose] abbrev MetaData (P : PureExpr) := Array (MetaDataElem P)

@[expose]
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

@[match_pattern]
abbrev MetaData.provenanceField : MetaDataElem.Field P := .label "provenance"

@[match_pattern]
abbrev MetaData.reachCheck : MetaDataElem.Field P := .label "reachCheck"
@[match_pattern]
abbrev MetaData.fullCheck : MetaDataElem.Field P := .label "fullCheck"
@[match_pattern]
abbrev MetaData.validityCheck : MetaDataElem.Field P := .label "validityCheck"
@[match_pattern]
abbrev MetaData.satisfiabilityCheck : MetaDataElem.Field P := .label "satisfiabilityCheck"

def MetaData.hasReachCheck {P : PureExpr} [BEq P.Ident] (md : MetaData P) : Bool :=
  match md.findElem MetaData.reachCheck with
  | some elem =>
    match elem.value with
    | .switch true => true
    | _ => false
  | none => false

def MetaData.hasFullCheck {P : PureExpr} [BEq P.Ident] (md : MetaData P) : Bool :=
  match md.findElem MetaData.fullCheck with
  | some elem =>
    match elem.value with
    | .switch true => true
    | _ => false
  | none =>
    -- Backward compatibility: reachCheck maps to fullCheck
    md.hasReachCheck

def MetaData.hasValidityCheck {P : PureExpr} [BEq P.Ident] (md : MetaData P) : Bool :=
  match md.findElem MetaData.validityCheck with
  | some elem =>
    match elem.value with
    | .switch true => true
    | _ => false
  | none => false

def MetaData.hasSatisfiabilityCheck {P : PureExpr} [BEq P.Ident] (md : MetaData P) : Bool :=
  match md.findElem MetaData.satisfiabilityCheck with
  | some elem =>
    match elem.value with
    | .switch true => true
    | _ => false
  | none => false

/-- Get the provenance from metadata. -/
def getProvenance {P : PureExpr} [BEq P.Ident] (md : MetaData P) : Option Provenance := do
  let elem ← md.findElem Imperative.MetaData.provenanceField
  match elem.value with
  | .provenance p => some p
  | _ => none

def getFileRange {P : PureExpr} [BEq P.Ident] (md: MetaData P) : Option FileRange := do
  let p ← getProvenance md
  p.toFileRange

/-- Create metadata with a provenance element. -/
def MetaData.ofProvenance {P : PureExpr} (p : Provenance) : MetaData P :=
  #[{ fld := MetaData.provenanceField, value := .provenance p }]

/-- Create metadata from a source range and URI, storing provenance. -/
def MetaData.ofSourceRange {P : PureExpr} (uri : Uri) (sr : SourceRange) : MetaData P :=
  MetaData.ofProvenance (Provenance.ofSourceRange uri sr)

/-- Create a DiagnosticModel from metadata and a message.
    Uses provenance or file range from metadata if available, otherwise uses a default location. -/
def MetaData.toDiagnostic {P : PureExpr} [BEq P.Ident] (md : MetaData P) (msg : String) (type : DiagnosticType := DiagnosticType.UserError): DiagnosticModel :=
  match getProvenance md with
  | some (.loc uri range) => DiagnosticModel.withRange { file := uri, range } msg type
  | some (.synthesized _) => DiagnosticModel.fromMessage msg type
  | none => DiagnosticModel.fromMessage msg type

/-- Create a DiagnosticModel from metadata and a Format message. -/
def MetaData.toDiagnosticF {P : PureExpr} [BEq P.Ident] (md : MetaData P) (msg : Std.Format) (type : DiagnosticType := DiagnosticType.UserError): DiagnosticModel :=
  MetaData.toDiagnostic md (toString msg) type

/-- Get the file range from metadata as a DiagnosticModel (for formatting).
    This is a compatibility function that formats the file range using byte offsets.
    For proper line/column display, use toDiagnostic and format with a FileMap at the top level. -/
def MetaData.formatFileRangeD {P : PureExpr} [BEq P.Ident] (md : MetaData P) (fileMap : Option Lean.FileMap := none) (includeEnd? : Bool := false) : Format :=
  match getFileRange md with
  | some fr => fr.format fileMap includeEnd?
  | none => f!""

/-- Metadata field for a related file range (e.g., the original assertion location
    when the primary file range points to the call site after inlining).
    There can be multiple `relatedFileRange` fields in a single metadata due to
    multiple levels of inlining. -/
def MetaData.relatedFileRange : MetaDataElem.Field P := .label "relatedFileRange"

/-- Get all related file ranges from metadata, in order.
    The returned array's order is determined by the call stack: the innermost
    (most deeply inlined) call comes first. -/
def getRelatedFileRanges {P : PureExpr} [BEq P.Ident] (md: MetaData P) : Array FileRange :=
  md.filterMap fun elem =>
    if elem.fld == Imperative.MetaData.relatedFileRange then
      match elem.value with
      | .provenance p => p.toFileRange
      | _ => none
    else none

/-- Get all related provenances from metadata, in order. -/
private def getRelatedProvenances {P : PureExpr} [BEq P.Ident] (md: MetaData P) : Array Provenance :=
  md.filterMap fun elem =>
    if elem.fld == Imperative.MetaData.relatedFileRange then
      match elem.value with
      | .provenance p => some p
      | _ => none
    else none

/-- Remove all metadata elements with the given field. -/
def MetaData.eraseAllElems {P : PureExpr} [BEq P.Ident]
    (md : MetaData P) (fld : MetaDataElem.Field P) : MetaData P :=
  md.filter (fun e => !(e.fld == fld))

/-- Label for a per-loop-invariant source provenance. Loop lowering stores one
    such element per invariant, in invariant order, so that loop elimination can
    attribute each invariant's verification condition to the specific invariant's
    source location rather than to the whole loop. -/
def MetaData.invariantProvenanceLabel : String := "invariantProvenance"

/-- Append a loop invariant's provenance to metadata. These are appended in
    invariant order. Note this matches on the `.label` constructor directly, so
    it needs no `BEq P.Ident` instance. -/
def MetaData.pushInvariantProvenance {P : PureExpr} (md : MetaData P) (p : Provenance) : MetaData P :=
  md.push { fld := .label MetaData.invariantProvenanceLabel, value := .provenance p }

/-- Get all per-invariant provenances from metadata, in the order they were
    pushed (matching the loop's invariant order). -/
def getInvariantProvenances {P : PureExpr} (md : MetaData P) : Array Provenance :=
  md.filterMap fun elem =>
    match elem.fld, elem.value with
    | .label l, .provenance p =>
      if l == MetaData.invariantProvenanceLabel then some p else none
    | _, _ => none

/-- Replace the primary provenance with a new one, shifting existing related
    provenances and prepending the old primary provenance. -/
def MetaData.setCallSiteFileRange {P : PureExpr} [BEq P.Ident]
    (md : MetaData P) (callSiteRange : MetaData P) : MetaData P :=
  match getProvenance callSiteRange, getProvenance md with
  | some csProv, some origProv =>
    let existingRelated := getRelatedProvenances md
    let md := md.eraseElem MetaData.provenanceField
    let md := md.eraseAllElems MetaData.relatedFileRange
    let md := md.pushElem MetaData.provenanceField (.provenance csProv)
    let md := md.pushElem MetaData.relatedFileRange (.provenance origProv)
    existingRelated.foldl (fun md p => md.pushElem MetaData.relatedFileRange (.provenance p)) md
  | some csProv, none =>
    let md := md.eraseElem MetaData.provenanceField
    md.pushElem MetaData.provenanceField (.provenance csProv)
  | none, _ => md

/-- Metadata field for property type classification (e.g., "divisionByZero"). -/
def MetaData.propertyType : MetaDataElem.Field P := .label "propertyType"

/-- Metadata value for division-by-zero property type classification. -/
def MetaData.divisionByZero : String := "divisionByZero"

/-- Metadata value for arithmetic-overflow property type classification. -/
def MetaData.arithmeticOverflow : String := "arithmeticOverflow"

/-- Metadata value for out-of-bounds-access property type classification. -/
def MetaData.outOfBoundsAccess : String := "outOfBoundsAccess"

/-- Read the property type classification from metadata, if present. -/
def MetaData.getPropertyType {P : PureExpr} [BEq P.Ident] (md : MetaData P) : Option String :=
  match md.findElem MetaData.propertyType with
  | some elem => match elem.value with
    | .msg s => some s
    | _ => none
  | none => none

/-- Metadata field for property summaries attached to assert/requires/ensures clauses. -/
def MetaData.propertySummary : MetaDataElem.Field P := .label "propertySummary"

/-- Read the property summary from metadata, if present. -/
def MetaData.getPropertySummary {P : PureExpr} [BEq P.Ident] (md : MetaData P) : Option String :=
  match md.findElem MetaData.propertySummary with
  | some elem => match elem.value with
    | .msg s => some s
    | _ => none
  | none => none

/-- Push a property summary into metadata. -/
def MetaData.withPropertySummary {P : PureExpr} (md : MetaData P) (msg : String) : MetaData P :=
  md.pushElem MetaData.propertySummary (.msg msg)

---------------------------------------------------------------------

end -- public section
end Imperative
