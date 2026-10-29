/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.Util.SourceRange
public import Strata.Util.FileRange
import all StrataDDM.Util.String
open StrataDDM

public section
namespace Strata.Pipeline

/-- Nanoseconds to milliseconds with rounding. -/
def nsToMs (ns : Nat) : Nat := (ns + 500000) / 1000000

/-- A phase represents a position in the phase hierarchy.
    Top-level phases have a single entry; subphases have multiple.
    Ordering is determined by position in the timing array, not by name. -/
structure Phase where
  path : Array String := #[]
  deriving BEq, DecidableEq, Hashable, Repr, Inhabited

namespace Phase

def base (name : String) : Phase :=
  { path := #[name] }

def pop (p : Phase) : Phase := { path := p.path.pop }

def subphase (parent : Phase) (name : String) : Phase :=
  { path := parent.path.push name }

def depth (p : Phase) : Nat := p.path.size

def leaf (p : Phase) : String :=
  match p.path.back? with
  | some name => name
  | none => "<unknown>"

def display (p : Phase) : String :=
  String.intercalate "." p.path.toList

instance : ToString Phase where
  toString p := p.display

end Phase


/-- How severe / actionable is this message? -/
inductive MessageImpact where
  /-- An unexpected failure that prevented some output from being generated,
      due to a fatal bug in Strata (e.g., a malformed overload entry that was
      skipped). -/
  | internalError
  /-- An unexpected condition that did not prevent output, but may indicate
      a bug in Strata worth investigating. -/
  | internalWarning
  /-- A known, documented limitation in Strata that may cause specs to be
      incomplete or imprecise. -/
  | knownLimitation
  /-- A fatal issue detected in the user source code. -/
  | userCodeError
  /-- A benign issue detected in the user source code. -/
  | userCodeWarning
  /-- The tool was invoked with invalid arguments, or if the argument is a file
      path, the corresponding file or directory doesn't exist or has
      unrecognizable structure. -/
  | configurationError
  deriving BEq, DecidableEq, Hashable, Ord, Repr, Lean.ToExpr

/--
Whether this impact level typically warrants aborting the pipeline.

N.B. Pipeline steps may want a custom abort strategy rather than
relying on this predicate.
-/
def MessageImpact.isFatal : MessageImpact → Bool
  | .internalError => true
  | .userCodeError => true
  | .configurationError => true
  | .internalWarning => false
  | .knownLimitation => false
  | .userCodeWarning => false

instance : ToString MessageImpact where
  toString
    | .internalError => "internalError"
    | .internalWarning => "internalWarning"
    | .knownLimitation => "knownLimitation"
    | .userCodeError => "userCodeError"
    | .userCodeWarning => "userCodeWarning"
    | .configurationError => "configurationError"

/-- A categorized message kind with category and impact.
    The phase is derived from pipeline context at emit time. -/
structure MessageKind where
  category : String
  impact : MessageImpact
  deriving BEq, DecidableEq, Hashable, Ord, Repr, Lean.ToExpr

instance : ToString MessageKind where
  toString mk := mk.category

namespace MessageKind

-- Laurel lowering phase
def laurelLoweringError : MessageKind :=
  { category := "error", impact := .internalError }
def laurelLoweringNotImpl : MessageKind :=
  { category := "notYetImplemented", impact := .knownLimitation }
def laurelLoweringUserError : MessageKind :=
  { category := "userError", impact := .userCodeError }

-- Laurel-to-Core translation phase
def laurelToCoreError : MessageKind :=
  { category := "error", impact := .internalError }

-- Verification phase
def verificationError : MessageKind :=
  { category := "error", impact := .internalError }
def verificationTimeout : MessageKind :=
  { category := "solverTimeout", impact := .knownLimitation }

/-! Generic kinds mirroring the four legacy `DiagnosticType` values. These are
    the default kinds used by the phase-independent `Message` constructors. -/

/-- A benign warning in the user's source or the tool. -/
def warning : MessageKind :=
  { category := "warning", impact := .internalWarning }
/-- A fatal error in the user's source code. -/
def userError : MessageKind :=
  { category := "userError", impact := .userCodeError }
/-- A known, documented limitation (feature not yet implemented). -/
def notYetImplemented : MessageKind :=
  { category := "notYetImplemented", impact := .knownLimitation }
/-- An internal bug in Strata. -/
def strataBug : MessageKind :=
  { category := "error", impact := .internalError }

end MessageKind

/-- A located, categorized message: a source range, a human-readable message
    string, and its kind. This is the phase-independent payload of a
    `PipelineMessage`, and the successor to `Strata.DiagnosticModel` (it carries
    a `MessageKind` in place of `DiagnosticType`). -/
structure Message where
  fileRange : FileRange
  message : String
  kind : MessageKind
  deriving Repr, BEq, Hashable

instance : Inhabited Message where
  default := { fileRange := FileRange.unknown, message := "", kind := MessageKind.userError }

namespace Message

/-- Create a `Message` from just a string (using a default, unknown location).
    Prefer `withRange` when a source location is available. -/
def fromString (msg : String) (kind : MessageKind := .userError) : Message :=
  { fileRange := FileRange.unknown, message := msg, kind }

/-- Create a `Message` from a `Format` (using a default, unknown location).
    Prefer `withRange` when a source location is available. -/
def fromFormat (fmt : Std.Format) (kind : MessageKind := .userError) : Message :=
  { fileRange := FileRange.unknown, message := toString fmt, kind }

/-- Create a `Message` with a source location. -/
def withRange (fr : FileRange) (msg : Std.Format) (kind : MessageKind := .userError) : Message :=
  { fileRange := fr, message := toString msg, kind }

/-- Fill in the location of a `Message` if it is currently unknown. -/
def withRangeIfUnknown (m : Message) (fr : FileRange) : Message :=
  if m.fileRange.range.isNone then { m with fileRange := fr } else m

/-- Format a `Message` using a `FileMap` to convert byte offsets to line/column
    positions. -/
def format (m : Message) (fileMap : Option Lean.FileMap) (includeEnd? : Bool := true) : Std.Format :=
  let rangeStr := m.fileRange.format fileMap includeEnd?
  if rangeStr.isEmpty then f!"{m.message}" else f!"{rangeStr} {m.message}"

/-- Format just the file-range portion of a `Message`. -/
def formatRange (m : Message) (fileMap : Option Lean.FileMap) (includeEnd? : Bool := true) : Std.Format :=
  m.fileRange.format fileMap includeEnd?

end Message

instance : ToString Message where
  toString m := toString (m.format none)

/-- A pipeline message: a `Message` payload stamped with the pipeline `Phase`
    it was emitted in. -/
structure PipelineMessage where
  phase : Phase
  message : Message

namespace PipelineMessage

/-- The message's kind. -/
def kind (m : PipelineMessage) : MessageKind := m.message.kind

/-- The message's source range (file + byte range). -/
def fileRange (m : PipelineMessage) : FileRange := m.message.fileRange

/-- The byte range within the source file. -/
def loc (m : PipelineMessage) : SourceRange := m.message.fileRange.range

/-- The source file path. -/
def file (m : PipelineMessage) : System.FilePath :=
  match m.message.fileRange.file with | .file p => p

end PipelineMessage

instance : ToString PipelineMessage where
  toString m := s!"{m.file}: {m.phase}.{m.kind}: {m.message.message}"

end Strata.Pipeline

/- Re-export the diagnostic types into the `Strata` namespace so existing
   `open Strata (...)` / `Strata.Message` references (formerly `DiagnosticModel`)
   resolve without importing `Strata.Pipeline` explicitly at the use site. -/
namespace Strata
export Strata.Pipeline (Message MessageKind MessageImpact)
end Strata

/- Also re-export the `Message`/`MessageKind` static members so that
   `Message.fromFormat`, `MessageKind.userError`, etc. resolve under
   `open Strata` (dot notation does not redirect through a bare alias). -/
namespace Strata.Message
export Strata.Pipeline.Message
  (fileRange message kind
   fromString fromFormat withRange withRangeIfUnknown format formatRange)
end Strata.Message

namespace Strata.MessageKind
export Strata.Pipeline.MessageKind
  (warning userError notYetImplemented strataBug
   laurelLoweringError laurelLoweringNotImpl laurelLoweringUserError
   laurelToCoreError verificationError verificationTimeout)
end Strata.MessageKind
end
