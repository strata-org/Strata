/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.Util.SourceRange
import all StrataDDM.Util.String

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
  /-- An unexpected failure that prevented some output from being generated
      (e.g., a malformed overload entry that was skipped). -/
  | internalError
  /-- An unexpected condition that did not prevent output, but may indicate
      a tool bug worth investigating. -/
  | internalWarning
  /-- A known, documented limitation that may cause specs to be incomplete
      or imprecise. -/
  | knownLimitation
  /-- An issue detected in the user source code. -/
  | userCodeIssue
  /-- The tool was invoked with invalid arguments or the on-disk pyspecs
      are invalid (e.g., missing module, unreadable file). -/
  | configurationError
  deriving BEq, DecidableEq, Hashable, Ord, Repr

/--
Whether this impact level typically warrants aborting the pipeline.

N.B. Pipeline steps may want a custom abort strategy rather than
relying on this predicate.
-/
def MessageImpact.isFatal : MessageImpact → Bool
  | .internalError => true
  | .configurationError => true
  | .internalWarning => false
  | .knownLimitation => false
  | .userCodeIssue => true

instance : ToString MessageImpact where
  toString
    | .internalError => "internalError"
    | .internalWarning => "internalWarning"
    | .knownLimitation => "knownLimitation"
    | .userCodeIssue => "userCodeIssue"
    | .configurationError => "configurationError"

/-- A categorized message kind with category and impact.
    The phase is derived from pipeline context at emit time. -/
structure MessageKind where
  category : String
  impact : MessageImpact
  deriving BEq, DecidableEq, Hashable, Ord, Repr

instance : ToString MessageKind where
  toString mk := mk.category

namespace MessageKind

-- Laurel lowering phase
def laurelLoweringError : MessageKind :=
  { category := "error", impact := .internalError }
def laurelLoweringNotImpl : MessageKind :=
  { category := "notYetImplemented", impact := .knownLimitation }
def laurelLoweringUserError : MessageKind :=
  { category := "userError", impact := .userCodeIssue }

-- Laurel-to-Core translation phase
def laurelToCoreError : MessageKind :=
  { category := "error", impact := .internalError }

-- Verification phase
def verificationError : MessageKind :=
  { category := "error", impact := .internalError }
def verificationTimeout : MessageKind :=
  { category := "solverTimeout", impact := .knownLimitation }

end MessageKind

/-- A located, categorized pipeline message. -/
structure PipelineMessage where
  file : System.FilePath
  loc : SourceRange
  phase : Phase
  kind : MessageKind
  message : String

instance : ToString PipelineMessage where
  toString m := s!"{m.file}: {m.phase}.{m.kind}: {m.message}"

end Strata.Pipeline
end
