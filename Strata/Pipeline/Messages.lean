/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Util.SourceRange

public section
namespace Strata.Pipeline

/-- A pipeline phase that produced a message. The `phaseNumber` determines
    the display order so that warnings are printed in pipeline execution order. -/
structure Phase where
  private mk ::
  phaseNumber : Nat
  name : String
  deriving BEq, DecidableEq, Hashable, Ord, Repr

instance : LT Phase where
  lt a b := a.phaseNumber < b.phaseNumber ∨
    (a.phaseNumber == b.phaseNumber ∧ a.name < b.name)

instance (a b : Phase) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.phaseNumber < b.phaseNumber ∨
    (a.phaseNumber == b.phaseNumber ∧ a.name < b.name)))

instance : ToString Phase where
  toString p := p.name

namespace Phase
/-- Resolving dotted module names to PySpec Ion file paths on disk. -/
def moduleResolution : Phase := { phaseNumber := 0, name := "moduleResolution" }
/-- Parsing PySpec Ion files into typed signatures. -/
def pySpecParsing : Phase := { phaseNumber := 1, name := "pySpecParsing" }
/-- Translating PySpec signatures into Laurel declarations. -/
def pySpecToLaurel : Phase := { phaseNumber := 2, name := "pySpecToLaurel" }
/-- Matching call sites in user Python AST to dispatch table entries from
    PySpec `@overload` declarations. -/
def overloadResolution : Phase := { phaseNumber := 3, name := "overloadResolution" }
/-- Laurel-to-Laurel lowering passes (resolution, diamond validation,
    constrained-type elimination, etc.). -/
def laurelLowering : Phase := { phaseNumber := 4, name := "laurelLowering" }
/-- Translating lowered Laurel to Core. -/
def laurelToCore : Phase := { phaseNumber := 5, name := "laurelToCore" }
/-- Core program transforms (type-checking, call elimination, symbolic eval). -/
def coreTransforms : Phase := { phaseNumber := 6, name := "coreTransforms" }
/-- SMT verification (encoding, solving). -/
def verification : Phase := { phaseNumber := 7, name := "verification" }
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
  /-- An issue detected in the user's Python source code. -/
  | userCodeIssue
  /-- The tool was invoked with invalid arguments or the on-disk pyspecs
      are invalid (e.g., missing module, unreadable file). -/
  | configurationError
  deriving BEq, DecidableEq, Hashable, Ord, Repr

/-- Whether this impact level should abort the pipeline. Fatal impacts
    indicate that the pipeline output would be incomplete or incorrect. -/
def MessageImpact.isFatal : MessageImpact → Bool
  | .internalError => true
  | .configurationError => true
  | .internalWarning => false
  | .knownLimitation => false
  | .userCodeIssue => false

instance : ToString MessageImpact where
  toString
    | .internalError => "internalError"
    | .internalWarning => "internalWarning"
    | .knownLimitation => "knownLimitation"
    | .userCodeIssue => "userCodeIssue"
    | .configurationError => "configurationError"

/-- A categorized message kind with phase, category, and impact. -/
structure MessageKind where
  phase : Phase
  category : String
  impact : MessageImpact
  deriving BEq, DecidableEq, Hashable, Ord, Repr

instance : LT MessageKind where
  lt a b := a.phase < b.phase ∨ (a.phase == b.phase ∧ a.category < b.category)

instance (a b : MessageKind) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.phase < b.phase ∨ (a.phase == b.phase ∧ a.category < b.category)))

instance : ToString MessageKind where
  toString mk := s!"{mk.phase}.{mk.category}"

namespace MessageKind

-- Type translation warnings
def unsupportedUnion : MessageKind :=
  { phase := .pySpecToLaurel, category := "unsupportedUnion", impact := .knownLimitation }

-- Unsupported Optional patterns
def unsupportedOptionalFloat : MessageKind :=
  { phase := .pySpecToLaurel, category := "unsupportedOptionalFloat", impact := .knownLimitation }
def unsupportedOptionalList : MessageKind :=
  { phase := .pySpecToLaurel, category := "unsupportedOptionalList", impact := .knownLimitation }
def unsupportedOptionalDict : MessageKind :=
  { phase := .pySpecToLaurel, category := "unsupportedOptionalDict", impact := .knownLimitation }
def unsupportedOptionalAny : MessageKind :=
  { phase := .pySpecToLaurel, category := "unsupportedOptionalAny", impact := .knownLimitation }
def unsupportedOptionalBytes : MessageKind :=
  { phase := .pySpecToLaurel, category := "unsupportedOptionalBytes", impact := .knownLimitation }

-- Internal type errors
def typeError : MessageKind :=
  { phase := .pySpecToLaurel, category := "typeError", impact := .internalWarning }

-- Precondition warnings
def placeholderExpr : MessageKind :=
  { phase := .pySpecToLaurel, category := "placeholderExpr", impact := .knownLimitation }
def floatLiteral : MessageKind :=
  { phase := .pySpecToLaurel, category := "floatLiteral", impact := .knownLimitation }
def isinstanceUnsupported : MessageKind :=
  { phase := .pySpecToLaurel, category := "isinstanceUnsupported", impact := .knownLimitation }
def forallListUnsupported : MessageKind :=
  { phase := .pySpecToLaurel, category := "forallListUnsupported", impact := .knownLimitation }
def forallDictUnsupported : MessageKind :=
  { phase := .pySpecToLaurel, category := "forallDictUnsupported", impact := .knownLimitation }

-- Declaration warnings
def missingMethodSelf : MessageKind :=
  { phase := .pySpecToLaurel, category := "missingMethodSelf", impact := .internalWarning }
def kwargsExpansionError : MessageKind :=
  { phase := .pySpecToLaurel, category := "kwargsExpansionError", impact := .internalWarning }
def postconditionUnsupported : MessageKind :=
  { phase := .pySpecToLaurel, category := "postconditionUnsupported", impact := .knownLimitation }

-- Overload dispatch warnings (in PySpec-to-Laurel phase)
def overloadNoArgs : MessageKind :=
  { phase := .pySpecToLaurel, category := "overloadNoArgs", impact := .internalError }
def overloadArgArity : MessageKind :=
  { phase := .pySpecToLaurel, category := "overloadArgArity", impact := .internalError }
def overloadArgNotStringLiteral : MessageKind :=
  { phase := .pySpecToLaurel, category := "overloadArgNotStringLiteral", impact := .internalError }
def overloadReturnArity : MessageKind :=
  { phase := .pySpecToLaurel, category := "overloadReturnArity", impact := .internalError }
def overloadReturnNotClass : MessageKind :=
  { phase := .pySpecToLaurel, category := "overloadReturnNotClass", impact := .internalError }
def overloadParamNameDisagreement : MessageKind :=
  { phase := .pySpecToLaurel, category := "overloadParamNameDisagreement", impact := .internalError }

-- PySpec parsing phase
def pySpecParsingError : MessageKind :=
  { phase := .pySpecParsing, category := "error", impact := .internalError }
def pySpecParsingWarning : MessageKind :=
  { phase := .pySpecParsing, category := "warning", impact := .knownLimitation }
def pySpecReadError : MessageKind :=
  { phase := .pySpecParsing, category := "readError", impact := .configurationError }

-- PySpec-to-Laurel assembly phase
def functionSignatureError : MessageKind :=
  { phase := .pySpecToLaurel, category := "functionSignatureError", impact := .internalError }
def typeNameCollision : MessageKind :=
  { phase := .pySpecToLaurel, category := "typeNameCollision", impact := .internalError }
def procedureNameCollision : MessageKind :=
  { phase := .pySpecToLaurel, category := "procedureNameCollision", impact := .internalError }

-- Module resolution phase
def invalidModuleName : MessageKind :=
  { phase := .moduleResolution, category := "invalidModuleName", impact := .internalWarning }
def missingAutoResolvedPySpec : MessageKind :=
  { phase := .moduleResolution, category := "missingAutoResolvedPySpec", impact := .knownLimitation }
def missingDispatchModule : MessageKind :=
  { phase := .moduleResolution, category := "missingDispatchModule", impact := .configurationError }
def missingExplicitPySpec : MessageKind :=
  { phase := .moduleResolution, category := "missingExplicitPySpec", impact := .configurationError }

-- Overload resolution phase
def overloadResolveWarning : MessageKind :=
  { phase := .overloadResolution, category := "resolveWarning", impact := .internalWarning }

-- Laurel lowering phase
def laurelLoweringWarning : MessageKind :=
  { phase := .laurelLowering, category := "warning", impact := .internalWarning }
def laurelLoweringError : MessageKind :=
  { phase := .laurelLowering, category := "error", impact := .internalError }
def laurelLoweringNotImpl : MessageKind :=
  { phase := .laurelLowering, category := "notYetImplemented", impact := .knownLimitation }
def laurelLoweringUserError : MessageKind :=
  { phase := .laurelLowering, category := "userError", impact := .userCodeIssue }

-- Laurel-to-Core translation phase
def laurelToCoreWarning : MessageKind :=
  { phase := .laurelToCore, category := "warning", impact := .internalWarning }
def laurelToCoreError : MessageKind :=
  { phase := .laurelToCore, category := "error", impact := .internalError }
def laurelToCoreNotImpl : MessageKind :=
  { phase := .laurelToCore, category := "notYetImplemented", impact := .knownLimitation }
def laurelToCoreUserError : MessageKind :=
  { phase := .laurelToCore, category := "userError", impact := .userCodeIssue }

-- Core transforms phase
def coreTransformWarning : MessageKind :=
  { phase := .coreTransforms, category := "warning", impact := .internalWarning }
def coreTransformError : MessageKind :=
  { phase := .coreTransforms, category := "error", impact := .internalError }
def coreTransformNotImpl : MessageKind :=
  { phase := .coreTransforms, category := "notYetImplemented", impact := .knownLimitation }
def coreTransformUserError : MessageKind :=
  { phase := .coreTransforms, category := "userError", impact := .userCodeIssue }

-- Verification phase
def verificationWarning : MessageKind :=
  { phase := .verification, category := "warning", impact := .internalWarning }
def verificationError : MessageKind :=
  { phase := .verification, category := "error", impact := .internalError }
def verificationTimeout : MessageKind :=
  { phase := .verification, category := "solverTimeout", impact := .knownLimitation }

end MessageKind

/-- A located, categorized pipeline message. -/
structure PipelineMessage where
  file : System.FilePath
  loc : SourceRange
  kind : MessageKind
  message : String

instance : ToString PipelineMessage where
  toString m := s!"{m.file}: {m.kind}: {m.message}"

end Strata.Pipeline
end
