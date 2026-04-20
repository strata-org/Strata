/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Util.SourceRange

public section
namespace Strata.Python.Specs

/-- A warning category for PySpec translation.
    Uses an open vocabulary (string fields) so new categories can be added
    without modifying an inductive type. -/
structure WarningKind where
  phase : String
  category : String
  deriving BEq, DecidableEq, Hashable, Ord, Repr

instance : LT WarningKind where
  lt a b := a.phase < b.phase ∨ (a.phase == b.phase ∧ a.category < b.category)

instance (a b : WarningKind) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.phase < b.phase ∨ (a.phase == b.phase ∧ a.category < b.category)))

namespace WarningKind

-- Type translation warnings
def emptyType : WarningKind := { phase := "pySpecToLaurel", category := "emptyType" }
def unsupportedUnion : WarningKind := { phase := "pySpecToLaurel", category := "unsupportedUnion" }

-- Unsupported Optional patterns
def unsupportedOptionalFloat : WarningKind := { phase := "pySpecToLaurel", category := "unsupportedOptionalFloat" }
def unsupportedOptionalList : WarningKind := { phase := "pySpecToLaurel", category := "unsupportedOptionalList" }
def unsupportedOptionalDict : WarningKind := { phase := "pySpecToLaurel", category := "unsupportedOptionalDict" }
def unsupportedOptionalAny : WarningKind := { phase := "pySpecToLaurel", category := "unsupportedOptionalAny" }
def unsupportedOptionalBytes : WarningKind := { phase := "pySpecToLaurel", category := "unsupportedOptionalBytes" }

-- Internal type errors
def typeError : WarningKind := { phase := "pySpecToLaurel", category := "typeError" }

-- Precondition warnings
def placeholderExpr : WarningKind := { phase := "pySpecToLaurel", category := "placeholderExpr" }
def floatLiteral : WarningKind := { phase := "pySpecToLaurel", category := "floatLiteral" }
def isinstanceUnsupported : WarningKind := { phase := "pySpecToLaurel", category := "isinstanceUnsupported" }
def forallListUnsupported : WarningKind := { phase := "pySpecToLaurel", category := "forallListUnsupported" }
def forallDictUnsupported : WarningKind := { phase := "pySpecToLaurel", category := "forallDictUnsupported" }

-- Declaration warnings
def missingMethodSelf : WarningKind := { phase := "pySpecToLaurel", category := "missingMethodSelf" }
def kwargsExpansionError : WarningKind := { phase := "pySpecToLaurel", category := "kwargsExpansionError" }
def postconditionUnsupported : WarningKind := { phase := "pySpecToLaurel", category := "postconditionUnsupported" }

-- Overload dispatch warnings
def overloadNoArgs : WarningKind := { phase := "pySpecToLaurel", category := "overloadNoArgs" }
def overloadArgArity : WarningKind := { phase := "pySpecToLaurel", category := "overloadArgArity" }
def overloadArgNotStringLiteral : WarningKind := { phase := "pySpecToLaurel", category := "overloadArgNotStringLiteral" }
def overloadReturnArity : WarningKind := { phase := "pySpecToLaurel", category := "overloadReturnArity" }
def overloadReturnNotClass : WarningKind := { phase := "pySpecToLaurel", category := "overloadReturnNotClass" }

-- PySpec parsing phase (generic — callers don't yet distinguish categories)
def pySpecParsingError : WarningKind := { phase := "pySpecParsing", category := "error" }
def pySpecParsingWarning : WarningKind := { phase := "pySpecParsing", category := "warning" }

end WarningKind

/-- An error encountered while processing a PySpec file. -/
structure SpecError where
  file : System.FilePath
  loc : SourceRange
  kind : WarningKind
  message : String

end Strata.Python.Specs
end
