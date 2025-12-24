
import Lean.Data.Position

namespace Strata


/-- A diagnostic produced by analyzing a file -/
structure Diagnostic where
  start : Lean.Position
  ending : Lean.Position
  message : String
  deriving Repr, BEq
