/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.Util.SourceRange

public section
namespace StrataPython.Specs

/-- An error encountered while processing a PySpec file. -/
structure SpecError where
  file : System.FilePath
  loc : StrataDDM.SourceRange
  message : String

end StrataPython.Specs
end
