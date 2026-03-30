/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Util.SourceRange

public section
namespace Strata.Python.Specs

/-- An error encountered while processing a PySpec file. -/
structure SpecError where
  file : System.FilePath
  loc : SourceRange
  message : String

end Strata.Python.Specs
end
