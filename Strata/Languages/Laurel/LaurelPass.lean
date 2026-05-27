/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Resolution
public import Strata.Util.Statistics

namespace Strata.Laurel

public section

mutual
structure ComesBefore where
  name : LaurelPass
  reason: String

/-- A single Laurel-to-Laurel pass. Each pass receives the current program and
    semantic model and returns the (possibly modified) program, accumulated
    diagnostics, and statistics. -/
structure LaurelPass where
  /-- Human-readable name, used for profiling and file emission. -/
  name : String
  /-- Whether `resolve` should be run after the pass. -/
  needsResolves : Bool := false
  /-- The pass action. -/
  run : Program → SemanticModel → Program × List DiagnosticModel × Statistics
  /-- A description of what this pass does, used for documentation generation. -/
  documentation : String
  comesBefore : List ComesBefore := []
end

end -- public section

end Strata.Laurel
