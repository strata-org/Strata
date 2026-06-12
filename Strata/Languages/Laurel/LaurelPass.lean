/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.SemanticModel
public import Strata.Util.Statistics

namespace Strata.Laurel

public section

structure PassDependency where
  passName : String
  reason: String

/-- A single Laurel-to-Laurel pass. Each pass receives the current program and
    semantic model and returns the (possibly modified) program, accumulated
    diagnostics, and statistics. -/
structure LaurelPass (Input: Type) (Output: Type) where
  /-- Human-readable name, used for profiling and file emission. -/
  name : String
  /-- Whether `resolve` should be run after the pass. -/
  needsResolves : Bool := false
  /-- The pass action. -/
  run : Input → SemanticModel → Output × List DiagnosticModel × Statistics
  /-- A description of what this pass does, used for documentation generation. -/
  documentation : String
  comesBefore : List PassDependency := []
  comesAfter : List PassDependency := []

abbrev LoweringPass := LaurelPass Laurel.Program Laurel.Program

end -- public section

end Strata.Laurel
