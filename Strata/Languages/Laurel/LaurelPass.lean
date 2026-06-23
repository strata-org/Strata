/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.SemanticModel
public import Strata.Util.Statistics
public import Strata.Languages.Core.Options

namespace Strata.Laurel

public section

/-- Options controlling Laurel-to-Core translation, threaded into every pass's `run`. -/
structure LaurelTranslateOptions where
  inlineFunctionsWhenPossible : Bool := false
  overflowChecks : Core.OverflowChecks := {}
  /-- Quantifier-free modifies frame for single-reference clauses. Set-valued entries
      keep the quantified frame. Use with the verifier's `useArrayTheory`. -/
  enumeratedModifiesClauses : Bool := false
  keepAllFilesPrefix : Option String := none

instance : Inhabited LaurelTranslateOptions where
  default := {}

mutual
structure ComesBefore where
  pass : LaurelPass
  reason: String

/-- A single Laurel-to-Laurel pass. Each pass receives the current program and
    semantic model and returns the (possibly modified) program, accumulated
    diagnostics, and statistics. -/
structure LaurelPass where
  /-- Human-readable name, used for profiling and file emission. -/
  name : String
  /-- Whether `resolve` should be run after the pass. -/
  needsResolves : Bool := false
  /-- The pass action; `options` carries the translate settings (e.g. the modifies-frame choice). -/
  run : LaurelTranslateOptions → Program → SemanticModel → Program × List DiagnosticModel × Statistics
  /-- A description of what this pass does, used for documentation generation. -/
  documentation : String
  comesBefore : List ComesBefore := []
end

end -- public section

end Strata.Laurel
