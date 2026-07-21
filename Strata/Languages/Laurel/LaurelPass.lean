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

/-- Selects how the transparency pass lowers procedures for a given analysis.

    - `Execute`: skip the transparency pass entirely. No `$asFunction` twins,
      no free postconditions, and no call redirection are produced. Genuine
      functions/externals are still emitted, but procedure calls stay procedure
      calls, which concrete interpretation requires — redirecting a call to a
      pure twin would drop its imperative meaning.
    - `Verify`: redirect calls to single-output procedures to their pure
      `$asFunction` twin so they remain constant-foldable during symbolic
      evaluation (avoiding the term blowup that occurs when each call produces a
      fresh symbolic output via the procedural twin). Since callers never
      observe the procedural output, the free postconditions that equate a
      procedure to its twin are omitted.
    - `BothSuboptimally`: generate the twins and the free postconditions tying
      each procedure to its twin, but leave call sites alone (procedure calls
      stay procedure calls, function calls stay function calls). More
      conservative than `Verify` at the cost of fresh symbolic outputs per call.

    Multi-output procedures are never redirected regardless of mode, since a
    single function application cannot fill multiple assignment targets. -/
inductive AnalysisMode where
  | Execute | Verify | BothSuboptimally
  deriving BEq

structure LaurelTranslateOptions where
  inlineFunctionsWhenPossible : Bool := false
  overflowChecks : Core.OverflowChecks := {}
  /-- Quantifier-free modifies frame for single-reference clauses. Set-valued entries
      keep the quantified frame. If the procedure's modifies clause contains sets,
      this option has no effect. Use with the verifier's `useArrayTheory`. -/
  enumeratedModifiesClauses : Bool := false
  keepAllFilesPrefix : Option String := none
  /-- How the transparency pass lowers procedures. Defaults to `Verify`, the
      analyze/verify behavior. See `AnalysisMode`. -/
  analysisMode : AnalysisMode := .Verify

instance : Inhabited LaurelTranslateOptions where
  default := {}

mutual

/-- The parameter-free metadata of a pass, independent of the `Input`/`Output`
    types it operates on. `LaurelPass` extends this so that passes with
    different parameterizations (e.g. `LaurelPass Program Program` and
    `LaurelPass UnorderedCoreWithLaurelTypes UnorderedCoreWithLaurelTypes`)
    share a common, type-parameter-free view that can be collected into a
    single homogeneous list. -/
structure PassMeta where
  /-- Human-readable name, used for profiling and file emission. -/
  name : String
  /-- Whether `resolve` should be run after the pass. -/
  needsResolves : Bool := false
  /-- A description of what this pass does, used for documentation generation. -/
  documentation : String
  /-- Passes that must run before this one. -/
  comesBefore : List PassDependency := []
  /-- Passes that must run after this one. -/
  comesAfter : List PassDependency := []

structure PassDependency where
  pass : PassMeta
  reason: String
end

/-- A single Laurel-to-Laurel pass. Each pass receives the current program and
    semantic model and returns the (possibly modified) program, accumulated
    diagnostics, and statistics. Extends `PassMeta` with the `run` action; the
    metadata fields remain directly accessible (e.g. `p.name`). -/
structure LaurelPass (Input: Type) (Output: Type) extends PassMeta where
  /-- The pass action. -/
  run : LaurelTranslateOptions → Input → SemanticModel → Output × List DiagnosticModel × Statistics

abbrev LoweringPass := LaurelPass Laurel.Program Laurel.Program

/-- Project a `LaurelPass` to its parameter-free metadata, discarding the
    `run` action and the `Input`/`Output` type parameters. -/
abbrev LaurelPass.meta {Input Output : Type} (p : LaurelPass Input Output) : PassMeta :=
  p.toPassMeta

end -- public section

end Strata.Laurel
