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

structure LaurelTranslateOptions where
  inlineFunctionsWhenPossible : Bool := false
  overflowChecks : Core.OverflowChecks := {}
  keepAllFilesPrefix : Option String := none
  /-- Names to pre-register as `.unresolved` before resolution. Used by language
      frontends to inject unmodeled external names without patching the resolver. -/
  externalNames : Std.HashSet String := {}
  /-- Type names treated as the gradual/dynamic top type in `isConsistent`.
      Used by language frontends (e.g. Python registers "Any" here). -/
  gradualTypes : Std.HashSet String := {}
  /-- Frontend-supplied realizer for the abstract `Coercion` verdict of the
      proof-relevant subtyping judgment: maps a verdict + the coerced term to a
      rewritten term carrying the concrete box/unbox call. `none` = identity
      (native Laurel inserts no coercion). Threaded onto `TypeLattice`. -/
  realizeCoercion : Option (Coercion → StmtExprMd → StmtExprMd) := none
  /-- Frontend-supplied truthiness coercion for boolean context (`if`/`while`/
      `assert`/`assume`/bool-ops): term + its synthesized type → to-bool-wrapped
      term. `none` = identity. Threaded onto `TypeLattice`. -/
  toBool : Option (StmtExprMd → HighType → StmtExprMd) := none

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
  run : Input → SemanticModel → LaurelTranslateOptions → Output × List DiagnosticModel × Statistics

abbrev LoweringPass := LaurelPass Laurel.Program Laurel.Program

/-- Project a `LaurelPass` to its parameter-free metadata, discarding the
    `run` action and the `Input`/`Output` type parameters. -/
abbrev LaurelPass.meta {Input Output : Type} (p : LaurelPass Input Output) : PassMeta :=
  p.toPassMeta

end -- public section

end Strata.Laurel
