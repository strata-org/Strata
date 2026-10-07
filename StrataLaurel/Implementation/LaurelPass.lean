/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import StrataLaurel.Implementation.SemanticModel
public import StrataLaurel.Implementation.LaurelNodeKind
public import StrataLaurel.Implementation.Program
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
  /-- Verify coroutines via rely/guarantee.

      NOTE (v1 limitation): on the caller-verification path, `has_next(co)` is
      elaborated as constant `true` (the opaque `resume` summary carries no
      completion information). An obligation of the form `!has_next(co) ==> P`
      therefore discharges *vacuously* — a vacuous pass, not a real proof that
      `P` holds when the coroutine has finished. Proving completion-dependent
      properties across the opaque resume is future work. -/
  verifyCoroutine : Bool := false
  /-- How the transparency pass lowers procedures. Defaults to `Verify`, the
      analyze/verify behavior. See `AnalysisMode`. -/
  analysisMode : AnalysisMode := .Verify
  /-- Type names treated as the gradual/dynamic top type in `isConsistent`.
      Used by language frontends (e.g. Python registers "Any" here). -/
  gradualTypes : Std.HashSet String := {}
  /-- Frontend-supplied realizer for the abstract `Coercion` verdict of the
      proof-relevant subtyping judgment: maps a verdict + the coerced term to a
      rewritten term carrying the concrete box/unbox call. `none` = identity
      (native Laurel inserts no coercion). Threaded onto `TypeLattice`. -/
  realizeCoercion : Option (Coercion → StmtExprMd → StmtExprMd) := none
  /-- Caller truthiness hook (Python str_to_bool/etc.); threaded to TypeLattice.toBool. -/
  toBool : Option (HighType → StmtExprMd → StmtExprMd) := none
  /-- Names reserved by the frontend's coercion machinery (the realizer's box/unbox bridge
      procedures + datatype constructors/accessors). A value binding may not shadow one; see
      `TypeLattice.reservedNames`. Threaded onto `TypeLattice`. Empty for native Laurel. -/
  reservedNames : Std.HashSet String := {}

instance : Inhabited LaurelTranslateOptions where
  default := {}

/-- The four `NodeKind` lists describe the pass's effect on the shapes present
    in the program. Pipeline ordering is *derived* from them rather than declared
    pass-by-pass: `LaurelCompilationPipeline.orderingFailures` folds the live shape set
    over the pipeline and checks each pass's `unsupported` list against it. -/
structure PassMeta where
  /-- Human-readable name, used for profiling and file emission. -/
  name : String
  /-- Whether `resolve` should be run after the pass. -/
  needsResolves : Bool := false
  /-- A description of what this pass does, used for documentation generation. -/
  documentation : String
  /-- Shapes this pass introduces into the program. Disjoint from `removes` and
      from `unsupported`; `orderingAnalysis` rejects a shape declared in both. -/
  creates : List NodeKind := []
  /-- Shapes that are gone from the program after this pass has run. -/
  removes : List NodeKind := []
  /-- Shapes this pass cannot handle, and which must therefore already have been
      removed by the time it runs. -/
  unsupported : List NodeKind := []

/-- A single pass over a `Program`. Each pass receives the current program and
    semantic model and returns the (possibly modified) program, accumulated
    diagnostics, and statistics. -/
structure LaurelPass extends PassMeta where
  /-- The pass action. -/
  run : LaurelTranslateOptions → Program → SemanticModel → Program × List Message × Statistics

/-- The result of a pass given a `Program` constructor it does not run on: the program
    unchanged, with a `.strataBug` diagnostic naming the pass. -/
def wrongProgram (passName : String) (program : Program) : Program × List Message × Statistics :=
  (program, [Message.fromString
    s!"Internal error: pass '{passName}' cannot run on a {program.kind} program" .strataBug], {})

/-- A pass that only runs on `Program.Unordered`. Declares `Program.Ordered` unsupported and
    reports `wrongProgram` on any other IR. -/
def LaurelPass.onUnordered (passMeta : PassMeta)
    (run : LaurelTranslateOptions → LaurelProgram → SemanticModel →
      LaurelProgram × List Message × Statistics) : LaurelPass where
  toPassMeta := { passMeta with unsupported := passMeta.unsupported ++ [NodeKind.Program.Ordered] }
  run := fun opts input model =>
    match input with
    | .Unordered p => let (p', d, s) := run opts p model; (.Unordered p', d, s)
    | other => wrongProgram passMeta.name other

end -- public section

end Strata.Laurel
