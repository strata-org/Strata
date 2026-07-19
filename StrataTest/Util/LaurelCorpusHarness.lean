/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataTest.Util.TestDiagnostics
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
meta import StrataDDM.Util.IO
meta import Strata.Languages.Laurel.Grammar.LaurelGrammar
meta import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
meta import Strata.Languages.Laurel.LaurelCompilationPipeline

/-!
# Laurel corpus-case harness — shared test infrastructure

The `Case`/`checkCase` harness used by the feature corpora (`GenericCompositeTest`,
`DynamicDispatchTest`, …): each case pairs a Laurel source with its expected `Expect`,
asserted at one point (a mismatch throws → fails the build under `#guard_msgs`). Verdicts
come from the VC-results path (`verifyToMergedResults`).
-/

meta section

open StrataTest.Util
open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-- The verification outcome a corpus case asserts on: did the program translate,
    how many VCs were emitted, and how many failed. -/
structure CaseResult where
  translated  : Bool
  numVCs      : Nat
  numFailures : Nat

/-- Parse a Laurel source string (by name) and run it, returning the `CaseResult`
    the corpus harness gates on. Uses the merged VC-results path: `translated` iff a
    Core program was produced and verified without a Core-side failure, `numVCs` the
    obligation count, `numFailures` the non-passing obligations. -/
def corpusMetricsOf (name : String) (source : String) : IO CaseResult := do
  let input := StrataDDM.Parser.stringInputContext name source
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name input
  let uri := Strata.Uri.file input.fileName
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"{name}: translation errors: {e}")
  | .ok prog =>
    let (results?, _diags) ← Laurel.verifyToMergedResults prog default
    match results? with
    | none => return { translated := false, numVCs := 0, numFailures := 0 }
    | some results =>
      let numFailures := results.foldl (fun acc vcr => if vcr.isNotSuccess then acc + 1 else acc) 0
      return { translated := true, numVCs := results.size, numFailures := numFailures }

/-- Parse a Laurel source string to a `Program` (used by the kind-checking pass in
    `checkCase`, which needs the program to re-run the diagnostic-capturing path). -/
def corpusParse (name : String) (source : String) : IO Program := do
  let input := StrataDDM.Parser.stringInputContext name source
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name input
  let uri := Strata.Uri.file input.fileName
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"{name}: translation errors: {e}")
  | .ok prog => pure prog

/-! ## Corpus case harness

`checkCase` is the single assertion point: a mismatch throws, which fails the build under
`#guard_msgs`. The `why` is a one-line rationale folded into the failure message; longer
design rationale stays as comments above the relevant table. -/

/-- Expected verification outcome of a corpus program. -/
inductive Expect
  | verifies                 -- translated, numFailures == 0, numVCs > 0 (non-vacuous)
  | failsExactly (n : Nat)   -- translated, numFailures == n (n ≥ 1; the false-twins)
  | failsAtLeast (n : Nat)   -- translated, numFailures ≥ n (e.g. a gated precondition)
  -- !translated (fails loud). The optional `kind` pins WHICH diagnostic fired: `.UserError`
  -- for a clean user rejection vs `.StrataBug` for the re-resolution internal-error net, so a
  -- move between the two fails loud. `some k` asserts k is PRESENT, not exclusive — a spurious
  -- extra diagnostic of another kind alongside it still passes; use `.rejectedExactly` when
  -- that matters. `none` keeps the coarse `!translated`-only check.
  | rejected (kind : Option DiagnosticType := none)
  -- !translated AND every non-Warning diagnostic is exactly `kind` (no OTHER kind leaked in).
  -- Catches a spurious cascade piled on the intended rejection — e.g. a divergent generic
  -- that must emit `.NotYetImplemented` with NO `.StrataBug` folded on top, which a
  -- presence-only `.rejected (some k)` pin would miss.
  | rejectedExactly (kind : DiagnosticType)

def Expect.descr : Expect → String
  | .verifies       => "verifies"
  | .failsExactly n => s!"fails ×{n}"
  | .failsAtLeast n => s!"fails ≥{n}"
  | .rejected none       => "rejected"
  | .rejected (some k)   => s!"rejected ({repr k})"
  | .rejectedExactly k   => s!"rejected (only {repr k})"

/-- One corpus case: a stable `name`, Laurel `src`, expected `outcome`, and a one-line
    `why` (the rationale, surfaced in the failure message). -/
structure Case where
  name    : String
  src     : String
  outcome : Expect
  why     : String := ""

/-- The single assertion point for a corpus case — replaces the repeated
    `let m ← …; unless m.translated && m.numFailures == N do throw …` boilerplate.
    Throws on mismatch (fails the build under `#guard_msgs`). -/
def checkCase (c : Case) : IO Unit := do
  let m ← corpusMetricsOf c.name c.src
  let ok := match c.outcome with
    | .verifies       => m.translated && m.numFailures == 0 && m.numVCs > 0
    | .failsExactly n => m.translated && m.numFailures == n
    | .failsAtLeast n => m.translated && m.numFailures >= n
    | .rejected _     => !m.translated
    | .rejectedExactly _ => !m.translated
  unless ok do
    throw (IO.userError s!"{c.name} [expected {c.outcome.descr}]: {c.why} — \
      got translated={m.translated} numVCs={m.numVCs} numFailures={m.numFailures}")
  -- A kind-pinned rejection re-runs the capturing path (which carries `.type`, unlike the
  -- VC-results path) to check the diagnostic kind.
  match c.outcome with
  | .rejected (some expectedKind) =>
    let prog ← corpusParse c.name c.src
    let diags ← verifyToDiagnosticModelsCapturing prog
    unless diags.any (·.type == expectedKind) do
      let kinds := diags.map (fun d => s!"{repr d.type}")
      throw (IO.userError s!"{c.name} [expected {c.outcome.descr}]: {c.why} — \
        no diagnostic of kind {repr expectedKind}; got kinds {kinds}")
  | .rejectedExactly expectedKind =>
    let prog ← corpusParse c.name c.src
    let diags ← verifyToDiagnosticModelsCapturing prog
    let nonWarning := diags.filter (·.type != .Warning)
    unless nonWarning.any (·.type == expectedKind) && nonWarning.all (·.type == expectedKind) do
      let kinds := nonWarning.map (fun d => s!"{repr d.type}")
      throw (IO.userError s!"{c.name} [expected {c.outcome.descr}]: {c.why} — \
        expected every non-Warning diagnostic to be {repr expectedKind}; got kinds {kinds}")
  | _ => pure ()

/-- Run every case in a feature table. -/
def checkCases (cases : List Case) : IO Unit := cases.forM checkCase

end Strata.Laurel
