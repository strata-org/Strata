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

The `Case`/`checkCase` harness used by the feature corpora (`PolymorphismCorpusTest`,
`DynamicDispatchTest`): each case pairs a Laurel source with its expected verification
`Expect`, asserted at one point (a mismatch throws → fails the build). Verdicts are
derived from the diagnostics/VC-results path (`verifyToMergedResults`) — no evaluator
statistics or cost measurement. No `#eval`s live here: this is pure infrastructure.

- `corpusParse` / `corpusMetricsOf` — parse a Laurel source string and run it to a `CaseResult`.
- `Expect` / `Case` / `checkCase` / `checkCases` — the corpus-case harness.
-/

meta section

open StrataTest.Util
open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-- The verification outcome a corpus case asserts on: did the program translate,
    how many VCs were emitted, and how many failed. Derived entirely from the
    diagnostics/VC-results path (`verifyToMergedResults`, over plain `Core.verify`) —
    no evaluator statistics, so the corpus harness carries no measurement machinery. -/
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

/-- Parse a Laurel source string to a `Program` (shared by the metrics path and
    the established `verifyToDiagnostics` path for the cross-check below). -/
def corpusParse (name : String) (source : String) : IO Program := do
  let input := StrataDDM.Parser.stringInputContext name source
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name input
  let uri := Strata.Uri.file input.fileName
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"{name}: translation errors: {e}")
  | .ok prog => pure prog

/-! ## Corpus case harness

A corpus case pairs a Laurel `src` with its expected verification `Expect`, so the
expected outcome lives in ONE place (the `expect` field) rather than being duplicated
across a test name suffix, an `unless` condition, and a throw message. `checkCase` is the
single assertion point; a mismatch throws (and under `#guard_msgs` that fails the build —
verified by deliberately breaking a case). The `why` is a one-line rationale folded into
the failure message; longer design rationale stays as comments above the relevant table. -/

/-- Expected verification outcome of a corpus program. -/
inductive Expect
  | verifies                 -- translated, numFailures == 0, numVCs > 0 (non-vacuous)
  | failsExactly (n : Nat)   -- translated, numFailures == n (n ≥ 1; the false-twins)
  | failsAtLeast (n : Nat)   -- translated, numFailures ≥ n (e.g. a gated precondition)
  -- !translated (a type error / unsupported shape: fails loud). The optional `kind` pins
  -- WHICH diagnostic kind fired (checked via a 2nd `verifyToDiagnosticModelsCapturing` pass,
  -- since `VerifyMetrics` carries no message). Tag `.UserError` for a clean user rejection,
  -- `.StrataBug` for the re-resolution internal-error net — so any future move BETWEEN the
  -- two fails loud. `none` (default) keeps the coarse `!translated`-only check; a `.rejected`
  -- case left coarse must be authored so its ONLY translation failure is the intended one.
  -- NOTE: `.rejected (some k)` asserts k is PRESENT, not exclusive — a spurious extra
  -- diagnostic of another kind alongside it still passes. Use `.rejectedExactly` when the
  -- rejection must be CLEAN (see below).
  | rejected (kind : Option DiagnosticType := none)
  -- !translated AND every non-Warning diagnostic is exactly `kind` — i.e. no OTHER kind
  -- leaked in. The strict form of `.rejected (some kind)`: it catches a spurious cascade
  -- piled on top of the intended rejection (e.g. a divergent generic that correctly emits
  -- `.NotYetImplemented` but must NOT also fold a `.StrataBug` internal-error on top). Prefer
  -- this for cases where a suppression/cascade regression would otherwise hide behind a
  -- presence-only pin.
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
  -- For a `.rejected` case with an expected diagnostic kind, re-run the capturing path
  -- (which carries `.type`/`.message`, unlike `VerifyMetrics`) and assert that a diagnostic
  -- of the expected kind fired. Distinguishes a clean `.UserError` reject from the
  -- re-resolution `.StrataBug` internal-error net.
  match c.outcome with
  | .rejected (some expectedKind) =>
    let prog ← corpusParse c.name c.src
    let diags ← verifyToDiagnosticModelsCapturing prog
    unless diags.any (·.type == expectedKind) do
      let kinds := diags.map (fun d => s!"{repr d.type}")
      throw (IO.userError s!"{c.name} [expected {c.outcome.descr}]: {c.why} — \
        no diagnostic of kind {repr expectedKind}; got kinds {kinds}")
  | .rejectedExactly expectedKind =>
    -- Every non-Warning diagnostic must be exactly `expectedKind` — no other kind leaked in.
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
