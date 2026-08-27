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
`GenericDatatypeTest`, `GenericMethodTest`, `PolyProcedureTest`,
`PolymorphicFunctionTest`): each case pairs a Laurel source with its expected `Expect`,
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
  -- How many VCs ended in a TOOLCHAIN ERROR rather than a solver VERDICT: SMT encoding
  -- error / solver crash (`isImplementationError`), solver timeout (`isTimeout`), or an
  -- `.err` SMT property inside an `.ok` outcome (`hasSMTError` — the inner channel that
  -- complements the outer `.error` case). `checkCase` requires this to be 0 for every
  -- outcome: a toolchain error neither witnesses a failure (an encoding crash counts in
  -- `numFailures` yet proves nothing false) nor a pass. The boundary is deliberately
  -- verdict-vs-error, NOT countermodel-vs-rest: `unknown` is a legitimate verdict that
  -- deductive mode rightly reports as failure (e.g. quantified `readField` obligations),
  -- so requiring countermodels-only would misclassify those twins.
  numErrorOutcomes : Nat

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
    | none => return { translated := false, numVCs := 0, numFailures := 0, numErrorOutcomes := 0 }
    | some results =>
      let numFailures := results.foldl (fun acc vcr => if vcr.isNotSuccess then acc + 1 else acc) 0
      let numErrorOutcomes := results.foldl (fun acc vcr =>
        if vcr.isImplementationError || vcr.isTimeout || vcr.hasSMTError then acc + 1 else acc) 0
      return { translated := true, numVCs := results.size, numFailures := numFailures, numErrorOutcomes := numErrorOutcomes }

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
  -- !translated (fails loud). The optional `kind` pins WHICH diagnostic fired: `.userError`
  -- for a clean user rejection vs `.strataBug` for the re-resolution internal-error net, so a
  -- move between the two fails loud. `some k` asserts k is PRESENT, not exclusive — a spurious
  -- extra diagnostic of another kind alongside it still passes; use `.rejectedExactly` when
  -- that matters. `none` keeps the coarse `!translated`-only check.
  | rejected (kind : Option MessageKind := none)
  -- !translated AND every non-warning diagnostic is exactly `kind` (no OTHER kind leaked in).
  -- Catches a spurious cascade piled on the intended rejection — e.g. a divergent generic
  -- that must emit `.notYetImplemented` with NO `.strataBug` folded on top, which a
  -- presence-only `.rejected (some k)` pin would miss.
  | rejectedExactly (kind : MessageKind)

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
  /-- TRANSITIONAL: how many VCs are expected to end in a toolchain error rather than a
      solver verdict, because a prerequisite fix is not on mainline yet.

      Non-zero only while the two Core SMT-encoder fixes are unmerged — "encode a
      polymorphic function's body in its own typeArg scope" and "encode free type variables
      as uninterpreted sorts, soundly". Without them a polymorphic procedure's OWN body VC
      (its `opaque ensures`) cannot be encoded and reports
      `Unimplemented encoding for type var`.

      The count is pinned EXACTLY, not as an upper bound: when the encoder fixes land the
      gap becomes 0 and every case carrying this field fails until the field is removed.
      That is deliberate — it makes the debt self-clearing rather than silently permanent.

      The documented errors are subtracted from `numFailures` before the outcome is
      checked, so the case still pins its real verdict count. A case whose INTENDED
      failing obligation is itself the one that errors pins nothing and must use
      `inertUntilEncoderFix` instead. -/
  knownEncoderErrors : Nat := 0
  /-- TRANSITIONAL: this case's intended failing obligation is *itself* the VC that fails
      to encode, so subtracting the toolchain error leaves no verdict to assert — the case
      currently pins NOTHING about soundness.

      Rather than delete it (losing the case) or let it pass on a count that happens to
      match for the wrong reason (a green test asserting nothing), the check is narrowed to
      what is still true: the program translates and the gap is exactly as documented. The
      soundness property is NOT asserted. Clears with the same encoder fixes as
      `knownEncoderErrors`. -/
  inertUntilEncoderFix : Bool := false

/-- The single assertion point for a corpus case — replaces the repeated
    `let m ← …; unless m.translated && m.numFailures == N do throw …` boilerplate.
    Throws on mismatch (fails the build under `#guard_msgs`). -/
def checkCase (c : Case) : IO Unit := do
  let m ← corpusMetricsOf c.name c.src
  -- The toolchain-error budget is `knownEncoderErrors`, normally 0: a must-fail twin whose
  -- "failure" is really an encoding/solver crash pins nothing (see the `numErrorOutcomes`
  -- docstring for the verdict-vs-error boundary). It is pinned EXACTLY in both directions,
  -- so an unexpected error fails loud AND a documented gap that has been fixed fails until
  -- the annotation is removed.
  let gap := c.knownEncoderErrors
  -- Verdict failures: total failures minus the documented toolchain errors, which are
  -- counted in `numFailures` (`isImplementationError`/`isTimeout` imply `isNotSuccess`).
  -- Nat subtraction saturates at 0, which is the conservative direction.
  let verdictFailures := m.numFailures - gap
  let ok :=
    if c.inertUntilEncoderFix then
      -- Deliberately NOT asserting the soundness property — see `inertUntilEncoderFix`.
      -- Only that the program still translates and the gap is exactly as documented.
      m.translated && m.numErrorOutcomes == gap
    else match c.outcome with
      -- `.verifies` also requires the error budget to be met exactly:
      -- `isImplementationError`/`isTimeout` imply `isNotSuccess` (→ numFailures > 0) so they
      -- can't slip through, but `hasSMTError` can — `isPass` looks only at
      -- `validityProperty = .unsat`, so a passing VC whose SATISFIABILITY sub-check returned
      -- `.err` would otherwise count as a clean verify.
      | .verifies       => m.translated && verdictFailures == 0 && m.numVCs > 0
                             && m.numErrorOutcomes == gap
      | .failsExactly n => m.translated && verdictFailures == n && m.numErrorOutcomes == gap
      | .failsAtLeast n => m.translated && verdictFailures >= n && m.numErrorOutcomes == gap
      | .rejected _     => !m.translated
      | .rejectedExactly _ => !m.translated
  unless ok do
    let inertNote := if c.inertUntilEncoderFix then " [inert until encoder fix]" else ""
    throw (IO.userError s!"{c.name} [expected {c.outcome.descr}]{inertNote}: {c.why} — \
      got translated={m.translated} numVCs={m.numVCs} numFailures={m.numFailures} \
      numErrorOutcomes={m.numErrorOutcomes} (expected exactly {gap})")
  -- A kind-pinned rejection re-runs the capturing path (which carries `.kind`, unlike the
  -- VC-results path) to check the diagnostic kind.
  match c.outcome with
  | .rejected (some expectedKind) =>
    let prog ← corpusParse c.name c.src
    let diags ← verifyToMessagesCapturing prog
    unless diags.any (·.kind == expectedKind) do
      let kinds := diags.map (fun d => s!"{repr d.kind}")
      throw (IO.userError s!"{c.name} [expected {c.outcome.descr}]: {c.why} — \
        no diagnostic of kind {repr expectedKind}; got kinds {kinds}")
  | .rejectedExactly expectedKind =>
    let prog ← corpusParse c.name c.src
    let diags ← verifyToMessagesCapturing prog
    let nonWarning := diags.filter (·.kind != .warning)
    unless nonWarning.any (·.kind == expectedKind) && nonWarning.all (·.kind == expectedKind) do
      let kinds := nonWarning.map (fun d => s!"{repr d.kind}")
      throw (IO.userError s!"{c.name} [expected {c.outcome.descr}]: {c.why} — \
        expected every non-Warning diagnostic to be {repr expectedKind}; got kinds {kinds}")
  | _ => pure ()

/-- Run every case in a feature table. -/
def checkCases (cases : List Case) : IO Unit := cases.forM checkCase

end Strata.Laurel
