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
# Differential-harness — shared test infrastructure

The measurement core (`VerifyMetrics` per program, via `verifyToMetrics`) plus the
cross-solution diff and the corpus-case harness. Imported by the corpus test files
(`VerifyMetricsCorpusTest` — the harness self-tests; `PolymorphismCorpusTest` — the
feature corpus). No `#eval`s live here: this is pure infrastructure.

- `corpusMetricsOf` / `corpusParse` — parse a Laurel source string and run it.
- `serializeMetrics` / `diffSerialized` — stable text rendering + cross-solution delta.
- `Expect` / `Case` / `checkCase` — the corpus-case harness: each case pairs a source
  with its expected outcome, asserted at one point (a mismatch throws → fails the build).
-/

meta section

open StrataTest.Util
open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-- Parse a Laurel source string (by name) and run `verifyToMetrics`. Takes
    `(name, source)` directly. `VerifyMetricsTest.metricsOf` carries a near-identical
    parse preamble over an `InputContext`; a follow-up could point it here, but it is
    left untouched by this split. -/
def corpusMetricsOf (name : String) (source : String) : IO VerifyMetrics := do
  let input := StrataDDM.Parser.stringInputContext name source
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name input
  let uri := Strata.Uri.file input.fileName
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"{name}: translation errors: {e}")
  | .ok prog => Laurel.verifyToMetrics prog default

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

/-- Core-evaluator stat keys we serialize, in a FIXED order so two runs are
    byte-comparable. HashMap iteration order is unstable, so we never dump all
    keys — we pull this fixed set via `Statistics.get` (0 if absent). -/
def coreStatKeys : List String :=
  [ "Evaluator.verify_numObligations",
    "Evaluator.processIteBranches_diverged",
    "Evaluator.processIteBranches_merged",
    "Evaluator.betweenStmt_capMerged",
    "Evaluator.simulatedStmts" ]

/-- Mode-independent verdict of one obligation outcome. Does NOT use
    `formatOutcome`/`label` (those depend on checkLevel/checkMode). -/
def outcomeVerdict (o : Except Core.VCError Core.VCOutcome) : String :=
  match o with
  | .ok vc => if vc.isPass then "pass" else "fail"
  | .error _ => "error"

/-- Serialize one program's metrics to a stable, sorted, line-oriented block.
    Format (all lines prefixed by the program name for grep/diff):
    ```
    <name> translated <bool>
    <name> numVCs <n>
    <name> numFailures <n>
    <name> vcDischargeMs <n|NA>
    <name> core <statKey> <int>      (one per coreStatKeys, fixed order)
    <name> vc <label> <verdict>      (sorted by label)
    ```
    vcDischargeMs is deliberately the LAST scalar and easy to drop when
    comparing for *correctness* only (timing is noisy; see diff modes). -/
def serializeMetrics (name : String) (m : VerifyMetrics) : String := Id.run do
  let mut lines : Array String := #[]
  lines := lines.push s!"{name} translated {m.translated}"
  lines := lines.push s!"{name} numVCs {m.numVCs}"
  lines := lines.push s!"{name} numFailures {m.numFailures}"
  let ms := match m.vcDischargeMs with | some n => toString n | none => "NA"
  lines := lines.push s!"{name} vcDischargeMs {ms}"
  for k in coreStatKeys do
    lines := lines.push s!"{name} core {k} {m.coreStats.get k}"
  -- verdicts sorted by label for determinism
  let verdicts := m.verdicts.map (fun (l, o) => (l, outcomeVerdict o))
  let sorted := verdicts.qsort (fun a b => a.1 < b.1)
  for (label, v) in sorted do
    lines := lines.push s!"{name} vc {label} {v}"
  return String.intercalate "\n" lines.toList

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
  | rejected (kind : Option DiagnosticType := none)

def Expect.descr : Expect → String
  | .verifies       => "verifies"
  | .failsExactly n => s!"fails ×{n}"
  | .failsAtLeast n => s!"fails ≥{n}"
  | .rejected none       => "rejected"
  | .rejected (some k)   => s!"rejected ({repr k})"

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
  | _ => pure ()

/-- Run every case in a feature table. -/
def checkCases (cases : List Case) : IO Unit := cases.forM checkCase

/-! ## Differ -/

/-- A parsed serialized line: `(programName, restOfLine)`. -/
private def splitLine (line : String) : Option (String × String) :=
  match line.splitOn " " with
  | name :: rest => some (name, String.intercalate " " rest)
  | [] => none

/-- Compare two serialized runs (solution A vs B). `ignoreTiming` drops the
    noisy `vcDischargeMs` line so correctness/structural diffs are deterministic.
    Returns a list of human-readable delta lines; empty = identical. A line
    containing a `vc … pass`→`fail` change is a REGRESSION; `fail`→`pass` a gain.
    Purely textual line-set diff — no re-running. -/
def diffSerialized (solA solB : String) (ignoreTiming : Bool := true) : List String := Id.run do
  -- A line is `<name> <field> …`; drop the `vcDischargeMs` *scalar* line by
  -- matching its field position (the 2nd token), not by token-anywhere.
  let isTimingLine (l : String) : Bool :=
    match l.splitOn " " with
    | _ :: "vcDischargeMs" :: _ => true
    | _ => false
  let norm (s : String) : List String :=
    (s.splitOn "\n").filter (fun l => !l.trim.isEmpty && !(ignoreTiming && isTimingLine l))
  -- Multiset (count-based) diff: a line present k times in A and j in B yields
  -- |k−j| deltas. Robust to duplicate identical lines (which `List.contains`
  -- would mask). Deterministic via sorting the union of keys.
  let count (ls : List String) : Std.HashMap String Nat :=
    ls.foldl (fun m l => m.insert l (m.getD l 0 + 1)) {}
  let cA := count (norm solA)
  let cB := count (norm solB)
  let keys := ((norm solA ++ norm solB).foldl (fun m l => m.insert l ()) (∅ : Std.HashMap String Unit)).toList.map (·.1)
  let mut deltas : Array String := #[]
  for k in keys.toArray.qsort (· < ·) do
    let a := cA.getD k 0
    let b := cB.getD k 0
    if a > b then for _ in [0:a-b] do deltas := deltas.push s!"- {k}"
    if b > a then for _ in [0:b-a] do deltas := deltas.push s!"+ {k}"
  return deltas.toList

end Strata.Laurel
