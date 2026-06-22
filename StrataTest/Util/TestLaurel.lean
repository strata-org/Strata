/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataDDM.Integration.Lean.HashCommands
import StrataDDM.Elab
import StrataDDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Resolution
import Strata.Languages.Laurel.LaurelCompilationPipeline
import Strata.Languages.Laurel

open Strata
open Strata.Laurel
open StrataDDM (SourcedProgram)

namespace StrataTest.Util

/-- Translate a `StrataDDM.Program` (typically produced by `#strata`) to a Laurel
    `Program`. Used by tests that need to plug in a custom post-translation
    pipeline stage; throws if translation fails. -/
def translateLaurel (program : StrataDDM.Program) : IO Laurel.Program := do
  match Laurel.TransM.run (Strata.Uri.file "<#strata>") (Laurel.parseProgram program) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok laurelProgram => pure laurelProgram

/-- Convert pipeline `DiagnosticModel`s (carrying file-global byte offsets in
    their `FileRange`) into `Diagnostic`s with snippet-local line/col, by
    subtracting `basePos` and looking up in a snippet `FileMap`. -/
private def renderSnippetLocal (basePos : Nat) (snippet : String)
    (dms : Array Strata.DiagnosticModel) : Array Strata.Diagnostic :=
  let fileMap := Lean.FileMap.ofString snippet
  dms.map fun dm =>
    let startB := dm.fileRange.range.start.byteIdx
    let stopB  := dm.fileRange.range.stop.byteIdx
    let startB' : Nat := if startB ≥ basePos then startB - basePos else 0
    let stopB'  : Nat := if stopB  ≥ basePos then stopB  - basePos else 0
    let startPos := fileMap.toPosition ⟨startB'⟩
    let endPos   := fileMap.toPosition ⟨stopB'⟩
    { start := { line := startPos.line, column := startPos.column }
      ending := { line := endPos.line, column := endPos.column }
      message := dm.message
      type := dm.type }

/-- Default options used by `testLaurel` when the caller doesn't override:
    quiet verifier, default solver. Override by passing
    `(options := …)` to `testLaurel`. -/
def defaultLaurelTestOptions : LaurelVerifyOptions :=
  { verifyOptions := .quiet }

/-- Run translate + resolve only on a parsed program. Skips SMT verification.
    Returns diagnostics as `DiagnosticModel`s so the caller can choose how to
    render them (snippet-local for inline annotations, file-global for editor
    navigation). -/
private def runLaurelResolutionRaw (program : StrataDDM.Program) :
    IO (Array Strata.DiagnosticModel) := do
  let uri := Strata.Uri.file "<#strata>"
  match Laurel.TransM.run uri (Laurel.parseProgram program) with
  | .error e =>
    return #[Strata.DiagnosticModel.fromMessage s!"Translation error: {e}"]
  | .ok laurelProgram =>
    let result := Laurel.resolve laurelProgram
    return result.errors

/-- Run the full Laurel pipeline (translate + resolve + verify).
    Returns diagnostics as `DiagnosticModel`s. -/
private def runLaurelPipelineRaw (program : StrataDDM.Program)
    (options : LaurelVerifyOptions) : IO (Array Strata.DiagnosticModel) := do
  let uri := Strata.Uri.file "<#strata>"
  match Laurel.TransM.run uri (Laurel.parseProgram program) with
  | .error e =>
    return #[Strata.DiagnosticModel.fromMessage s!"Translation error: {e}"]
  | .ok laurelProgram =>
    -- Use the *capturing* entry point: a verify-phase type/symbolic error comes
    -- back as a structured `DiagnosticModel` (rather than thrown like the CLI),
    -- so it flows through the same snippet-local `line:col` rendering as every
    -- other diagnostic instead of leaking a raw byte offset in its message.
    Laurel.verifyToDiagnosticModelsCapturing laurelProgram options

/-! ## Inline-annotation matcher

Negative tests embed `// ^^^^^^ <kind>: <message>` annotations directly in the
source of a `#strata` block. Each annotation pins one expected diagnostic to
the line above it. Example:

```
#strata
program Laurel;
procedure foo() opaque {
  var x: int := 1;
  var y: x := 2
//       ^ error: 'x' resolves to variable, but expected ...
};
#end
```

The `testLaurel` / `testLaurelResolution` helpers parse these
annotations from the snippet, run the pipeline, and assert exact match
between actual diagnostics and annotations: every diagnostic must have an
annotation, every annotation must fire, positions must match exactly,
and the actual message must contain the annotation text as a substring.
-/

/-- One expected diagnostic parsed from a `// ^^^ <kind>: <message>` comment. -/
private structure DiagnosticAnnotation where
  /-- 1-indexed line within the snippet that the diagnostic applies to. -/
  line : Nat
  /-- 0-indexed column of first caret. -/
  colStart : Nat
  /-- 0-indexed column past the last caret. -/
  colEnd : Nat
  /-- Diagnostic kind: "error", "warning", "not-yet-implemented", "strata-bug". -/
  kind : String
  /-- Substring expected to appear in the diagnostic message. -/
  message : String

/-- Render the `kind` of a `Diagnostic` to the string used in annotations. -/
private def diagnosticKindString (t : Strata.DiagnosticType) : String :=
  match t with
  | .Warning => "warning"
  | .UserError => "error"
  | .NotYetImplemented => "not-yet-implemented"
  | .StrataBug => "strata-bug"

/-! ## Unified reporting normal form

Actual diagnostics (`Strata.Diagnostic`) and expected annotations
(`DiagnosticAnnotation`) are two views of the *same* thing — a kinded message
pinned to a `line:col` range. They are compared against each other and printed
side-by-side in mismatch reports, so they MUST share one coordinate system and
one layout. Rather than keep two parallel formatters in sync by discipline
(they drifted once — actuals went file-relative while expecteds stayed
snippet-local), both project into a single `LocatedMessage` and flow through
the *one* `render` / `matches` below. There is no other way to format or
compare a located message, so the two views cannot diverge again. -/

/-- The common normal form: a kinded, located message in **snippet-local**
    coordinates (1-indexed line, 0-indexed columns), the system both
    `Strata.Diagnostic` and `DiagnosticAnnotation` natively use. `message` is
    the substring to match (when this is an expected annotation) or the full
    diagnostic text (when this is an actual diagnostic). -/
private structure LocatedMessage where
  line : Nat
  colStart : Nat
  colEnd : Nat
  kind : String
  message : String

/-- View an actual pipeline `Diagnostic` as a `LocatedMessage`. -/
private def LocatedMessage.ofDiagnostic (d : Strata.Diagnostic) : LocatedMessage :=
  { line := d.start.line, colStart := d.start.column, colEnd := d.ending.column
    kind := diagnosticKindString d.type, message := d.message }

/-- View an expected `DiagnosticAnnotation` as a `LocatedMessage`. -/
private def LocatedMessage.ofAnnotation (a : DiagnosticAnnotation) : LocatedMessage :=
  { line := a.line, colStart := a.colStart, colEnd := a.colEnd
    kind := a.kind, message := a.message }

/-- The single renderer for any located message — used for BOTH the
    "actual diagnostics" and "expected (annotated)" halves of every report, so
    the two are always in the same coordinate system and layout.

    Prints the **file-relative** `line:col` range (snippet line `L` is file line
    `block.baseLine + L - 1`; columns coincide). The filename is intentionally
    omitted: the Lean test runner already reports which file a diagnostic came
    from, and dropping it keeps `#guard_msgs` goldens stable regardless of how
    the file was opened. With `showSnippet := true` the snippet-relative range
    is appended in parens — useful for correlating against inline `// ^^^`
    annotations, which are snippet-local.

    Format: `<fileLine>:<colStart>-<colEnd>  <kind>: <message>`, or with
    `showSnippet`:
    `<fileLine>:<colStart>-<colEnd> (snippet <line>:<colStart>-<colEnd>)  <kind>: <message>` -/
private def LocatedMessage.render (block : SourcedProgram) (m : LocatedMessage)
    (showSnippet : Bool := false) : String :=
  let fileLine := block.baseLine + m.line - 1
  let snippet := if showSnippet then
      s!" (snippet {m.line}:{m.colStart}-{m.colEnd})"
    else ""
  s!"{fileLine}:{m.colStart}-{m.colEnd}{snippet}  {m.kind}: {m.message}"

/-- Format an actual `Diagnostic` for reporting. Thin wrapper over
    `LocatedMessage.render` so callers don't project by hand. -/
def formatDiagnostic (block : SourcedProgram) (d : Strata.Diagnostic)
    (showSnippet : Bool := false) : String :=
  (LocatedMessage.ofDiagnostic d).render block showSnippet

/-- Number of leading whitespace characters (`' '` or `'\t'`) in a list. -/
private def leadingWhitespace (cs : List Char) : Nat :=
  (cs.takeWhile (fun c => c == ' ' || c == '\t')).length

private def listStartsWith (xs : List Char) (prefix_ : String) : Bool :=
  let p := prefix_.toList
  p.length ≤ xs.length && (xs.take p.length) == p

/-- Parse `// ^^^^ <kind>: <message>` annotations out of a snippet. The
    annotation lives on the line *after* the offending source line. Lines
    are returned 1-indexed (matching `Lean.Position.line`). -/
private def parseAnnotations (snippet : String) : Array DiagnosticAnnotation := Id.run do
  let lineLists : Array (List Char) :=
    ((snippet.splitOn "\n").map String.toList).toArray
  let mut annotations : Array DiagnosticAnnotation := #[]
  for i in [0:lineLists.size] do
    let chars : List Char := lineLists[i]!
    let leadWs := leadingWhitespace chars
    let body : List Char := chars.drop leadWs
    unless listStartsWith body "//" do continue
    -- Past the `//`: any non-caret prefix (typically spaces), then carets, then
    -- optional whitespace, then `<kind>: <message>`.
    let afterMarker : List Char := body.drop 2
    let preCarets : List Char := afterMarker.takeWhile (· != '^')
    let carets : List Char :=
      (afterMarker.drop preCarets.length).takeWhile (· == '^')
    if carets.isEmpty then continue
    let trailing : List Char :=
      (afterMarker.drop (preCarets.length + carets.length)).dropWhile
        (fun c => c == ' ' || c == '\t')
    let some colonIdx := trailing.findIdx? (· == ':')
      | continue
    let kind := (String.ofList (trailing.take colonIdx)).trimAscii.toString
    let message := (String.ofList (trailing.drop (colonIdx + 1))).trimAscii.toString
    -- Caret columns: leadWs + 2 (for `//`) + offset of first caret.
    let colStart := leadWs + 2 + preCarets.length
    let colEnd := colStart + carets.length
    -- Diagnostic applies to the *previous* non-comment, non-blank line.
    let mut target := i
    let mut found := false
    while target > 0 && !found do
      target := target - 1
      let prev : List Char := lineLists[target]!
      let prevWs := leadingWhitespace prev
      let prevBody : List Char := prev.drop prevWs
      if listStartsWith prevBody "//" || prevBody.isEmpty then continue
      found := true
    unless found do continue
    annotations := annotations.push {
      line := target + 1, colStart, colEnd, kind, message
    }
  pure annotations

/-- Substring containment on `String`. Direct rather than the
    `(d.splitOn a).length > 1` trick. -/
private def isSubstrOf (needle haystack : String) : Bool :=
  !needle.isEmpty && (haystack.splitOn needle).length > 1

/-- Does an actual diagnostic satisfy an expected annotation? Both are viewed
    as `LocatedMessage`s and compared in the shared snippet-local coordinate
    system: start line and the full column range must agree exactly, kinds must
    be equal, and the expected `message` must appear as a substring of the
    actual one (real messages carry volatile detail — unique-id suffixes, full
    types — so we pin only the stable fragment). The diagnostic's *ending* line
    is intentionally not constrained, so a future multi-line diagnostic doesn't
    silently fail to match. -/
private def LocatedMessage.matches (actual expected : LocatedMessage) : Bool :=
  actual.line == expected.line
    && actual.colStart == expected.colStart
    && actual.colEnd == expected.colEnd
    && actual.kind == expected.kind
    && isSubstrOf expected.message actual.message

/-- Format a single annotation for reporting. Thin wrapper over
    `LocatedMessage.render` — the SAME renderer used for actual diagnostics, so
    the "expected (annotated)" and "actual diagnostic" halves of a mismatch
    report are always in the same coordinate system and layout. -/
private def formatAnnotation (block : SourcedProgram) (a : DiagnosticAnnotation)
    (showSnippet : Bool := false) : String :=
  (LocatedMessage.ofAnnotation a).render block showSnippet

/-- Drive a `SourcedProgram` against its inline annotations.

    - If the snippet contains no annotations, succeeds iff the pipeline
      produces no diagnostics and prints `ok`.
    - Otherwise asserts an exact match: every diagnostic must be annotated,
      every annotation must fire. Throws on mismatch. -/
private def runAndCheck (block : SourcedProgram)
    (run : StrataDDM.Program → IO (Array Strata.DiagnosticModel))
    (showSnippet : Bool := false) : IO Unit := do
  let annotations := parseAnnotations block.source
  let dms ← run block.program
  let actual := renderSnippetLocal block.basePos block.source dms
  -- Echo each diagnostic's file-relative `line:col` (computed from the snippet's
  -- `baseLine`, no manual offsets) so the localization is always visible — and a
  -- `#guard_msgs` golden can pin it. The annotation matching below still runs, so
  -- the test asserts correctness rather than just printing. `showSnippet` adds
  -- the snippet-relative range for correlating against inline `// ^^^` markers.
  for d in actual do
    IO.println (formatDiagnostic block d showSnippet)
  if annotations.isEmpty then
    unless actual.isEmpty do
      let mut report := s!"expected no diagnostics, got {actual.size}:\n"
      for d in actual do
        report := report ++ s!"  {formatDiagnostic block d showSnippet}\n"
      throw <| IO.userError report
    return
  -- Pair up: every actual diagnostic must match exactly one annotation.
  let mut unmatchedDiags : Array Strata.Diagnostic := #[]
  let mut matchedAnnotationIdxs : Array Nat := #[]
  for d in actual do
    let mut matchIdx? : Option Nat := none
    for h : i in [0:annotations.size] do
      let a := annotations[i]
      if !matchedAnnotationIdxs.contains i
          && (LocatedMessage.ofDiagnostic d).matches (LocatedMessage.ofAnnotation a) then
        matchIdx? := some i
        break
    match matchIdx? with
    | some i => matchedAnnotationIdxs := matchedAnnotationIdxs.push i
    | none => unmatchedDiags := unmatchedDiags.push d
  let mut unmatchedAnnotations : Array DiagnosticAnnotation := #[]
  for h : i in [0:annotations.size] do
    if !matchedAnnotationIdxs.contains i then
      unmatchedAnnotations := unmatchedAnnotations.push annotations[i]
  if unmatchedDiags.isEmpty && unmatchedAnnotations.isEmpty then return
  let mut report := s!"diagnostics did not match annotations\n"
  if !unmatchedAnnotations.isEmpty then
    report := report ++ s!"\nExpected (annotated) but never fired:\n"
    for a in unmatchedAnnotations do
      report := report ++ s!"  {formatAnnotation block a showSnippet}\n"
  if !unmatchedDiags.isEmpty then
    report := report ++ s!"\nActual diagnostics with no matching annotation:\n"
    for d in unmatchedDiags do
      report := report ++ s!"  {formatDiagnostic block d showSnippet}\n"
  throw <| IO.userError report

/-- Run the full Laurel pipeline (translate + resolve + verify) on a
    `#strata`-parsed program. If the snippet has inline `// ^^^ kind: message`
    annotations, asserts an exact match; otherwise expects no diagnostics.

    `options` defaults to `defaultLaurelTestOptions` (quiet verifier, default
    solver). Pass an explicit value to override the solver, timeout, etc. — for
    example, `(options := { verifyOptions := { .quiet with solver := "z3" } })`.

    Each diagnostic's file-relative `line:col` range is always printed. Set
    `showSnippet := true` to also append the snippet-relative range — useful for
    correlating against the inline `// ^^^` annotations, which are
    snippet-local. -/
def testLaurel (block : SourcedProgram)
    (options : LaurelVerifyOptions := defaultLaurelTestOptions)
    (showSnippet : Bool := false) : IO Unit :=
  runAndCheck block (runLaurelPipelineRaw · options) showSnippet

/-- Path to the directory for intermediate files, inside the build directory.
    Resolved from the current working directory so it works on any machine. -/
def buildDir : IO String := do
  let cwd ← IO.currentDir
  return s!"{cwd}/.lake/build/intermediatePrograms/"

def testLaurelKeepIntermediates (block : SourcedProgram) : IO Unit := do
  let dir ← buildDir
  runAndCheck block (runLaurelPipelineRaw · { translateOptions := { keepAllFilesPrefix := dir}})

/-- Like `testLaurel` but skips SMT verification (translate + resolve only).
    Use when the test only cares about resolution, not the verifier — e.g.
    "shadowing in nested blocks is OK", or asserting a specific resolution
    error without the verifier surfacing unrelated noise.

    As with `testLaurel`, each diagnostic's file-relative `line:col` range is
    printed; `showSnippet := true` appends the snippet-relative range. -/
def testLaurelResolution (block : SourcedProgram)
    (showSnippet : Bool := false) : IO Unit :=
  runAndCheck block runLaurelResolutionRaw showSnippet

end StrataTest.Util
