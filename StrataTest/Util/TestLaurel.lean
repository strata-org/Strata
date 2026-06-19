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

/-- Pretty-print a `Diagnostic` for error reporting, prefixed with its
    **file-relative** `line:col` range — anchored to the enclosing `.lean`
    source rather than the `#strata` snippet. A snippet line `L` is file line
    `block.baseLine + L - 1` (`baseLine` is the file line of the snippet's first
    line); columns coincide. The filename is intentionally omitted: the Lean
    test runner already reports which file a diagnostic came from, and dropping
    it keeps `#guard_msgs` goldens stable regardless of how the file was opened.

    With `showSnippet := true`, the snippet-relative `line:col` range is also
    shown in parentheses — useful when correlating against inline `// ^^^`
    annotations, which are snippet-local. It is off by default so goldens show
    only the file-relative location.

    Format: `<fileLine>:<colStart>-<colEnd>  <kind>: <message>`,
    or with `showSnippet`:
    `<fileLine>:<colStart>-<colEnd> (snippet <line>:<colStart>-<colEnd>)  <kind>: <message>` -/
def formatDiagnostic (block : SourcedProgram) (d : Strata.Diagnostic)
    (showSnippet : Bool := false) : String :=
  let kind := match d.type with
    | .Warning => "warning"
    | .UserError => "error"
    | .NotYetImplemented => "not-yet-implemented"
    | .StrataBug => "strata-bug"
  let fileLine := block.baseLine + d.start.line - 1
  let snippet := if showSnippet then
      s!" (snippet {d.start.line}:{d.start.column}-{d.ending.column})"
    else ""
  s!"{fileLine}:{d.start.column}-{d.ending.column}{snippet}  {kind}: {d.message}"

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

/-- Try to match an annotation to a diagnostic. The annotation pins the
    diagnostic's *start* line and column range; `d.ending.line` is treated as
    informational so that a future multi-line diagnostic doesn't silently fail
    to match. -/
private def matchesAnnotation (d : Strata.Diagnostic) (a : DiagnosticAnnotation) : Bool :=
  d.start.line == a.line
    && d.start.column == a.colStart
    && d.ending.column == a.colEnd
    && diagnosticKindString d.type == a.kind
    && isSubstrOf a.message d.message

/-- Format a single annotation for error reporting. -/
private def formatAnnotation (a : DiagnosticAnnotation) : String :=
  s!"{a.line}:{a.colStart}-{a.colEnd}  {a.kind}: {a.message}"

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
      if !matchedAnnotationIdxs.contains i && matchesAnnotation d a then
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
      report := report ++ s!"  {formatAnnotation a}\n"
  if !unmatchedDiags.isEmpty then
    report := report ++ s!"\nActual diagnostics with no matching annotation:\n"
    for d in unmatchedDiags do
      report := report ++ s!"  {formatDiagnostic block d}\n"
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
