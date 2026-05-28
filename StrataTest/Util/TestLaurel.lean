/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean.HashCommands
import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Resolution
import Strata.Languages.Laurel.LaurelCompilationPipeline
import Strata.Languages.Laurel.Laurel

open Strata
open Strata.Laurel

namespace StrataTest.Util

/-- Translate a `Strata.Program` (typically produced by `#strata`) to a Laurel
    `Program`. Used by tests that need to plug in a custom post-translation
    pipeline stage; throws if translation fails. -/
def translateLaurel (program : Strata.Program) : IO Laurel.Program := do
  match Laurel.TransM.run (Strata.Uri.file "<#strata>") (Laurel.parseProgram program) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok laurelProgram => pure laurelProgram

/-- Pretty-print a `Diagnostic` for error reporting.
    Format: `<line>:<colStart>-<colEnd>  <kind>: <message>` -/
def formatDiagnostic (d : Strata.Diagnostic) : String :=
  let kind := match d.type with
    | .Warning => "warning"
    | .UserError => "error"
    | .NotYetImplemented => "not-yet-implemented"
    | .StrataBug => "strata-bug"
  s!"{d.start.line}:{d.start.column}-{d.ending.column}  {kind}: {d.message}"

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

/-- Run translate + resolve only on a parsed program. Skips SMT verification.
    Returns diagnostics as `DiagnosticModel`s so the caller can choose how to
    render them (snippet-local for inline annotations, file-global for editor
    navigation). -/
private def runLaurelResolutionRaw (program : Strata.Program) :
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
private def runLaurelPipelineRaw (program : Strata.Program) :
    IO (Array Strata.DiagnosticModel) := do
  let uri := Strata.Uri.file "<#strata>"
  match Laurel.TransM.run uri (Laurel.parseProgram program) with
  | .error e =>
    return #[Strata.DiagnosticModel.fromMessage s!"Translation error: {e}"]
  | .ok laurelProgram =>
    let options : LaurelVerifyOptions := { verifyOptions := .quiet }
    Laurel.verifyToDiagnosticModels laurelProgram options

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

/-- Try to match an annotation to a diagnostic. -/
private def matchesAnnotation (d : Strata.Diagnostic) (a : DiagnosticAnnotation) : Bool :=
  d.start.line == a.line
    && d.ending.line == a.line
    && d.start.column == a.colStart
    && d.ending.column == a.colEnd
    && diagnosticKindString d.type == a.kind
    && (a.message.isEmpty || (d.message.splitOn a.message).length > 1)

/-- Format a single annotation for error reporting. -/
private def formatAnnotation (a : DiagnosticAnnotation) : String :=
  s!"{a.line}:{a.colStart}-{a.colEnd}  {a.kind}: {a.message}"

/-- Drive a `SourcedProgram` against its inline annotations.

    - If the snippet contains no annotations, succeeds iff the pipeline
      produces no diagnostics and prints `ok`.
    - Otherwise asserts an exact match: every diagnostic must be annotated,
      every annotation must fire. Throws on mismatch. -/
private def runAndCheck (block : SourcedProgram)
    (run : Strata.Program → IO (Array Strata.DiagnosticModel)) : IO Unit := do
  let annotations := parseAnnotations block.source
  let dms ← run block.program
  let actual := renderSnippetLocal block.basePos block.source dms
  if annotations.isEmpty then
    unless actual.isEmpty do
      let mut report := s!"expected no diagnostics, got {actual.size}:\n"
      for d in actual do
        report := report ++ s!"  {formatDiagnostic d}\n"
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
      report := report ++ s!"  {formatDiagnostic d}\n"
  throw <| IO.userError report

/-- Run the full Laurel pipeline (translate + resolve + verify) on a
    `#strata`-parsed program. If the snippet has inline `// ^^^ kind: message`
    annotations, asserts an exact match; otherwise expects no diagnostics
    and prints `ok`. -/
def testLaurel (block : SourcedProgram) : IO Unit :=
  runAndCheck block runLaurelPipelineRaw

/-- Like `testLaurel` but skips SMT verification (translate + resolve only).
    Use when the test only cares about resolution, not the verifier — e.g.
    "shadowing in nested blocks is OK", or asserting a specific resolution
    error without the verifier surfacing unrelated noise. -/
def testLaurelResolution (block : SourcedProgram) : IO Unit :=
  runAndCheck block runLaurelResolutionRaw

end StrataTest.Util
