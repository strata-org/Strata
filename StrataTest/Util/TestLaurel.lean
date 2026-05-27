/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean.HashCommandsExpect
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

/-- Run translate + resolve only on a parsed program. Skips SMT verification.
    Useful for resolution-only negative tests where running the verifier would
    surface unrelated noise. -/
private def runLaurelResolution (program : Strata.Program) (source : String) :
    IO (Array Strata.Diagnostic) := do
  let uri := Strata.Uri.file "<#strata>"
  match Laurel.TransM.run uri (Laurel.parseProgram program) with
  | .error e =>
    return #[{ start := ⟨0, 0⟩, ending := ⟨0, 0⟩,
               message := s!"Translation error: {e}", type := .UserError }]
  | .ok laurelProgram =>
    let result := Laurel.resolve laurelProgram
    let files := Map.insert Map.empty uri (Lean.FileMap.ofString source)
    return result.errors.map (fun dm => dm.toDiagnostic files)

/-- Run the full Laurel pipeline (translate + resolve + verify). -/
private def runLaurelPipeline (program : Strata.Program) (source : String) :
    IO (Array Strata.Diagnostic) := do
  let uri := Strata.Uri.file "<#strata>"
  match Laurel.TransM.run uri (Laurel.parseProgram program) with
  | .error e =>
    return #[{ start := ⟨0, 0⟩, ending := ⟨0, 0⟩,
               message := s!"Translation error: {e}", type := .UserError }]
  | .ok laurelProgram =>
    let files := Map.insert Map.empty uri (Lean.FileMap.ofString source)
    let options : LaurelVerifyOptions := { verifyOptions := .quiet }
    Laurel.verifyToDiagnostics files laurelProgram options

/-- Positive-test helper: run the full Laurel pipeline on a `#strata`-parsed
    program and print diagnostics. Empty output means the program checks
    cleanly. -/
def testLaurel (program : Strata.Program) : IO Unit := do
  let pipelineDiags ← runLaurelPipeline program ""
  if pipelineDiags.isEmpty then
    IO.println "ok"
  else
    for d in pipelineDiags do IO.println (formatDiagnostic d)

/-- Positive resolution-only helper: run translate + resolve and print
    diagnostics. Use when the test only cares about resolution, not the
    verifier (e.g. "shadowing in nested blocks is OK"). -/
def testLaurelResolution (program : Strata.Program) : IO Unit := do
  let resolutionDiags ← runLaurelResolution program ""
  if resolutionDiags.isEmpty then
    IO.println "ok"
  else
    for d in resolutionDiags do IO.println (formatDiagnostic d)

/-! ## Inline-annotation negative-test machinery

Negative tests embed `// ^^^^^^ <kind>: <message>` annotations directly in the
source of a `#strata_expect` block. Each annotation pins one expected
diagnostic to the line above it. Example:

```
#strata_expect
program Laurel;
procedure foo() opaque {
  var x: int := 1;
  var y: x := 2
//       ^ error: 'x' resolves to variable, but expected ...
};
#end
```

The `testLaurelExpect` / `testLaurelExpectResolution` helpers parse these
annotations from `block.source`, run the pipeline, and assert exact match
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

/-- Drive an `ExpectedBlock` against its inline annotations. Throws on any
    mismatch. -/
private def runWithAnnotations (block : Strata.ExpectedBlock)
    (run : Strata.Program → String → IO (Array Strata.Diagnostic)) : IO Unit := do
  let annotations := parseAnnotations block.source
  let pipelineDiags ← run block.program block.source
  let actual := block.parseDiagnostics ++ pipelineDiags
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

/-- Negative-test helper: run the full Laurel pipeline and assert that the
    diagnostics match the inline `// ^^^ kind: message` annotations in the
    block exactly. Throws on any mismatch. -/
def testLaurelExpect (block : Strata.ExpectedBlock) : IO Unit :=
  runWithAnnotations block runLaurelPipeline

/-- Resolution-only negative-test helper. Runs translate + resolve only and
    asserts inline annotations match. Use when the test asserts a
    resolution-pass diagnostic and running the verifier would surface
    unrelated noise. -/
def testLaurelExpectResolution (block : Strata.ExpectedBlock) : IO Unit :=
  runWithAnnotations block runLaurelResolution

end StrataTest.Util
