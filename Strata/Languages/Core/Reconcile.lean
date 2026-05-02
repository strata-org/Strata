/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Verifier

/-!
# Reconcile Phase for Split-Solve-Reconcile

This module implements the **Reconcile** phase of the Split-Solve-Reconcile
workflow. It reads `.smt2` files (produced by `strata verify --no-solve`)
and their corresponding `.result` files from an SMT solver, and produces
`VCResults` identical to what a full `strata verify` would have returned.

All obligation metadata is embedded directly in the `.smt2` files via
`set-info` directives, so no separate manifest file is needed.
-/

namespace Core
open Imperative
open Strata

public section

/-! ## String ↔ type conversions for set-info values -/

/-- Parse a property type from its string form (as emitted in `set-info :property`). -/
def propertyTypeOfString (s : String) : Imperative.PropertyType :=
  match s with
  | "cover" => .cover
  | "assert" => .assert
  | "divisionByZero" => .divisionByZero
  | "arithmeticOverflow" => .arithmeticOverflow
  | _ => .assert

/-- Parse a verdict string into a `Core.SMT.Result` with no model. -/
def smtResultOfString (s : String) : Core.SMT.Result :=
  match s with
  | "sat" => .sat []
  | "unsat" => .unsat
  | "unknown" => .unknown
  | _ => .err s!"unrecognized verdict: {s}"

/-! ## Result file parsing -/

/-- Classify a raw solver output line as a verdict. -/
private def lineVerdict? (line : String) : Option Core.SMT.Result :=
  match line.trimAscii.toString with
  | "sat" => some (.sat [])
  | "unsat" => some .unsat
  | "unknown" => some .unknown
  | _ => none

/-- Parse a `.result` file's contents into `(satResult, valResult)`. -/
def parseResultFile (content : String)
    (satisfiabilityCheck validityCheck : Bool) :
    Core.SMT.Result × Core.SMT.Result :=
  let lines := content.splitOn "\n"
  let verdicts := lines.filterMap lineVerdict?
  match satisfiabilityCheck, validityCheck with
  | true, true =>
    match verdicts with
    | v1 :: v2 :: _ => (v1, v2)
    | [v1] => (v1, .err "missing validity verdict")
    | _ => (.err "missing satisfiability verdict", .err "missing validity verdict")
  | true, false =>
    match verdicts with
    | v1 :: _ => (v1, .unknown)
    | [] => (.err "missing satisfiability verdict", .unknown)
  | false, true =>
    match verdicts with
    | v1 :: _ => (.unknown, v1)
    | [] => (.unknown, .err "missing validity verdict")
  | false, false =>
    (.unknown, .unknown)

/-! ## SMT2-based reconcile -/

/-- Metadata extracted from a single `.smt2` file's `set-info` directives. -/
structure SMT2Meta where
  file : Option String := none
  start : Option Nat := none
  stop : Option Nat := none
  label : String := "unknown"
  property : String := "assert"
  resolvedSat : Option String := none
  resolvedVal : Option String := none
  hasSatCheck : Bool := false
  hasValCheck : Bool := false
  deriving Repr

private def extractQuoted (line : String) : Option String :=
  match line.splitOn "\"" with
  | _ :: val :: _ => some val
  | _ => none

/-- Parse `set-info` directives from SMT2 file content. -/
def parseSMT2Meta (content : String) : SMT2Meta :=
  content.splitOn "\n" |>.foldl (init := ({} : SMT2Meta)) fun info line =>
    let l := line.trimAscii.toString
    if l.startsWith "(set-info :file " then
      { info with file := extractQuoted l }
    else if l.startsWith "(set-info :start " then
      { info with start := (l.drop 17 |>.dropRight 1 |>.trimAscii).toNat? }
    else if l.startsWith "(set-info :stop " then
      { info with stop := (l.drop 16 |>.dropRight 1 |>.trimAscii).toNat? }
    else if l.startsWith "(set-info :final-message " then
      { info with label := extractQuoted l |>.getD "unknown" }
    else if l.startsWith "(set-info :property " then
      { info with property := extractQuoted l |>.getD "assert" }
    else if l.startsWith "(set-info :resolved-sat " then
      { info with resolvedSat := extractQuoted l }
    else if l.startsWith "(set-info :resolved-val " then
      { info with resolvedVal := extractQuoted l }
    else if l.startsWith "(set-info :sat-message " then
      { info with hasSatCheck := true }
    else if l.startsWith "(set-info :unsat-message " then
      { info with hasValCheck := true }
    else info

/-- Build a `VCResult` from parsed SMT2 metadata and solver output. -/
def reconcileFromSMT2 (smt2 : SMT2Meta) (solverOutput : Option String)
    (options : VerifyOptions) : VCResult :=
  let property := propertyTypeOfString smt2.property
  let fileRange : Option Strata.FileRange :=
    match smt2.file, smt2.start, smt2.stop with
    | some f, some s, some e => some { file := .file f, range := { start := ⟨s⟩, stop := ⟨e⟩ } }
    | _, _, _ => none
  let md : Imperative.MetaData Expression :=
    match fileRange with
    | some fr => (Imperative.MetaData.empty).pushElem Imperative.MetaData.fileRange (.fileRange fr)
    | none => Imperative.MetaData.empty
  let obligation : Imperative.ProofObligation Expression :=
    { label := smt2.label, property, assumptions := [], obligation := default, metadata := md }
  let satisfiabilityCheck := smt2.hasSatCheck || smt2.resolvedSat.isSome
  let validityCheck := smt2.hasValCheck || smt2.resolvedVal.isSome
  let peSat? := smt2.resolvedSat.map smtResultOfString
  let peVal? := smt2.resolvedVal.map smtResultOfString
  let (solverSat, solverVal) := match solverOutput with
    | some content =>
      parseResultFile content (satisfiabilityCheck && peSat?.isNone) (validityCheck && peVal?.isNone)
    | none => (.unknown, .unknown)
  let satResult := peSat?.getD solverSat
  let valResult := peVal?.getD solverVal
  buildVCResult obligation satResult valResult
    satisfiabilityCheck validityCheck [] options

/-- Reconcile all `.smt2` files in a directory. Reads each `.smt2` file for
obligation metadata and pairs it with the corresponding `.result` file. -/
def reconcileDirectory (vcDir : System.FilePath)
    (options : VerifyOptions) : IO VCResults := do
  let entries ← vcDir.readDir
  let smt2Files := entries.filter (·.fileName.endsWith ".smt2")
    |>.qsort (fun a b => a.fileName < b.fileName)
  let mut results : VCResults := #[]
  for entry in smt2Files do
    let content ← IO.FS.readFile entry.path
    let smt2 := parseSMT2Meta content
    let resultPath := vcDir / (entry.fileName.dropRight 5 ++ ".result")
    let solverOutput ← do
      if ← resultPath.pathExists then
        some <$> IO.FS.readFile resultPath
      else
        pure none
    let r := reconcileFromSMT2 smt2 solverOutput options
    results := results.push r
  return results.mergeByAssertion

end -- public section
end Core
