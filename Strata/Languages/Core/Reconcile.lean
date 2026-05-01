/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Manifest
public import Strata.Languages.Core.Verifier

/-!
# Reconcile Phase for Split-Solve-Reconcile

This module implements the **Reconcile** phase of the Split-Solve-Reconcile
workflow (see `docs/design/SplitSolveReconcile.md`). It consumes a manifest
(produced by `strata verify --no-solve`) and a set of `.result` files from an
SMT solver, and produces a `VCResults` identical to what a full `strata verify`
would have returned.

The key property: **no pipeline re-execution**. All the expensive steps
(parse, transform, symbolic eval, SMT encoding) happen during the Generate
phase. Reconcile only reads and interprets solver output.
-/

namespace Core
open Lean (Json ToJson FromJson)
open Imperative
open Strata

public section

/-! ## Reconstructed proof obligations

When we read a manifest, we rebuild a thin `ProofObligation` carrying just
the fields needed by `mergeByAssertion` and the rendering layer:
 - `label`
 - `property`
 - `metadata` containing the primary `fileRange`, any related file ranges,
   and the `fullCheck` switch (for correct result grouping and display).

The `assumptions` and `obligation` fields are set to safe defaults because
the reconcile phase does not re-run the solver.
-/

/-- Build a `MetaData Expression` from manifest fields. Populates the primary
`fileRange`, any related file ranges, and the `fullCheck` switch. -/
def reconstructMetadata (mo : ManifestObligation) : Imperative.MetaData Expression := Id.run do
  let mut md : Imperative.MetaData Expression := Imperative.MetaData.empty
  if let some loc := mo.sourceLocation then
    md := md.pushElem Imperative.MetaData.fileRange (.fileRange loc.toFileRange)
  for rel in mo.relatedLocations do
    md := md.pushElem Imperative.MetaData.relatedFileRange (.fileRange rel.toFileRange)
  if mo.hasFullCheck then
    md := md.pushElem Imperative.MetaData.fullCheck (.switch true)
  return md

/-- Reconstruct a `ProofObligation` carrying only the fields the reconcile
phase needs. -/
def reconstructObligation (mo : ManifestObligation) :
    Imperative.ProofObligation Expression :=
  { label := mo.label,
    property := propertyTypeOfManifestString mo.property,
    assumptions := [],
    obligation := default,
    metadata := reconstructMetadata mo }

/-! ## Reconcile options -/

/-- Subset of `VerifyOptions` that can be overridden at reconcile time. The
reconcile command can re-classify and re-render solver results without
re-solving, so `checkMode`, `checkLevel`, and `verbose` are overridable.
Other fields come from the manifest. -/
structure ReconcileOverride where
  checkMode : Option VerificationMode := none
  checkLevel : Option CheckLevel := none
  verbose : Option VerboseMode := none
  deriving Repr, Inhabited

/-- Resolve the effective `VerifyOptions` by merging manifest-stored options
with user-supplied overrides. -/
def resolveOptions (m : Manifest) (ov : ReconcileOverride) : VerifyOptions :=
  { VerifyOptions.default with
    checkMode := ov.checkMode.getD (VerificationMode.ofManifestString m.options.checkMode),
    checkLevel := ov.checkLevel.getD (CheckLevel.ofManifestString m.options.checkLevel),
    verbose := ov.verbose.getD (VerboseMode.ofManifestString m.options.verbose) }

/-! ## Core reconcile algorithm -/

/-- Build a single `VCResult` from a manifest entry and the corresponding
solver result pair. Delegates to `buildVCResult` (the single source of truth
shared with `getObligationResult`). -/
def reconcileOne (mo : ManifestObligation) (options : VerifyOptions)
    (satResult valResult : Core.SMT.Result) : VCResult :=
  let obligation := reconstructObligation mo
  let phases := reconstructPhaseValidation mo.phaseValidation
  buildVCResult obligation satResult valResult
    mo.satisfiabilityCheck mo.validityCheck phases options

/-- Read the solver result for one manifest obligation. When resolved by the
evaluator, returns the stored result. Otherwise, reads `smtFile`'s `.result`
sibling from the VC directory. Missing files are surfaced as `.err` so
reconcile does not abort. -/
def readObligationResult (vcDir : System.FilePath) (mo : ManifestObligation) :
    IO (Core.SMT.Result × Core.SMT.Result) := do
  let peSat? : Option Core.SMT.Result :=
    mo.resolvedBySim.bind (·.satisfiability) |>.map smtResultOfManifestString
  let peVal? : Option Core.SMT.Result :=
    mo.resolvedBySim.bind (·.validity) |>.map smtResultOfManifestString
  -- Both evaluator-resolved: no file read needed.
  match peSat?, peVal? with
  | some s, some v => return (s, v)
  | _, _ =>
    -- At least one check unresolved by the evaluator → read the solver file.
    let (solverSat, solverVal) ←
      match mo.smtFile with
      | none =>
        let msg := s!"manifest obligation '{mo.label}' has unresolved check(s) but no smtFile"
        pure ((.err msg : Core.SMT.Result), (.err msg : Core.SMT.Result))
      | some smtRel =>
        let resultName :=
          if smtRel.endsWith ".smt2" then
            (smtRel.dropEnd ".smt2".length).toString ++ ".result"
          else
            smtRel ++ ".result"
        let path := vcDir / resultName
        readResultFile path
          (peSat?.isNone && mo.satisfiabilityCheck)
          (peVal?.isNone && mo.validityCheck)
    -- Evaluator results override solver-produced slots.
    return (peSat?.getD solverSat, peVal?.getD solverVal)

/-- Reconcile a manifest with the `.result` files under `vcDir`. -/
def reconcile (m : Manifest) (vcDir : System.FilePath)
    (ov : ReconcileOverride := {}) : IO VCResults := do
  let options := resolveOptions m ov
  let mut results : VCResults := #[]
  for mo in m.obligations do
    let (satResult, valResult) ← readObligationResult vcDir mo
    let r := reconcileOne mo options satResult valResult
    results := results.push r
  return results.mergeByAssertion

/-- High-level entry point: read `vcDir/manifest.json` and reconcile. -/
def reconcileDirectory (vcDir : System.FilePath)
    (ov : ReconcileOverride := {}) : IO (Except String VCResults) := do
  match ← readManifest vcDir with
  | .error e => return .error e
  | .ok m =>
    let results ← reconcile m vcDir ov
    return .ok results

/-- Validate that every expected `.result` file exists. Returns the list of
missing files (relative to `vcDir`). -/
def missingResultFiles (m : Manifest) (vcDir : System.FilePath) :
    IO (Array String) := do
  let mut missing : Array String := #[]
  for mo in m.obligations do
    -- Skip if the evaluator already resolved every requested check.
    let peSat? := mo.resolvedBySim.bind (·.satisfiability)
    let peVal? := mo.resolvedBySim.bind (·.validity)
    let needsSolverSat := mo.satisfiabilityCheck && peSat?.isNone
    let needsSolverVal := mo.validityCheck && peVal?.isNone
    if !needsSolverSat && !needsSolverVal then continue
    match mo.smtFile with
    | none => missing := missing.push s!"<obligation {mo.label}: no smtFile>"
    | some smtRel =>
      let resultName :=
        if smtRel.endsWith ".smt2" then
          (smtRel.dropEnd ".smt2".length).toString ++ ".result"
        else
          smtRel ++ ".result"
      let path := vcDir / resultName
      let exists_? ← path.pathExists
      if !exists_? then
        missing := missing.push resultName
  return missing

end -- public section
end Core
