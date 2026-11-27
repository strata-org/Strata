/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.Options
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! # The passive VC generators of `--vcgen`

`--vcgen usp` and `--vcgen uwp` select the passive VC generator: `Core.verifyProgram`
runs its order (`passiveVCGenPhases`), which lowers each body to a passification
CFG and discharges its VCs via `Imperative.PassiveVCGen` (see `PassiveVCGenUwpUspTest`
for detailed coverage), where `--vcgen symbolic`, the default, runs symbolic
evaluation. The flag's values are tested in `VCGenFlagsTest`. -/

namespace Core.VCGenModeTest

/-! ## The default VC generator is symbolic evaluation -/

#guard Core.VerifyOptions.default.vcgen == Core.VCGenMode.symbolic

/-! ## Dispatch: each mode runs its own phases

`verifyProgram` runs the phases `corePipelinePhases` lists for the mode. With
`keepAllFilesPrefix` set, each phase writes the program it produced to
`<prefix>.<n>.<phase>.core.st`, so the names of the files are the phases that ran. -/

def trivialPgm :=
#strata
program Core;
procedure P(x : int) {
  assert [t]: (x == x);
};
#end

/-- The phases `verifyProgram` ran under `mode`, from the files they wrote, in
    order; and the labels of its results with their verdicts. -/
def runUnder (mode : Core.VCGenMode) : IO (List String × List (String × Bool)) := do
  match Strata.strataProgramToCore trivialPgm with
  | .error e => throw (IO.userError s!"translate error: {e}")
  | .ok prog =>
    IO.FS.withTempDir fun dir => do
      let pfx := (dir / "p").toString
      let opts := { Core.VerifyOptions.quiet with vcgen := mode, keepAllFilesPrefix := some pfx }
      match ← (Strata.Core.verifyProgram prog opts).toBaseIO with
      | .error msg => throw (IO.userError s!"error: {msg}")
      | .ok results =>
        let names ← dir.readDir
        -- `p.<n>.<phase>.core.st`
        let phases := (names.toList.filterMap fun e =>
          match e.fileName.splitOn "." with
          | "p" :: n :: phase :: _ => n.toNat?.map (·, phase)
          | _ => none).toArray.qsort (·.1 < ·.1) |>.toList.map (·.2)
        pure (phases, results.toList.map fun r => (r.obligation.label, r.isSuccess))

/-- The phases the pipeline of `mode` lists. -/
def phasesOf (mode : Core.VCGenMode) : List String :=
  (Core.corePipelinePhases { Core.VerifyOptions.quiet with vcgen := mode }).map (·.phase.name)

-- Each mode runs exactly the phases its pipeline lists: symbolic evaluation under
-- `--vcgen symbolic`, CFG loop elimination and the passive VC phase under `uwp` and `usp`.
/--
info: true: [typeCheck, assertNoCFGBodies, callElim, termCheck, precondElim, seqTotalize, insertLoopInvariantAsserts, loopElim, genOpaqueTypeParams, monomorphizeFunctions, simplify, nondetElim, symbolicEval, betaReduce, commonSubexprElim, lambdaLift, separateVarNames]
-/
#guard_msgs in #eval do
  let (ran, _) ← runUnder .symbolic
  IO.println s!"{ran == phasesOf .symbolic}: {ran}"

/--
info: true: [hoistNondetChoices, typeCheck, cfgLoopElim, callElim, termCheck, precondElim, seqTotalize, insertLoopInvariantAsserts, loopElim, genOpaqueTypeParams, monomorphizeFunctions, simplify, declObligations, passiveVC, betaReduce, lambdaLift, separateVarNames]
-/
#guard_msgs in #eval do
  let (ran, _) ← runUnder .uwp
  IO.println s!"{ran == phasesOf .uwp}: {ran}"

/--
info: true: [hoistNondetChoices, typeCheck, cfgLoopElim, callElim, termCheck, precondElim, seqTotalize, insertLoopInvariantAsserts, loopElim, genOpaqueTypeParams, monomorphizeFunctions, simplify, declObligations, passiveVC, betaReduce, lambdaLift, separateVarNames]
-/
#guard_msgs in #eval do
  let (ran, _) ← runUnder .usp
  IO.println s!"{ran == phasesOf .usp}: {ran}"

/-- The program the passive VC phase produced under `mode`, as the file it wrote. -/
def passiveText (mode : Core.VCGenMode) : IO String := do
  match Strata.strataProgramToCore trivialPgm with
  | .error e => throw (IO.userError s!"translate error: {e}")
  | .ok prog =>
    IO.FS.withTempDir fun dir => do
      let pfx := (dir / "p").toString
      let opts := { Core.VerifyOptions.quiet with vcgen := mode, keepAllFilesPrefix := some pfx }
      let _ ← (Strata.Core.verifyProgram prog opts).toBaseIO
      let names ← dir.readDir
      match names.find? (·.fileName.endsWith ".passiveVC.core.st") with
      | some e => IO.FS.readFile e.path
      | none => pure ""

-- The calculus follows the mode. Both define the block preconditions `A`; only `uwp`
-- defines the weakest preconditions `W` of an assertion's goal.
/-- info: ((true, false), true, true) -/
#guard_msgs in #eval do
  let usp ← passiveText .usp
  let uwp ← passiveText .uwp
  pure ((usp.contains "$__vcA", usp.contains "$__vcW"), (uwp.contains "$__vcA", uwp.contains "$__vcW"))

-- Every mode proves the assertion.
/-- info: [[("t", true)], [("t", true)], [("t", true)]] -/
#guard_msgs in #eval do
  pure [(← runUnder .symbolic).2, (← runUnder .uwp).2, (← runUnder .usp).2]

end Core.VCGenModeTest
