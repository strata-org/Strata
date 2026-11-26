/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel
meta import Strata.Languages.Core

/-!
# Calls to Cortex procedures without a body

A Cortex procedure without a body lowers to an abstract Core procedure: a call to it means its
contract, and call elimination replaces the call exactly. Neither `ext` nor `prim` below has a
postcondition, so the contract of each allows every `int`.

`prim` is not external: its contract is its whole meaning, as for a primitive of an API. The
counterexample of `primNonneg` is a value that contract allows, so deductive verification reports
a failure.

`ext` is external (`Cortex.Procedure.external`): it models code that Strata does not see, such as
a library method, so the lowering marks the call (`Core.externalAssumePrefix`). A counterexample
through the call may come from the model, not from the code, so `extNonneg` is unknown in
deductive verification and is not reported as a bug in bug-finding verification.
-/

open StrataTest.Util
open Strata

meta section

/-- Each obligation's label and outcome for the Core program that Cortex lowers the
    `#strata`-parsed Laurel program `block` to, with the procedures `externals` made external,
    verified by symbolic execution in the mode `mode`. -/
private def verifyThroughCortex (externals : List String) (mode : Core.VerificationMode)
    (block : StrataDDM.SourcedProgram) : IO Unit := do
  let laurel ← translateLaurel block.program
  let some cortex := (Cortex.toCortex {} laurel).1
    | throw (IO.userError "Cortex translation failed")
  let cortex := { cortex with procedures := cortex.procedures.map fun p =>
    { p with external := externals.contains p.name } }
  let core ← IO.ofExcept (Cortex.toCoreProgram cortex)
  let opts := { Core.VerifyOptions.quiet with symExec := some .default, checkMode := mode }
  let rs ← EIO.toIO (fun e => IO.Error.userError (toString e)) (Core.verifyProgram core opts)
  for r in rs do IO.println s!"{r.obligation.label}: {r.formatOutcome}"

private def callsPgm : StrataDDM.SourcedProgram :=
#strata
program Laurel;
procedure ext(x: int) returns (r: int);
procedure prim(x: int) returns (r: int);
procedure callsExt(x: int) returns (y: int)
  opaque
{
    y := ext(x);
    assert y >= 0 summary "extNonneg"
};
procedure callsPrim(x: int) returns (y: int)
  opaque
{
    y := prim(x);
    assert y >= 0 summary "primNonneg"
};
#end

-- Deductive verification: `extNonneg` (`assert_0`) is unknown, `primNonneg` (`assert_2`) fails.
/--
info: assert_0: ❓ unknown
assert_2: ❌ fail
-/
#guard_msgs in
#eval verifyThroughCortex ["ext"] .deductive callsPgm

-- Bug-finding verification: `extNonneg` is unknown, which is not a bug-finding success; the
-- assertion after the exact call to `prim` is satisfiable, as for any assertion that can hold.
/--
info: assert_0: ❓ unknown
assert_2: ❓ satisfiable
-/
#guard_msgs in
#eval verifyThroughCortex ["ext"] .bugFinding callsPgm

-- With `ext` not external, the call to it is exact too, and `extNonneg` fails like `primNonneg`.
/--
info: assert_0: ❌ fail
assert_2: ❌ fail
-/
#guard_msgs in
#eval verifyThroughCortex [] .deductive callsPgm


/-- The error of lowering `block` to Core after relabelling its assertions with a label that has
    the external-call marker prefix, which the lowering reserves. -/
private def lowerWithMarkerLabel (block : StrataDDM.SourcedProgram) : IO Unit := do
  let laurel ← translateLaurel block.program
  let some cortex := (Cortex.toCortex {} laurel).1
    | throw (IO.userError "Cortex translation failed")
  let relabel : Cortex.IRCmd → Cortex.IRCmd
    | .cmd (.assert _ e md) => .cmd (.assert s!"{Core.externalAssumePrefix}0" e md)
    | c => c
  let relabelBody (b : Cortex.Body) : Cortex.Body :=
    let blocks := b.cfg.blocks.map fun (l, blk) => (l, { blk with cmds := blk.cmds.map relabel })
    { b with cfg := { b.cfg with blocks } }
  let cortex := { cortex with procedures := cortex.procedures.map fun p =>
    { p with body := p.body.map relabelBody } }
  match Cortex.toCoreProgram cortex with
  | .ok _ => IO.println "lowered"
  | .error e => IO.println e

/--
info: ❌ The label "$__externalAssume_0" starts with "$__externalAssume_", which the lowering of Cortex to Core reserves for its markers.
-/
#guard_msgs in
#eval lowerWithMarkerLabel callsPgm

end
