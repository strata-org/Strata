/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
## A heap's `Map` field is an SMT `Array` under `--incremental`

Laurel verifies with array theory on, so a `Map` is an SMT `Array` in every term. The heap is
a datatype whose field is a `Map`, and the datatype declared to a live solver has to give that
field the same `Array` sort; with an uninterpreted `Map` sort there, every read of the heap is
rejected as a `select` on a non-array. `Core.verify` walks the obligation tree on live solvers
under `--incremental`, for Laurel as for every front end, so each goal below gets the same
results, verdicts and models, with `incremental` off and on.
-/

private def heapProgram :=
#strata
program Laurel;
composite Counter { var value: int }

procedure bump(c: Counter)
  opaque
  modifies c
{
  c#value := c#value + 1
};

procedure bumpTwice(c: Counter)
  opaque
  modifies c
{
  var before: int := c#value;
  c#value := c#value + 1;
  c#value := c#value + 1;
  assert c#value == before + 2;
  assert c#value == before + 3
};
#end

private def bothWays (p : StrataDDM.Program) : IO Unit := do
  let uri := Strata.Uri.file "<#strata>"
  match Laurel.TransM.run uri (Laurel.parseProgram p) with
  | .error e => IO.println s!"translation error: {e}"
  | .ok program =>
    let run (incremental : Bool) : IO (List String) := do
      let options := { defaultLaurelTestOptions with
        verifyOptions := { defaultLaurelTestOptions.verifyOptions with incremental } }
      let (results, _) ← Laurel.verifyToVcResults program options
      pure ((results.getD #[]).toList.map fun r =>
        s!"{r.obligation.label} {(r.formatOutcome.splitOn "!").headD ""}")
    let plain ← run false
    let walked ← run true
    if plain == walked then
      IO.println s!"agree on {plain.length}:"
      for v in walked do IO.println s!"  {v}"
    else IO.println s!"differ:\n  per-obligation: {plain}\n  incremental: {walked}"

/--
info: agree on 8:
  set_$result_calls_Int.SafeDiv_0 ✅ pass
  set_$result_calls_Int.SafeMod_0 ✅ pass
  set_$result_calls_Int.SafeDivT_0 ✅ pass
  set_$result_calls_Int.SafeModT_0 ✅ pass
  assert(865) ✅ pass
  assert(1075) ✅ pass
  assert(1107) ❌ fail
  assert(945) ✅ pass
-/
#guard_msgs in
#eval bothWays heapProgram
