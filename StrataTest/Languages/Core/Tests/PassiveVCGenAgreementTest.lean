/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Examples.EmbeddedData
meta import StrataTest.Languages.Core.Tests.CoreTextTestUtils

meta section

/-! # `usp` and `uwp` against `--vcgen symbolic` on the Core examples

Every shipped Core example (`Examples/*.core.st`) is verified with `--vcgen symbolic`,
`usp` and `uwp`, and the verdict of each obligation is compared, by label (the
passive generator lists a procedure's postconditions after its assertions, so the
order is not compared). `--vcgen symbolic` refuses a program with a CFG body; on such a
program `uwp` is compared with `usp` instead. This keeps the generators' agreement from
regressing silently.

A program both modes refuse counts as agreeing. Known disagreements, which a change
should leave alone or remove, are listed in `known`: none among the examples today.
(Outside them, `--vcgen symbolic` may simplify away an expression the SMT encoder cannot
express, which the passive generator then sends to the solver; and a
monomorphization bug for recursive polymorphic functions affects both modes.) -/

namespace Strata.Test.PassiveVCGenAgreement

open Strata

/-- The verdict of each obligation of `p` under `mode`, sorted, or the error. -/
private def verdicts (p : StrataDDM.Program) (mode : Core.VCGenMode) :
    IO (Except String (List (String × String))) := do
  try
    let r ← Strata.Core.verify p (options := { Core.VerifyOptions.quiet with vcgen := mode })
    let vs := r.toList.map fun r =>
      (r.obligation.label, if r.isSuccess then "pass" else if r.isFailure then "fail" else "other")
    pure (.ok (vs.toArray.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))).toList)
  catch e => pure (.error s!"{e}")

/-- The examples, by file name, on which the modes are known to disagree. -/
private def known : List String := []

/-- info: 15 examples; disagreements: [] -/
#guard_msgs in
#eval show IO Unit from do
  let mut n := 0
  let mut disagree : Array String := #[]
  for (path, text) in embeddedExampleFiles do
    if !path.endsWith ".core.st" || path.startsWith "expected/" then continue
    let p ← Strata.Core.TestUtils.parseCoreText path text.toUTF8
    n := n + 1
    let e ← verdicts p .symbolic
    -- A CFG body, which symbolic evaluation refuses: compare the two calculi.
    let e ← match e with
      | .error msg => if (msg.splitOn "CFG body").length > 1 then verdicts p .usp else pure e
      | _ => pure e
    for m in [Core.VCGenMode.usp, .uwp] do
      let u ← verdicts p m
      let same := match e, u with
        | .ok a, .ok b => a == b
        | .error _, .error _ => true
        | _, _ => false
      if !same && !known.contains path then
        disagree := disagree.push s!"{path} ({repr m |>.pretty})"
  IO.println s!"{n} examples; disagreements: {disagree.toList}"

end Strata.Test.PassiveVCGenAgreement

end
