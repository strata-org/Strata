/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Options
meta import Strata.Languages.Core
meta import StrataDDM
meta import StrataDDM.BuiltinDialects
meta import StrataTest.Languages.Core.Tests.CoreTextTestUtils

meta section

/-! # End-to-end VC generation for `Examples/CFGLoopFree.core.st`

Reads a Core source file whose procedures have unstructured (`cfg`) bodies —
loop-free and call-free — parses it, and verifies it through the passification
VC generator with `--vcgen uwp` and `--vcgen usp`. Each source assertion and
each checked `ensures` becomes its own obligation, discharged by cvc5.

The file is read from disk at test time (relative to the package root, as the
test runner runs), so the test exercises the checked-in example itself rather
than an inline copy. Each result carries the source location of its assertion,
printed as the CLI prints it. -/

namespace Strata.CFGLoopFreeExampleTest

open Strata.Core.TestUtils

private def examplePath : System.FilePath := "Examples" / "CFGLoopFree.core.st"

private def verifyExample (mode : Core.VCGenMode) : IO Unit := do
  let pgm ← parseCoreFile examplePath
  IO.println (← Core.verify pgm
    (options := { Core.VerifyOptions.quiet with vcgen := mode }))

/--
info:
Obligation: else_m_gt_x
Property: assert
Result: ✅ pass

Obligation: max_ge_x
Property: assert
Result: ✅ pass

Obligation: max_ge_y
Property: assert
Result: ✅ pass

Obligation: max_is_arg
Property: assert
Result: ✅ pass

Obligation: below_r_le_hi
Property: assert
Result: ✅ pass

Obligation: clamp_ge_lo
Property: assert
Result: ✅ pass

Obligation: clamp_le_hi
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyExample .uwp

/--
info:
Obligation: else_m_gt_x
Property: assert
Result: ✅ pass

Obligation: max_ge_x
Property: assert
Result: ✅ pass

Obligation: max_ge_y
Property: assert
Result: ✅ pass

Obligation: max_is_arg
Property: assert
Result: ✅ pass

Obligation: below_r_le_hi
Property: assert
Result: ✅ pass

Obligation: clamp_ge_lo
Property: assert
Result: ✅ pass

Obligation: clamp_le_hi
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyExample .usp

/-- Verify the example as the `strata verify` CLI does (with the input context,
    so locations resolve) and print each result the way the CLI prints it:
    `file(line, col) [label]: outcome`. -/
private def verifyExampleWithLocations (mode : Core.VCGenMode) : IO Unit := do
  let text ← IO.FS.readFile examplePath
  let ictx := Lean.Parser.mkInputContext text "CFGLoopFree.core.st"
  let results ← Core.verify (← parseCoreFile examplePath) ictx
    (options := { Core.VerifyOptions.quiet with vcgen := mode })
  for r in results do
    let pos := Imperative.MetaData.formatFileRangeD r.obligation.metadata (some ictx.fileMap)
    IO.println s!"{pos} [{r.obligation.label}]: {r.formatOutcome}"

/--
info: CFGLoopFree.core.st(23, 4) [else_m_gt_x]: ✅ pass
CFGLoopFree.core.st(9, 2) [max_ge_x]: ✅ pass
CFGLoopFree.core.st(10, 2) [max_ge_y]: ✅ pass
CFGLoopFree.core.st(11, 2) [max_is_arg]: ✅ pass
CFGLoopFree.core.st(45, 4) [below_r_le_hi]: ✅ pass
CFGLoopFree.core.st(36, 2) [clamp_ge_lo]: ✅ pass
CFGLoopFree.core.st(37, 2) [clamp_le_hi]: ✅ pass
-/
#guard_msgs in
#eval verifyExampleWithLocations .uwp

/-! ## The same program with a false assertion

The goldens above contain only passing assertions, which a generator that assumed
too much would also pass. Here two assertions of `Max` are made false (`m > x`
becomes `m < x` on the arm where `m = y > x`, and `max_ge_x` becomes strict, which
fails when `m = x`), and `Clamp` is broken on one of the three paths into its exit
(above `hi`, `r` becomes `hi + 1`, so `clamp_le_hi` fails there only, through the
three-way join). Each is reported failing in both calculi while the others still
pass. -/

/-- The verdict of each result of the mutated example, by label. -/
private def verifyMutated (mode : Core.VCGenMode) : IO Unit := do
  let text ← IO.FS.readFile examplePath
  let text := text.replace "assert [else_m_gt_x]: (int.gt(m, x))" "assert [else_m_gt_x]: (int.lt(m, x))"
  let text := text.replace "ensures [max_ge_x]: (int.ge(m, x))" "ensures [max_ge_x]: (int.gt(m, x))"
  -- `Clamp` broken on one of its three paths into `done`: above `hi`, `r` is one more.
  let text := text.replace "  above: {\n    r := hi;" "  above: {\n    r := int.add(hi, 1);"
  let results ← Core.verify (← parseCoreText "mutated.core.st" text.toUTF8)
    (options := { Core.VerifyOptions.quiet with vcgen := mode })
  IO.println (results.toList.map fun r =>
    (r.obligation.label, if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))

/-- info: [(else_m_gt_x, fail), (max_ge_x, fail), (max_ge_y, pass), (max_is_arg, pass), (below_r_le_hi, pass), (clamp_ge_lo, pass), (clamp_le_hi, fail)] -/
#guard_msgs in
#eval verifyMutated .uwp

/-- info: [(else_m_gt_x, fail), (max_ge_x, fail), (max_ge_y, pass), (max_is_arg, pass), (below_r_le_hi, pass), (clamp_ge_lo, pass), (clamp_le_hi, fail)] -/
#guard_msgs in
#eval verifyMutated .usp

end Strata.CFGLoopFreeExampleTest

end
