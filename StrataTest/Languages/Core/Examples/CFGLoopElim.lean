/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT

  Regression coverage for CFG-native loop elimination
  (`Strata/Transform/CFGLoopElim.lean`, `cfgLoopElimPipelinePhase`).

  A `.cfg`-bodied loop, verified through the verifier, exercises the CFG-native
  loop-elimination phase. Without that phase, the fuel-only `evalCFGBlocks`
  worklist unrolls the loop back-edge and verification does not terminate
  (unbounded heap growth). With it, the loop region is replaced by an acyclic
  invariant-based encoding (the back-edge is cut), so verification terminates
  with the maintenance VC (`arbitrary_iter_maintain_invariant`) present and
  discharged.
-/

import Strata.Languages.Core.Program
import Strata.Languages.Core.Verifier
import Strata.Transform.StructuredToUnstructured

namespace Strata

/-- Rewrite every structured procedure body in a program to its CFG form, so a
    subsequent `verify` drives the `.cfg` evaluation path (and hence the
    CFG-native loop-elimination phase). Procedures already in CFG form and
    non-procedure declarations are left untouched. -/
def toCFGProgram (corePgm : Core.Program) : Core.Program :=
  { corePgm with
    decls := corePgm.decls.map fun
      | .proc proc md =>
        match proc.body with
        | .structured ss => .proc { proc with body := .cfg (Imperative.stmtsToCFG ss) } md
        | .cfg _ => .proc proc md
      | other => other }

/-- Verify a program after rewriting its bodies to CFG form. Mirrors the
    top-level `Strata.verify` (`Verifier.lean`) with the CFG rewrite spliced in
    before `Core.verify`. -/
def verifyViaCFG (env : Program) : IO Core.VCResults := do
  let (program, errors) := Core.getProgram env Inhabited.default
  if errors.isEmpty then
    let cfgProgram := toCFGProgram program
    IO.FS.withTempDir (fun tempDir =>
      EIO.toIO (fun dm => IO.Error.userError (toString (dm.format none)))
        (Core.verify cfgProgram tempDir))
  else
    panic! s!"DDM Transform Error: {repr errors}"

/-- A bounded loop with an invariant (same shape as `loopGuardPrecondPgm` in
    FunctionPreconditions.lean). Verified in CFG form below. -/
def cfgLoopElimPgm :=
#strata
program Core;

procedure test(n : int)
spec {
  requires n != 0;
}
{
  var i : int := 0;
  while (i / n < 10)
    invariant i >= 0
  {
    i := i + 1;
  }
};

#end

/-
  Before CFG loop elimination this `#eval` did not terminate (the back-edge was
  unrolled until heap exhaustion). With the pass it produces a bounded VC set:
  VC1 entry-invariant (`inv$_3`), the header guard div-by-zero check
  (`branch_cond_…SafeDiv`), and VC2 maintenance
  (`arbitrary_iter_maintain_invariant_0_0`) — all discharged.
-/
/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: inv$_3
Property: assert
Assumptions:
test_requires_0: !(n@1 == 0)
Obligation:
true

Label: branch_cond_calls_Int.SafeDiv_0
Property: division by zero check
Assumptions:
test_requires_0: !(n@1 == 0)
Obligation:
!(n@1 == 0)

Label: arbitrary_iter_maintain_invariant_0_0
Property: assert
Assumptions:
test_requires_0: !(n@1 == 0)
<cfgBranch_true: i / n < 10>: 0 / n@1 < 10
assume_guard_0: i@1 / n@1 < 10
assume_loop_invariant_0_0: i@1 >= 0
Obligation:
i@1 + 1 >= 0

---
info:
Obligation: inv$_3
Property: assert
Result: ✅ pass

Obligation: branch_cond_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyViaCFG cfgLoopElimPgm

end Strata
