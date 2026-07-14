/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)

/-!
# Per-call-site type-variable freshening (CallElim) — Core regression tests

`Core.CallElim.callElimCmd` inlines a polymorphic procedure's contract at each
call site, freshening the callee's declared type variables to globally-fresh
names per site (`freshenTypeArgsSubst`, `Strata/Transform/CoreTransform.lean`).
Without that, the inlined contract reuses the LITERAL type variable at every
site, so calling one polymorphic procedure at two concrete types in one body
forces the variable to unify with both — a whole-program type-check ABORT that
masked unrelated obligations.

These exercise the fix at the Core layer DIRECTLY (the bug lives in CallElim, a
Core transform). Unlike the Laurel corpus — whose oracle is a failure *count* —
`Core.verify` reports each obligation by LABEL and verdict, so these pin WHICH
obligation fails, not just how many. The callees use `free ensures` so the
postcondition is inlined as an assume at the call site (the path the freshening
governs) without emitting a proof obligation for the polymorphic body itself
(whose free type variable has no SMT sort).
-/

namespace Strata.PolyProcFreshenMultiInst

-- One polymorphic procedure called at `int` AND `bool` in a single body — the
-- exact shape that pre-fix aborted with "Impossible to unify a with bool".
-- Per-call-site freshening gives each call its own type variable, so both
-- call-site obligations are well-formed and pass.
def multiInstPgm : Program :=
#strata
program Core;
procedure idp<a>(x : a, out r : a)
spec {
  free ensures (r == x);
};
procedure Test() spec { ensures true; }
{
  var ai : int;
  call idp(7, out ai);
  assert (ai == 7);
  var bb : bool;
  call idp(true, out bb);
  assert (bb == true);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Assumptions:
callElimAssume_idp_ensures_0_7: ai@1 == 7
Obligation:
ai@1 == 7

Label: assert_1
Property: assert
Assumptions:
callElimAssume_idp_ensures_0_7: ai@1 == 7
callElimAssume_idp_ensures_0_3: bb@1 == true
Obligation:
bb@1 == true

Label: Test_ensures_0
Property: assert
Assumptions:
callElimAssume_idp_ensures_0_7: ai@1 == 7
callElimAssume_idp_ensures_0_3: bb@1 == true
Obligation:
true

---
info:
Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: assert_1
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify multiInstPgm

end Strata.PolyProcFreshenMultiInst

---------------------------------------------------------------------

namespace Strata.PolyProcFreshenSoundness

-- Soundness twin of the multi-instantiation case: the bool-slot assertion is
-- FALSE (`bb == false` after `idp(true)`). The freshened postcondition keeps the
-- bool call coupled to its own concrete type, so the WRONG obligation — `assert_1`
-- specifically — fails (not `assert_0`, not merely "one of them"). This pins the
-- per-obligation identity that a count-only oracle cannot.
def wrongBoolPgm : Program :=
#strata
program Core;
procedure idp<a>(x : a, out r : a)
spec {
  free ensures (r == x);
};
procedure Test() spec { ensures true; }
{
  var ai : int;
  call idp(7, out ai);
  assert (ai == 7);
  var bb : bool;
  call idp(true, out bb);
  assert (bb == false);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Assumptions:
callElimAssume_idp_ensures_0_7: ai@1 == 7
Obligation:
ai@1 == 7

Label: assert_1
Property: assert
Assumptions:
callElimAssume_idp_ensures_0_7: ai@1 == 7
callElimAssume_idp_ensures_0_3: bb@1 == true
Obligation:
bb@1 == false

Label: Test_ensures_0
Property: assert
Assumptions:
callElimAssume_idp_ensures_0_7: ai@1 == 7
callElimAssume_idp_ensures_0_3: bb@1 == true
Obligation:
true

---
info:
Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: assert_1
Property: assert
Result: ❓ unknown
Model:
(bb@1, true) (ai@1, 7) 

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify wrongBoolPgm

end Strata.PolyProcFreshenSoundness

---------------------------------------------------------------------

namespace Strata.PolyProcFreshenNoAbortMask

-- The ship-blocker regression. A poison multi-instantiation of `idp` (int + bool
-- in one body) must NOT abort whole-program type-checking and mask a real bug.
-- `RealBug`'s false `assert (1 == 2)` must still be REPORTED — and at its own
-- label, `assert_0`. Pre-fix, the unify abort suppressed this obligation entirely.
def noAbortMaskPgm : Program :=
#strata
program Core;
procedure idp<a>(x : a, out r : a)
spec {
  free ensures (r == x);
};
procedure RealBug() spec { ensures true; }
{
  assert (1 == 2);
};
procedure Poison() spec { ensures true; }
{
  var ai : int;
  call idp(7, out ai);
  var bb : bool;
  call idp(true, out bb);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Obligation:
false

Label: RealBug_ensures_0
Property: assert
Obligation:
true

Label: Poison_ensures_0
Property: assert
Assumptions:
callElimAssume_idp_ensures_0_7: ai@1 == 7
callElimAssume_idp_ensures_0_3: bb@1 == true
Obligation:
true

---
info:
Obligation: assert_0
Property: assert
Result: ❌ fail

Obligation: RealBug_ensures_0
Property: assert
Result: ✅ pass

Obligation: Poison_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify noAbortMaskPgm

end Strata.PolyProcFreshenNoAbortMask

---------------------------------------------------------------------

namespace Strata.PolyProcFreshenOldInout

-- Exercises the `old`-typed inout freshening branch specifically (the `oldVars`
-- path in `callElimCmd`, distinct from the plain input/output and postcondition
-- freshening the cases above cover). `bump<a>` takes an inout `g : a` and a
-- `free ensures (z == old g)`, so the type of the `old g` temp is the callee's
-- SOURCE type variable `a` and must be freshened per call site like every other
-- slot. `g := 5` before the call makes `old g` load-bearing (≠ the post-call `g`),
-- and the inlined assume becomes `r == 5`, so `assert (r == 5)` passes only if the
-- freshened `old`-typed temp resolved correctly.
def oldInoutPgm : Program :=
#strata
program Core;
procedure bump<a>(inout g : a, out z : a)
spec {
  free ensures (z == old g);
}
{
  z := g;
};
procedure Test(inout g : int, out r : int) spec { ensures true; }
{
  g := 5;
  call bump(g, out g, out r);
  assert (r == 5);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Assumptions:
callElimAssume_bump_ensures_0_5: r@2 == 5
Obligation:
r@2 == 5

Label: Test_ensures_0
Property: assert
Assumptions:
callElimAssume_bump_ensures_0_5: r@2 == 5
Obligation:
true

---
info:
Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify oldInoutPgm

end Strata.PolyProcFreshenOldInout

end
