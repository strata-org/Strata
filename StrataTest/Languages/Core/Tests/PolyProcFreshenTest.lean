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
(whose free type variable has no SMT sort); the final case adds a non-free
`requires`, inlined as a per-site assert.
-/

namespace Strata.PolyProcFreshenMultiInst

-- One polymorphic procedure called at `int` AND `bool` in a single body.
-- Without per-call-site freshening, this shape would force `a` to unify with
-- both `int` and `bool`, aborting whole-program type-checking. Freshening gives
-- each call its own type variable, so both call-site obligations are
-- well-formed and pass.
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
callElimAssume_idp_ensures_0_3: ai@1 == 7
Obligation:
ai@1 == 7

Label: assert_1
Property: assert
Assumptions:
callElimAssume_idp_ensures_0_3: ai@1 == 7
callElimAssume_idp_ensures_0_7: bb@1 == true
Obligation:
bb@1 == true

Label: Test_ensures_0
Property: assert
Assumptions:
callElimAssume_idp_ensures_0_3: ai@1 == 7
callElimAssume_idp_ensures_0_7: bb@1 == true
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
-- FALSE (`bb == false` after `idp(true)`). Per-call-site instantiation keeps
-- the bool call coupled to its own concrete type, so the WRONG obligation —
-- `assert_1` specifically — fails (not `assert_0`, not merely "one of them").
-- This pins the per-obligation identity that a count-only oracle cannot.
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
callElimAssume_idp_ensures_0_3: ai@1 == 7
Obligation:
ai@1 == 7

Label: assert_1
Property: assert
Assumptions:
callElimAssume_idp_ensures_0_3: ai@1 == 7
callElimAssume_idp_ensures_0_7: bb@1 == true
Obligation:
bb@1 == false

Label: Test_ensures_0
Property: assert
Assumptions:
callElimAssume_idp_ensures_0_3: ai@1 == 7
callElimAssume_idp_ensures_0_7: bb@1 == true
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

-- A poison multi-instantiation of `idp` (int + bool in one body) must NOT abort
-- whole-program type-checking and mask a real bug: `RealBug`'s false
-- `assert (1 == 2)` must still be REPORTED — and at its own label, `assert_0`.
-- Without freshening, the unify abort would suppress this obligation entirely.
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
callElimAssume_idp_ensures_0_3: ai@1 == 7
callElimAssume_idp_ensures_0_7: bb@1 == true
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

---------------------------------------------------------------------

namespace Strata.PolyProcFreshenMultiTypeParam

-- Multi-type-parameter callee (`swap<a, b>`) called at two DIFFERENT
-- instantiations in one body: `swap(1, true, ...)` binds `(a, b) = (int, bool)`,
-- `swap(false, 2, ...)` binds `(a, b) = (bool, int)`. `freshenTypeArgsSubst` zips
-- the callee's type-arg LIST with fresh names, so this exercises the list handling
-- (not just the single-`<a>` shape the cases above cover): a partial zip or a
-- per-parameter (rather than per-typeArg) substitution would leave one of `a`/`b`
-- shared across sites and fail the type check. The (int,bool)/(bool,int) crossing
-- makes each site's `rx`/`ry` slots resolve to opposite concrete types, so the
-- rendered VCs carry each site's contract at its own instantiation and all four
-- assertions pass.
def multiTypeParamPgm : Program :=
#strata
program Core;
procedure swap<a, b>(x : a, y : b, out rx : b, out ry : a)
spec {
  free ensures (rx == y);
  free ensures (ry == x);
};
procedure Test() spec { ensures true; }
{
  var i : int;
  var b : bool;
  call swap(1, true, out b, out i);
  assert (b == true);
  assert (i == 1);
  var b2 : bool;
  var i2 : int;
  call swap(false, 2, out i2, out b2);
  assert (i2 == 2);
  assert (b2 == false);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Assumptions:
callElimAssume_swap_ensures_0_6: b@1 == true
callElimAssume_swap_ensures_1_7: i@1 == 1
Obligation:
b@1 == true

Label: assert_1
Property: assert
Assumptions:
callElimAssume_swap_ensures_0_6: b@1 == true
callElimAssume_swap_ensures_1_7: i@1 == 1
Obligation:
i@1 == 1

Label: assert_2
Property: assert
Assumptions:
callElimAssume_swap_ensures_0_6: b@1 == true
callElimAssume_swap_ensures_1_7: i@1 == 1
callElimAssume_swap_ensures_0_14: i2@1 == 2
callElimAssume_swap_ensures_1_15: b2@1 == false
Obligation:
i2@1 == 2

Label: assert_3
Property: assert
Assumptions:
callElimAssume_swap_ensures_0_6: b@1 == true
callElimAssume_swap_ensures_1_7: i@1 == 1
callElimAssume_swap_ensures_0_14: i2@1 == 2
callElimAssume_swap_ensures_1_15: b2@1 == false
Obligation:
b2@1 == false

Label: Test_ensures_0
Property: assert
Assumptions:
callElimAssume_swap_ensures_0_6: b@1 == true
callElimAssume_swap_ensures_1_7: i@1 == 1
callElimAssume_swap_ensures_0_14: i2@1 == 2
callElimAssume_swap_ensures_1_15: b2@1 == false
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

Obligation: assert_2
Property: assert
Result: ✅ pass

Obligation: assert_3
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify multiTypeParamPgm

end Strata.PolyProcFreshenMultiTypeParam

---------------------------------------------------------------------

namespace Strata.PolyProcFreshenQuantPost

-- Quantified postcondition whose BINDER is annotated with the callee's type
-- variable (`forall y : a :: ...`). Pins per-site rendering of a quantified
-- contract: `pick<a>` at `int` and `bool` yields `forall y : int` at the first
-- site and `forall y : bool` at the second. Note the cross-site unification
-- abort is carried by the `forAll []`-schemed temp declarations (`LTy.instantiate`
-- passes monomorphic schemes through verbatim), not by expression annotations —
-- an annotation is compatibility-checked per occurrence (`tvar_annotated`), so
-- the binder types here are anchored by the spliced concrete arguments. The
-- `.quant` slot of the expression substitution (`replaceUserProvidedType`) is
-- exercised as contract-instantiation hygiene rather than as the abort guard.
def quantPostPgm : Program :=
#strata
program Core;
procedure pick<a>(x : a, out r : a)
spec {
  free ensures (forall y : a :: (y == x) ==> (y == r));
};
procedure Test() spec { ensures true; }
{
  var ai : int;
  call pick(7, out ai);
  assert (ai == 7);
  var bb : bool;
  call pick(true, out bb);
  assert (bb == true);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Assumptions:
callElimAssume_pick_ensures_0_3: forall y : int :: y == 7 ==> y == ai@1
Obligation:
ai@1 == 7

Label: assert_1
Property: assert
Assumptions:
callElimAssume_pick_ensures_0_3: forall y : int :: y == 7 ==> y == ai@1
callElimAssume_pick_ensures_0_7: forall y : bool :: y == true ==> y == bb@1
Obligation:
bb@1 == true

Label: Test_ensures_0
Property: assert
Assumptions:
callElimAssume_pick_ensures_0_3: forall y : int :: y == 7 ==> y == ai@1
callElimAssume_pick_ensures_0_7: forall y : bool :: y == true ==> y == bb@1
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
#eval Core.verify quantPostPgm

end Strata.PolyProcFreshenQuantPost

---------------------------------------------------------------------

namespace Strata.PolyProcFreshenRequires

-- A non-free `requires` is inlined as an ASSERT at each call site. This pins
-- the requires-inlining path end to end at two instantiations: per-site labels
-- (`callElimAssert_req_requires_0_3`/`_0_8`) and per-site binder types
-- (`forall y : int` vs `forall y : bool`). Note the binder types are anchored
-- by the spliced concrete arguments (`y == x` with `x := 7`/`true`), so this
-- exercises the signature-instantiation path shared with the ensures cases;
-- the expression-level substitution on `requires` is not independently
-- observable here (arg splicing re-anchors the annotations).
def reqPgm : Program :=
#strata
program Core;
procedure req<a>(x : a, out r : a)
spec {
  requires (forall y : a :: (y == x) ==> (y == x));
  free ensures (r == x);
};
procedure Test() spec { ensures true; }
{
  var ai : int;
  call req(7, out ai);
  assert (ai == 7);
  var bb : bool;
  call req(true, out bb);
  assert (bb == true);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: callElimAssert_req_requires_0_3
Property: assert
Obligation:
forall y : int :: y == 7 ==> y == 7

Label: assert_0
Property: assert
Assumptions:
callElimAssume_req_ensures_1_4: ai@1 == 7
Obligation:
ai@1 == 7

Label: callElimAssert_req_requires_0_8
Property: assert
Assumptions:
callElimAssume_req_ensures_1_4: ai@1 == 7
Obligation:
forall y : bool :: y == true ==> y == true

Label: assert_1
Property: assert
Assumptions:
callElimAssume_req_ensures_1_4: ai@1 == 7
callElimAssume_req_ensures_1_9: bb@1 == true
Obligation:
bb@1 == true

Label: Test_ensures_0
Property: assert
Assumptions:
callElimAssume_req_ensures_1_4: ai@1 == 7
callElimAssume_req_ensures_1_9: bb@1 == true
Obligation:
true

---
info:
Obligation: callElimAssert_req_requires_0_3
Property: assert
Result: ✅ pass

Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: callElimAssert_req_requires_0_8
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
#eval Core.verify reqPgm

end Strata.PolyProcFreshenRequires

end
