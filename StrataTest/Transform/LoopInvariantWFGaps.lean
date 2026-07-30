/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! # Loop invariant well-formedness gaps

These tests pin the *current* behavior of well-formedness (WF) checking for
loop invariants, which is incomplete and unsound. They exist to document the
gap and to fail loudly when it is fixed.

`PrecondElim` emits invariant WF obligations into the loop's **pre-state**
(`Strata/Transform/PrecondElim.lean`, the `.loop` case). But an invariant is
*assumed* and *re-asserted* at the arbitrary mid-loop state
(`mid_assumes` / `maintain_asserts` in
`Strata/Transform/InsertLoopInvariantAsserts.lean`), which is a strictly weaker
state. Pre-state definedness neither implies nor is implied by definedness at
the loop head.

Core has no program point meaning "at the loop head, before the invariant is
assumed", so there is nowhere correct to put these obligations. See
`docs/CoreLoopInvariantWFBlock.md` for the analysis and a proposed
pre-invariant-proof block.

Contrast `StrataTest/Transform/PrecondElim.lean`, where the same dependency
expressed as a *procedure contract* is handled correctly: `mkContractWFProc`
chains assert-WF-then-assume per clause, so a later clause may rely on an
earlier one.
-/

namespace Strata

/-! ## Defect 1: unsoundness — the mid-loop occurrence gets no WF obligation

`d` starts at `1` and *decreases* toward `0`. The sole division-by-zero
obligation is evaluated in the pre-state, where `d == 1`, so it reduces to
`true` and passes. Meanwhile the invariant is assumed at the mid-loop state
with `d` unconstrained, and the counterexample model below reports `d@1 = 0` —
a state in which the assumed invariant divides by zero. No obligation is ever
generated for that occurrence.

When the pre-invariant-proof block lands, `loop_invariant_usesdiv_calls_*`
should be checked at the loop head instead, and should *fail* here.
-/
def unsoundInvariantWFPgm :=
#strata
program Core;

procedure Unsound(n : int)
spec {
  requires (0 <= n);
}
{
  var i : int;
  var d : int;
  i := 0;
  d := 1;
  while (i < n)
  invariant [usesdiv]: ((n / d) >= 0)
  {
      d := (d - 1);
      i := (i + 1);
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: loop_invariant_usesdiv_calls_Int.SafeDiv_0
Property: division by zero check
Assumptions:
Unsound_requires_0: 0 <= n@1
Obligation:
true

Label: insertLoopInvAssert_entry_invariant_loop_0_0_usesdiv
Property: assert
Assumptions:
Unsound_requires_0: 0 <= n@1
Obligation:
n@1 / 1 >= 0

Label: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0_usesdiv
Property: assert
Assumptions:
<label_ite_cond_true: i < n>: 0 < n@1
loopElimAssume_guard_loop_1: i@1 < n@1
insertLoopInvAssume_invariant_loop_0_0_usesdiv: n@1 / d@1 >= 0
Unsound_requires_0: 0 <= n@1
insertLoopInvAssume_entry_invariant_loop_0_0_usesdiv: n@1 / 1 >= 0
Obligation:
n@1 / (d@1 - 1) >= 0

---
info:
Obligation: loop_invariant_usesdiv_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_0_usesdiv
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0_usesdiv
Property: assert
Result: ❓ unknown
Model:
(n@1, 1) (d@1, 0) (i@1, 0)
-/
#guard_msgs in
#eval Core.verify unsoundInvariantWFPgm

/-! ## Defect 2: incompleteness — no assume-chaining between invariants

Invariant `pos` (`0 < d`) is precisely what makes invariant `usesdiv`
(`n / d`) well-defined. But `invAsserts` in `PrecondElim`'s `.loop` case is a
`flatMap` with no accumulator, so invariant *k* cannot rely on invariants
*0..k-1*.

The claim to read off the VC dump below is the **empty assumption set** on
`loop_invariant_usesdiv_calls_Int.SafeDiv_0`: it is asked to prove `!(d@1 == 0)`
with nothing available, even though the immediately preceding invariant states
`0 < d`. Contrast `Contract_pre_Contract_requires_1_calls_*` further down, which
does carry the earlier clause.

When the pre-invariant-proof block lands and reuses `processCondition`, this
obligation should carry `0 < d` as an assumption.

Incidental to the defect: `d` is unconstrained at entry, so the `entry_invariant`
assertions for both `pos` and `usesdiv` also fail here. That is an ordinary
invariant-not-established failure, not the WF gap; `d` is left unconstrained
only so the WF obligation is not vacuously discharged by the pre-state.
-/
def unchainedInvariantWFPgm :=
#strata
program Core;

procedure Chain(n : int)
{
  var i : int;
  var d : int;
  i := 0;
  havoc d;
  while (i < n)
  invariant [pos]: (0 < d)
  invariant [usesdiv]: ((n / d) >= 0)
  {
      i := (i + 1);
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: loop_invariant_usesdiv_calls_Int.SafeDiv_0
Property: division by zero check
Obligation:
!(d@1 == 0)

Label: insertLoopInvAssert_entry_invariant_loop_0_0_pos
Property: assert
Obligation:
0 < d@1

Label: insertLoopInvAssert_entry_invariant_loop_0_1_usesdiv
Property: assert
Obligation:
n@1 / d@1 >= 0

Label: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0_pos
Property: assert
Assumptions:
<label_ite_cond_true: i < n>: 0 < n@1
loopElimAssume_guard_loop_1: i@1 < n@1
insertLoopInvAssume_invariant_loop_0_0_pos: 0 < d@1
insertLoopInvAssume_invariant_loop_0_1_usesdiv: n@1 / d@1 >= 0
insertLoopInvAssume_entry_invariant_loop_0_0_pos: 0 < d@1
insertLoopInvAssume_entry_invariant_loop_0_1_usesdiv: n@1 / d@1 >= 0
Obligation:
0 < d@1

Label: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_1_usesdiv
Property: assert
Assumptions:
<label_ite_cond_true: i < n>: 0 < n@1
loopElimAssume_guard_loop_1: i@1 < n@1
insertLoopInvAssume_invariant_loop_0_0_pos: 0 < d@1
insertLoopInvAssume_invariant_loop_0_1_usesdiv: n@1 / d@1 >= 0
insertLoopInvAssume_entry_invariant_loop_0_0_pos: 0 < d@1
insertLoopInvAssume_entry_invariant_loop_0_1_usesdiv: n@1 / d@1 >= 0
Obligation:
n@1 / d@1 >= 0

---
info:
Obligation: loop_invariant_usesdiv_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❌ fail
Model:
(d@1, 0) (n@1, 0) (i@1, 0) 

Obligation: insertLoopInvAssert_entry_invariant_loop_0_0_pos
Property: assert
Result: ❌ fail
Model:
(d@1, 0) (n@1, 0) (i@1, 0) 

Obligation: insertLoopInvAssert_entry_invariant_loop_0_1_usesdiv
Property: assert
Result: ❌ fail
Model:
(d@1, 0) (n@1, 0) (i@1, 0) 

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0_pos
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_1_usesdiv
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify unchainedInvariantWFPgm

/-! ## Contrast: the same dependency in a contract works

`mkContractWFProc` chains assert-WF-then-assume per clause, so `requires 0 < d`
is available as an assumption when checking WF of `requires (n / d) >= 0`.
This is the discipline that loop invariants lack, and that the proposed block
would let them reuse.
-/
def contractChainingPgm :=
#strata
program Core;

procedure Contract(n : int, d : int)
spec {
  requires (0 < d);
  requires ((n / d) >= 0);
}
{
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: Contract_pre_Contract_requires_1_calls_Int.SafeDiv_0
Property: division by zero check
Assumptions:
Contract_requires_0: 0 < d@1
Obligation:
!(d@1 == 0)

---
info:
Obligation: Contract_pre_Contract_requires_1_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify contractChainingPgm

end Strata
end
