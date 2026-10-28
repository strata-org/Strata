/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.MetaVerifier

open StrataDDM (Program)

/-!
`gen_smt_vcs` closes `smtVCsCorrect p` with an axiom stating that its goals imply
the denotation of the VCs, so the goals must have the denotation's meaning
(issue #1488): operators are translated with their SMT-LIB semantics, and a VC
the denotation does not cover is refused rather than trusted.
-/

namespace Strata

/-- `bvudiv` by zero is all ones in SMT-LIB, so this assertion holds. -/
def udivPgm : Program :=
#strata
program Core;
procedure P(x : bv W8) {
  assert [udiv_zero]: bv8.uDiv(x, bv{8}(0)) == bv{8}(255);
};
#end

/-- The goal is stated with `BitVec.smtUDiv`, not Lean's `/` (for which it would be false). -/
theorem udivPgm_correct : smtVCsCorrect udivPgm := by
  gen_smt_vcs
  intro x
  rw [BitVec.smtUDiv_zero]
  decide

/-- A VC over a datatype has no denotation, so `smtVCsCorrect` is `False` for this
    program; the tactic must not introduce an axiom proving it. -/
def dtPgm : Program :=
#strata
program Core;
datatype Option () { None(), Some(val: int) };
procedure Q(o : Option) {
  assert [tag]: Option..isSome(o) || Option..isNone(o);
};
#end

/--
error: gen_smt_vcs: verification condition 'tag' uses a datatype, which the denotation of SMT queries does not cover yet, so no Lean goal can be created for it; the SMT path still checks it
-/
#guard_msgs in
example : smtVCsCorrect dtPgm := by
  gen_smt_vcs

end Strata
