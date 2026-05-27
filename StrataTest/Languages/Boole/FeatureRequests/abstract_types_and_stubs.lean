/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- missing Strata categories/model types
- missing stdlib/pervasive symbols
- examples such as `guide/quants`, `broadcast_proof`, `guide/higher_order_fns`
- Verus links:
  `guide/quants`: https://github.com/verus-lang/verus/blob/main/examples/guide/quants.rs
  `broadcast_proof`: https://github.com/verus-lang/verus/blob/main/examples/broadcast_proof.rs
  `guide/higher_order_fns`: https://github.com/verus-lang/verus/blob/main/examples/guide/higher_order_fns.rs
- Remaining gap: model-type coverage such as `Thread`, `Cell`, `Rwlock`
-/

private def abstractTypesAndStubsSeed : Strata.Program :=
#strata
program Boole;

type Thread;
type Cell;
type Rwlock;
type SeqInt;

function Seq_len(s: SeqInt) : int;

axiom (∀ s: SeqInt . (0 <= Seq_len(s)));

procedure abstract_type_and_stub_seed(s: SeqInt) returns ()
spec {
  requires 0 <= Seq_len(s);
}
{
  assert 0 <= Seq_len(s);
};
#end

/-- info:
Obligation: assert_2_1035
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" abstractTypesAndStubsSeed (options := .quiet)

example : Strata.smtVCsCorrect abstractTypesAndStubsSeed := by
  gen_smt_vcs
  all_goals (try grind)
