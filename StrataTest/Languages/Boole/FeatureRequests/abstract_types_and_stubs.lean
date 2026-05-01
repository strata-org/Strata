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
- Current status: Core has `Sequence` support, but Boole does not yet lower
  Boole `Sequence` types end to end
- Remaining gap: model-type coverage such as `Thread`, `Cell`, `Rwlock`, etc.,
  plus deciding how much stub generation is still needed after translation
  pruning
-/

private def abstractTypesAndStubsSeed : Strata.Program :=
#strata
program Boole;

// Target shape: model/library coverage that still matters after pruning older
// sequence/pervasive scaffolding from translation output.
//
// The Boole frontend still rejects Boole `Sequence` types, so this seed keeps
// abstract stubs for now.

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

#guard_msgs (drop info) in
#eval Strata.Boole.verify "cvc5" abstractTypesAndStubsSeed

example : Strata.smtVCsCorrect abstractTypesAndStubsSeed := by
  gen_smt_vcs
  all_goals (try grind)
