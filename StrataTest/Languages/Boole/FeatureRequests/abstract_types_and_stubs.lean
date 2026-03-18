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
-/

private def abstractTypesAndStubsSeed : Strata.Program :=
#strata
program Boole;

// Target shape: more of the Verus library surface, including model types like
// `Thread`, `Cell`, `Rwlock`, and library symbols such as `Seq_len`, `Seq_get`,
// `Map_len`, etc., should appear here exactly as referenced by translation.

type Thread;
type Cell;
type SeqInt;

function Seq_len(s: SeqInt) : int;
function Seq_get(s: SeqInt, i: int) : int;

axiom (forall s: SeqInt :: 0 <= Seq_len(s));

procedure abstract_type_and_stub_seed(s: SeqInt) returns ()
spec {
  requires 0 <= Seq_len(s);
}
{
  assert 0 <= Seq_len(s);
};
#end

#eval Strata.Boole.verify "cvc5" abstractTypesAndStubsSeed

example : Strata.smtVCsCorrect abstractTypesAndStubsSeed := by
  gen_smt_vcs
  all_goals (try grind)
