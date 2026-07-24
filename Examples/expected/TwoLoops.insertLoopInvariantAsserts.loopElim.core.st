program Core;

function N () : int;
axiom [ax_N]: 0 <= N;
procedure TwoLoops ()
{
  var i : int;
  var j : int;
  i := 0;
  assert [insertLoopInvAssert_entry_invariant_loop_0_0]: 0 <= i && i <= N;
  assume [insertLoopInvAssume_entry_invariant_loop_0_0]: 0 <= i && i <= N;
  if (i < N) {
    loopElim_arbitrary_iter_facts_loop_2: {
      loopElim_havoc_loop_2: {
        havoc i;
      }
      assume [loopElimAssume_guard_loop_2]: i < N;
      assume [insertLoopInvAssume_invariant_loop_0_0]: 0 <= i && i <= N;
      i := i + 1;
      assert [insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0]: 0 <= i && i <= N;
    }
    loopElim_havoc_loop_2: {
      havoc i;
    }
    assume [loopElimAssume_not_guard_loop_2]: !(i < N);
  }
  assume [insertLoopInvAssume_exit_invariant_loop_0_0]: 0 <= i && i <= N;
  assume [insertLoopInvAssume_exit_not_guard_loop_0]: !(i < N);
  j := 0;
  assert [insertLoopInvAssert_entry_invariant_loop_1_0]: 0 <= j && j <= N;
  assume [insertLoopInvAssume_entry_invariant_loop_1_0]: 0 <= j && j <= N;
  if (j < N) {
    loopElim_arbitrary_iter_facts_loop_3: {
      loopElim_havoc_loop_3: {
        havoc j;
      }
      assume [loopElimAssume_guard_loop_3]: j < N;
      assume [insertLoopInvAssume_invariant_loop_1_0]: 0 <= j && j <= N;
      j := j + 1;
      assert [insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_1_0]: 0 <= j && j <= N;
    }
    loopElim_havoc_loop_3: {
      havoc j;
    }
    assume [loopElimAssume_not_guard_loop_3]: !(j < N);
  }
  assume [insertLoopInvAssume_exit_invariant_loop_1_0]: 0 <= j && j <= N;
  assume [insertLoopInvAssume_exit_not_guard_loop_1]: !(j < N);
};
