program Core;

function N () : int;
axiom [ax_N]: int.le(0, N);
procedure TwoLoops ()
{
  var i : int;
  var j : int;
  i := 0;
  assert [insertLoopInvAssert_entry_invariant_loop_0_0]: int.le(0, i) && int.le(i, N);
  assume [insertLoopInvAssume_entry_invariant_loop_0_0]: int.le(0, i) && int.le(i, N);
  if (int.lt(i, N)) {
    loopElim_arbitrary_iter_facts_loop_2: {
      loopElim_havoc_loop_2: {
        havoc i;
      }
      assume [loopElimAssume_guard_loop_2]: int.lt(i, N);
      assume [insertLoopInvAssume_invariant_loop_0_0]: int.le(0, i) && int.le(i, N);
      i := int.add(i, 1);
      assert [insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0]: int.le(0, i) && int.le(i, N);
    }
    loopElim_havoc_loop_2: {
      havoc i;
    }
    assume [loopElimAssume_not_guard_loop_2]: !(int.lt(i, N));
  }
  assume [insertLoopInvAssume_exit_invariant_loop_0_0]: int.le(0, i) && int.le(i, N);
  assume [insertLoopInvAssume_exit_not_guard_loop_0]: !(int.lt(i, N));
  j := 0;
  assert [insertLoopInvAssert_entry_invariant_loop_1_0]: int.le(0, j) && int.le(j, N);
  assume [insertLoopInvAssume_entry_invariant_loop_1_0]: int.le(0, j) && int.le(j, N);
  if (int.lt(j, N)) {
    loopElim_arbitrary_iter_facts_loop_3: {
      loopElim_havoc_loop_3: {
        havoc j;
      }
      assume [loopElimAssume_guard_loop_3]: int.lt(j, N);
      assume [insertLoopInvAssume_invariant_loop_1_0]: int.le(0, j) && int.le(j, N);
      j := int.add(j, 1);
      assert [insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_1_0]: int.le(0, j) && int.le(j, N);
    }
    loopElim_havoc_loop_3: {
      havoc j;
    }
    assume [loopElimAssume_not_guard_loop_3]: !(int.lt(j, N));
  }
  assume [insertLoopInvAssume_exit_invariant_loop_1_0]: int.le(0, j) && int.le(j, N);
  assume [insertLoopInvAssume_exit_not_guard_loop_1]: !(int.lt(j, N));
};
