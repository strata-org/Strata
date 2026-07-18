program Core;

procedure loopSimple (n : int, out r : int)
spec {
  requires [loopSimple_requires_0]: n >= 0;
  } {
  var sum : int;
  var i : int;
  sum := 0;
  i := 0;
  assert [insertLoopInvAssert_entry_invariant_loop_0_0]: i <= n;
  assert [insertLoopInvAssert_entry_invariant_loop_0_1]: i * (i - 1) div 2 == sum;
  assume [insertLoopInvAssume_entry_invariant_loop_0_0]: i <= n;
  assume [insertLoopInvAssume_entry_invariant_loop_0_1]: i * (i - 1) div 2 == sum;
  if (i < n) {
    loopElim_arbitrary_iter_facts_loop_1: {
      loopElim_havoc_loop_1: {
        havoc sum;
        havoc i;
      }
      assume [loopElimAssume_guard_loop_1]: i < n;
      assume [insertLoopInvAssume_invariant_loop_0_0]: i <= n;
      assume [insertLoopInvAssume_invariant_loop_0_1]: i * (i - 1) div 2 == sum;
      var $__loop_measure_loop_0 : int;
      assume [insertLoopInvAssume_measure_loop_0]: $__loop_measure_loop_0 == n - i;
      assert [insertLoopInvAssert_measure_lb_loop_0]: !($__loop_measure_loop_0 < 0);
      sum := sum + i;
      i := i + 1;
      assert [insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0]: i <= n;
      assert [insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_1]: i * (i - 1) div 2 == sum;
      assert [insertLoopInvAssert_measure_decrease_loop_0]: n - i < $__loop_measure_loop_0;
    }
    loopElim_havoc_loop_1: {
      havoc sum;
      havoc i;
    }
    assume [loopElimAssume_not_guard_loop_1]: !(i < n);
  }
  assume [insertLoopInvAssume_exit_invariant_loop_0_0]: i <= n;
  assume [insertLoopInvAssume_exit_invariant_loop_0_1]: i * (i - 1) div 2 == sum;
  assume [insertLoopInvAssume_exit_not_guard_loop_0]: !(i < n);
  assert [sum_assert]: n * (n - 1) div 2 == sum;
  assert [neg_cond]: i == n;
  r := sum;
};
