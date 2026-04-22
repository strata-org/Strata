program Core;

procedure loopSimple (n : int, out r : int)
spec {
  requires [loopSimple_requires_0]: n >= 0;
  } {
  var sum : int;
  var i : int;
  sum := 0;
  i := 0;
  loop_0: {
    first_iter_asserts_0: {
      assert [entry_invariant_0_0]: i <= n;
      assert [entry_invariant_0_1]: i * (i - 1) div 2 == sum;
      assume [assume_entry_invariant_0_0]: i <= n;
      assume [assume_entry_invariant_0_1]: i * (i - 1) div 2 == sum;
    }
    if (i < n) {
      arbitrary_iter_facts_0: {
        loop_havoc_0: {
          havoc sum;
          havoc i;
        }
        arbitrary_iter_assumes_0: {
          assume [assume_guard_0]: i < n;
          assume [assume_invariant_0_0]: i <= n;
          assume [assume_invariant_0_1]: i * (i - 1) div 2 == sum;
        }
        var $__loop_measure_0 : int;
        assume [assume_measure_0]: $__loop_measure_0 == n - i;
        assert [measure_lb_0]: !($__loop_measure_0 < 0);
        sum := sum + i;
        i := i + 1;
        assert [arbitrary_iter_maintain_invariant_0_0]: i <= n;
        assert [arbitrary_iter_maintain_invariant_0_1]: i * (i - 1) div 2 == sum;
        assert [measure_decrease_0]: n - i < $__loop_measure_0;
      }
      loop_havoc_0: {
        havoc sum;
        havoc i;
      }
      assume [not_guard_0]: !(i < n);
      assume [invariant_0_0]: i <= n;
      assume [invariant_0_1]: i * (i - 1) div 2 == sum;
    }
  }
  assert [sum_assert]: n * (n - 1) div 2 == sum;
  assert [neg_cond]: i == n;
  r := sum;
};
