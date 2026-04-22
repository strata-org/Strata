program Core;

function N () : int;
axiom [ax_N]: 0 <= N;
procedure TwoLoops ()
{
  var i : int;
  var j : int;
  i := 0;
  loop_0: {
    first_iter_asserts_0: {
      assert [entry_invariant_0_0]: 0 <= i && i <= N;
      assume [assume_entry_invariant_0_0]: 0 <= i && i <= N;
    }
    if (i < N) {
      arbitrary_iter_facts_0: {
        loop_havoc_0: {
          havoc i;
        }
        arbitrary_iter_assumes_0: {
          assume [assume_guard_0]: i < N;
          assume [assume_invariant_0_0]: 0 <= i && i <= N;
        }
        i := i + 1;
        assert [arbitrary_iter_maintain_invariant_0_0]: 0 <= i && i <= N;
      }
      loop_havoc_0: {
        havoc i;
      }
      assume [not_guard_0]: !(i < N);
      assume [invariant_0_0]: 0 <= i && i <= N;
    }
  }
  j := 0;
  loop_1: {
    first_iter_asserts_1: {
      assert [entry_invariant_1_0]: 0 <= j && j <= N;
      assume [assume_entry_invariant_1_0]: 0 <= j && j <= N;
    }
    if (j < N) {
      arbitrary_iter_facts_1: {
        loop_havoc_1: {
          havoc j;
        }
        arbitrary_iter_assumes_1: {
          assume [assume_guard_1]: j < N;
          assume [assume_invariant_1_0]: 0 <= j && j <= N;
        }
        j := j + 1;
        assert [arbitrary_iter_maintain_invariant_1_0]: 0 <= j && j <= N;
      }
      loop_havoc_1: {
        havoc j;
      }
      assume [not_guard_1]: !(j < N);
      assume [invariant_1_0]: 0 <= j && j <= N;
    }
  }
};
