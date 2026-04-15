/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier


-- Regression tests for LoopElim entry invariant soundness:
-- The loop-to-passive transformation must check the loop invariant unconditionally
-- at the loop entry point, before evaluating the guard. This test covers a
-- scenario where a false invariant was previously accepted because the check was
-- placed inside the `ite guard` branch.

namespace Strata

-- false guard (n = 0, so loop never runs).
-- The invariant s == 42 is false (s = 0), and must be caught at entry.
def falseInvariantNeverExecuted :=
#strata
program Core;

procedure zeroIter() returns (s : int)
{
  var n : int;
  n := 0;
  s := 0;
  while (n > 0)
    invariant s == 42
  { s := 42; }
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: entry_invariant_0_0
Property: assert
Obligation:
false

Label: arbitrary_iter_maintain_invariant_0_0
Property: assert
Assumptions:
<dead_branch: #false>: false
<dead_branch: #false>: false
assume_entry_invariant_0_0: false
Obligation:
true



Result: Obligation: entry_invariant_0_0
Property: assert
Result: ❌ always false and is reachable from declaration entry
Model:
($__t.0, false) (n, 0) ($__t.1, false) (s, 0) 


[DEBUG] Evaluated program:
program Core;

procedure zeroIter () returns (s : int)
{
  var $__t.0 : bool := n > 0;
  var $__t.1 : bool := s == 42;
  var n : int;
  n := 0;
  s := 0;
  loop_0: {
    first_iter_asserts_0: {
      assert [entry_invariant_0_0]: false;
      assume [assume_entry_invariant_0_0]: false;
      }
    if (false) {
      arbitrary_iter_facts_0: {
        loop_havoc_0: {
          havoc s;
          }
        arbitrary_iter_assumes_0: {
          assume [assume_guard_0]: $__t.0;
          assume [assume_invariant_0_0]: $__t.1;
          }
        s := 42;
        assert [arbitrary_iter_maintain_invariant_0_0]: $__t.1;
        }
      loop_havoc_0: {
        havoc s;
        }
      assume [not_guard_0]: !$__t.0;
      assume [invariant_0_0]: $__t.1;
      }
    }
  };

---
info:
Obligation: entry_invariant_0_0
Property: assert
Result: ❌ always false and is reachable from declaration entry
Model:
($__t.0, false) (n, 0) ($__t.1, false) (s, 0) 

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass (❗path unreachable)
-/
#guard_msgs in
#eval verify falseInvariantNeverExecuted
        (options := { Core.VerifyOptions.default with checkLevel := .full })

end Strata
