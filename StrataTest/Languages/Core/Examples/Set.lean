/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
open Strata

---------------------------------------------------------------------
-- A Set program read from text: type checking infers the element types
-- of the Set operators, and the SMT encoding proves the assertions.
private def setPgm :=
#strata
program Core;

procedure SetOps()
{
  assert [contains_inserted]: Set.contains(Set.insert(Set.empty<int>(), 1), 1);
  assert [not_in_empty]: !Set.contains(Set.empty<int>(), 1);
  assert [removed]:
    !Set.contains(Set.remove(Set.insert(Set.empty<int>(), 1), 1), 1);
  assert [in_union]:
    Set.contains(Set.union(Set.insert(Set.empty<int>(), 1),
                           Set.insert(Set.empty<int>(), 2)), 2);
  assert [in_intersect]:
    Set.contains(Set.intersect(Set.insert(Set.empty<int>(), 1),
                               Set.insert(Set.empty<int>(), 1)), 1);
  assert [not_in_difference]:
    !Set.contains(Set.difference(Set.insert(Set.empty<int>(), 1),
                                 Set.insert(Set.empty<int>(), 1)), 1);
};
#end

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram setPgm) |>.snd |>.isEmpty

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: contains_inserted
Property: assert
Obligation:
Set.contains(Set.insert(Set.empty<int>(), 1), 1)

Label: not_in_empty
Property: assert
Obligation:
!(Set.contains(Set.empty<int>(), 1))

Label: removed
Property: assert
Obligation:
!(Set.contains(Set.remove(Set.insert(Set.empty<int>(), 1), 1), 1))

Label: in_union
Property: assert
Obligation:
Set.contains(Set.union(Set.insert(Set.empty<int>(), 1), Set.insert(Set.empty<int>(), 2)), 2)

Label: in_intersect
Property: assert
Obligation:
Set.contains(Set.intersect(Set.insert(Set.empty<int>(), 1), Set.insert(Set.empty<int>(), 1)), 1)

Label: not_in_difference
Property: assert
Obligation:
!(Set.contains(Set.difference(Set.insert(Set.empty<int>(), 1), Set.insert(Set.empty<int>(), 1)), 1))

---
info:
Obligation: contains_inserted
Property: assert
Result: ✅ pass

Obligation: not_in_empty
Property: assert
Result: ✅ pass

Obligation: removed
Property: assert
Result: ✅ pass

Obligation: in_union
Property: assert
Result: ✅ pass

Obligation: in_intersect
Property: assert
Result: ✅ pass

Obligation: not_in_difference
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify setPgm
