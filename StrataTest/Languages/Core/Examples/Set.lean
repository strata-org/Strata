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

---------------------------------------------------------------------
-- Extensionality depends on the SMT encoding. Two sets with the same members are
-- equal under the array encoding, but not provably so under the default encoding,
-- whose `Set.*` axioms speak only about membership. The tests run quietly, so they
-- pin the verdicts and not the models the solver chooses.
private def setExtPgm :=
#strata
program Core;

procedure SetExt(s : Set int, t : Set int)
{
  assume [same_members]: (forall x : int :: Set.contains(s, x) == Set.contains(t, x));
  assert [ext]: s == t;
};
#end

/--
info:
Obligation: ext
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Strata.Core.verify setExtPgm (options := .quiet)

/--
info:
Obligation: ext
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify setExtPgm
  (options := { Core.VerifyOptions.quiet with useArrayTheory := true })

---------------------------------------------------------------------
-- `Set` is uninterpreted in Strata, so five pairwise-distinct `Set bool` values are
-- consistent and `assert false` must fail. cvc5 and z3 both define a sort named `Set`
-- (cvc5's has exactly four `Set Bool` values), so the encoder must not emit Strata's
-- sort under that name.
private def setCardPgm :=
#strata
program Core;

procedure SetCard(a : Set bool, b : Set bool, c : Set bool, d : Set bool, e : Set bool)
{
  assume [pairwise_distinct]: !(a == b) && !(a == c) && !(a == d) && !(a == e) && !(b == c) &&
    !(b == d) && !(b == e) && !(c == d) && !(c == e) && !(d == e);
  assert [unreachable]: false;
};
#end

/--
info:
Obligation: unreachable
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Strata.Core.verify setCardPgm (options := .quiet)

/--
info:
Obligation: unreachable
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Strata.Core.verify setCardPgm (options := { Core.VerifyOptions.quiet with solver := "z3" })
