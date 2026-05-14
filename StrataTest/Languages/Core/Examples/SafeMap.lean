/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Core.Verifier


---------------------------------------------------------------------
namespace Strata


def safeMapPgm :=
#strata
program Core;

// --- Type Declarations ---
datatype OptionInt () { None(), Some(val: int) };

// --- Pure Functions ---
function is_present(opt : OptionInt) : bool {
    OptionInt..isSome(opt)
}

// --- Procedures ---
procedure Register(id : int, value : int, inout registry : Map int OptionInt, inout count : int)
spec {
    requires [id_not_in_registry]: !is_present(registry[id]);
    ensures  [registry_id_eq_val]: registry[id] == Some(value);
    ensures  [count_incremented]:  count == old count + 1;
}
{
    registry := registry[id := Some(value)];
    count := count + 1;
};

procedure GetValue(id : int, registry : Map int OptionInt, out res : OptionInt)
spec {
    requires [id_ge_zero]:  id >= 0;
    ensures [value_for_id]: res == registry[id];
}
{
    res := registry[id];
};

procedure Main(inout registry : Map int OptionInt, inout count : int)
spec {
}
{
    assume [count_eq_zero]: count == 0;
    assume [registry_empty]: (forall i : int :: {registry[i]} registry[i] == None());

    call Register(101, 500, registry, count, out registry, out count);

    var result : OptionInt;
    call GetValue(101, registry, out result);

    if (OptionInt..isSome(result)) {
        assert [value_of_101]: OptionInt..val(result) == 500;
    } else {
        // Unreachable, based on `Register` ensures.
        cover [unreachable_cover]: true;
        assert [unreachable_assert]: false;
    }
};
#end

/--
info:
Obligation: registry_id_eq_val
Property: assert
Result: ✅ pass

Obligation: count_incremented
Property: assert
Result: ✅ pass

Obligation: value_for_id
Property: assert
Result: ✅ pass

Obligation: callElimAssert_id_not_in_registry_12
Property: assert
Result: ✅ pass

Obligation: callElimAssert_id_ge_zero_3
Property: assert
Result: ✅ pass

Obligation: assert_value_of_101_calls_OptionInt..val_0
Property: assert
Result: ✅ pass

Obligation: value_of_101
Property: assert
Result: ✅ pass

Obligation: unreachable_cover
Property: cover
Result: ❌ fail

Obligation: unreachable_assert
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify safeMapPgm (options := .quiet)
