/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Languages.Core.Logic.InterpreterHoareRelation
import StrataTest.Languages.Core.Tests.Logic.HoareUtils
import Strata.Languages.Core.ProgramProps
import StrataDDM.Integration.Lean.HashCommands

/-! # Hoare logic for Core programs using `Map`

Each procedure below builds and transforms maps with `mapConst`, `update` (`m[k := v]`) and
`select` (`m[k]`), and its contract is proved as a `Core.Logic.Hoare` triple
(`Procedure.contractTriple`) in every model of `Core.Factory`. The bodies are straight-line, and
every value they compute is a literal, so `Procedure.contractTriple_of_meetsContractOnLits`
proves a contract by running the body with Core's concrete evaluator (`Core.runLits`), whose map
literals (`LConst.mapConst`) carry the default and the entries.
`native_decide` decides the run's premises: `decide +kernel` gets stuck on `LExpr.eval`, on the
`Std.HashMap` lookups behind `Core.Factory[_]?`, and on the type-checked program. The last also
blocks the structural premises (the body's shape, `contractChecksTyped` and the no-functions check),
which all read the type-checked program.

The procedures: a histogram (`Counts`), swapping two entries through a local (`Swap`), a write of
the default that makes a map equal to the constant map again (`ResetToDefault`), a later write
winning over an earlier one (`LastWriteWins`), a set of integers as a `Map int bool`
(`IntSet`), and a two-dimensional grid as a map of maps (`Grid`). `WrongCount` has a false
`ensures`, and the run does not prove it.

Every body also terminates, from an environment binding the outputs and not the locals, so no
execution of it gets stuck (`Core.runLits_terminates`).

Key results: `counts_meets_contract`, `swap_meets_contract`, `resetToDefault_meets_contract`,
`lastWriteWins_meets_contract`, `intSet_meets_contract`, `grid_meets_contract`, and
`counts_terminates`, `swap_terminates`, `resetToDefault_terminates`, `lastWriteWins_terminates`,
`intSet_terminates`, `grid_terminates`, `wrongCount_terminates`.
-/

open StrataDDM (Program)

namespace Strata

open Core.Logic.Hoare
open HoareUtils

private def mapPgm : Program :=
#strata
program Core;

procedure Counts(out m : Map int int)
spec {
  ensures [counts]: m[1] == 2 && m[2] == 1 && m[3] == 0;
}
{
  m := mapConst<int>(0);
  m := m[1 := int.add(m[1], 1)];
  m := m[2 := int.add(m[2], 1)];
  m := m[1 := int.add(m[1], 1)];
};

procedure Swap(out m : Map int int)
spec {
  ensures [swapped]: m[1] == 20 && m[2] == 10;
  ensures [untouched]: m[3] == 0;
}
{
  m := mapConst<int>(0)[1 := 10][2 := 20];
  var t : int := m[1];
  m := m[1 := m[2]];
  m := m[2 := t];
};

procedure ResetToDefault(out m : Map int int)
spec {
  ensures [isConst]: m == mapConst<int>(0);
}
{
  m := mapConst<int>(0)[5 := 7][6 := 8];
  m := m[5 := 0][6 := 0];
};

procedure LastWriteWins(out m : Map int int)
spec {
  ensures [last]: m[1] == 30;
  ensures [sameMap]: m == mapConst<int>(0)[1 := 30];
}
{
  m := mapConst<int>(0)[1 := 10];
  m := m[1 := 20][1 := 30];
};

procedure IntSet(out s : Map int bool, out n : int)
spec {
  ensures [members]: !(s[3]) && s[5] && s[8] && !(s[4]);
  ensures [count]: n == 2;
}
{
  s := mapConst<int>(false)[3 := true][5 := true];
  s := s[3 := false][8 := true];
  n := int.add(int.add(if s[3] then 1 else 0, if s[5] then 1 else 0),
    if s[8] then 1 else 0);
};

procedure Grid(out g : Map int (Map int int))
spec {
  ensures [written]: g[1][2] == 7;
  ensures [sameRow]: g[1][3] == 0;
  ensures [otherRow]: g[0][2] == 0;
}
{
  g := mapConst<int>(mapConst<int>(0));
  g := g[1 := g[1][2 := 7]];
};

procedure WrongCount(out m : Map int int)
spec {
  ensures [wrong]: m[1] == 1;
}
{
  m := mapConst<int>(0)[1 := 1];
  m := m[1 := int.add(m[1], 1)];
};
#end

/-- The type-checked program, whose operators carry their instantiated types. -/
private def mapAST : Core.Program := typeCheckedAST mapPgm

/-! ## A histogram

`Counts` tallies the keys `1, 2, 1` in a map starting at the constant map `0`; reading the map
before each update makes every count depend on the previous ones. -/

/-- **`Counts` meets its contract**: keys `1` and `2` are counted twice and once, and an uncounted
    key stays `0`. -/
theorem counts_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple mapAST testParams "Counts" :=
  contract_by_run mapAST "Counts"

/-! ## Swapping two entries

`Swap` exchanges the values at keys `1` and `2` through the local `t`, which leaving the
procedure drops; the postconditions mention only the output. -/

/-- **`Swap` meets its contract**: the two values are exchanged and the other keys keep the
    default. -/
theorem swap_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple mapAST testParams "Swap" :=
  contract_by_run mapAST "Swap"

/-! ## Writing the default back

Setting a key to the default drops its entry from the literal (`LConst.mapUpdate`), so after both
keys are reset the map literal is the constant map itself and the equality is decided. -/

/-- **`ResetToDefault` meets its contract**: the map equals `mapConst(0)` again. -/
theorem resetToDefault_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple mapAST testParams "ResetToDefault" :=
  contract_by_run mapAST "ResetToDefault"

/-! ## The last write wins

Updating a key replaces its entry, so the map after three writes to key `1` is the map with only
the last one. -/

/-- **`LastWriteWins` meets its contract**: key `1` holds the last value, and the map is the
    constant map updated once. -/
theorem lastWriteWins_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple mapAST testParams "LastWriteWins" :=
  contract_by_run mapAST "LastWriteWins"

/-! ## A set of integers

`IntSet` keeps a set as a `Map int bool` that is `false` by default: inserting is writing `true`,
removing is writing the default back, which drops the entry. -/

/-- **`IntSet` meets its contract**: `3` was removed, `5` and `8` are members, `4` never was, and
    counting the members among `3, 5, 8` gives `2`. -/
theorem intSet_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple mapAST testParams "IntSet" :=
  contract_by_run mapAST "IntSet"

/-! ## A grid as a map of maps

`Grid` writes one cell of a two-dimensional grid by updating a row and writing the row back; the
default of the outer map is itself a map literal. -/

/-- **`Grid` meets its contract**: the written cell holds `7`, and the other cells of its row and
    of another row keep the default. -/
theorem grid_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple mapAST testParams "Grid" :=
  contract_by_run mapAST "Grid"

/-! ## A false postcondition is not proved

`WrongCount` claims key `1` holds `1` after it is incremented to `2`; the run evaluates the
postcondition to `false`, so `contractTriple_of_meetsContractOnLits` does
not apply. -/

example :
    Procedure.meetsContractOnLits fuel (procOf mapAST "WrongCount") (bodyOf mapAST "WrongCount") =
      false := by
  native_decide

/-! ## No execution gets stuck

Each body terminates, from every environment over `Core.Factory` whose store binds every output
to a value of its type and leaves undeclared the locals the body declares, as a procedure's
entry store does: every execution finishes, so none gets stuck
(`EventLang.MustTerminate.not_mayGetStuck`) and none diverges. `Core.runLits_terminates` proves
it from a run of the body with `runLits` in which every write is at the type of its target
(`Core.runLitsProgresses`); `HoareUtils.bodyTerminates_of_progresses` applies it to a
procedure of this file. This covers `WrongCount` as well: its body runs, and only its
postcondition is false. -/

/-- **`Counts` terminates.** -/
theorem counts_terminates : BodyTerminates mapAST "Counts" :=
  bodyTerminates_of_progresses (by native_decide)

/-- **`Swap` terminates**, from a store where its local `t` is undeclared. -/
theorem swap_terminates : BodyTerminates mapAST "Swap" :=
  bodyTerminates_of_progresses (by native_decide)

/-- **`ResetToDefault` terminates.** -/
theorem resetToDefault_terminates : BodyTerminates mapAST "ResetToDefault" :=
  bodyTerminates_of_progresses (by native_decide)

/-- **`LastWriteWins` terminates.** -/
theorem lastWriteWins_terminates : BodyTerminates mapAST "LastWriteWins" :=
  bodyTerminates_of_progresses (by native_decide)

/-- **`IntSet` terminates.** -/
theorem intSet_terminates : BodyTerminates mapAST "IntSet" :=
  bodyTerminates_of_progresses (by native_decide)

/-- **`Grid` terminates.** -/
theorem grid_terminates : BodyTerminates mapAST "Grid" :=
  bodyTerminates_of_progresses (by native_decide)

/-- **`WrongCount` terminates**, although its contract does not hold. -/
theorem wrongCount_terminates : BodyTerminates mapAST "WrongCount" :=
  bodyTerminates_of_progresses (by native_decide)

end Strata
