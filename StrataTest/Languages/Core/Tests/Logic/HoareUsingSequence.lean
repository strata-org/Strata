/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Languages.Core.Logic.InterpreterHoareRelation
import StrataTest.Languages.Core.Tests.Logic.HoareUtils
import Strata.Languages.Core.ProgramProps
import StrataDDM.Integration.Lean.HashCommands

/-! # Hoare logic for Core programs using `Sequence`

Each procedure below builds and transforms sequences with `Sequence.empty`, `Sequence.build`,
`Sequence.select`, `Sequence.update`, `Sequence.append`, `Sequence.take`, `Sequence.drop`,
`Sequence.contains` and `Sequence.length`, and its contract is proved as a `Core.Logic.Hoare`
triple (`Procedure.contractTriple`) in every model of `Core.Factory`. The bodies are
straight-line, and every value they compute is a literal, so
`Procedure.contractTriple_of_meetsContractOnLits` proves a contract by running the body with
Core's concrete evaluator (`Core.runLits`), whose sequence literals (`LConst.sequenceConst`) hold
the elements. `native_decide` decides the run's premises: `decide +kernel` gets stuck on
`LExpr.eval`, on the `Std.HashMap` lookups behind `Core.Factory[_]?`, and on the type-checked
program. The last also blocks the structural premises (the body's shape, `contractChecksTyped` and
the no-functions check), which all read the type-checked program.

The procedures: building a sequence and reading it back (`Build3`), reversing one by reading
its elements (`Reverse3`), splitting one with `take` and `drop` and joining the halves
(`SplitJoin`), writing one element (`UpdateAt`), membership (`Members`), and the sum of a
sequence's elements (`Sum3`). Two do not get a proof: `OutOfBounds` reads past the end, where
`Sequence.select` has no specified value, so the evaluator declines and the run stops; and
`WrongLength` has a false `ensures`.

Every body but `OutOfBounds`'s also terminates, from an environment binding the outputs and not
the locals, so no execution of it gets stuck (`Core.runLits_terminates`).

Key results: `build3_meets_contract`, `reverse3_meets_contract`, `splitJoin_meets_contract`,
`updateAt_meets_contract`, `members_meets_contract`, `sum3_meets_contract`, and
`build3_terminates`, `reverse3_terminates`, `splitJoin_terminates`, `updateAt_terminates`,
`members_terminates`, `sum3_terminates`, `wrongLength_terminates`.
-/

open StrataDDM (Program)

namespace Strata

open Core.Logic.Hoare
open HoareUtils

private def seqPgm : Program :=
#strata
program Core;

procedure Build3(out s : Sequence int, out n : int)
spec {
  ensures [length]: n == 3;
  ensures [elements]: Sequence.select(s, 0) == 10 && Sequence.select(s, 1) == 20 &&
    Sequence.select(s, 2) == 30;
}
{
  s := Sequence.build(Sequence.build(Sequence.build(Sequence.empty<int>(), 10), 20), 30);
  n := Sequence.length(s);
};

procedure Reverse3(out t : Sequence int)
spec {
  ensures [reversed]: t ==
    Sequence.build(Sequence.build(Sequence.build(Sequence.empty<int>(), 3), 2), 1);
}
{
  var s : Sequence int :=
    Sequence.build(Sequence.build(Sequence.build(Sequence.empty<int>(), 1), 2), 3);
  t := Sequence.empty<int>();
  t := Sequence.build(t, Sequence.select(s, 2));
  t := Sequence.build(t, Sequence.select(s, 1));
  t := Sequence.build(t, Sequence.select(s, 0));
};

procedure SplitJoin(out s : Sequence int, out u : Sequence int)
spec {
  ensures [joined]: u == s;
  ensures [halves]: Sequence.length(Sequence.take(s, 2)) == 2 &&
    Sequence.select(Sequence.drop(s, 2), 0) == 3;
}
{
  s := Sequence.build(Sequence.build(Sequence.build(Sequence.build(
    Sequence.empty<int>(), 1), 2), 3), 4);
  var front : Sequence int := Sequence.take(s, 2);
  var back : Sequence int := Sequence.drop(s, 2);
  u := Sequence.append(front, back);
};

procedure UpdateAt(out s : Sequence int)
spec {
  ensures [written]: Sequence.select(s, 1) == 99;
  ensures [others]: Sequence.select(s, 0) == 10 && Sequence.select(s, 2) == 30;
  ensures [length]: Sequence.length(s) == 3;
}
{
  s := Sequence.build(Sequence.build(Sequence.build(Sequence.empty<int>(), 10), 20), 30);
  s := Sequence.update(s, 1, 99);
};

procedure Members(out b : bool)
spec {
  ensures [members]: b;
}
{
  var s : Sequence int :=
    Sequence.build(Sequence.build(Sequence.empty<int>(), 20), 40);
  b := Sequence.contains(s, 20) && Sequence.contains(s, 40) && !Sequence.contains(s, 25);
};

procedure Sum3(out total : int)
spec {
  ensures [sum]: total == 60;
}
{
  var s : Sequence int :=
    Sequence.build(Sequence.build(Sequence.build(Sequence.empty<int>(), 10), 20), 30);
  total := 0;
  total := int.add(total, Sequence.select(s, 0));
  total := int.add(total, Sequence.select(s, 1));
  total := int.add(total, Sequence.select(s, 2));
};

procedure OutOfBounds(out r : int)
spec {
  ensures [anything]: r == 0;
}
{
  var s : Sequence int := Sequence.build(Sequence.empty<int>(), 10);
  r := Sequence.select!(s, 5);
};

procedure WrongLength(out n : int)
spec {
  ensures [wrong]: n == 3;
}
{
  var s : Sequence int := Sequence.build(Sequence.build(Sequence.empty<int>(), 1), 2);
  n := Sequence.length(s);
};
#end

/-- The type-checked program, whose operators carry their instantiated types. -/
private def seqAST : Core.Program := typeCheckedAST seqPgm

/-! ## Building a sequence and reading it back

`Build3` appends three elements to the empty sequence; its length and elements are the literal's. -/

/-- **`Build3` meets its contract**: the sequence has three elements, in the order they were
    appended. -/
theorem build3_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple seqAST testParams "Build3" :=
  contract_by_run seqAST "Build3"

/-! ## Reversing a sequence

`Reverse3` reads the elements of the local `s` from last to first into `t`. Sequence literals of
a sort without `Map` are equal exactly when their elements are (`LConst.eql`), so the equality
with the reversed literal is decided. -/

/-- **`Reverse3` meets its contract**: `t` is `s` reversed. -/
theorem reverse3_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple seqAST testParams "Reverse3" :=
  contract_by_run seqAST "Reverse3"

/-! ## Splitting and joining

`SplitJoin` splits a sequence at index `2` with `take` and `drop` and appends the halves. -/

/-- **`SplitJoin` meets its contract**: joining the halves gives the sequence back, and each half
    is where the split put it. -/
theorem splitJoin_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple seqAST testParams "SplitJoin" :=
  contract_by_run seqAST "SplitJoin"

/-! ## Writing one element

`UpdateAt` overwrites the element at index `1`, within bounds. -/

/-- **`UpdateAt` meets its contract**: the written element changes, the others and the length do
    not. -/
theorem updateAt_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple seqAST testParams "UpdateAt" :=
  contract_by_run seqAST "UpdateAt"

/-! ## Membership

`Members` tests two elements of a sequence and one value that is not in it. -/

/-- **`Members` meets its contract**: `20` and `40` are in the sequence and `25` is not. -/
theorem members_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple seqAST testParams "Members" :=
  contract_by_run seqAST "Members"

/-! ## Summing the elements

`Sum3` adds the elements of a sequence one by one into an accumulator. -/

/-- **`Sum3` meets its contract**: the elements add up to `60`. -/
theorem sum3_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple seqAST testParams "Sum3" :=
  contract_by_run seqAST "Sum3"

/-! ## Reading past the end

`Sequence.select!` past the end of a sequence has no specified value: no axiom constrains it. The
evaluator declines there instead of choosing one, so the run stops and proves nothing, neither
the contract nor termination. -/

example : Core.runLits fuel [] (bodyOf seqAST "OutOfBounds") = none := by native_decide

/-! ## A false postcondition is not proved

`WrongLength` claims a two-element sequence has length `3`; the run evaluates the postcondition
to `false`, so `contractTriple_of_meetsContractOnLits` does not
apply. -/

example :
    Procedure.meetsContractOnLits fuel (procOf seqAST "WrongLength") (bodyOf seqAST "WrongLength") =
      false := by
  native_decide

/-! ## No execution gets stuck

Each body terminates, from every environment over `Core.Factory` whose store binds every output
to a value of its type and leaves undeclared the locals the body declares, as a procedure's
entry store does: every execution finishes, so none gets stuck
(`EventLang.MustTerminate.not_mayGetStuck`) and none diverges. `Core.runLits_terminates` proves
it from a run of the body with `runLits` in which every write is at the type of its target
(`Core.runLitsProgresses`); `HoareUtils.bodyTerminates_of_progresses` applies it to a
procedure of this file. This covers `WrongLength` as well: its body runs, and only its
postcondition is false. -/

/-- **`Build3` terminates.** -/
theorem build3_terminates : BodyTerminates seqAST "Build3" :=
  bodyTerminates_of_progresses (by native_decide)

/-- **`Reverse3` terminates**, from a store where its local `s` is undeclared. -/
theorem reverse3_terminates : BodyTerminates seqAST "Reverse3" :=
  bodyTerminates_of_progresses (by native_decide)

/-- **`SplitJoin` terminates**, from a store where its locals `front` and `back` are
    undeclared. -/
theorem splitJoin_terminates : BodyTerminates seqAST "SplitJoin" :=
  bodyTerminates_of_progresses (by native_decide)

/-- **`UpdateAt` terminates.** -/
theorem updateAt_terminates : BodyTerminates seqAST "UpdateAt" :=
  bodyTerminates_of_progresses (by native_decide)

/-- **`Members` terminates**, from a store where its local `s` is undeclared. -/
theorem members_terminates : BodyTerminates seqAST "Members" :=
  bodyTerminates_of_progresses (by native_decide)

/-- **`Sum3` terminates**, from a store where its local `s` is undeclared. -/
theorem sum3_terminates : BodyTerminates seqAST "Sum3" :=
  bodyTerminates_of_progresses (by native_decide)

/-- **`WrongLength` terminates**, although its contract does not hold. -/
theorem wrongLength_terminates : BodyTerminates seqAST "WrongLength" :=
  bodyTerminates_of_progresses (by native_decide)

end Strata
