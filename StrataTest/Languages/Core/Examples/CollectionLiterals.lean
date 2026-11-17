/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
open Strata

/-! # Evaluation of map and sequence operations on literals

The concrete evaluators of the `Map` and `Sequence` operations of `Core.Factory` compute their
result when every argument is a literal, producing `mapConst`/`sequenceConst` literals. -/

---------------------------------------------------------------------

/-- Map operations on literals. A `select` at the symbolic key `k` is not evaluated, so its
    obligation keeps the map literals, printed as `mapConst` and `update` applications, and the
    SMT encoding expands them the same way. -/
private def mapLitPgm :=
#strata
program Core;

const k : int;

procedure MapLits()
{
  var m0 : Map int int;
  var m1 : Map int int;
  var m2 : Map int int;
  var m3 : Map int int;
  m0 := mapConst<int>(0);
  m1 := m0[1 := 10][2 := 20];
  m2 := m0[2 := 20][1 := 10];
  m3 := m1[1 := 0][2 := 0];
  assert [sel_1]: m1[1] == 10;
  assert [sel_2]: m1[2] == 20;
  assert [sel_dflt]: m1[3] == 0;
  assert [overwrite]: m1[1 := 30][1] == 30;
  assert [reset_to_dflt]: m3 == m0;
  assert [sym_key]: m1[k] == m2[k];
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: sel_1
Property: assert
Obligation:
true

Label: sel_2
Property: assert
Obligation:
true

Label: sel_dflt
Property: assert
Obligation:
true

Label: overwrite
Property: assert
Obligation:
true

Label: reset_to_dflt
Property: assert
Obligation:
true

Label: sym_key
Property: assert
Obligation:
(((mapConst<int>(0))[2:=20])[1:=10])[k] == (((mapConst<int>(0))[1:=10])[2:=20])[k]

---
info:
Obligation: sel_1
Property: assert
Result: ✅ pass

Obligation: sel_2
Property: assert
Result: ✅ pass

Obligation: sel_dflt
Property: assert
Result: ✅ pass

Obligation: overwrite
Property: assert
Result: ✅ pass

Obligation: reset_to_dflt
Property: assert
Result: ✅ pass

Obligation: sym_key
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify mapLitPgm

---------------------------------------------------------------------

/-- Sequence operations on literals. `Sequence.take!` past the end has no specified result, so
    its evaluator declines and the obligation keeps the call, its argument printed as
    `Sequence.empty`. -/
private def seqLitPgm :=
#strata
program Core;

procedure SeqLits()
{
  var s : Sequence int;
  var t : Sequence int;
  s := Sequence.build(Sequence.build(Sequence.build(Sequence.empty<int>(), 10), 20), 30);
  t := Sequence.append(s, Sequence.build(Sequence.empty<int>(), 40));
  assert [len]: Sequence.length(t) == 4;
  assert [sel]: Sequence.select(t, 3) == 40;
  assert [upd]: Sequence.select(Sequence.update(t, 0, 5), 0) == 5;
  assert [contains]: Sequence.contains(t, 20);
  assert [not_contains]: !Sequence.contains(t, 25);
  assert [take]: Sequence.take(t, 2) == Sequence.drop(Sequence.take(s, 2), 0);
  assert [drop]: Sequence.length(Sequence.drop(t, 1)) == 3;
  assert [seq_ne]: !(s == t);
  assert [take_oob]: int.ge(Sequence.length(Sequence.take!(Sequence.empty<int>(), 1)), 0);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: len
Property: assert
Obligation:
true

Label: assert_sel_calls_Sequence.select_0
Property: out-of-bounds access check
Obligation:
true

Label: sel
Property: assert
Obligation:
true

Label: assert_upd_calls_Sequence.update_0
Property: out-of-bounds access check
Obligation:
true

Label: assert_upd_calls_Sequence.select_1
Property: out-of-bounds access check
Obligation:
true

Label: upd
Property: assert
Obligation:
true

Label: contains
Property: assert
Obligation:
true

Label: not_contains
Property: assert
Obligation:
true

Label: assert_take_calls_Sequence.take_0
Property: out-of-bounds access check
Obligation:
true

Label: assert_take_calls_Sequence.take_1
Property: out-of-bounds access check
Obligation:
true

Label: assert_take_calls_Sequence.drop_2
Property: out-of-bounds access check
Obligation:
true

Label: take
Property: assert
Obligation:
true

Label: assert_drop_calls_Sequence.drop_0
Property: out-of-bounds access check
Obligation:
true

Label: drop
Property: assert
Obligation:
true

Label: seq_ne
Property: assert
Obligation:
true

Label: take_oob
Property: assert
Obligation:
int.ge(Sequence.length(Sequence.take!(Sequence.empty<int>(), 1)), 0)

---
info:
Obligation: len
Property: assert
Result: ✅ pass

Obligation: assert_sel_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: sel
Property: assert
Result: ✅ pass

Obligation: assert_upd_calls_Sequence.update_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assert_upd_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: upd
Property: assert
Result: ✅ pass

Obligation: contains
Property: assert
Result: ✅ pass

Obligation: not_contains
Property: assert
Result: ✅ pass

Obligation: assert_take_calls_Sequence.take_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assert_take_calls_Sequence.take_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assert_take_calls_Sequence.drop_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: take
Property: assert
Result: ✅ pass

Obligation: assert_drop_calls_Sequence.drop_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: drop
Property: assert
Result: ✅ pass

Obligation: seq_ne
Property: assert
Result: ✅ pass

Obligation: take_oob
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify seqLitPgm

---------------------------------------------------------------------

/-- A nested literal: a map whose values are sequences. The read at the symbolic key `k` is not
    evaluated, so the obligation keeps the map literal and its sequence entry, and the SMT
    encoding names the monomorphized copies of `mapConst`, `update`, `Sequence.empty` and
    `Sequence.build` at both element types. They exist because every literal is built by
    evaluating these operators, which the program calls at those types before monomorphization:
    only `Sequence.build` adds elements and only `update` adds entries. -/
private def nestedLitPgm :=
#strata
program Core;

const k : int;

procedure NestedLits()
{
  var m : Map int (Sequence int);
  m := mapConst<int>(Sequence.empty<int>())[1 := Sequence.build(Sequence.empty<int>(), 7)];
  assert [nested_sym_key]: k == 1 ==> Sequence.length(m[k]) == 1;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: nested_sym_key
Property: assert
Obligation:
k == 1 ==> Sequence.length(((mapConst<int>(Sequence.empty<int>()))[1:=Sequence.build(Sequence.empty<int>(), 7)])[k]) == 1

---
info:
Obligation: nested_sym_key
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify nestedLitPgm
