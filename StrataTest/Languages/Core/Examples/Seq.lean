/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Transform.SeqTotalize
import StrataDDM.Integration.Lean.HashCommands

meta section
open Strata

---------------------------------------------------------------------
private def seqPgm :=
#strata
program Core;

const s : Sequence int;

procedure P()
{
  var t : Sequence int;

  t := Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30);
  assume [s_empty]: Sequence.length(s) == 0;

  assert [t_length]: Sequence.length(t) == 3;
  assert [t_0]: Sequence.select(t, 0) == 10;
  assert [t_1]: Sequence.select(t, 1) == 20;
  assert [t_2]: Sequence.select(t, 2) == 30;

  // This should fail: length is 3, not 0
  assert [t_length_wrong]: Sequence.length(t) == 0;
};
#end

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram seqPgm) |>.snd |>.isEmpty

/--
info: program Core;

function s () : Sequence int;
procedure P ()
{
  var t : (Sequence int);
  t := Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30);
  assume [s_empty]: Sequence.length(s) == 0;
  assert [t_length]: Sequence.length(t) == 3;
  assert [t_0]: Sequence.select(t, 0) == 10;
  assert [t_1]: Sequence.select(t, 1) == 20;
  assert [t_2]: Sequence.select(t, 2) == 30;
  assert [t_length_wrong]: Sequence.length(t) == 0;
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram seqPgm) |>.fst

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: t_length
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.length(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30)) == 3

Label: assert_t_0_calls_Sequence.select_0
Property: out-of-bounds access check
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
int.lt(0, Sequence.length(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30)))

Label: t_0
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select!(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 0) == 10

Label: assert_t_1_calls_Sequence.select_0
Property: out-of-bounds access check
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
int.lt(1, Sequence.length(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30)))

Label: t_1
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select!(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1) == 20

Label: assert_t_2_calls_Sequence.select_0
Property: out-of-bounds access check
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
int.lt(2, Sequence.length(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30)))

Label: t_2
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select!(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 2) == 30

Label: t_length_wrong
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.length(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30)) == 0

---
info:
Obligation: t_length
Property: assert
Result: ✅ pass

Obligation: assert_t_0_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: t_0
Property: assert
Result: ✅ pass

Obligation: assert_t_1_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: t_1
Property: assert
Result: ✅ pass

Obligation: assert_t_2_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: t_2
Property: assert
Result: ✅ pass

Obligation: t_length_wrong
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Strata.Core.verify seqPgm

---------------------------------------------------------------------
-- Additional tests for append, update, contains, take, and drop.
---------------------------------------------------------------------

private def seqOpsPgm :=
#strata
program Core;

const s : Sequence int;

procedure SeqOps()
{
  var t : Sequence int;
  var u : Sequence int;
  var v : Sequence int;

  // Build a sequence [10, 20, 30]
  t := Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30);
  assume [s_empty]: Sequence.length(s) == 0;

  // --- append ---
  u := Sequence.build(Sequence.build(s, 40), 50);
  v := Sequence.append(t, u);
  assert [append_length]: Sequence.length(v) == 5;
  assert [append_elem_0]: Sequence.select(v, 0) == 10;
  assert [append_elem_4]: Sequence.select(v, 4) == 50;

  // --- update ---
  u := Sequence.update(t, 1, 99);
  assert [update_length]: Sequence.length(u) == 3;
  assert [update_same]: Sequence.select(u, 1) == 99;
  assert [update_other]: Sequence.select(u, 0) == 10;

  // --- contains ---
  assert [contains_yes]: Sequence.contains(t, 20);

  // --- take ---
  u := Sequence.take(t, 2);
  assert [take_length]: Sequence.length(u) == 2;
  assert [take_elem]: Sequence.select(u, 0) == 10;

  // --- drop ---
  u := Sequence.drop(t, 1);
  assert [drop_length]: Sequence.length(u) == 2;
  assert [drop_elem]: Sequence.select(u, 0) == 20;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram seqOpsPgm) |>.snd |>.isEmpty

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: append_length
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.length(Sequence.append(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), Sequence.build(Sequence.build(s, 40), 50))) == 5

Label: assert_append_elem_0_calls_Sequence.select_0
Property: out-of-bounds access check
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
int.lt(0, Sequence.length(Sequence.append(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), Sequence.build(Sequence.build(s, 40), 50))))

Label: append_elem_0
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select!(Sequence.append(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), Sequence.build(Sequence.build(s, 40), 50)), 0) == 10

Label: assert_append_elem_4_calls_Sequence.select_0
Property: out-of-bounds access check
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
int.lt(4, Sequence.length(Sequence.append(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), Sequence.build(Sequence.build(s, 40), 50))))

Label: append_elem_4
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select!(Sequence.append(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), Sequence.build(Sequence.build(s, 40), 50)), 4) == 50

Label: set_u_calls_Sequence.update_0
Property: out-of-bounds access check
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
int.lt(1, Sequence.length(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30)))

Label: update_length
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.length(Sequence.update!(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1, 99)) == 3

Label: assert_update_same_calls_Sequence.select_0
Property: out-of-bounds access check
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
int.lt(1, Sequence.length(Sequence.update!(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1, 99)))

Label: update_same
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select!(Sequence.update!(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1, 99), 1) == 99

Label: assert_update_other_calls_Sequence.select_0
Property: out-of-bounds access check
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
int.lt(0, Sequence.length(Sequence.update!(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1, 99)))

Label: update_other
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select!(Sequence.update!(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1, 99), 0) == 10

Label: contains_yes
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.contains(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 20)

Label: set_u_calls_Sequence.take_0
Property: out-of-bounds access check
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
int.le(2, Sequence.length(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30)))

Label: take_length
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.length(Sequence.take!(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 2)) == 2

Label: assert_take_elem_calls_Sequence.select_0
Property: out-of-bounds access check
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
int.lt(0, Sequence.length(Sequence.take!(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 2)))

Label: take_elem
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select!(Sequence.take!(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 2), 0) == 10

Label: set_u_calls_Sequence.drop_0
Property: out-of-bounds access check
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
int.le(1, Sequence.length(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30)))

Label: drop_length
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.length(Sequence.drop!(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1)) == 2

Label: assert_drop_elem_calls_Sequence.select_0
Property: out-of-bounds access check
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
int.lt(0, Sequence.length(Sequence.drop!(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1)))

Label: drop_elem
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select!(Sequence.drop!(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1), 0) == 20

---
info:
Obligation: append_length
Property: assert
Result: ✅ pass

Obligation: assert_append_elem_0_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: append_elem_0
Property: assert
Result: ✅ pass

Obligation: assert_append_elem_4_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: append_elem_4
Property: assert
Result: ✅ pass

Obligation: set_u_calls_Sequence.update_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: update_length
Property: assert
Result: ✅ pass

Obligation: assert_update_same_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: update_same
Property: assert
Result: ✅ pass

Obligation: assert_update_other_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: update_other
Property: assert
Result: ✅ pass

Obligation: contains_yes
Property: assert
Result: ❓ unknown

Obligation: set_u_calls_Sequence.take_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: take_length
Property: assert
Result: ✅ pass

Obligation: assert_take_elem_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: take_elem
Property: assert
Result: ✅ pass

Obligation: set_u_calls_Sequence.drop_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: drop_length
Property: assert
Result: ✅ pass

Obligation: assert_drop_elem_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: drop_elem
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify seqOpsPgm

---------------------------------------------------------------------

----------------------------------------------------------------------
-- Tests for Sequence.empty<T>() syntax (issue #1027)
----------------------------------------------------------------------

private def seqEmptyPgm :=
#strata
program Core;

procedure SeqEmpty()
{
  var s : Sequence int;

  // Create an empty sequence using Sequence.empty syntax
  s := Sequence.empty<int>();
  assert [empty_length]: Sequence.length(s) == 0;

  // Build on top of an empty sequence
  s := Sequence.build(Sequence.empty<int>(), 42);
  assert [build_on_empty_length]: Sequence.length(s) == 1;
  assert [build_on_empty_elem]: Sequence.select(s, 0) == 42;
};
#end

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram seqEmptyPgm) |>.snd |>.isEmpty

/--
info: program Core;

procedure SeqEmpty ()
{
  var s : (Sequence int);
  s := Sequence.empty<int>();
  assert [empty_length]: Sequence.length(s) == 0;
  s := Sequence.build(Sequence.empty<int>(), 42);
  assert [build_on_empty_length]: Sequence.length(s) == 1;
  assert [build_on_empty_elem]: Sequence.select(s, 0) == 42;
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram seqEmptyPgm) |>.fst

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: empty_length
Property: assert
Obligation:
true

Label: build_on_empty_length
Property: assert
Obligation:
true

Label: assert_build_on_empty_elem_calls_Sequence.select_0
Property: out-of-bounds access check
Obligation:
true

Label: build_on_empty_elem
Property: assert
Obligation:
true

---
info:
Obligation: empty_length
Property: assert
Result: ✅ pass

Obligation: build_on_empty_length
Property: assert
Result: ✅ pass

Obligation: assert_build_on_empty_elem_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: build_on_empty_elem
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify seqEmptyPgm

----------------------------------------------------------------------

-- Exercise various element types for Sequence.empty<T>().
private def seqEmptyTypesPgm :=
#strata
program Core;

procedure SeqEmptyTypes()
{
  var sb : Sequence bool;
  var ssi : Sequence (Sequence int);
  var smi : Sequence (Map int bool);

  sb := Sequence.empty<bool>();
  ssi := Sequence.empty<Sequence int>();
  smi := Sequence.empty<Map int bool>();

  assert [bool_len]: Sequence.length(sb) == 0;
  assert [seq_seq_len]: Sequence.length(ssi) == 0;
  assert [seq_map_len]: Sequence.length(smi) == 0;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram seqEmptyTypesPgm) |>.snd |>.isEmpty

/--
info: program Core;

procedure SeqEmptyTypes ()
{
  var sb : (Sequence bool);
  var ssi : (Sequence (Sequence int));
  var smi : (Sequence (Map int bool));
  sb := Sequence.empty<bool>();
  ssi := Sequence.empty<Sequence int>();
  smi := Sequence.empty<Map int bool>();
  assert [bool_len]: Sequence.length(sb) == 0;
  assert [seq_seq_len]: Sequence.length(ssi) == 0;
  assert [seq_map_len]: Sequence.length(smi) == 0;
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram seqEmptyTypesPgm) |>.fst

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: bool_len
Property: assert
Obligation:
true

Label: seq_seq_len
Property: assert
Obligation:
true

Label: seq_map_len
Property: assert
Obligation:
true

---
info:
Obligation: bool_len
Property: assert
Result: ✅ pass

Obligation: seq_seq_len
Property: assert
Result: ✅ pass

Obligation: seq_map_len
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify seqEmptyTypesPgm

-- select! on a ground-pinned sequence: no out-of-bounds obligation emitted.

private def seqSelectBangPgm :=
#strata
program Core;

const g : Sequence int;

procedure P()
{
  // Pin a length-2 sequence [10, 20] with ground facts.
  assume [g_len]: Sequence.length(g) == 2;
  assume [g_0]: Sequence.select!(g, 0) == 10;
  assume [g_1]: Sequence.select!(g, 1) == 20;

  assert [read_0]: Sequence.select!(g, 0) == 10;
  assert [read_1]: Sequence.select!(g, 1) == 20;
};
#end

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram seqSelectBangPgm) |>.snd |>.isEmpty

/--
info: program Core;

function g () : Sequence int;
procedure P ()
{
  assume [g_len]: Sequence.length(g) == 2;
  assume [g_0]: Sequence.select!(g, 0) == 10;
  assume [g_1]: Sequence.select!(g, 1) == 20;
  assert [read_0]: Sequence.select!(g, 0) == 10;
  assert [read_1]: Sequence.select!(g, 1) == 20;
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram seqSelectBangPgm) |>.fst

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: read_0
Property: assert
Assumptions:
g_len: Sequence.length(g) == 2
g_0: Sequence.select!(g, 0) == 10
g_1: Sequence.select!(g, 1) == 20
Obligation:
Sequence.select!(g, 0) == 10

Label: read_1
Property: assert
Assumptions:
g_len: Sequence.length(g) == 2
g_0: Sequence.select!(g, 0) == 10
g_1: Sequence.select!(g, 1) == 20
Obligation:
Sequence.select!(g, 1) == 20

---
info:
Obligation: read_0
Property: assert
Result: ✅ pass

Obligation: read_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify seqSelectBangPgm

-- select! reasons through constructors (build) via its interaction axioms.

private def seqSelectBangBuildPgm :=
#strata
program Core;

const s : Sequence int;

procedure P()
{
  var t : Sequence int;

  t := Sequence.build(Sequence.build(s, 10), 20);
  assume [s_empty]: Sequence.length(s) == 0;

  assert [reads_20]: Sequence.select!(t, 1) == 20;
  assert [reads_10]: Sequence.select!(t, 0) == 10;
};
#end

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram seqSelectBangBuildPgm) |>.snd |>.isEmpty

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: reads_20
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select!(Sequence.build(Sequence.build(s, 10), 20), 1) == 20

Label: reads_10
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select!(Sequence.build(Sequence.build(s, 10), 20), 0) == 10

---
info:
Obligation: reads_20
Property: assert
Result: ✅ pass

Obligation: reads_10
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify seqSelectBangBuildPgm

-- `Sequence.select!` equals `Sequence.select` wherever the latter's precondition
-- holds, so a fact stated with one proves a lemma stated with the other. The lemma
-- `consistent` stays unknown as long as the axioms have a model.

private def seqUnsafeAgreesInRangePgm :=
#strata
program Core;

const s : Sequence int;
axiom [s_len]: Sequence.length(s) == 1;
axiom [s_0]: Sequence.select!(s, 0) == 1;

lemma [consistent]: false;
lemma [select_agrees]: forall i : int :: int.le(0, i) && int.lt(i, Sequence.length(s)) ==> Sequence.select(s, i) == 1;
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: consistent
Property: assert
Assumptions:
s_len: Sequence.length(s) == 1
s_0: Sequence.select!(s, 0) == 1
Obligation:
false

Label: select_agrees_calls_Sequence.select_0
Property: out-of-bounds access check
Assumptions:
s_len: Sequence.length(s) == 1
s_0: Sequence.select!(s, 0) == 1
Obligation:
int.le(0, i@1) && int.lt(i@1, Sequence.length(s)) ==> int.le(0, i@1) && int.lt(i@1, Sequence.length(s))

Label: select_agrees
Property: assert
Assumptions:
s_len: Sequence.length(s) == 1
s_0: Sequence.select!(s, 0) == 1
Obligation:
int.le(0, i@2) && int.lt(i@2, Sequence.length(s)) ==> Sequence.select!(s, i@2) == 1

---
info:
Obligation: consistent
Property: assert
Result: ❓ unknown

Obligation: select_agrees_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: select_agrees
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify seqUnsafeAgreesInRangePgm

-- Out of range, `Sequence.select!` stays unconstrained: the lemma does not follow,
-- although it holds in the list model.

private def seqUnsafeOutOfRangePgm :=
#strata
program Core;

const s : Sequence int;
axiom [s_len]: Sequence.length(s) == 2;
axiom [s_5]: Sequence.select!(s, 5) == 1;

lemma [select_no_transfer]: forall i : int :: int.le(0, i) && int.lt(i, Sequence.length(s)) ==> Sequence.select(s, i) == 1;
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: select_no_transfer_calls_Sequence.select_0
Property: out-of-bounds access check
Assumptions:
s_len: Sequence.length(s) == 2
s_5: Sequence.select!(s, 5) == 1
Obligation:
int.le(0, i@1) && int.lt(i@1, Sequence.length(s)) ==> int.le(0, i@1) && int.lt(i@1, Sequence.length(s))

Label: select_no_transfer
Property: assert
Assumptions:
s_len: Sequence.length(s) == 2
s_5: Sequence.select!(s, 5) == 1
Obligation:
int.le(0, i@2) && int.lt(i@2, Sequence.length(s)) ==> Sequence.select!(s, i@2) == 1

---
info:
Obligation: select_no_transfer_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: select_no_transfer
Property: assert
Result: ❓ unknown
Model:
(i@2, 0)
-/
#guard_msgs in
#eval Strata.Core.verify seqUnsafeOutOfRangePgm

-- A checked sequence operation and its total twin denote the same function, so
-- in bounds the two agree. They are encoded as one solver symbol.

private def seqCheckedTotalPgm :=
#strata
program Core;

const g : Sequence int;

procedure P()
{
  assume [g_len]: Sequence.length(g) == 2;
  assert [select_pair]: Sequence.select(g, 0) == Sequence.select!(g, 0);
  assert [update_pair]: Sequence.update(g, 0, 7) == Sequence.update!(g, 0, 7);
  assert [take_pair]: Sequence.take(g, 1) == Sequence.take!(g, 1);
  assert [drop_pair]: Sequence.drop(g, 1) == Sequence.drop!(g, 1);
};
#end

/--
info:
Obligation: assert_select_pair_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: select_pair
Property: assert
Result: ✅ pass

Obligation: assert_update_pair_calls_Sequence.update_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: update_pair
Property: assert
Result: ✅ pass

Obligation: assert_take_pair_calls_Sequence.take_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: take_pair
Property: assert
Result: ✅ pass

Obligation: assert_drop_pair_calls_Sequence.drop_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: drop_pair
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify seqCheckedTotalPgm (options := .quiet)

-- Out of range, the checked operation's bounds obligation is not provable (the
-- solver answers unknown rather than fail, as for `t_length_wrong` above,
-- because the length axiom is quantified); the equality with the total twin
-- still holds, since after `SeqTotalize` both sides are the same term.

private def seqCheckedTotalOobPgm :=
#strata
program Core;

const g : Sequence int;

procedure Q()
{
  assume [g_len]: Sequence.length(g) == 2;
  assert [select_oob]: Sequence.select(g, 5) == Sequence.select!(g, 5);
};
#end

/--
info:
Obligation: assert_select_oob_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ❓ unknown

Obligation: select_oob
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify seqCheckedTotalOobPgm (options := .quiet)



-- Out of range, a lemma relating the two forms is valid too: each checked operation
-- carries an axiom equating it with its total twin at every argument, which is what
-- makes `seqTotalize`'s rewrite of the lemma valid. The bounds obligations of the
-- checked calls stay unknown.

private def seqCheckedTotalLemmaPgm :=
#strata
program Core;

const g : Sequence int;
axiom [g_len]: Sequence.length(g) == 2;

lemma [select_oob]: Sequence.select(g, 5) == Sequence.select!(g, 5);
lemma [update_oob]: Sequence.update(g, 5, 7) == Sequence.update!(g, 5, 7);
lemma [take_oob]: Sequence.take(g, 5) == Sequence.take!(g, 5);
lemma [drop_oob]: Sequence.drop(g, 5) == Sequence.drop!(g, 5);
#end

/--
info:
Obligation: select_oob_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ❓ unknown

Obligation: select_oob
Property: assert
Result: ✅ pass

Obligation: update_oob_calls_Sequence.update_0
Property: out-of-bounds access check
Result: ❓ unknown

Obligation: update_oob
Property: assert
Result: ✅ pass

Obligation: take_oob_calls_Sequence.take_0
Property: out-of-bounds access check
Result: ❓ unknown

Obligation: take_oob
Property: assert
Result: ✅ pass

Obligation: drop_oob_calls_Sequence.drop_0
Property: out-of-bounds access check
Result: ❓ unknown

Obligation: drop_oob
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify seqCheckedTotalLemmaPgm (options := .quiet)

-- A function the caller supplies in `moreFns` is rewritten as the program is, so a call
-- of it agrees with the total twin in the program. Each mode proves `a`.

private def seqExtFnPgm :=
#strata
program Core;

const g : Sequence int;

function gTake(s : Sequence int) : Sequence int { Sequence.take(s, 1) }

procedure P()
{
  assume [g_len]: Sequence.length(g) == 3;
  assert [a]: gTake(g) == Sequence.take(g, 1);
};
#end

/--
info: symbolic: [(assert_a_calls_Sequence.take_0, true), (a, true)]
wp: [(assert_a_calls_Sequence.take_0, true), (a, true)]
uwp: [(assert_a_calls_Sequence.take_0, true), (a, true)]
usp: [(assert_a_calls_Sequence.take_0, true), (a, true)]
-/
#guard_msgs in
#eval show IO Unit from do
  -- Type-check the program, then pass `gTake` in `moreFns` instead of declaring it.
  let .ok p := strataProgramToCore seqExtFnPgm | IO.println "translation failed"
  let .ok p := Core.typeCheck Core.VerifyOptions.quiet p | IO.println "type checking failed"
  let fns := p.decls.filterMap fun d => match d with
    | .func f _ => some f.toLFunc
    | _ => none
  let p : Core.Program := { decls := p.decls.filter fun d => !(d matches .func _ _) }
  for (mode, vcgen) in [("symbolic", Core.VCGenMode.symbolic), ("wp", .wp), ("uwp", .uwp),
      ("usp", .usp)] do
    let rs ← (Core.verifyProgram p { Core.VerifyOptions.quiet with vcgen }
      (Lambda.Factory.ofArray fns.toArray)).toIO fun e => IO.userError (toString e)
    IO.println s!"{mode}: {rs.toList.map fun r => (r.obligation.label, r.isSuccess)}"

-- The loop invariant of a CFG block, kept in the block's metadata, is rewritten too.

private def seqCFGInvariantPgm :=
#strata
program Core;

const g : Sequence int;

procedure P(out r : int)
cfg entry {
  entry: {
    r := 0;
    goto loop;
  }
  @[loopInvariant = (Sequence.select!(g, 0) == Sequence.select(g, 0))]
  loop: {
    branch (int.lt(r, 3)) goto loop else goto done;
  }
  done: {
    return;
  }
};
#end

/-- info: (true, 0, 2) -/
#guard_msgs in
#eval
  let p := (Core.getProgram seqCFGInvariantPgm).fst
  match Core.Transform.run p Core.SeqTotalize.totalizeProgram with
  | .ok (changed, q) =>
    let out := toString (Std.format q)
    -- The occurrences of the checked and of the total `select`.
    (changed, (out.splitOn "Sequence.select(").length - 1,
      (out.splitOn "Sequence.select!(").length - 1)
  | .error _ => (false, 0, 0)

end
----------------------------------------------------------------------
