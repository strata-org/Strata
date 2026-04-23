/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

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

Label: t_0
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 0) == 10

Label: t_1
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1) == 20

Label: t_2
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 2) == 30

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

Obligation: t_0
Property: assert
Result: ✅ pass

Obligation: t_1
Property: assert
Result: ✅ pass

Obligation: t_2
Property: assert
Result: ✅ pass

Obligation: t_length_wrong
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval verify seqPgm

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

Label: append_elem_0
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select(Sequence.append(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), Sequence.build(Sequence.build(s, 40), 50)), 0) == 10

Label: append_elem_4
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select(Sequence.append(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), Sequence.build(Sequence.build(s, 40), 50)), 4) == 50

Label: update_length
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.length(Sequence.update(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1, 99)) == 3

Label: update_same
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select(Sequence.update(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1, 99), 1) == 99

Label: update_other
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select(Sequence.update(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1, 99), 0) == 10

Label: contains_yes
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.contains(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 20)

Label: take_length
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.length(Sequence.take(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 2)) == 2

Label: take_elem
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select(Sequence.take(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 2), 0) == 10

Label: drop_length
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.length(Sequence.drop(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1)) == 2

Label: drop_elem
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.select(Sequence.drop(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1), 0) == 20

---
info:
Obligation: append_length
Property: assert
Result: ✅ pass

Obligation: append_elem_0
Property: assert
Result: ✅ pass

Obligation: append_elem_4
Property: assert
Result: ✅ pass

Obligation: update_length
Property: assert
Result: ✅ pass

Obligation: update_same
Property: assert
Result: ✅ pass

Obligation: update_other
Property: assert
Result: ✅ pass

Obligation: contains_yes
Property: assert
Result: ❓ unknown

Obligation: take_length
Property: assert
Result: ✅ pass

Obligation: take_elem
Property: assert
Result: ✅ pass

Obligation: drop_length
Property: assert
Result: ✅ pass

Obligation: drop_elem
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify seqOpsPgm

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

  // Create an empty sequence using the new syntax
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
Sequence.length(Sequence.empty<int>()) == 0

Label: build_on_empty_length
Property: assert
Obligation:
Sequence.length(Sequence.build(Sequence.empty<int>(), 42)) == 1

Label: build_on_empty_elem
Property: assert
Obligation:
Sequence.select(Sequence.build(Sequence.empty<int>(), 42), 0) == 42

---
info:
Obligation: empty_length
Property: assert
Result: ✅ pass

Obligation: build_on_empty_length
Property: assert
Result: ✅ pass

Obligation: build_on_empty_elem
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify seqEmptyPgm

----------------------------------------------------------------------
