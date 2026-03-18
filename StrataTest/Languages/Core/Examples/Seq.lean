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

procedure P() returns ()
{
  var t : Sequence int;

  t := Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30);
  assume [s_empty]: Sequence.length(s) == 0;

  assert [t_length]: Sequence.length(t) == 3;
  assert [t_0]: Sequence.get(t, 0) == 10;
  assert [t_1]: Sequence.get(t, 1) == 20;
  assert [t_2]: Sequence.get(t, 2) == 30;

  // This should fail: length is 3, not 0
  assert [t_length_wrong]: Sequence.length(t) == 0;
};
#end

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram seqPgm) |>.snd |>.isEmpty

/--
info: function s () : Sequence int;
procedure P () returns ()
{
  var t : (Sequence int);
  t := Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30);
  assume [s_empty]: Sequence.length(s) == 0;
  assert [t_length]: Sequence.length(t) == 3;
  assert [t_0]: Sequence.get(t, 0) == 10;
  assert [t_1]: Sequence.get(t, 1) == 20;
  assert [t_2]: Sequence.get(t, 2) == 30;
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
Sequence.get(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 0) == 10

Label: t_1
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.get(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1) == 20

Label: t_2
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.get(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 2) == 30

Label: t_length_wrong
Property: assert
Assumptions:
s_empty: Sequence.length(s) == 0
Obligation:
Sequence.length(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30)) == 0



Result: Obligation: t_length_wrong
Property: assert
Result: ❓ unknown


[DEBUG] Evaluated program:
function s () : Sequence int;
procedure P () returns ()
{
  var t : (Sequence int);
  t := Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30);
  assume [s_empty]: Sequence.length(s) == 0;
  assert [t_length]: Sequence.length(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30)) == 3;
  assert [t_0]: Sequence.get(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 0) == 10;
  assert [t_1]: Sequence.get(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 1) == 20;
  assert [t_2]: Sequence.get(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30), 2) == 30;
  assert [t_length_wrong]: Sequence.length(Sequence.build(Sequence.build(Sequence.build(s, 10), 20), 30)) == 0;
  };

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

procedure SeqOps() returns ()
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
  assert [append_elem_0]: Sequence.get(v, 0) == 10;
  assert [append_elem_4]: Sequence.get(v, 4) == 50;

  // --- update ---
  u := Sequence.update(t, 1, 99);
  assert [update_length]: Sequence.length(u) == 3;
  assert [update_same]: Sequence.get(u, 1) == 99;
  assert [update_other]: Sequence.get(u, 0) == 10;

  // --- contains ---
  assert [contains_yes]: Sequence.contains(t, 20);

  // --- take ---
  u := Sequence.take(t, 2);
  assert [take_length]: Sequence.length(u) == 2;
  assert [take_elem]: Sequence.get(u, 0) == 10;

  // --- drop ---
  u := Sequence.drop(t, 1);
  assert [drop_length]: Sequence.length(u) == 2;
  assert [drop_elem]: Sequence.get(u, 0) == 20;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram seqOpsPgm) |>.snd |>.isEmpty

---------------------------------------------------------------------
