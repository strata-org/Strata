/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.DL.Imperative.BasicBlock
import StrataDDM.Integration.Lean.HashCommands

/-! # Regression: body variable resolution with an `out`-first parameter list

The DDM→Core translation partitions procedure parameters into inputs-then-outputs
for the header, but the body's de Bruijn indices are assigned against the
*original declaration order*. When an `out` (or `inout`) parameter is declared
before a plain input, building the body scope from the partitioned order made
body references resolve to the wrong parameter.

Here `caller` declares `out r` first, so partitioning reorders the header to
`(a, b, out r)`. The body must still refer to `a`, `b`, and `r` by their
original meaning: with the bug, `assert a > 0` silently became `assert b > 0`
(with `b` unconstrained), so the false assertion vacuously "passed". -/

meta section

---------------------------------------------------------------------
namespace Strata

def outFirstParams :=
#strata
program Core;
procedure caller (out r : int, a : int, b : int)
{
  r := 0;
  assume [pa]: a == -1;
  assume [pb]: b == -1;
  assert [aa]: a > 0;
};
#end

-- No errors in translation.
/--
info: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram outFirstParams) |>.snd

-- The header is partitioned (inputs first, `out r` last), but the body still
-- references `a`, `b`, and `r` by their original meaning — not shifted by the
-- header reordering.
/--
info: program Core;

procedure caller (a : int, b : int, out r : int)
{
  r := 0;
  assume [pa]: a == -1;
  assume [pb]: b == -1;
  assert [aa]: a > 0;
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram outFirstParams) |>.fst

---------------------------------------------------------------------

-- Sibling case: an `inout` parameter declared first. `inout` is a distinct
-- case in the header partition (it enters *both* the input and output lists).
-- The body scope must still be built in declaration order so `a`, `b`, and the
-- `inout` `r` keep their original meanings.
def inoutFirstParams :=
#strata
program Core;
procedure caller (inout r : int, a : int, b : int)
{
  r := 0;
  assume [pa]: a == -1;
  assume [pb]: b == -1;
  assert [aa]: a > 0;
};
#end

-- No errors in translation.
/--
info: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram inoutFirstParams) |>.snd

-- The body still references `a`, `b`, and the `inout` `r` by their original
-- meaning.
/--
info: program Core;

procedure caller (inout r : int, a : int, b : int)
{
  r := 0;
  assume [pa]: a == -1;
  assume [pb]: b == -1;
  assert [aa]: a > 0;
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram inoutFirstParams) |>.fst

---------------------------------------------------------------------

-- Mixed case: an `out`, an `inout`, and a plain read-only input, with the
-- `out` declared first so partitioning genuinely reorders the header
-- (`out r` moves last, the `inout s` stays an input). This combines both
-- distinct paths in one signature; the body must keep every reference intact.
def mixedParams :=
#strata
program Core;
procedure caller (out r : int, inout s : int, a : int)
{
  r := s;
  assume [pa]: a == -1;
  assume [ps]: s == 5;
  assert [aa]: a > 0;
};
#end

-- No errors in translation.
/--
info: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram mixedParams) |>.snd

-- `r := s` keeps `s`, the assumptions keep `a`/`s`, and `assert a > 0` stays
-- `a` — none are shifted by the header reordering.
/--
info: program Core;

procedure caller (inout s : int, a : int, out r : int)
{
  r := s;
  assume [pa]: a == -1;
  assume [ps]: s == 5;
  assert [aa]: a > 0;
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram mixedParams) |>.fst

---------------------------------------------------------------------

-- Spec coverage: `requires`/`ensures` expressions resolve against the same
-- declaration-order body scope, so the fix corrects them too. With `out r`
-- declared first, a buggy scope would misresolve the spec — `requires a > b`
-- and `ensures r == a` must keep their original variables.
def outFirstSpec :=
#strata
program Core;
procedure caller (out r : int, a : int, b : int)
spec {
  requires a > b;
  ensures r == a;
}
{
  r := a;
};
#end

/--
info: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram outFirstSpec) |>.snd

/--
info: program Core;

procedure caller (a : int, b : int, out r : int)
spec {
  requires [caller_requires_0]: a > b;
  ensures [caller_ensures_1]: r == a;
  } {
  r := a;
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram outFirstSpec) |>.fst

---------------------------------------------------------------------

-- CFG-body coverage: `translateCFGProcedure` applies the same declaration-order
-- scope fix as `translateProcedure`. The CST formatter and the verify pipeline
-- do not handle CFG bodies, so extract the translated CFG and format it directly
-- (as `StrataTest/.../Examples/Loops.lean` does). With `out r` first, a buggy
-- scope would rewrite the body's `a` to `b`; the rendered blocks must keep `a`.
private def entryCmds (p : StrataDDM.Program) (n : Nat) : List Core.Command :=
  let corePgm : Core.Program := TransM.run Inhabited.default (translateProgram p) |>.fst
  let proc := match corePgm.decls[n]? with
              | .some (.proc pr _) => pr | _ => Inhabited.default
  match proc.body with
  | .cfg cfg => match cfg.blocks with
                | (_, b) :: _ => b.cmds
                | []          => []
  | _ => []

def outFirstCFG :=
#strata
program Core;
procedure caller (out r : int, a : int, b : int)
cfg entry {
  entry: {
    r := a;
    assume [pa]: a == -1;
    assert [aa]: a > 0;
    return;
  }
};
#end

-- Translation succeeds with no errors.
/--
info: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram outFirstCFG) |>.snd

-- The rendered entry-block commands keep `r := a`, `assume a == -1`, and
-- `assert a > 0` (we format only `cmds`, not the transfer, whose metadata
-- carries an unstable source offset).
/--
info: [r := a;, assume [pa]: a == -1;, assert [aa]: a > 0;]
-/
#guard_msgs in
#eval Std.format (entryCmds outFirstCFG 0)

---------------------------------------------------------------------

end Strata

end
