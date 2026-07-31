/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.ProgramType
meta import Strata.Transform.PrecondElim

meta section

open Core
open Core.PrecondElim
open Strata

/-! # Loop invariant well-formedness

A loop invariant is *assumed* and re-asserted at the arbitrary mid-loop state,
over the havoc'd loop-carried variables. Its well-formedness (WF) must
therefore be checked at that state, not in the loop's pre-state, where more is
known and a definedness obligation can be vacuously discharged.

`PrecondElim.mkLoopInvariantWFBlock` synthesizes the missing program point as a
severed proof block placed before the loop:

```
if * { havoc(M); assert WF(I_k); assume I_k; ...; assume false } else { }
```

`havoc(M)` reaches the loop-head state, the asserts precede every `assume I_k`,
and `assume false` severs the branch so the havoc cannot leak into the
pre-state. See `docs/CoreLoopInvariantWFBlock.md`.

These tests inspect the transform output directly. For the end-to-end VC
behavior see `StrataTest/Languages/Core/Examples/Loops.lean`.
-/

namespace LoopInvariantWFTests

def translate (t : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

def transformProgram (t : StrataDDM.Program) : Core.Program :=
  let program := translate t
  match Core.Transform.run program PrecondElim.precondElim
      { Core.Transform.CoreTransformState.emp with factory := some Core.Factory } with
  | .error e => panic! s!"PrecondElim failed: {e}"
  | .ok (_changed, program) =>
    match Core.typeCheck Core.VerifyOptions.default program with
    | .error e => panic! s!"Type check failed: {Std.format e}"
    | .ok program => program.stripMetaData

/-! ### The WF check moves from the pre-state into a severed loop-head block

Previously this emitted a bare `assert !(d == 0)` before the loop, evaluated
where `d == 1`, so the obligation was vacuous. Now the check sits inside
`if * { ... }` after `havoc d`, so it is checked at the state where the
invariant is actually assumed.

`d` is havoc'd because the body assigns it; `i` likewise. `n` is not, being a
parameter the loop does not modify.
-/
def loopHeadWFPgm :=
#strata
program Core;

procedure Unsound(n : int)
{
  var i : int;
  var d : int;
  i := 0;
  d := 1;
  while (i < n)
  invariant [usesdiv]: ((n / d) >= 0)
  {
      d := (d - 1);
      i := (i + 1);
  }
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

procedure Unsound (n : int)
{
  var i : int;
  var d : int;
  i := 0;
  d := 1;
  if * {
    loop_invariant_wf: {
      havoc d;
      havoc i;
      assert [loop_invariant_usesdiv_calls_Int.SafeDiv_0]: !(d == 0);
      assume [assume_wf_loop_invariant_0_usesdiv]: n / d >= 0;
      assume [loop_invariant_wf_sever]: false;
    }
  }
  while (i < n)
  invariant [usesdiv]: n / d >= 0
  {
    d := d - 1;
    i := i + 1;
  }
};
-/
#guard_msgs in
#eval (Std.format (transformProgram loopHeadWFPgm))

/-! ### WF obligations chain across invariants

Invariant `pos` is asserted-then-assumed before `usesdiv`'s WF check, so
`usesdiv` may rely on it — the discipline `processCondition` already gave
procedure contracts. Here that chaining is load-bearing: `d` is havoc'd, so
`0 < d` is the only thing establishing `d != 0` at the loop head.
-/
def chainedInvariantWFPgm :=
#strata
program Core;

procedure Chain(n : int)
{
  var i : int;
  var d : int;
  i := 0;
  d := 1;
  while (i < n)
  invariant [pos]: (0 < d)
  invariant [usesdiv]: ((n / d) >= 0)
  {
      d := (d + 1);
      i := (i + 1);
  }
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

procedure Chain (n : int)
{
  var i : int;
  var d : int;
  i := 0;
  d := 1;
  if * {
    loop_invariant_wf: {
      havoc d;
      havoc i;
      assume [assume_wf_loop_invariant_0_pos]: 0 < d;
      assert [loop_invariant_usesdiv_calls_Int.SafeDiv_0]: !(d == 0);
      assume [assume_wf_loop_invariant_1_usesdiv]: n / d >= 0;
      assume [loop_invariant_wf_sever]: false;
    }
  }
  while (i < n)
  invariant [pos]: 0 < d
  invariant [usesdiv]: n / d >= 0
  {
    d := d + 1;
    i := i + 1;
  }
};
-/
#guard_msgs in
#eval (Std.format (transformProgram chainedInvariantWFPgm))

/-! ### Total invariants emit no block

A loop whose invariants call no partial function is left untouched, rather than
gaining a dead proof block.
-/
def totalInvariantPgm :=
#strata
program Core;

procedure Total(n : int)
{
  var i : int;
  i := 0;
  while (i < n)
  invariant [lo]: (0 <= i)
  {
      i := (i + 1);
  }
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

procedure Total (n : int)
{
  var i : int;
  i := 0;
  while (i < n)
  invariant [lo]: 0 <= i
  {
    i := i + 1;
  }
};
-/
#guard_msgs in
#eval (Std.format (transformProgram totalInvariantPgm))

/-! ### Only loop-carried variables are havoc'd

`d` is a parameter the loop never assigns, so it is not part of the loop-head
state and is not havoc'd — only the loop-carried `i` and `s` are. This matches
the write-set `LoopElim` havocs for the mid-loop state
(`Block.modifiedVars` minus `Block.definedVars`).

(A `var` declared *inside* the body is likewise excluded by the
`definedVars` filter, but such a loop currently fails to typecheck for an
unrelated pre-existing reason — the loop guard is rebuilt from the body's
scope — so it is not exercised here.)
-/
def loopCarriedPgm :=
#strata
program Core;

procedure LoopCarried(n : int, d : int)
{
  var i : int;
  var s : int;
  i := 0;
  s := 0;
  while (i < n)
  invariant [dv]: ((s / d) >= 0)
  {
      s := (s + i);
      i := (i + 1);
  }
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

procedure LoopCarried (n : int, d : int)
{
  var i : int;
  var s : int;
  i := 0;
  s := 0;
  if * {
    loop_invariant_wf: {
      havoc s;
      havoc i;
      assert [loop_invariant_dv_calls_Int.SafeDiv_0]: !(d == 0);
      assume [assume_wf_loop_invariant_0_dv]: s / d >= 0;
      assume [loop_invariant_wf_sever]: false;
    }
  }
  while (i < n)
  invariant [dv]: s / d >= 0
  {
    s := s + i;
    i := i + 1;
  }
};
-/
#guard_msgs in
#eval (Std.format (transformProgram loopCarriedPgm))

end LoopInvariantWFTests
end
