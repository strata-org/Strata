/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section

/-!
# CFG sibling-block scoping

`@[scope(b)]` on the `rest` argument of `cfg_blocks_cons` makes a declaration
introduced in a CFG block visible to every textually-later block. The contract
is purely left-to-right in source order: it is not goto/dominance aware. These
tests pin both directions of that boundary, plus the silent shadowing that
falls out of ordinary nested-scope resolution.

The shipped CFG examples (`Examples/CFGSimple.core.st`, `CFGNondet.core.st`)
declare no `var` locals, so nothing else in the tree exercises this path.
-/

namespace Strata.CFGSiblingScope

/-! ## A textually-later block sees an earlier block's declaration.

`x` is declared in `entry` and read by the later block `next`. This fails name
resolution before the scoping change and elaborates cleanly after it. -/

private def siblingForwardScope :=
#strata
program Core;

procedure P(out y : int)
cfg entry {
  entry: {
    var x : int;
    x := 1;
    goto next;
  }
  next: {
    y := x;
    return;
  }
};
#end

/-! ## Forward visibility chains transitively across blocks.

`cfg_blocks_cons` folds blocks in source order, so `@[scope(b)]` should make an
earlier block's declarations visible to every later block, not just the next
one. `entry` declares `x`; `mid` reads `x` and declares `z`; `last` reads both
`z` (one block back) and `x` (two blocks back). `last` seeing `x` exercises the
recursive application of the attribute — a bug that propagated visibility only
one level would leave `x` unresolved in `last`. -/

private def siblingChainedScope :=
#strata
program Core;

procedure S(out y : int)
cfg entry {
  entry: {
    var x : int;
    x := 1;
    goto mid;
  }
  mid: {
    var z : int;
    z := x;
    goto last;
  }
  last: {
    y := x + z;
    return;
  }
};
#end

/-! ## The contract is textual, not dominance-based.

Same program with the entry block written second: `next` textually precedes the
`entry` block that declares `x`, so `x` is out of scope at its use even though
control flow reaches `next` only through `entry`. -/

/--
error: Unknown expr identifier x
-/
#guard_msgs in
private def siblingEntrySecond :=
#strata
program Core;

procedure Q(out y : int)
cfg entry {
  next: {
    y := x;
    return;
  }
  entry: {
    var x : int;
    x := 1;
    goto next;
  }
};
#end

/-! ## A later block re-declaring a propagated name silently shadows it.

Both blocks declare `w`; the later declaration shadows the one propagated from
the earlier block rather than colliding. This is ordinary nested-scope
shadowing — pinned here because CFG blocks are semantically siblings, so a
future translator may want to reject it instead.

The two `w`s have different types (`bool` in `entry`, `int` in `next`) so the
test discriminates: `w := 2` and `y := w` in `next` only type-check if the
local `int` `w` shadows the propagated `bool` `w`. If the shadow leaked, the
propagated `bool` `w` would be visible and both assignments would be a type
mismatch, so a clean elaboration is evidence the shadow is effective. -/

private def siblingShadow :=
#strata
program Core;

procedure R(out y : int)
cfg entry {
  entry: {
    var w : bool;
    w := true;
    goto next;
  }
  next: {
    var w : int;
    w := 2;
    y := w;
    return;
  }
};
#end

end Strata.CFGSiblingScope

end
