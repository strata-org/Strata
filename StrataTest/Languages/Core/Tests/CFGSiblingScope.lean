/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
import StrataDDM.Integration.Lean.HashCommands
meta import StrataTest.Languages.Core.Tests.TestUtil

meta section

/-!
# CFG sibling-block scoping

`@[scope(b)]` on the `rest` argument of `cfg_blocks_cons` makes a declaration
introduced in a CFG block visible to every textually-later block. The contract
is purely left-to-right in source order: it is not goto/dominance aware. These
tests pin both directions of that boundary, plus the type checker's rejection
of a local redeclared in a later block.

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
    y := int.add(x, z);
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

/-! ## Local names are unique within a control-flow graph body

The parser accepts a local redeclared in a later block; the Core type checker rejects it. -/

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

/--
info: REJECTED: Procedure 'R': [R]: a CFG-local is declared in two dominance-comparable blocks.
-/
#guard_msgs in
#eval Core.TestUtil.coreVerdict <| Core.TestUtil.translate siblingShadow

/-! Distinct local names in sibling blocks are accepted. -/

private def siblingDistinct :=
#strata
program Core;

procedure T(out y : int)
cfg entry {
  entry: {
    var w : bool;
    w := true;
    goto next;
  }
  next: {
    var v : int;
    v := 2;
    y := v;
    return;
  }
};
#end

/--
info: ACCEPTED
-/
#guard_msgs in
#eval Core.TestUtil.coreVerdict <| Core.TestUtil.translate siblingDistinct

/-! Two sibling branches, neither dominating the other, may each declare a local `w`. -/

private def siblingBranchesShareName :=
#strata
program Core;

procedure V(out y : int)
cfg entry {
  entry: {
    goto left, right;
  }
  left: {
    var w : int;
    w := 1;
    y := w;
    return;
  }
  right: {
    var w : int;
    w := 2;
    y := w;
    return;
  }
};
#end

/--
info: ACCEPTED
-/
#guard_msgs in
#eval Core.TestUtil.coreVerdict <| Core.TestUtil.translate siblingBranchesShareName

/-! A local may not reuse the name of a procedure parameter. -/

private def localShadowsParam :=
#strata
program Core;

procedure U(out y : int)
cfg entry {
  entry: {
    var y : int;
    y := 2;
    return;
  }
};
#end

/--
info: REJECTED: Procedure 'U': [U]: a CFG-local shadows a procedure formal, output, or `old` binding.
-/
#guard_msgs in
#eval Core.TestUtil.coreVerdict <| Core.TestUtil.translate localShadowsParam

end Strata.CFGSiblingScope

end
