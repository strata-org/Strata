/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Examples.EmbeddedData
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
import all Strata.DL.Imperative.CFGDominators
import all Strata.Languages.Core.ProcedureType
import StrataDDM.Integration.Lean.HashCommands

meta section

/-!
# `CFG.typeCheck` tests

A bare `#strata` block only runs DDM name resolution, not `CFG.typeCheck`, so
these drive the checker explicitly via `Core.typeCheck` on the translated
program.

## Negatives — each pins a well-formedness error `CFG.typeCheck`
(`ProcedureType.lean`) reports:

* duplicate block labels (`checkUniqueLabels`),
* an entry label with no matching block (`checkEntryExists`),
* a transfer to a label that does not exist, as a `goto` and as a `branch`'s
  false target (`checkTargetLabels`),
* a read of a local declared on non-dominating branches — rejected by the
  pre-loop `checkDomScoped` oracle guard, in two variants: the local declared
  on only one arm, and the local declared independently on both arms of a
  symmetric diamond,
* a branch condition that is not of type `bool` (the per-block `condGoto`
  guard check),
* the same local declared by two dominance-comparable blocks — rejected by the
  pre-loop `checkInitsIncomparable` guard (reachable blocks only),
* a local declared twice within one block — rejected by the pre-loop
  `checkBlockInitsNodup` guard,
* a block-level declaration on a block that lies on a cycle, through a self-loop
  or through two blocks, including the hidden declaration of a nondeterministic
  `goto` — rejected by the pre-loop `checkNoLoopInits` guard (a loop-carried
  `init` would be re-initialized on re-entry),
* two declarers of the same local where one can reach the other, by one edge or
  two, three declarers where one is reachable from the other two, and three
  declarers that all reach a fourth — rejected by the pre-loop
  `checkInitsNotReachable` guard,
* a read after three chained diamonds of a local declared on one arm of the
  first — rejected by `checkDomScoped`,
* a CFG-local that shadows a formal — rejected by `checkInitsNotHeader`,
* a local declared at different types in two blocks, in either block order or
  with one block unreachable — rejected by `checkInitTypesAgree`,
* a polymorphic formal used at conflicting types in two reachable blocks —
  rejected by unification in the per-block loop, and
* an unreachable block reading a local declared in another unreachable block —
  rejected by the per-block check.

## Positives — each drives `CFG.typeCheck` to an `.ok` result and pins the
annotated program it returns:

* a well-formed dominance-scoped CFG, covering the success path the guards gate
  (the per-block scope frame seeded from strict dominators, the per-block loop,
  the `condGoto` bool check, and annotated-block re-emission),
* order-independence: a dominator's local is in scope at its dominatee even when
  a dead-end sibling is listed between them in source order,
* a dead-code (unreachable) block re-declaring a reachable local is accepted —
  unreachable blocks are excluded from the incomparability check,
* a dominator's alias-typed local (`type MyInt := int`) is in scope at its
  dominatee — the seeded type is resolved the same way the declaring `init`
  stores it,
* locals are inherited across several dominator-tree levels, through a block
  that declares nothing and a merge whose immediate dominator is not one of its
  predecessors,
* a polymorphic formal used at a conflicting type only in an unreachable block
  is accepted,
* a local declared as an alias on one arm and as its underlying type on the
  other is accepted,
* a loop with two back edges is accepted,
* three declarers of one local, none reachable from another, are accepted, and
* a branch condition whose type another block solves is accepted in either
  block order.

## Type annotations

The printed program shows no expression types, so some tests read the type
annotations of the annotated commands and branch conditions directly:

* a type variable solved by a later block resolves an earlier block's
  annotations,
* an unreachable block does not share fresh type variables with a later live
  block, and
* a branch condition in a block that declares locals reads the formals it names,
  and may name a local the same block declares.

## Shipped examples

`Examples/CFGSimple.core.st` and `Examples/CFGNondet.core.st` are type-checked
(pinning the annotated program) and passed to `Core.verify`, which rejects them
because it requires structured procedure bodies.

## Differential

Two checks run on every test program in this file (not the shipped examples):
`computeDominators` against the set-dataflow reference
`computeDominatorsFullFuel`, and the cycle guard against a per-label search and
the reach-comparability, incomparability and dominance-scoping guards against
pairwise reference formulas.
-/

namespace Strata.CFGTypeCheck

open _root_.Strata.Core

private def translatePgm (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-! ## Duplicate block label. -/

private def dupLabelPgm :=
#strata
program Core;

procedure P(out y : int)
cfg entry {
  entry: {
    y := 1;
    goto done;
  }
  done: {
    return;
  }
  done: {
    return;
  }
};
#end

/--
info: error: [P]: Duplicate block labels in CFG: [done]
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm dupLabelPgm).stripMetaData))

/-! ## Entry label with no matching block. -/

private def missingEntryPgm :=
#strata
program Core;

procedure P(out y : int)
cfg start {
  entry: {
    y := 1;
    return;
  }
};
#end

/--
info: error: [P]: Entry label "start" not found in CFG blocks. Available labels: [entry]
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm missingEntryPgm).stripMetaData))

/-! ## Transfer to a label that does not exist. -/

private def badGotoPgm :=
#strata
program Core;

procedure P(out y : int)
cfg entry {
  entry: {
    y := 1;
    goto nowhere;
  }
};
#end

/--
info: error: [P]: Block "entry" branches to unknown label "nowhere". Available labels: [entry]
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm badGotoPgm).stripMetaData))

/-! ## A `branch` whose false target does not exist. -/

private def badElsePgm :=
#strata
program Core;

procedure P(c : bool, out y : int)
cfg entry {
  entry: {
    y := 1;
    branch (c) goto entry else goto nowhere;
  }
};
#end

/--
info: error: [P]: Block "entry" branches to unknown label "nowhere". Available labels: [entry]
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm badElsePgm).stripMetaData))

/-! ## Read of a local declared only on a non-dominating branch.

`entry` branches to `a` or `b`; only `a` declares `x`. `c` is reached from both,
so `a` does not dominate `c`, and `x` is out of scope at `c`. The read is placed
in `c`'s transfer guard so the diagnostic is not tied to a source byte range. -/

private def nonDomUsePgm :=
#strata
program Core;

procedure P(cond : bool, out y : int)
cfg entry {
  entry: {
    branch (cond) goto a else goto b;
  }
  a: {
    var x : int;
    x := 1;
    goto c;
  }
  b: {
    goto c;
  }
  c: {
    branch (x == 0) goto d else goto d;
  }
  d: {
    y := 1;
    return;
  }
};
#end

/--
info: error: [P]: a CFG-local is read or assigned on a path where its declaration does not dominate.
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm nonDomUsePgm).stripMetaData))

/-! ## Read of a local declared independently on both arms of a symmetric diamond.

`entry` branches to `a` or `b`; **both** arms declare their own `x`, and `c` is
reached from both. Neither arm dominates `c`, so the read is rejected exactly as
in the single-arm case. -/

private def symDiamondPgm :=
#strata
program Core;

procedure P(cond : bool, out y : int)
cfg entry {
  entry: {
    branch (cond) goto a else goto b;
  }
  a: {
    var x : int;
    x := 1;
    goto c;
  }
  b: {
    var x : int;
    x := 2;
    goto c;
  }
  c: {
    branch (x == 0) goto d else goto d;
  }
  d: {
    y := 1;
    return;
  }
};
#end

/--
info: error: [P]: a CFG-local is read or assigned on a path where its declaration does not dominate.
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm symDiamondPgm).stripMetaData))

/-! ## Branch condition that is not of type bool.

`CFG.typeCheck` resolves each `condGoto` guard and requires it to have type
`bool`; an `int`-typed guard is rejected. -/

private def nonBoolGuardPgm :=
#strata
program Core;

procedure P(x : int, out y : int)
cfg entry {
  entry: {
    branch (x) goto a else goto a;
  }
  a: {
    y := 1;
    return;
  }
};
#end

/--
info: error: [P]: Branch condition in block "entry" is not of type bool, got int
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm nonBoolGuardPgm).stripMetaData))

/-! ## Same local declared by two dominance-comparable blocks.

`a` dominates `b` and both declare `x`. The order-independent
`checkInitsIncomparable` guard runs before the per-block loop, so this
CFG-level message surfaces regardless of source block order (here `a` is listed
after `b`), rather than the low-level "already in context" from the loop. -/

private def comparableDeclPgm :=
#strata
program Core;

procedure P(out y : int)
cfg entry {
  entry: {
    goto a;
  }
  b: {
    var x : int;
    x := 2;
    y := x;
    return;
  }
  a: {
    var x : int;
    x := 1;
    goto b;
  }
};
#end

/--
info: error: [P]: a CFG-local is declared in two dominance-comparable blocks.
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm comparableDeclPgm).stripMetaData))

/-! ## Same local declared twice within one block.

A single block declares `x` twice. The `checkBlockInitsNodup` guard runs before
the per-block loop, so this CFG-level message surfaces ahead of the low-level
"already in context" error the loop would otherwise report. -/

private def dupInitInBlockPgm :=
#strata
program Core;

procedure P(out y : int)
cfg entry {
  entry: {
    var x : int;
    var x : int;
    y := x;
    return;
  }
};
#end

/--
info: error: [P]: a block declares the same local more than once.
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm dupInitInBlockPgm).stripMetaData))

/-! ## A well-formed dominance-scoped CFG type-checks successfully.

`entry` declares `x`, then branches on the bool guard `a == b` (over the int
formals) to block `p` or `q`; both go to `done`. `entry` dominates every block,
so its `x` is seeded into the frame at the read in `p`, and the branch guard
type-checks as bool. The assertion pins the annotated program the checker
returns. -/

private def wellFormedCFGPgm :=
#strata
program Core;

procedure P(a : int, b : int, out y : int)
cfg entry {
  entry: {
    var x : int;
    x := 1;
    branch (a == b) goto p else goto q;
  }
  p: {
    y := x;
    goto done;
  }
  q: {
    y := 2;
    goto done;
  }
  done: {
    return;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure P (a : int, b : int, out y : int)
cfg entry {
  entry: {
    var x : int;
    x := 1;
    branch (a == b) goto p else goto q;
  }
  p: {
    y := x;
    goto done;
  }
  q: {
    y := 2;
    goto done;
  }
  done: {
    return;
  }
};
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm wellFormedCFGPgm).stripMetaData))

/-! ## A dominator's local is in scope at its dominatee regardless of sibling order.

`entry` branches to `a` or `b`; `a` declares `x` and goes to `c`; `b` is a
dead-end sibling; `c` is reached only through `a`, so `a` dominates `c` and `x`
is validly in scope at the read in `c`. The dead-end sibling `b` is listed
between `a` and `c` in source order, so this pins that acceptance does not depend
on where a sibling sits in the block list: a dominator's local is in scope at its
dominatee regardless. -/

private def siblingBetweenDeclAndUsePgm :=
#strata
program Core;

procedure P(cond : bool, out y : int)
cfg entry {
  entry: {
    branch (cond) goto a else goto b;
  }
  a: {
    var x : int;
    x := 1;
    goto c;
  }
  b: {
    y := 2;
    return;
  }
  c: {
    y := x;
    return;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure P (cond : bool, out y : int)
cfg entry {
  entry: {
    branch (cond) goto a else goto b;
  }
  a: {
    var x : int;
    x := 1;
    goto c;
  }
  b: {
    y := 2;
    return;
  }
  c: {
    y := x;
    return;
  }
};
-/
#guard_msgs in
#eval (Std.format
  (Core.typeCheck .default (translatePgm siblingBetweenDeclAndUsePgm).stripMetaData))

/-! ## A dead-code block re-declaring a reachable local does not cause a rejection.

`entry` is reachable and declares `x`; `dead` has no predecessor (nothing jumps
to it) and independently declares its own `x`. Because `dead` is unreachable
from `entry`, it is excluded from the incomparability check, so its declaration
is not treated as dominance-comparable with `entry`'s. (A preds-less non-entry
block's dominator set is defined to be every label, which — without the reachability
filter — would make `entry` "dominate" `dead` and flag the pair as comparable.)
The program type-checks. -/

private def deadCodeRedeclarePgm :=
#strata
program Core;

procedure P(out y : int)
cfg entry {
  entry: {
    var x : int;
    x := 1;
    y := x;
    return;
  }
  dead: {
    var x : int;
    x := 2;
    return;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure P (out y : int)
cfg entry {
  entry: {
    var x : int;
    x := 1;
    y := x;
    return;
  }
  dead: {
    var x : int;
    x := 2;
    return;
  }
};
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm deadCodeRedeclarePgm).stripMetaData))

/-! ## A dominator's alias-typed local is in scope at its dominatee.

`entry` declares `x : MyInt` (a type alias for `int`) and goes to `b`, which
`entry` dominates; `b` assigns and reads `x`. The dominated block's scope frame
is seeded with the alias-resolved type the declaring `init` stored (via the same
`preprocess`/`postprocess` path `init` uses), so the `set`/read in `b` unify
against the resolved type rather than the raw alias. -/

private def aliasLocalPgm :=
#strata
program Core;

type MyInt := int;

procedure P(out y : int)
cfg entry {
  entry: {
    var x : MyInt;
    x := 1;
    goto b;
  }
  b: {
    x := 2;
    y := x;
    return;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

type MyInt := int;
procedure P (out y : int)
cfg entry {
  entry: {
    var x : int;
    x := 1;
    goto b;
  }
  b: {
    x := 2;
    y := x;
    return;
  }
};
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm aliasLocalPgm).stripMetaData))

/-! ## Locals inherited across several dominator-tree levels.

`entry` declares `x` and branches to `a` (which declares its own `z`) or `b`;
both reach `c`, whose immediate dominator is `entry` although `entry` is not one
of its predecessors. `c` declares `w` and continues through `e`, which declares
nothing, to `d`. `d` reads `x` (declared two dominator-tree levels above `c`) and
`w`, so its scope must carry both through the non-declaring `e`. -/

private def deepDomScopePgm :=
#strata
program Core;

procedure P(p : int, q : int, out y : int)
cfg entry {
  entry: {
    var x : int;
    x := 1;
    branch (p == q) goto a else goto b;
  }
  a: {
    var z : int;
    z := x;
    goto c;
  }
  b: {
    goto c;
  }
  c: {
    var w : int;
    w := x;
    goto e;
  }
  e: {
    goto d;
  }
  d: {
    y := x;
    y := w;
    return;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure P (p : int, q : int, out y : int)
cfg entry {
  entry: {
    var x : int;
    x := 1;
    branch (p == q) goto a else goto b;
  }
  a: {
    var z : int;
    z := x;
    goto c;
  }
  b: {
    goto c;
  }
  c: {
    var w : int;
    w := x;
    goto e;
  }
  e: {
    goto d;
  }
  d: {
    y := x;
    y := w;
    return;
  }
};
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm deepDomScopePgm).stripMetaData))

/-! ## A block-level declaration on a cycle is rejected.

`loop` declares `x` and can reach itself (`entry -> loop -> loop`), so the
declaration would be re-initialized on re-entry — which the Imperative `init`
semantics cannot step. The pre-loop `checkNoLoopInits` guard rejects it with a
CFG-level message rather than certifying a body that gets stuck at runtime. -/

private def loopInitPgm :=
#strata
program Core;

procedure P(cond : bool, out y : int)
cfg entry {
  entry: {
    goto loop;
  }
  loop: {
    var x : int;
    x := 1;
    branch (cond) goto loop else goto done;
  }
  done: {
    y := 0;
    return;
  }
};
#end

/--
info: error: [P]: a CFG-local is declared in a block that lies on a cycle; a loop-carried declaration would be re-initialized on re-entry.
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm loopInitPgm).stripMetaData))

/-! ## Two reach-comparable declarers of the same local are rejected.

`entry` branches to `d` or `e`; `d` declares `x` and falls through to `e`; `e`
also declares `x`. `d` and `e` are dominance-incomparable (both reachable via a
distinct entry edge), so `checkInitsIncomparable` alone would accept this. But
the path `entry -> d -> e` runs `d`'s `init x` and then `e`'s `init x` with `x`
already set, which the Imperative `init` semantics cannot step. The
`checkInitsNotReachable` guard rejects the pair because `e` is reachable from
`d`. -/

private def reachComparableInitPgm :=
#strata
program Core;

procedure P(cond : bool, out y : int)
cfg entry {
  entry: {
    branch (cond) goto d else goto e;
  }
  d: {
    var x : int;
    x := 1;
    goto e;
  }
  e: {
    var x : int;
    x := 2;
    y := x;
    return;
  }
};
#end

/--
info: error: [P]: a CFG-local is declared in two blocks where one is reachable from the other; a single path would re-initialize it.
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm reachComparableInitPgm).stripMetaData))

/-! ## A declaration on a two-block cycle is rejected.

`a` declares `x` and jumps to `b`, which can jump back to `a`. Neither block has
a self-loop; `a` lies on a cycle only through `b`. -/

private def loopInitTwoBlockPgm :=
#strata
program Core;

procedure P(cond : bool, out y : int)
cfg entry {
  entry: {
    goto a;
  }
  a: {
    var x : int;
    x := 1;
    goto b;
  }
  b: {
    branch (cond) goto a else goto done;
  }
  done: {
    y := 0;
    return;
  }
};
#end

/--
info: error: [P]: a CFG-local is declared in a block that lies on a cycle; a loop-carried declaration would be re-initialized on re-entry.
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm loopInitTwoBlockPgm).stripMetaData))

/-! ## Reach-comparable declarers two edges apart are rejected.

As `reachComparableInitPgm`, but `d` reaches `e` only through `m`. -/

private def reachComparableFarPgm :=
#strata
program Core;

procedure P(cond : bool, out y : int)
cfg entry {
  entry: {
    branch (cond) goto d else goto e;
  }
  d: {
    var x : int;
    x := 1;
    goto m;
  }
  m: {
    goto e;
  }
  e: {
    var x : int;
    x := 2;
    y := x;
    return;
  }
};
#end

/--
info: error: [P]: a CFG-local is declared in two blocks where one is reachable from the other; a single path would re-initialize it.
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm reachComparableFarPgm).stripMetaData))

/-! ## A read after three chained diamonds of a local declared on one arm.

`b0` declares `x` on one arm of the first diamond; `a3`, after two more diamonds,
reads it. `b0` does not dominate `a3`, so the read is rejected. -/

private def chainedDiamondPgm :=
#strata
program Core;

procedure P(c : bool, out y : int)
cfg a0 {
  a0: {
    branch (c) goto b0 else goto c0;
  }
  b0: {
    var x : int;
    x := 1;
    goto a1;
  }
  c0: {
    goto a1;
  }
  a1: {
    branch (c) goto b1 else goto c1;
  }
  b1: {
    goto a2;
  }
  c1: {
    goto a2;
  }
  a2: {
    branch (c) goto b2 else goto c2;
  }
  b2: {
    goto a3;
  }
  c2: {
    goto a3;
  }
  a3: {
    y := x;
    return;
  }
};
#end

/--
info: error: [P]: a CFG-local is read or assigned on a path where its declaration does not dominate.
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm chainedDiamondPgm).stripMetaData))

/-! ## A loop with two back edges type-checks.

`h` is the loop header; `b1` jumps back to it directly and `b2` either jumps
back or exits. The annotated program keeps the entry and every block, in source
order. -/

private def multiBackEdgePgm :=
#strata
program Core;

procedure P(c : bool, out y : int)
cfg entry {
  entry: {
    y := 0;
    goto h;
  }
  h: {
    branch (c) goto b1 else goto b2;
  }
  b1: {
    y := 1;
    goto h;
  }
  b2: {
    branch (c) goto h else goto done;
  }
  done: {
    return;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure P (c : bool, out y : int)
cfg entry {
  entry: {
    y := 0;
    goto h;
  }
  h: {
    branch (c) goto b1 else goto b2;
  }
  b1: {
    y := 1;
    goto h;
  }
  b2: {
    branch (c) goto h else goto done;
  }
  done: {
    return;
  }
};
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm multiBackEdgePgm).stripMetaData))

/-! ## A local declared at different types in two blocks is rejected, in either block order.

`a` declares `x : int` and jumps to `c`; `b` declares `x : bool` and returns; `c`
reads `x`. Only `a` dominates `c`, but translation types the read from whichever
declaration of `x` comes last before `c` in the source, so acceptance would
depend on where `b` is listed. `checkInitTypesAgree` rejects both orders with the
same message. -/

private def typeConflictBeforeUsePgm :=
#strata
program Core;

procedure P(cond : bool, out y : int)
cfg entry {
  entry: {
    branch (cond) goto a else goto b;
  }
  a: {
    var x : int;
    x := 1;
    goto c;
  }
  b: {
    var x : bool;
    x := true;
    return;
  }
  c: {
    y := x;
    return;
  }
};
#end

/--
info: error: [P]: CFG-local `x` is declared at different types in different blocks.
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm typeConflictBeforeUsePgm).stripMetaData))

private def typeConflictAfterUsePgm :=
#strata
program Core;

procedure P(cond : bool, out y : int)
cfg entry {
  entry: {
    branch (cond) goto a else goto b;
  }
  a: {
    var x : int;
    x := 1;
    goto c;
  }
  c: {
    y := x;
    return;
  }
  b: {
    var x : bool;
    x := true;
    return;
  }
};
#end

/--
info: error: [P]: CFG-local `x` is declared at different types in different blocks.
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm typeConflictAfterUsePgm).stripMetaData))

/-! ## An unreachable block declaring a local at another type is rejected too.

`entry` declares `x : int` and jumps to `use`, which reads `x`; `dead` has no
incoming edge and declares `x : bool`. Listed between the two, `dead` is the
declaration translation would type the read from, so the check also covers
unreachable declarers. -/

private def typeConflictDeadPgm :=
#strata
program Core;

procedure P(out y : int)
cfg entry {
  entry: {
    var x : int;
    x := 1;
    goto use;
  }
  dead: {
    var x : bool;
    x := true;
    return;
  }
  use: {
    y := x;
    return;
  }
};
#end

/--
info: error: [P]: CFG-local `x` is declared at different types in different blocks.
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm typeConflictDeadPgm).stripMetaData))

/-! ## A local declared as an alias and as its underlying type is accepted.

`a` declares `x : MyInt` and `b` declares `x : int`, where `type MyInt := int`.
`checkInitTypesAgree` compares the types after aliases are resolved, so the two
declarations agree and the program type-checks. -/

private def aliasAgreePgm :=
#strata
program Core;

type MyInt := int;

procedure P(cond : bool, out y : int)
cfg entry {
  entry: {
    branch (cond) goto a else goto b;
  }
  a: {
    var x : MyInt;
    x := 1;
    y := x;
    return;
  }
  b: {
    var x : int;
    x := 2;
    y := x;
    return;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

type MyInt := int;
procedure P (cond : bool, out y : int)
cfg entry {
  entry: {
    branch (cond) goto a else goto b;
  }
  a: {
    var x : int;
    x := 1;
    y := x;
    return;
  }
  b: {
    var x : int;
    x := 2;
    y := x;
    return;
  }
};
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm aliasAgreePgm).stripMetaData))

/-! ## A CFG-local that shadows a formal is rejected.

`entry` declares `var x`, but `x` is already a procedure formal. The structured
path rejects the same shadowing with "already in context"; `checkInitsNotHeader`
gives the CFG-level message. -/

private def shadowFormalPgm :=
#strata
program Core;

procedure P(x : int, out y : int)
cfg entry {
  entry: {
    var x : int;
    x := 5;
    y := x;
    return;
  }
};
#end

/--
info: error: [P]: a CFG-local shadows a procedure formal, output, or `old` binding.
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm shadowFormalPgm).stripMetaData))

/-! ## A polymorphic formal used at conflicting types across blocks is rejected.

`P<a>` takes `x : a`; `entry` assigns `x` to the `int` output `y`, and `n`
assigns `x` to the `bool` output `b`. Each use constrains the type parameter
`a`, and because the type substitution is threaded from one block to the next,
the two uses unify `a` to both `int` and `bool` and the procedure is rejected —
exactly as the structured path rejects the same body. The conflict spans two
blocks, so catching it exercises the cross-block substitution threading rather
than a single block's local unification. -/

private def polyConflictPgm :=
#strata
program Core;

procedure P<a>(x : a, out y : int, out b : bool)
cfg entry {
  entry: {
    y := x;
    goto n;
  }
  n: {
    b := x;
    return;
  }
};
#end

/-- The format carries a volatile `(lo-hi)` byte-range prefix; drop it and pin
the concrete message so the test fails if the body is rejected for a different
reason than the cross-block type conflict. Only the leading `(lo-hi) ` segment
is dropped: every later `) `-separated segment is rejoined, so a message that
itself contains `) ` is preserved in full. -/
private def errorTail (s : String) : String :=
  match s.splitOn ") " with
  | _ :: rest@(_ :: _) => ") ".intercalate rest
  | _ => s

/--
info: "Impossible to unify bool with int."
-/
#guard_msgs in
#eval errorTail
  (Std.format (Core.typeCheck .default (translatePgm polyConflictPgm).stripMetaData)).pretty

/-! ## A conflicting use inside an *unreachable* block does not poison unification.

Same polymorphic formal `P<a>` as `polyConflictPgm`, but the `bool` use lives in
`dead`, a block with no incoming edge (`entry` just returns). Because `dead` is
unreachable, its unification of `a` to `bool` must be isolated: it is checked
locally but not folded back into the carried substitution, so it neither
conflicts with the reachable `int` use nor leaks `bool` into the reachable
blocks' annotated output. The procedure is therefore accepted. -/

private def deadPolyConflictPgm :=
#strata
program Core;

procedure P<a>(x : a, out y : int, out b : bool)
cfg entry {
  entry: {
    y := x;
    return;
  }
  dead: {
    b := x;
    return;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure P (x : $__ty0, out y : int, out b : bool)
cfg entry {
  entry: {
    y := x;
    return;
  }
  dead: {
    b := x;
    return;
  }
};
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm deadPolyConflictPgm).stripMetaData))

/-! ## A branch condition whose type a later block solves.

`c : a` is a polymorphic formal. `entry` branches on `c`, which requires `a` to
be `bool`; `t` uses `c` at `bool` too. The condition's type is unified with
`bool`, so the body is accepted whether `t` is listed after `entry` or before
it. -/

private def guardSolvedLaterPgm :=
#strata
program Core;

procedure P<a>(c : a, out y : int)
cfg entry {
  entry: {
    branch (c) goto t else goto t;
  }
  t: {
    assume (c == true);
    y := 0;
    return;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure P (c : $__ty0, out y : int)
cfg entry {
  entry: {
    branch (c) goto t else goto t;
  }
  t: {
    assume [assume_0]: c == true;
    y := 0;
    return;
  }
};
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm guardSolvedLaterPgm).stripMetaData))

private def guardSolvedEarlierPgm :=
#strata
program Core;

procedure P<a>(c : a, out y : int)
cfg entry {
  t: {
    assume (c == true);
    y := 0;
    return;
  }
  entry: {
    branch (c) goto t else goto t;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure P (c : $__ty0, out y : int)
cfg entry {
  t: {
    assume [assume_0]: c == true;
    y := 0;
    return;
  }
  entry: {
    branch (c) goto t else goto t;
  }
};
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm guardSolvedEarlierPgm).stripMetaData))

/-! ## A nondeterministic `goto` on a cycle is rejected.

The translator lowers `goto h, done` to a branch on a fresh `$__nondet_N`, which
it declares in the same block. `h` jumps back to itself, so that declaration is
on a cycle and `checkNoLoopInits` rejects the body. -/

private def nondetLoopPgm :=
#strata
program Core;

procedure P(out y : int)
cfg entry {
  entry: {
    y := 0;
    goto h;
  }
  h: {
    goto h, done;
  }
  done: {
    return;
  }
};
#end

/--
info: error: [P]: a CFG-local is declared in a block that lies on a cycle; a loop-carried declaration would be re-initialized on re-entry.
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm nondetLoopPgm).stripMetaData))

/-! ## An unreachable block cannot read a local declared in another one.

`d1` and `d2` are both unreachable. `d2` reads `x`, which `d1` declares, but an
unreachable block is checked against the base environment alone, so the read is
rejected. -/

private def deadReadsDeadPgm :=
#strata
program Core;

procedure P(out y : int)
cfg entry {
  entry: {
    y := 0;
    return;
  }
  d1: {
    var x : int;
    x := 1;
    goto d2;
  }
  d2: {
    y := x;
    return;
  }
};
#end

/--
info: "[y := (x : int)] No free variables are allowed here!\nFree Variables: [x]"
-/
#guard_msgs in
#eval errorTail
  (Std.format (Core.typeCheck .default (translatePgm deadReadsDeadPgm).stripMetaData)).pretty

/-! ## Type annotations in the annotated body.

The printed program above shows no expression type annotations, so these tests
read them directly: for each block of the annotated CFG, the type annotation on
every free variable and operator in its commands and branch guard, in order. -/

open Lambda in
/-- The `(name, type)` annotation of every free variable and operator in `e`,
left to right. -/
private def exprAnnots : Core.Expression.Expr → List (String × String)
  | .fvar _ x ty => [(toString (Std.format x), toString (Std.format ty))]
  | .op _ o ty => [(toString (Std.format o), toString (Std.format ty))]
  | .app _ a b => exprAnnots a ++ exprAnnots b
  | .eq _ a b => exprAnnots a ++ exprAnnots b
  | .ite _ c t e => exprAnnots c ++ exprAnnots t ++ exprAnnots e
  | .abs _ _ _ e => exprAnnots e
  | .quant _ _ _ _ tr e => exprAnnots tr ++ exprAnnots e
  | _ => []

open Imperative in
/-- The annotations, in `exprAnnots` order, of the expressions a command carries:
a deterministic `init`/`set` right-hand side, an `assert`/`assume`/`cover`
condition, or a call's input arguments; `[]` for every other command. -/
private def cmdAnnots : Core.Command → List (String × String)
  | .cmd (.init _ _ (.det e) _) => exprAnnots e
  | .cmd (.set _ (.det e) _) => exprAnnots e
  | .cmd (.assert _ e _) => exprAnnots e
  | .cmd (.assume _ e _) => exprAnnots e
  | .cmd (.cover _ e _) => exprAnnots e
  | .call _ args _ => args.flatMap fun
      | .inArg e => exprAnnots e
      | _ => []
  | _ => []

/-- For each block of each CFG body that `typeCheck` returns, the annotations of
its commands and of its branch guard. -/
private def annotatedTypes (p : Core.Program) :
    Except String (List (String × List (String × String))) := do
  let p' ← (Core.typeCheck .default p.stripMetaData).mapError (toString ·.message)
  pure <| p'.decls.flatMap fun d =>
    match d with
    | Core.Decl.proc q _ =>
      match q.body with
      | .cfg g => g.blocks.map fun (l, blk) =>
          (l, blk.cmds.flatMap cmdAnnots ++
            match blk.transfer with
            | .condGoto c _ _ _ => exprAnnots c
            | .finish _ => [])
      | .structured _ => []
    | _ => []

/-! ### A type variable solved by a later block resolves an earlier block.

`entry` only compares `x : a` with itself, which leaves its type variable
unsolved; `n` then solves it to `int`. The final substitution is applied to every
block, so `entry`'s annotations read `int` too. -/

private def laterSolvesEarlierPgm :=
#strata
program Core;

procedure P<a>(x : a, out y : int)
cfg entry {
  entry: {
    assert (x == x);
    goto n;
  }
  n: {
    y := x;
    return;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: Except.ok [("entry", [("x", "some int"), ("x", "some int")]), ("n", [("x", "some int")])]
-/
#guard_msgs in
#eval annotatedTypes (translatePgm laterSolvesEarlierPgm)

/-! ### An unreachable block does not share fresh type variables.

`dead` and the later live block `live` each compare two `None()`s, which leaves
each block's element type a fresh, unsolved type variable. `dead`'s generator
state is carried forward, so `live` gets a different variable rather than
reusing `dead`'s. -/

private def deadThenLivePolyPgm :=
#strata
program Core;

datatype Opt (a : Type) { None(), Some(v: a) };

procedure P(out y : int)
cfg entry {
  entry: {
    goto live;
  }
  dead: {
    assert (None() == None());
    return;
  }
  live: {
    assert (None() == None());
    y := 1;
    return;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: Except.ok [("entry", []),
 ("dead", [("None", "some (Opt $__ty3)"), ("None", "some (Opt $__ty3)")]),
 ("live", [("None", "some (Opt $__ty7)"), ("None", "some (Opt $__ty7)")])]
-/
#guard_msgs in
#eval annotatedTypes (translatePgm deadThenLivePolyPgm)

/-! ## A branch condition reads the right variables after the block's own declarations.

The transfer is in scope of the block's commands, so a condition that names a
formal still resolves to that formal when the block declares locals first, and a
condition may name a local the same block declares. Each test reads the type
annotations of the condition's variables, which the printed program does not
show. -/

/-- `entry` declares `flag` and then branches on the formal `c`. -/
private def guardAfterLocalPgm :=
#strata
program Core;

procedure P(c : bool, out y : int)
cfg entry {
  entry: {
    var flag : bool;
    flag := false;
    branch (c) goto t else goto f;
  }
  t: {
    y := 1;
    return;
  }
  f: {
    y := 0;
    return;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: Except.ok [("entry", [("c", "some bool")]), ("t", []), ("f", [])]
-/
#guard_msgs in
#eval annotatedTypes (translatePgm guardAfterLocalPgm)

/-- `entry` branches on `flag`, a local it declares itself. -/
private def guardOnOwnLocalPgm :=
#strata
program Core;

procedure P(c : bool, out y : int)
cfg entry {
  entry: {
    var flag : bool;
    flag := c;
    branch (flag) goto t else goto f;
  }
  t: {
    y := 1;
    return;
  }
  f: {
    y := 0;
    return;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: Except.ok [("entry", [("c", "some bool"), ("flag", "some bool")]), ("t", []), ("f", [])]
-/
#guard_msgs in
#eval annotatedTypes (translatePgm guardOnOwnLocalPgm)

-- `wellFormedCFGPgm`'s `entry` declares `x`, then branches on the formals
-- `a == b`.
/--
info: [Strata.Core] Type checking succeeded.

---
info: Except.ok [("entry", [("a", "some int"), ("b", "some int")]), ("p", [("x", "some int")]), ("q", []), ("done", [])]
-/
#guard_msgs in
#eval annotatedTypes (translatePgm wellFormedCFGPgm)

/-! ## Three declarers of one local.

`checkInitsNotReachable` on locals with three or more reachable declarers: one
where a declarer is reachable from both others (rejected), one where no declarer
reaches another (accepted), and one where three declarers all reach a fourth
(rejected). The last is the case where `initsNotReachableB`'s search reaches a
block from more than two declarers. -/

/-- `c` is reachable from both `a` and `b`, which are themselves unrelated. -/
private def threeDeclReachPgm :=
#strata
program Core;

procedure P(cond : bool, out y : int)
cfg entry {
  entry: {
    branch (cond) goto a else goto m;
  }
  m: {
    branch (cond) goto b else goto c;
  }
  a: {
    var x : int;
    x := 1;
    y := x;
    goto c;
  }
  b: {
    var x : int;
    x := 2;
    y := x;
    goto c;
  }
  c: {
    var x : int;
    x := 3;
    y := x;
    return;
  }
};
#end

/--
info: error: [P]: a CFG-local is declared in two blocks where one is reachable from the other; a single path would re-initialize it.
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm threeDeclReachPgm).stripMetaData))

/-- `a`, `b` and `c` declare the same local, and no one of them reaches another. -/
private def threeDeclApartPgm :=
#strata
program Core;

procedure P(cond : bool, out y : int)
cfg entry {
  entry: {
    branch (cond) goto a else goto m;
  }
  m: {
    branch (cond) goto b else goto c;
  }
  a: {
    var x : int;
    x := 1;
    y := x;
    return;
  }
  b: {
    var x : int;
    x := 2;
    y := x;
    return;
  }
  c: {
    var x : int;
    x := 3;
    y := x;
    return;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure P (cond : bool, out y : int)
cfg entry {
  entry: {
    branch (cond) goto a else goto m;
  }
  m: {
    branch (cond) goto b else goto c;
  }
  a: {
    var x : int;
    x := 1;
    y := x;
    return;
  }
  b: {
    var x : int;
    x := 2;
    y := x;
    return;
  }
  c: {
    var x : int;
    x := 3;
    y := x;
    return;
  }
};
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm threeDeclApartPgm).stripMetaData))

/-- `a`, `b` and `c` declare the same local, none reaches another, and all three
jump to `d`, which declares it too. -/
private def fourDeclMergePgm :=
#strata
program Core;

procedure P(cond : bool, out y : int)
cfg entry {
  entry: {
    branch (cond) goto a else goto m;
  }
  m: {
    branch (cond) goto b else goto c;
  }
  a: {
    var x : int;
    x := 1;
    y := x;
    goto d;
  }
  b: {
    var x : int;
    x := 2;
    y := x;
    goto d;
  }
  c: {
    var x : int;
    x := 3;
    y := x;
    goto d;
  }
  d: {
    var x : int;
    x := 4;
    y := x;
    return;
  }
};
#end

/--
info: error: [P]: a CFG-local is declared in two blocks where one is reachable from the other; a single path would re-initialize it.
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm fourDeclMergePgm).stripMetaData))

/-! ## Differential: `computeDominators` matches the set-dataflow reference.

`computeDominators` derives each block's dominators from the immediate-dominator
tree; `computeDominatorsFullFuel` computes them directly from the textbook set
equations. This check runs both on the CFG body of every program above (a range
of shapes: straight-line, diamonds, a merge, an unreachable block, cycles, and
an alias-typed local) and asserts the two dominator maps agree label-by-label
(order-insensitively). -/

open Imperative in
/-- Reference dominator sets: the fixpoint of `dom(entry) = {entry}` and
`dom(n) = {n} ∪ ⋂ dom(p)` over the predecessors `p` of `n`, iterated a fixed
`n*n+1` times, with every non-entry block starting at all labels. It is
quadratic in passes, so it lives beside its only consumer rather than in the
`CFGDominators` module, where the checker could call it. -/
private def computeDominatorsFullFuel
    (cfg : CFG String (DetBlock String Core.Command Core.Expression)) :
    Std.HashMap String (List String) := Id.run do
  let allLabels := cfg.labels
  let preds := cfg.predMap
  let mut dom : Std.HashMap String (List String) := {}
  for l in allLabels do
    dom := dom.insert l (if l == cfg.entry then [cfg.entry] else allLabels)
  let fuel := allLabels.length * allLabels.length + 1
  for _ in List.range fuel do
    for l in allLabels do
      if l != cfg.entry then
        let ps := preds.getD l []
        let inter : List String :=
          match ps with
          | [] => allLabels
          | p :: rest =>
            let restSets := rest.map (fun q => Std.HashSet.ofList (dom.getD q []))
            (dom.getD p []).filter (fun x => restSets.all (·.contains x))
        let newDom := l :: inter.filter (· != l)
        dom := dom.insert l newDom
  return dom

open Imperative in
/-- Order-insensitive agreement of two dominator maps over a CFG's labels: for
every block label, the two maps assign the same dominator set (compared by mutual
containment, so map iteration order and order within a set do not matter). -/
private def domMapsAgree (cfg : CFG String (DetBlock String Core.Command Core.Expression))
    (d1 d2 : Std.HashMap String (List String)) : Bool :=
  cfg.labels.all (fun l =>
    let s1 := d1.getD l []
    let s2 := d2.getD l []
    s1.all (s2.contains ·) && s2.all (s1.contains ·))

open Imperative in
private def allCFGBodies (p : Core.Program) :
    List (CFG String (DetBlock String Core.Command Core.Expression)) :=
  p.decls.flatMap fun d =>
    match d with
    | Core.Decl.proc q _ =>
      match q.body with
      | .cfg g => [g]
      | .structured _ => []
    | _ => []

/-- Every test program above, translated; both differential checks run on all
of them. -/
private def allPgms : List Core.Program :=
  [ translatePgm dupLabelPgm, translatePgm missingEntryPgm, translatePgm badGotoPgm,
    translatePgm badElsePgm,
    translatePgm nonDomUsePgm, translatePgm symDiamondPgm, translatePgm nonBoolGuardPgm,
    translatePgm comparableDeclPgm, translatePgm dupInitInBlockPgm,
    translatePgm wellFormedCFGPgm, translatePgm siblingBetweenDeclAndUsePgm,
    translatePgm deadCodeRedeclarePgm, translatePgm aliasLocalPgm,
    translatePgm deepDomScopePgm,
    translatePgm loopInitPgm, translatePgm reachComparableInitPgm,
    translatePgm loopInitTwoBlockPgm, translatePgm reachComparableFarPgm,
    translatePgm chainedDiamondPgm, translatePgm multiBackEdgePgm,
    translatePgm typeConflictBeforeUsePgm, translatePgm typeConflictAfterUsePgm,
    translatePgm typeConflictDeadPgm,
    translatePgm aliasAgreePgm,
    translatePgm shadowFormalPgm, translatePgm polyConflictPgm,
    translatePgm deadPolyConflictPgm,
    translatePgm laterSolvesEarlierPgm, translatePgm deadThenLivePolyPgm,
    translatePgm threeDeclReachPgm, translatePgm threeDeclApartPgm,
    translatePgm fourDeclMergePgm,
    translatePgm guardSolvedLaterPgm, translatePgm guardSolvedEarlierPgm,
    translatePgm nondetLoopPgm, translatePgm deadReadsDeadPgm,
    translatePgm guardAfterLocalPgm, translatePgm guardOnOwnLocalPgm ]

/-- `computeDominators` and the set-dataflow reference agree on every CFG body
of the already-translated program `p`. -/
private def domsAgreeOnPgm (p : Core.Program) : Bool :=
  (allCFGBodies p).all fun cfg =>
    domMapsAgree cfg cfg.computeDominators (computeDominatorsFullFuel cfg)

/-- info: true -/
#guard_msgs in
#eval allPgms.all (fun p => domsAgreeOnPgm p.stripMetaData)

/-! ## Differential check: guards with per-local grouping

`cycleLabelsWith` (one strongly-connected-components pass) must agree with a
per-label `onCycleWith` search, and `initsNotReachableB` (one capped multi-source
search per local), `initsIncomparableB` and `domScopedB` (per-local declarer
groups) must agree with the pairwise reference formulas below, on every CFG body
of the test programs. -/

/-- Reference for `cycleLabelsWith`: does `l` lie on a cycle, i.e. is it
reachable in one or more steps from itself? -/
private def onCycleWith (succs : Std.HashMap String (List String)) (fuel : Nat)
    (l : String) : Bool :=
  (Imperative.CFG.reachableSetFromSuccsWith succs fuel l).contains l

open Imperative in
/-- Pairwise reference for `initsNotReachableB`: a reach set per declarer, and a
check over every ordered pair of distinct same-local reachable declarers. -/
private def initsNotReachableRef (ds : List (Core.Expression.Ident × String))
    (reachable : Std.HashSet String) (succs : Std.HashMap String (List String))
    (fuel : Nat) : Bool :=
  let reaches := fun (a b : String) =>
    (CFG.reachableSetFromSuccsWith succs fuel a).contains b
  ds.all fun p1 => ds.all fun p2 =>
    !(reachable.contains p1.2 && reachable.contains p2.2 &&
      p1.1 == p2.1 && p1.2 != p2.2 && reaches p1.2 p2.2)

/-- Pairwise reference for `initsIncomparableB`: every ordered pair of distinct
same-local reachable declarers is dominance-incomparable. -/
private def initsIncomparableRef (dom : Std.HashMap String (List String))
    (reachable : Std.HashSet String) (ds : List (Core.Expression.Ident × String)) : Bool :=
  ds.all fun p1 => ds.all fun p2 =>
    !(reachable.contains p1.2 && reachable.contains p2.2 &&
      p1.1 == p2.1 && p1.2 != p2.2 && Imperative.CFG.Dom.dominates dom p1.2 p2.2)

/-- Reference for `domScopedB`: every use of a CFG-local in a reachable block is
checked against every declarer in `cfgInitDeclBlocks`. -/
private def domScopedRef (dom : Std.HashMap String (List String))
    (reachable : Std.HashSet String) (cfg : Core.DetCFG) : Bool :=
  let inits := Std.HashSet.ofList (Core.WF.cfgInitVars cfg)
  let ds := Core.Procedure.cfgInitDeclBlocks cfg
  cfg.blocks.all fun lb =>
    !(reachable.contains lb.1) ||
    (Core.WF.blockReadVars lb.2 ++ Core.WF.blockSetTargets lb.2).all fun x =>
      !(inits.contains x) ||
      ds.any (fun p => p.1 == x && Imperative.CFG.Dom.dominates dom p.2 lb.1)

open Imperative in
private def linearGuardsAgreeOnPgm (p : Core.Program) : Bool :=
  (allCFGBodies p).all fun cfg =>
    let succs := cfg.succMap
    let fuel := cfg.blocks.length
    let labels := cfg.labels
    let onCyc := CFG.cycleLabelsWith succs labels
    let reachable := cfg.reachableLabels
    let ds := Core.Procedure.cfgInitDeclBlocks cfg
    labels.all (fun l => onCyc.contains l == onCycleWith succs fuel l) &&
    Core.Procedure.initsNotReachableB ds reachable succs ==
      initsNotReachableRef ds reachable succs fuel &&
    (let dom := cfg.computeDominators
     Core.Procedure.initsIncomparableB dom reachable cfg ==
       initsIncomparableRef dom reachable ds &&
     Core.Procedure.domScopedB dom reachable cfg == domScopedRef dom reachable cfg)

/-- info: true -/
#guard_msgs in
#eval allPgms.all (fun p => linearGuardsAgreeOnPgm p.stripMetaData)

/-! ## The shipped CFG examples, end to end.

Each example is parsed from its embedded source text, type-checked, and passed
to `Core.verify`. Type checking accepts it and returns the annotated program;
verification then stops at the verifier's requirement that every procedure
body be structured. Symbolic evaluation called directly, without the verifier's
pipeline, rejects the CFG body as well rather than dropping its obligations. -/

/-- The shipped example `name`, parsed as a Core program. -/
private def parseExample (name : String) : IO StrataDDM.Program := do
  let some (_, src) := embeddedExampleFiles.find? (·.1 == name)
    | throw (IO.userError s!"no embedded example {name}")
  let dialects :=
    StrataDDM.Elab.LoadedDialects.ofDialects! #[StrataDDM.initDialect, _root_.Strata.Core]
  let header := "program Core;\n\n"
  let body := if src.startsWith header then (src.drop header.length).toString else src
  StrataDDM.Elab.parseStrataProgramFromDialect dialects "Core"
    (StrataDDM.Parser.stringInputContext ⟨name⟩ body)

/-- Type-check, symbolically evaluate, and verify the shipped example `name`,
printing each result. -/
private def runExample (name : String) : IO Unit := do
  let p ← parseExample name
  IO.println (Std.format (Core.typeCheck .default (translatePgm p).stripMetaData))
  match Core.toCoreProofObligationProgram .quiet (translatePgm p) with
  | .ok _ => IO.println "symbolic evaluation: ok"
  | .error e => IO.println s!"symbolic evaluation: {e.message}"
  try
    let results ← _root_.Strata.Core.verify p
    IO.println s!"verify: {results.size} results"
  catch e => IO.println s!"verify: {e}"

/--
info: [Strata.Core] Type checking succeeded.

ok: program Core;

procedure Max (x : int, y : int, out m : int)
spec {
  ensures [Max_ensures_0]: int.ge(m, x);
  ensures [Max_ensures_1]: int.ge(m, y);
  ensures [Max_ensures_2]: m == x || m == y;
  } cfg entry {
  entry: {
    branch (int.ge(x, y)) goto then_branch else goto else_branch;
  }
  then_branch: {
    m := x;
    goto done;
  }
  else_branch: {
    m := y;
    goto done;
  }
  done: {
    return;
  }
};
procedure CountUp (n : int, out y : int)
spec {
  requires [CountUp_requires_0]: int.ge(n, 0);
  ensures [CountUp_ensures_1]: y == n;
  } cfg entry {
  entry: {
    y := 0;
    goto loop;
  }
  loop: {
    branch (int.lt(y, n)) goto body else goto done;
  }
  body: {
    y := int.add(y, 1);
    goto loop;
  }
  done: {
    return;
  }
};

symbolic evaluation: toCoreProofObligationProgram: procedure 'Max' has a CFG body; symbolic evaluation supports only structured bodies.
verify: ❌ Expected every procedure body to be structured, but found procedure Max with a CFG body.
-/
#guard_msgs in
#eval runExample "CFGSimple.core.st"

/--
info: [Strata.Core] Type checking succeeded.

ok: program Core;

procedure NondetChoice (out y : int)
spec {
  ensures [NondetChoice_ensures_0]: y == 1 || y == 2;
  } cfg entry {
  entry: {
    goto left, right;
  }
  left: {
    y := 1;
    goto done;
  }
  right: {
    y := 2;
    goto done;
  }
  done: {
    return;
  }
};

symbolic evaluation: toCoreProofObligationProgram: procedure 'NondetChoice' has a CFG body; symbolic evaluation supports only structured bodies.
verify: ❌ Expected every procedure body to be structured, but found procedure NondetChoice with a CFG body.
-/
#guard_msgs in
#eval runExample "CFGNondet.core.st"

end Strata.CFGTypeCheck

end
