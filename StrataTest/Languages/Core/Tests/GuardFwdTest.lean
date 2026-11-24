/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Transform.GuardFwd
import Strata.Transform.WPLoop
import Strata.Transform.DeadDefElim
import Strata.Transform.Passive.CoreWPSSA
import Strata.Languages.Core.Factory
import Strata.Languages.Core
import Strata.MetaVerifier
import StrataTest.Languages.Core.Tests.ObligationProgramTestUtils

/-! # Guard forwarding on examples

`guardFwd` on obligation programs: under a known guard, a definition `x := ite(g, a, b)` reads
as its selected arm, at spine positions (the arms of a conditional) and inside a guarded fact;
a definition made in one arm of an `ite *` is not used in the other arm; an assertion's condition
is only rewritten exactly (a copy replaced by its variable, `a == a` by `true`).  On a program
whose two arms assign constants, the WP pipeline with guard forwarding writes a smaller SMT query
than without it.  On the family of `Examples/CSEPathSplits.core.st`, guarded-merge folding over
the reach flags closes every obligation without a solver.  On the outputs of the WP and SSA phases
for random statement lists, the erasure of unread definitions after it leaves a list never larger
than it leaves without it. -/

namespace GuardFwdTest

open Core Lambda Imperative Imperative.GuardFwd Imperative.DeadDefElim Imperative.WP Core.WP
  ObligationProgramTestUtils

def bv (n : String) : Expression.Expr := .fvar Core.valueLoc (id' n) (some .bool)
def ite (c t f : Expression.Expr) : Expression.Expr := .ite Core.valueLoc c t f
def initT (x : String) (ty : LMonoTy) (e : Expression.Expr) : Statement :=
  .cmd (.cmd (.init (id' x) (.forAll [] ty) (.det e) md))
def assume' (l : String) (e : Expression.Expr) : Statement := .cmd (.cmd (.assume l e md))

/-- The printed list after guard forwarding and the erasure of unread definitions. -/
def gf (ss : Statements) : String := toString (Std.format (deadDefElimH [] (guardFwd ss)))

/-! ## Both arms constant

The SSA shape of `if (c == 1) { x := 1 } else { x := -1 }`: `x@4` is `1` under `g`, so the merge
`x@5` reads `1` and `-1` directly, and the chain through `x@1` and `x@4` is unread. -/

#guard gf [initT "g" .bool (.eq Core.valueLoc (iv "c") (int 1)),
    initT "x@4" .int (ite (bv "g") (int 1) (iv "x@1")),
    initT "x@5" .int (ite (bv "g") (iv "x@4") (int (-1))),
    assert' "a" (gt (iv "x@5") (int 0))] == lines [
    "{",
    "  var g : bool := c == 1;",
    "  var x@5 : int := if g then 1 else int.neg(1);",
    "  assert [a]: int.gt(x@5, 0);",
    "}"]

/-! ## A guarded fact reading a merge

The fact of the `g` side reads the merge `h@15 := ite(g, h@14, h@2)`: under `g` it reads
`h@14`, so the fact no longer depends on `h@2`. -/

#guard gf [initT "h@15" .int (ite (bv "g") (iv "h@14") (iv "h@2")),
    assume' "post" (ite (bv "g") (gt (add (iv "h@15") (int 1)) (int 0)) Core.true),
    assert' "a" (gt (iv "y") (int 0))] == lines [
    "{",
    "  assume [post]: if g then int.gt(int.add(h@14, 1), 0) else true;",
    "  assert [a]: int.gt(y, 0);",
    "}"]

/-! ## Scoping and assertions

A definition made in the `then` arm of an `ite *` is unknown in the `else` arm, and an
assertion's condition is not rewritten under a guard. -/

#guard gf [ndIte [initT "x@2" .int (ite (bv "g") (int 1) (int 2)),
      assert' "t" (ite (bv "g") (gt (iv "x@2") (int 0)) Core.true)]
    [initT "z@3" .int (ite (bv "g") (iv "x@2") (int 3)),
      assert' "e" (gt (iv "z@3") (int 0))]] == lines [
    "{",
    "  if * {",
    "    var x@2 : int := if g then 1 else 2;",
    "    assert [t]: if g then int.gt(x@2, 0) else true;",
    "  }",
    "  else {",
    "    var z@3 : int := if g then x@2 else 3;",
    "    assert [e]: int.gt(z@3, 0);",
    "  }",
    "}"]

/-! ## Exact rewrites of an assertion

A copy `r@2 := y@1` is replaced by its variable in an assertion, and `y@1 == y@1` is `true`. -/

#guard gf [initT "y@1" .int (add (iv "c") (int 1)), initT "r@2" .int (iv "y@1"),
    assert' "a" (.eq Core.valueLoc (iv "r@2") (iv "y@1"))] == lines [
    "{",
    "  assert [a]: true;",
    "}"]

/-! ## The SMT query of a program whose arms assign constants

`--vcgen wp` with guard forwarding writes the query of `a` with fewer bytes than the same
pipeline without the phase. -/

def bothArmConst : StrataDDM.Program :=
#strata
program Core;
procedure P(c : int, out x : int)
{
  if (c == 1) { x := 1; } else { x := int.neg(1); }
  if (c == 2) { x := 2; } else { x := int.neg(2); }
  if (c == 3) { x := 3; } else { x := int.neg(3); }
  if (c == 4) { x := 4; } else { x := int.neg(4); }
  assert [a]: int.gt(x, 0);
};
#end

/-- The bytes of the SMT queries written for `pgm` under `--vcgen wp`, with the default order in
    which the rewrite loop is replaced by one round of its components (`guardFwd`, `defInline`,
    `deadDefElim`) or, when `withoutGuardFwd` holds, by the round without `guardFwd`. -/
def queryBytes (pgm : StrataDDM.Program) (withoutGuardFwd : Bool) : IO Nat := do
  let opts : Core.VerifyOptions := { Core.VerifyOptions.quiet with vcgen := .wp }
  let names := (Strata.Core.corePipelinePhases opts).map Strata.Core.phaseName |>.flatMap fun n =>
    if n == "wpLoop" then
      (if withoutGuardFwd then [] else ["guardFwd"]) ++ ["defInline", "deadDefElim"]
    else [n]
  let phases ← IO.ofExcept (Strata.Core.resolvePhases (Strata.Core.nameablePhases opts) names)
  let vp ← IO.ofExcept (Strata.Core.validatePipeline phases)
  return (← wpQueries pgm "_test_vcs_guard_fwd" (some vp)).utf8ByteSize

/-- info: true -/
#guard_msgs in
#eval do
  let with_ ← queryBytes bothArmConst false
  let without ← queryBytes bothArmConst true
  IO.println (decide (0 < with_ ∧ with_ < without))

/-! ## Guarded-merge folding over reach flags

The procedure of `Examples/CSEPathSplits.core.st` with 10 branches, each assuming a fact about a
shared `y`, setting `r := y`, checking `r == y` and leaving the block; the postcondition reads the
merge of every branch's `r` and of the fall-through `r`, which reaches `y` only through the reach
flag of the fall-through path.  Under `--vcgen wp` every obligation is closed without a solver: run
with the solver skipped, every obligation is proved. -/

def pathSplits : StrataDDM.Program :=
#strata
program Core;
procedure Dispatch(x : int, out y : int, out r : int)
spec {
  ensures [r_is_y]: r == y;
}
{
  y := x;
  y := int.add(int.mul(y, y), y);
  y := int.add(int.mul(y, y), y);
  done: {
    if (x == 0) { assume [a0]: int.ge(int.add(y, 0), 0); r := y; assert [b0]: r == y; exit done; }
    if (x == 1) { assume [a1]: int.ge(int.add(y, 1), 0); r := y; assert [b1]: r == y; exit done; }
    if (x == 2) { assume [a2]: int.ge(int.add(y, 2), 0); r := y; assert [b2]: r == y; exit done; }
    if (x == 3) { assume [a3]: int.ge(int.add(y, 3), 0); r := y; assert [b3]: r == y; exit done; }
    if (x == 4) { assume [a4]: int.ge(int.add(y, 4), 0); r := y; assert [b4]: r == y; exit done; }
    if (x == 5) { assume [a5]: int.ge(int.add(y, 5), 0); r := y; assert [b5]: r == y; exit done; }
    if (x == 6) { assume [a6]: int.ge(int.add(y, 6), 0); r := y; assert [b6]: r == y; exit done; }
    if (x == 7) { assume [a7]: int.ge(int.add(y, 7), 0); r := y; assert [b7]: r == y; exit done; }
    if (x == 8) { assume [a8]: int.ge(int.add(y, 8), 0); r := y; assert [b8]: r == y; exit done; }
    if (x == 9) { assume [a9]: int.ge(int.add(y, 9), 0); r := y; assert [b9]: r == y; exit done; }
    r := y;
  }
};
#end

/--
info: b0: proved
b1: proved
b2: proved
b3: proved
b4: proved
b5: proved
b6: proved
b7: proved
b8: proved
b9: proved
r_is_y: proved
-/
#guard_msgs in
#eval do
  let opts : Core.VerifyOptions := { Core.VerifyOptions.quiet with
    vcgen := .wp
    skipSolver := true }
  for r in ← Strata.Core.verify pathSplits (options := opts) do
    IO.println s!"{r.obligation.label}: {if r.isSuccess then "proved" else "not proved"}"

/-! ## The erasure after guard forwarding leaves no more nodes

On the outputs of the WP and SSA phases for random statement lists (`RProg`), erasing unread
definitions after guard forwarding leaves at most the nodes the erasure alone leaves (the
Plausible property below, statement of a future theorem).  Guard forwarding alone can grow its
input: it moves a compound candidate to its only use, and only the erasure removes the definition
left unread. -/

/-- Does erasing unread definitions after guard forwarding leave on `o` at most the nodes the
    erasure alone leaves? -/
def neverLarger (o : Statements) : Bool :=
  WPLoop.blockSize (deadDefElimH [] (guardFwd o)) ≤ WPLoop.blockSize (deadDefElimH [] o)

/-- info: Unable to find a counter-example -/
#guard_msgs in
#eval Plausible.Testable.check (∀ r : RProg, neverLarger (obligations ["c"] r.stmts) = true)
  { numInst := 300, randomSeed := some 7 }

end GuardFwdTest
