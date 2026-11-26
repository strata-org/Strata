/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Transform.DefInline
import Strata.Transform.WPLoop
import Strata.Transform.DeadDefElim
import Strata.Transform.Passive.CoreWPSSA
import Strata.Languages.Core.Factory
import Strata.Languages.Core
import Strata.MetaVerifier
import StrataTest.Languages.Core.Tests.ObligationProgramTestUtils

/-! # Inlining of single-use definitions on examples

`defInline` on obligation programs: a chain of definitions each read once becomes one term in the
obligation that reads its last name, the constants of its sums folded (`Core.DefInline.addFold`),
and the erasure of unread definitions after it removes the chain; a definition read twice stays;
a function value stays; a definition made in one arm of an `ite *` is not substituted in the
other arm.  Under `--vcgen wp` the obligation of the program
`x := x + 1` (three times) then `assert x > 0` reads no definition.  On the outputs of the WP and
SSA phases for random statement lists, the inlining followed by the erasure of unread definitions
leaves at most the nodes the erasure alone leaves. -/

namespace DefInlineTest

open Core Lambda Imperative Imperative.DefInline Imperative.DeadDefElim Imperative.WP Core.WP
  ObligationProgramTestUtils

/-- The printed list after the inlining of the Core pipeline and the erasure of unread
    definitions. -/
def di (ss : Statements) : String :=
  toString (Std.format (deadDefElimH [] (defInline (.after DefInline.addFold) ss)))

/-! ## A chain read once

The SSA shape of `x := x + 1` three times then `assert x > 0`: each definition is read once, so
the obligation reads the nested sum and no definition is left. -/

#guard di [initInt "x@1" (add (iv "x") (int 1)), initInt "x@2" (add (iv "x@1") (int 1)),
    initInt "x@3" (add (iv "x@2") (int 1)), assert' "a" (gt (iv "x@3") (int 0))] == lines [
    "{",
    "  assert [a]: int.gt(int.add(x, 3), 0);",
    "}"]

/-! ## The folding of the constants of a sum

Only `(a + c₁) + c₂` with integer literals `c₁` and `c₂`, at the root, is rewritten. -/

#guard toString (Std.format (DefInline.addFold (add (add (iv "x") (int 1)) (int 2)))) ==
  "int.add(x, 3)"
#guard DefInline.addFold (add (int 1) (add (iv "x") (int 2))) == add (int 1) (add (iv "x") (int 2))
#guard DefInline.addFold (add (add (iv "x") (iv "y")) (int 2)) ==
  add (add (iv "x") (iv "y")) (int 2)
#guard DefInline.addFold (gt (add (add (iv "x") (int 1)) (int 2)) (int 0)) ==
  gt (add (add (iv "x") (int 1)) (int 2)) (int 0)

/-! ## A definition read twice stays -/

#guard di [initInt "y@1" (add (iv "x") (int 1)), initInt "z@2" (add (iv "y@1") (iv "y@1")),
    assert' "a" (gt (iv "z@2") (int 0))] == lines [
    "{",
    "  var y@1 : int := int.add(x, 1);",
    "  assert [a]: int.gt(int.add(y@1, y@1), 0);",
    "}"]

/-! ## A function value stays

Substituting it would create a beta redex. -/

#guard di [initInt "f" (.abs Core.valueLoc "" (some .int) (.bvar Core.valueLoc 0)),
    assert' "a" (gt (.app Core.valueLoc (.fvar Core.valueLoc (id' "f") none) (int 1)) (int 0))] == lines [
    "{",
    "  var f : int := fun __q0 : int => __q0;",
    "  assert [a]: int.gt(f(1), 0);",
    "}"]

/-! ## Arms are scoped

`y` is defined in the `then` arm and read once, in the `else` arm, which reads the entry value
of `y`, not the `then` arm's definition. -/

#guard di [ndIte [initInt "y" (add (iv "x") (int 1)), assert' "a" (gt (iv "x") (int 0))]
    [assert' "b" (gt (iv "y") (int 0))]] == lines [
    "{",
    "  if * {",
    "    var y : int := int.add(x, 1);",
    "    assert [a]: int.gt(x, 0);",
    "  }",
    "  else {",
    "    assert [b]: int.gt(y, 0);",
    "  }",
    "}"]

/-! ## Under `--vcgen wp`

The obligation of `a` reads the nested sum directly. -/

def incrPgm :=
#strata
program Core;
procedure P(x : int)
{
  var y : int := x;
  y := int.add(y, 1);
  y := int.add(y, 1);
  y := int.add(y, 1);
  assert [a]: (int.gt(y, x));
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: a
Property: assert
Obligation:
int.gt(int.add(x@0, 3), x@0)

Wrote problem to _test_definline_vcs/a_0.smt2.
-/
#guard_msgs in
#eval do
  let vcDir : System.FilePath := "_test_definline_vcs"
  IO.FS.createDirAll vcDir
  let _ ← Strata.Core.verify incrPgm (options := { Core.VerifyOptions.default with
    vcgen := .wp, verbose := .debug, vcDirectory := vcDir })
  IO.FS.removeDirAll vcDir

/-! With the contextual rewriting phase after `betaReduce` in the same order, the phase rewrites
the obligation of `a`, `x@0 + 3 > x@0`, to `true`, so no problem is written for a solver. -/

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: a
Property: assert
Obligation:
true
-/
#guard_msgs in
#eval do
  let vcDir : System.FilePath := "_test_definline_vcs_rewrite"
  IO.FS.createDirAll vcDir
  let options := { Core.VerifyOptions.default with
    vcgen := .wp, verbose := .debug, vcDirectory := vcDir }
  let .ok pipeline := Strata.Core.splicePhasesAfter "betaReduce"
      [Strata.Core.passContextualRewrite] (Strata.Core.corePipelinePhases options)
      >>= Strata.Core.validatePipeline
    | throw (IO.userError "the order does not compose")
  let _ ← Strata.Core.verify incrPgm (options := options) (pipeline := some pipeline)
  IO.FS.removeDirAll vcDir

/-! ## The erasure after the inlining leaves no more nodes

On the outputs of the WP and SSA phases for random statement lists (`RProg`), the inlining
followed by the erasure of unread definitions leaves at most the nodes the erasure alone leaves
(the Plausible property below, statement of a future theorem). -/

/-- Does the inlining followed by the erasure leave on `o` at most the nodes the erasure alone
    leaves? -/
def neverLarger (o : Statements) : Bool :=
  WPLoop.blockSize (deadDefElimH [] (defInline (.after DefInline.addFold) o)) ≤
    WPLoop.blockSize (deadDefElimH [] o)

/-- info: Unable to find a counter-example -/
#guard_msgs in
#eval Plausible.Testable.check (∀ r : RProg, neverLarger (obligations ["c"] r.stmts) = true)
  { numInst := 300, randomSeed := some 7 }

/-- `n` increments of `x`, then an assertion. -/
def f8a (n : Nat) : Statements :=
  (List.replicate n (set' "x" (add (iv "x") (int 1)))) ++ [assert' "a" (gt (iv "x") (int 0))]

/- On `f8a`, the erasure after the inlining leaves only the obligation, on `x@0` plus the number
of increments. -/
/-- info: [{
  assert [a]: int.gt(int.add(x@0, 10), 0);
}, {
  assert [a]: int.gt(int.add(x@0, 40), 0);
}, {
  assert [a]: int.gt(int.add(x@0, 160), 0);
}]
-/
#guard_msgs in
#eval [10, 40, 160].map fun n =>
  Std.format (deadDefElimH [] (defInline (.after DefInline.addFold) (obligations ["x"] (f8a n))))

end DefInlineTest
