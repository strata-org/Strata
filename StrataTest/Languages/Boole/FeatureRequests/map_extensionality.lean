/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier
import Strata.Languages.Boole.Verify
-- Test fixtures build Core expressions directly; no source locations. -- sourcerange:file-ok

open Strata
open Lambda

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:guide/ext_equal`
- Verus link:
  `guide/ext_equal`: https://github.com/verus-lang/verus/blob/main/examples/guide/ext_equal.rs
- Original gap: extensional equality lowered to ordinary equality
- Current status: implemented for direct `Map` types via Boole `=~=`
- Lowering: `a =~= b` becomes `∀ i . a[i] == b[i]`
- Remaining gap: named map synonyms and non-map extensional equality
-/

private def mapExtensionalitySeed : Strata.Program :=
#strata
program Boole;

// Implemented shape for direct `Map` types: `a =~= b` lowers to
// `∀ i: int . a[i] == b[i]`.
//
// spec {
//   requires ∀ i: int . a[i] == b[i];
//   ensures a =~= b;
// }

// TODO(feature:extensional-equality): normalize type synonyms so
// `type IntMap := Map int int` also works with `=~=`.
// TODO(feature:extensional-equality): extend the same idea to other collection
// types such as sequences once we settle the intended semantics.
// TODO(feature:extensional-equality): review quantified triggers/solver
// behavior as more extensional cases are added.

procedure map_extensionality_seed(a: Map int int, b: Map int int) returns ()
spec {
  requires ∀ i: int . a[i] == b[i];
  ensures a =~= b;
}
{
  assert a =~= b;
};
#end

#guard_msgs (drop info) in
#eval Strata.Boole.verify "cvc5" mapExtensionalitySeed

example : Strata.smtVCsCorrect mapExtensionalitySeed := by
  gen_smt_vcs
  all_goals
    intro Map inst select a b hPointwise i
    exact hPointwise i

/-!
Regression test for extensional equality nested under an outer quantifier.

The Boole frontend lowers `a =~= b` to `∀ i . a[i] == b[i]`. When `a` and `b`
are themselves outer bound variables, introducing that extra quantifier must
lift their de Bruijn indices so they keep referring to the outer map binders
instead of the new index binder.
-/

private def quantifiedMapExtensionalityCaptureSeed : Strata.Program :=
#strata
program Boole;

procedure quantified_map_extensionality_capture() returns ()
spec {
  ensures ∀ a: Map int int, b: Map int int . a =~= b;
}
{
};
#end

private def mkExprApp (f : Core.Expression.Expr) (args : List Core.Expression.Expr) :
    Core.Expression.Expr :=
  Lambda.LExpr.mkApp Strata.SourceRange.none f args

private def loweredQuantifiedMapExtensionalityCapture? : Option Core.Expression.Expr := do
  let booleProg <- (Strata.Boole.getProgram quantifiedMapExtensionalityCaptureSeed).toOption
  let coreProg <-
    (Strata.Boole.toCoreProgram booleProg quantifiedMapExtensionalityCaptureSeed.globalContext).toOption
  coreProg.decls.findSome? fun decl =>
    match decl.getProc? with
    | some proc =>
        if proc.header.name == "quantified_map_extensionality_capture" then
          proc.spec.postconditions.values.head?.map (·.expr)
        else
          none
    | none => none

private def expectedQuantifiedMapExtensionalityCapture : Core.Expression.Expr :=
  let mapIntInt := Core.mapTy .int .int
  let lhs := mkExprApp Core.mapSelectOp [.bvar Strata.SourceRange.none 2, .bvar Strata.SourceRange.none 0]
  let rhs := mkExprApp Core.mapSelectOp [.bvar Strata.SourceRange.none 1, .bvar Strata.SourceRange.none 0]
  .quant Strata.SourceRange.none .all "" (some mapIntInt) (.bvar Strata.SourceRange.none 0)
    (.quant Strata.SourceRange.none .all "" (some mapIntInt) (.bvar Strata.SourceRange.none 0)
      (.quant Strata.SourceRange.none .all "" (some .int) lhs (.eq Strata.SourceRange.none lhs rhs)))

#guard loweredQuantifiedMapExtensionalityCapture? == some expectedQuantifiedMapExtensionalityCapture
