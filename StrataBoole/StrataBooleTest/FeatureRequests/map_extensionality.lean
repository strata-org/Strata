/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier
import StrataBoole.Verify
-- Test fixtures build Core expressions directly with synthesized provenance

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

private def mapExtensionalitySeed : StrataDDM.Program :=
#strata
program Boole;

// `a =~= b` lowers to `∀ i: int . a[i] == b[i]`.
// Remaining gap: named map type synonyms do not yet work with `=~=`.

procedure map_extensionality_seed(a: Map int int, b: Map int int) returns ()
spec {
  requires ∀ i: int . a[i] == b[i];
  ensures a =~= b;
}
{
  assert a =~= b;
};
#end

/-- info:
Obligation: assert_2_1060
Property: assert
Result: ✅ pass

Obligation: map_extensionality_seed_ensures_1_1037
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" mapExtensionalitySeed (options := .quiet)

/--
The VCs are provable regardless of `useArrayTheory`: under `true` the `Map` is
encoded as an SMT array (denoted by `SmtArray`), under `false` as an
uninterpreted sort with an axiomatized `select` function.
-/
example : ∀ useArrayTheory,
    Strata.smtVCsCorrectBoole mapExtensionalitySeed { useArrayTheory } := by
  intro useArrayTheory
  cases useArrayTheory
  case false =>
    gen_smt_vcs_boole
    all_goals
      intro Map inst select a b hPointwise i
      exact hPointwise i
  case true =>
    gen_smt_vcs_boole
    all_goals
      intro a b hPointwise i
      exact hPointwise i

/-!
Regression test for extensional equality nested under an outer quantifier.

The Boole frontend lowers `a =~= b` to `∀ i . a[i] == b[i]`. When `a` and `b`
are themselves outer bound variables, introducing that extra quantifier must
lift their de Bruijn indices so they keep referring to the outer map binders
instead of the new index binder.
-/

private def quantifiedMapExtensionalityCaptureSeed : StrataDDM.Program :=
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
  Lambda.LExpr.mkApp (ExprSourceLoc.synthesized "test") f args

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
  let lhs := mkExprApp Core.mapSelectOp [.bvar (ExprSourceLoc.synthesized "test") 2, .bvar (ExprSourceLoc.synthesized "test") 0]
  let rhs := mkExprApp Core.mapSelectOp [.bvar (ExprSourceLoc.synthesized "test") 1, .bvar (ExprSourceLoc.synthesized "test") 0]
  .quant (ExprSourceLoc.synthesized "test") .all "" (some mapIntInt) (.bvar (ExprSourceLoc.synthesized "test") 0)
    (.quant (ExprSourceLoc.synthesized "test") .all "" (some mapIntInt) (.bvar (ExprSourceLoc.synthesized "test") 0)
      (.quant (ExprSourceLoc.synthesized "test") .all "" (some .int) lhs (.eq (ExprSourceLoc.synthesized "test") lhs rhs)))

#guard (loweredQuantifiedMapExtensionalityCapture?.map (·.eraseMetadata)) == some expectedQuantifiedMapExtensionalityCapture.eraseMetadata
