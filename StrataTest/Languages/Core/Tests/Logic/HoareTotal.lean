/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Core.Tests.Logic.HoareUtils
import Strata.Languages.Core.Logic.HoareTotal

open Imperative
open StrataDDM (Program)

namespace Strata.HoareTotalTest

open HoareUtils

/-- The program.  It comes first in the file: the translation records the byte offsets of its
    statements in their metadata, which the bodies below spell out with `loc`, so an edit above
    it moves them. -/
private def countPgm : Program :=
#strata
program Core;

procedure CountUp(out y : int)
spec {
  ensures y == 10;
}
{
  y := 0;
  while (int.le(y, 9)) {
    y := int.add(y, 1);
  }
};

procedure CountDown(n : int, out r : int)
spec {
  requires int.ge(n, 0);
  ensures r == 0;
}
{
  r := n;
  while (int.gt(r, 0)) {
    if (int.gt(r, 1)) {
      r := int.sub(r, 2);
    } else {
      r := int.sub(r, 1);
    }
  }
};
#end

def countPgmAST : Core.Program := cstToAST countPgm

/-! # Total correctness of two counting loops

`CountUp` counts `y` from `0` up to `10`; `CountDown` counts `r` from an input `n ≥ 0` down to
`0`, by two while `r > 1` and by one otherwise.  Both are proved to meet their contracts under
total correctness (`Procedure.contractTripleTotal`): the body terminates (it has no `assume`,
so termination with valid assertions is termination of every run), and every completed reachable run
ends in the postcondition.

Over partial correctness (see `loopTerm_meets_contract` in `Hoare.lean`) the proofs add:
- a measure that every iteration decreases, `10 - y` for `CountUp` and `r` for `CountDown`,
  read off the integer the variable holds (`intMeasure`);
- that every assignment can execute: its right-hand side evaluates to an integer, and the
  variable it writes holds an integer (`Core.valueOfStoredTy_int`); at entry, the output
  typing in the total contract's precondition gives that;
- that every loop guard and `if` condition evaluates to a Boolean
  (`Core.eval_tt_or_ff_of_ofBool`).

`CountDown` needs its precondition for the postcondition: from a negative `n` the loop does
not run and `r` ends negative.

The facts that bind the translated program to its spelled-out bodies (`up_body_eq`,
`down_body_eq`), the contract clauses (`up_post_expr`, `down_pre_expr`, `down_post_expr`),
the input and output typings, and the procedure lookup and `contractChecksTyped` premises use
`native_decide`: the translation is `partial`, so the kernel cannot reduce it.

The section `Assume` shows that an `assume` may feed a total postcondition:
`assume false` establishes `False` (`assume_false_total`), and `havoc r; assume r > 0`
establishes `r > 0` (`havoc_assume_pos_total`).  It also shows that a reachable failing
assertion is caught although no run finishes (`reachable_failing_assert_not_total`).
-/

private abbrev π : String → Option Core.Procedure := countPgmAST.findProcByString?

def yId : Core.Expression.Ident := ⟨"y", ()⟩
private def nId : Core.Expression.Ident := ⟨"n", ()⟩
private def rId : Core.Expression.Ident := ⟨"r", ()⟩

/-- The binary integer operation `op` applied to the variable `x` and the literal `k`. -/
abbrev opE (op : Core.Expression.Expr) (x : Core.Expression.Ident) (k : Int) :
    Core.Expression.Expr :=
  .app Core.valueLoc (.app Core.valueLoc op (v x)) (.intConst Core.valueLoc k)

/-- An expression evaluating both to the Boolean `decide p` and to `b` has `decide p = b`. -/
private theorem decide_of_eval {ρ : Env Core.Expression} {e : Core.Expression.Expr} {p : Prop}
    [Decidable p] (he : Core.Expression.eval ρ.factory ρ.store e =
      some (Lambda.SemValue.ofBool ρ.factory.model.tcInterp (decide p))) (b : Bool)
    (hb : Core.Expression.eval ρ.factory ρ.store e =
      some (Lambda.SemValue.ofBool ρ.factory.model.tcInterp b)) : decide p = b :=
  Lambda.SemValue.ofBool_injective (Option.some.inj (he.symm.trans hb))

/-! ## `CountUp` -/

/-- The body of the loop of `CountUp`. -/
abbrev upLoopBody : Core.Statements :=
  [Core.Statement.set yId (opE Core.intAddOp yId 1) (loc 649 668)]

/-- The loop of `CountUp`. -/
abbrev upLoop : Core.Statement :=
  .loop (.det (opE Core.intLeOp yId 9)) none [] upLoopBody (loc 622 672)

/-- The translated body of `CountUp`. -/
abbrev upBody : Core.Statements :=
  [Core.Statement.set yId (.intConst Core.valueLoc 0) (loc 612 619)] ++ [upLoop]

/-- The translated body of `CountUp` is `upBody`: `y := 0` followed by the loop that adds
    `1` to `y` while `y <= 9`. -/
theorem up_body_eq : (procOf countPgmAST "CountUp").body = .structured upBody false := by
  native_decide

/-- Every postcondition clause of `CountUp` is `y == 10`. -/
theorem up_post_expr : ∀ lc ∈ (procOf countPgmAST "CountUp").spec.postconditions.toList,
    lc.2.expr = eqInt yId 10 := by
  native_decide

/-- The invariant of `CountUp`'s loop: `y` holds an integer between `0` and `10`. -/
private abbrev UpInv (ρ : Env Core.Expression) : Prop :=
  Pinned ρ ∧ ∃ k, ρ.store yId = some (intOf ρ.factory k) ∧ 0 ≤ k ∧ k ≤ 10

/-- With `y` holding `k`, the guard `int.le(y, 9)` evaluates to `k ≤ 9`. -/
private theorem up_guard_eval {ρ : Env Core.Expression} (hp : Pinned ρ) {k : Int}
    (hy : ρ.store yId = some (intOf ρ.factory k)) :
    Core.Expression.eval ρ.factory ρ.store (opE Core.intLeOp yId 9) =
      some (Lambda.SemValue.ofBool ρ.factory.model.tcInterp (decide (k ≤ 9))) :=
  Core.eval_intLe (hp ▸ Core.coreFactory_intLe) (Core.eval_fvar_int _ hy) (Core.eval_intConst _ _ 9)

/-- One iteration takes `y` from `k ≤ 9` to `k + 1`, decreasing `10 - y`. -/
private theorem up_iteration (m : Nat) :
    Core.Logic.HoareTotal.Triple π testParams
      (fun ρ => (UpInv ρ ∧ Core.Expression.eval ρ.factory ρ.store (opE Core.intLeOp yId 9) =
        some (HasBool.ttVal ρ.factory)) ∧ intMeasure yId (fun k => (10 - k).toNat) ρ = m)
      upLoopBody
      (fun ρ => UpInv ρ ∧ intMeasure yId (fun k => (10 - k).toNat) ρ < m) := by
  refine Core.Logic.HoareTotal.set π testParams yId _ _ _ _
    (fun ρ₀ ⟨⟨⟨hp, k, hy, _⟩, _⟩, _⟩ _ =>
      ⟨_, Core.eval_intAdd (hp ▸ Core.coreFactory_intAdd) (Core.eval_fvar_int _ hy)
        (Core.eval_intConst _ _ 1), Core.valueOfStoredTy_int hy (k + 1)⟩)
    (fun ρ₀ σ' w ⟨⟨⟨hp, k, hy, hlo, _⟩, hg⟩, hm⟩ hev hup => ?_)
  have hle := of_decide_eq_true (decide_of_eval (up_guard_eval hp hy) true hg)
  have hw := Option.some.inj (hev.symm.trans (Core.eval_intAdd (hp ▸ Core.coreFactory_intAdd)
    (Core.eval_fvar_int _ hy) (Core.eval_intConst _ _ 1)))
  subst hw
  cases hup with
  | update _ hnew _ =>
    refine ⟨⟨hp, k + 1, hnew, by omega, by omega⟩, ?_⟩
    rw [intMeasure_eq hnew, ← hm, intMeasure_eq hy]
    omega

/-- **`CountUp` meets its contract under total correctness**: its body terminates and ends
    with `y == 10`. -/
theorem countUp_meets_contract_total :
    Core.Logic.Hoare.Procedure.contractTripleTotal countPgmAST testParams "CountUp" := by
  refine Core.Logic.Hoare.Procedure.contractTripleTotal_of_core_typed
      (hmono := by native_decide) _ _ _ _ _
    (by native_decide) up_body_eq (by native_decide) ?_
  rw [Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)]
  refine Core.Logic.HoareTotal.block π testParams ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide))
  refine Core.Logic.HoareTotal.of_storeWF_pre π testParams ?_
  refine Core.Logic.HoareTotal.seq π testParams (Mid := UpInv) ?_ ?_ (by covered)
  · -- `y := 0` can execute, since the output `y` holds an integer at entry.
    refine Core.Logic.HoareTotal.set π testParams yId _ _ _ _
      (fun ρ₀ ⟨⟨_, _, _, _, hout⟩, hwf⟩ _ => ?_) (fun ρ₀ σ' w ⟨hpre, _⟩ hev hup => ?_)
    · obtain ⟨k, hk⟩ := Core.Logic.Hoare.Procedure.outputAsPredicate_int hwf hout yId
        (by native_decide)
      exact ⟨_, Core.eval_intConst _ _ 0, Core.valueOfStoredTy_int hk 0⟩
    · have hw := Option.some.inj (hev.symm.trans (Core.eval_intConst _ _ 0))
      subst hw
      cases hup with
      | update _ hnew _ => exact ⟨hpre.2.1, 0, hnew, by decide, by decide⟩
  · -- The loop terminates with `y = 10`.
    refine Core.Logic.HoareTotal.consequence π testParams
      (Core.Logic.HoareTotal.while_rule π testParams (intMeasure yId fun k => (10 - k).toNat)
        (fun ρ ⟨hp, k, hy, _⟩ _ => Core.eval_tt_or_ff_of_ofBool (up_guard_eval hp hy))
        up_iteration (by covered)
        (fun _ => Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide)))
      (fun _ h => h) (fun ρ ⟨⟨hp, k, hy, _, hhi⟩, hg⟩ => ?_)
    have hgt := of_decide_eq_false (decide_of_eval (up_guard_eval hp hy) false hg)
    obtain rfl : k = 10 := by omega
    exact post_eqInt up_post_expr hp hy

/-! ## `CountDown` -/

/-- The `if` in the body of the loop of `CountDown`. -/
private abbrev downIte : Core.Statement :=
  .ite (.det (opE Core.intGtOp rId 1))
    [Core.Statement.set rId (opE Core.intSubOp rId 2) (loc 838 857)]
    [Core.Statement.set rId (opE Core.intSubOp rId 1) (loc 877 896)] (loc 812 902)

/-- The loop of `CountDown`. -/
private abbrev downLoop : Core.Statement :=
  .loop (.det (opE Core.intGtOp rId 0)) none [] [downIte] (loc 785 906)

/-- The translated body of `CountDown`. -/
private abbrev downBody : Core.Statements :=
  [Core.Statement.set rId (v nId) (loc 775 782)] ++ [downLoop]

/-- The translated body of `CountDown` is `downBody`: `r := n` followed by the loop that
    decreases `r` while `r > 0`. -/
private theorem down_body_eq : (procOf countPgmAST "CountDown").body = .structured downBody false :=
    by
  native_decide

/-- Every precondition clause of `CountDown` is `int.ge(n, 0)`. -/
private theorem down_pre_expr :
    ∀ lc ∈ (procOf countPgmAST "CountDown").spec.preconditions.toList, lc.2.expr = ge0 nId := by
  native_decide

/-- Every postcondition clause of `CountDown` is `r == 0`. -/
private theorem down_post_expr :
    ∀ lc ∈ (procOf countPgmAST "CountDown").spec.postconditions.toList,
      lc.2.expr = eqInt rId 0 := by
  native_decide

/-- The invariant of `CountDown`'s loop: `r` holds a non-negative integer. -/
private abbrev DownInv (ρ : Env Core.Expression) : Prop :=
  Pinned ρ ∧ ∃ k, ρ.store rId = some (intOf ρ.factory k) ∧ 0 ≤ k

/-- With `r` holding `k`, `int.gt(r, j)` evaluates to `k > j`. -/
private theorem down_gt_eval {ρ : Env Core.Expression} (hp : Pinned ρ) {k : Int}
    (hr : ρ.store rId = some (intOf ρ.factory k)) (j : Int) :
    Core.Expression.eval ρ.factory ρ.store (opE Core.intGtOp rId j) =
      some (Lambda.SemValue.ofBool ρ.factory.model.tcInterp (decide (k > j))) :=
  Core.eval_intGt (hp ▸ Core.coreFactory_intGt) (Core.eval_fvar_int _ hr) (Core.eval_intConst _ _ j)

/-- With `r` holding `k`, `int.sub(r, j)` evaluates to `k - j`. -/
private theorem down_sub_eval {ρ : Env Core.Expression} (hp : Pinned ρ) {k : Int}
    (hr : ρ.store rId = some (intOf ρ.factory k)) (j : Int) :
    Core.Expression.eval ρ.factory ρ.store (opE Core.intSubOp rId j) =
      some (intOf ρ.factory (k - j)) :=
  Core.eval_intSub (hp ▸ Core.coreFactory_intSub) (Core.eval_fvar_int _ hr)
    (Core.eval_intConst _ _ j)

/-- `r := int.sub(r, j)`, from `r` holding `k` with `0 ≤ k - j < k`, keeps the invariant and
    decreases the measure `r` below `m` when it was `m`. -/
private theorem down_step (j : Int) (md : MetaData Core.Expression) (m : Nat)
    (Pre : Env Core.Expression → Prop)
    (hpre : ∀ ρ, Pre ρ → ∃ k, Pinned ρ ∧ ρ.store rId = some (intOf ρ.factory k) ∧
      0 ≤ k - j ∧ k - j < k ∧ intMeasure rId Int.toNat ρ = m) :
    Core.Logic.HoareTotal.Triple π testParams Pre
      [Core.Statement.set rId (opE Core.intSubOp rId j) md]
      (fun ρ => DownInv ρ ∧ intMeasure rId Int.toNat ρ < m) := by
  refine Core.Logic.HoareTotal.set π testParams rId _ _ _ _ (fun ρ₀ h _ => ?_)
    (fun ρ₀ σ' w h hev hup => ?_)
  · obtain ⟨k, hp, hr, -⟩ := hpre ρ₀ h
    exact ⟨_, down_sub_eval hp hr j, Core.valueOfStoredTy_int hr (k - j)⟩
  · obtain ⟨k, hp, hr, hlo, hlt, hm⟩ := hpre ρ₀ h
    have hw := Option.some.inj (hev.symm.trans (down_sub_eval hp hr j))
    subst hw
    cases hup with
    | update _ hnew _ =>
      refine ⟨⟨hp, k - j, hnew, hlo⟩, ?_⟩
      rw [intMeasure_eq hnew, ← hm, intMeasure_eq hr]
      omega

/-- One iteration takes `r` from `k > 0` down by two if `k > 1` and by one otherwise. -/
private theorem down_iteration (m : Nat) :
    Core.Logic.HoareTotal.Triple π testParams
      (fun ρ => (DownInv ρ ∧ Core.Expression.eval ρ.factory ρ.store (opE Core.intGtOp rId 0) =
        some (HasBool.ttVal ρ.factory)) ∧ intMeasure rId Int.toNat ρ = m)
      [downIte]
      (fun ρ => DownInv ρ ∧ intMeasure rId Int.toNat ρ < m) := by
  refine Core.Logic.HoareTotal.ite π testParams
    (fun ρ ⟨⟨⟨hp, k, hr, _⟩, _⟩, _⟩ _ => Core.eval_tt_or_ff_of_ofBool (down_gt_eval hp hr 1))
    (down_step 2 _ m _ fun ρ ⟨⟨⟨⟨hp, k, hr, _⟩, _⟩, hm⟩, hc⟩ => ⟨k, hp, hr, ?_⟩)
    (down_step 1 _ m _ fun ρ ⟨⟨⟨⟨hp, k, hr, _⟩, hg⟩, hm⟩, hc⟩ => ⟨k, hp, hr, ?_⟩)
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide))
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide))
  · have h1 := of_decide_eq_true (decide_of_eval (down_gt_eval hp hr 1) true hc)
    exact ⟨by omega, by omega, hm⟩
  · have h0 := of_decide_eq_true (decide_of_eval (down_gt_eval hp hr 0) true hg)
    have h1 := of_decide_eq_false (decide_of_eval (down_gt_eval hp hr 1) false hc)
    exact ⟨by omega, by omega, hm⟩

/-- **`CountDown` meets its contract under total correctness**: from `n ≥ 0` its body
    terminates and ends with `r == 0`. -/
theorem countDown_meets_contract_total :
    Core.Logic.Hoare.Procedure.contractTripleTotal countPgmAST testParams "CountDown" := by
  refine Core.Logic.Hoare.Procedure.contractTripleTotal_of_core_typed
      (hmono := by native_decide) _ _ _ _ _
    (by native_decide) down_body_eq (by native_decide) ?_
  rw [Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)]
  refine Core.Logic.HoareTotal.block π testParams ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide))
  refine Core.Logic.HoareTotal.of_storeWF_pre π testParams ?_
  refine Core.Logic.HoareTotal.seq π testParams (Mid := DownInv) ?_ ?_ (by covered)
  · -- `r := n` can execute: `n ≥ 0` is an integer and the output `r` holds one at entry.
    refine Core.Logic.HoareTotal.set π testParams rId _ _ _ _
      (fun ρ₀ ⟨hpre, hwf⟩ _ => ?_) (fun ρ₀ σ' w ⟨hpre, hwf⟩ hev hup => ?_)
    · obtain ⟨k, hn, _⟩ := nonneg_of_pre hpre hwf (by native_decide) down_pre_expr
        (by native_decide)
      obtain ⟨j, hr⟩ := Core.Logic.Hoare.Procedure.outputAsPredicate_int hwf hpre.2.2.2.2 rId
        (by native_decide)
      exact ⟨_, Core.eval_fvar_int _ hn, Core.valueOfStoredTy_int hr k⟩
    · obtain ⟨k, hn, hk⟩ := nonneg_of_pre hpre hwf (by native_decide) down_pre_expr
        (by native_decide)
      have hw := Option.some.inj (hev.symm.trans (Core.eval_fvar_int _ hn))
      subst hw
      cases hup with
      | update _ hnew _ => exact ⟨hpre.2.1, k, hnew, hk⟩
  · -- The loop terminates with `r = 0`.
    refine Core.Logic.HoareTotal.consequence π testParams
      (Core.Logic.HoareTotal.while_rule π testParams (intMeasure rId Int.toNat)
        (fun ρ ⟨hp, k, hr, _⟩ _ => Core.eval_tt_or_ff_of_ofBool (down_gt_eval hp hr 0))
        down_iteration (by covered)
        (fun _ => Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide)))
      (fun _ h => h) (fun ρ ⟨⟨hp, k, hr, hk⟩, hg⟩ => ?_)
    have h0 := of_decide_eq_false (decide_of_eval (down_gt_eval hp hr 0) false hg)
    obtain rfl : k = 0 := by omega
    exact post_eqInt down_post_expr hp hr

/-! ## Assumptions under total correctness

The total triple owes its postcondition only on reachable runs, as the partial one does, so an
`assume` may feed the postcondition, and a run an `assume` makes unreachable need not
terminate. -/

section Assume

variable (π : String → Option Core.Procedure) (md : MetaData Core.Expression)

/-- The literal `false`. -/
private abbrev falseE : Core.Expression.Expr := .boolConst Core.valueLoc false

/-- **`assume false` establishes `False` under total correctness**, from entries whose
    runtime factory is over `Core.Factory`: the assumption executes, and no run past it is
    reachable. -/
theorem assume_false_total :
    Core.Logic.HoareTotal.Triple π testParams Pinned [Core.Statement.assume "a" falseE md]
      (fun _ => False) :=
  Core.Logic.HoareTotal.assume_eval π testParams "a" falseE md _ _ (fun _ h => h)
    fun ρ₀ _ htt => HasBool.ttVal_ne_ffVal _ (Option.some.inj
      (htt.symm.trans (Core.eval_boolConst ρ₀.factory ρ₀.store false)))

/-- The runtime factory is over `Core.Factory` and `r` holds an integer of it. -/
private abbrev RInt (ρ : Env Core.Expression) : Prop :=
  Pinned ρ ∧ ∃ k, ρ.store rId = some (intOf ρ.factory k)

/-- **`havoc r; assume r > 0` establishes `r > 0` under total correctness**, from entries
    where `r` holds an integer: the havoc gives `r` some integer, and the assumption, which
    the postcondition may use, makes it positive. -/
theorem havoc_assume_pos_total :
    Core.Logic.HoareTotal.Triple π testParams RInt
      ([Core.Statement.havoc rId md] ++ [Core.Statement.assume "a" (opE Core.intGtOp rId 0) md])
      (fun ρ => Pinned ρ ∧ ∃ k, ρ.store rId = some (intOf ρ.factory k) ∧ 0 < k) := by
  refine Core.Logic.HoareTotal.seq π testParams (Mid := RInt) ?_ ?_ (by covered)
  · refine Core.Logic.HoareTotal.havoc π testParams rId md _ _
      (fun _ ⟨_, k, hk⟩ _ => ⟨_, Core.valueOfStoredTy_int hk 0⟩)
      (fun ρ₀ σ' v ⟨hp, k, hk⟩ hupd hty => ?_)
    obtain ⟨old, ty, hold, holdt, hvtc, hvmono⟩ := hty
    rw [hk] at hold
    cases hold
    obtain rfl := Core.valueOfTy_unique holdt
      (⟨rfl, rfl⟩ : HasVal.valueOfTy ρ₀.factory (intOf ρ₀.factory k) intLTy)
    simp only [Lambda.LTy.toMonoType?, Option.some.injEq] at hvmono
    obtain ⟨j, hj⟩ := Lambda.SemValue.exists_ofInt hvmono.symm
    cases hupd with
    | update _ hnew _ => exact ⟨hp, j, by show σ' rId = _; rw [hnew, hj, hvtc]⟩
  · exact Core.Logic.HoareTotal.assume_eval π testParams "a" _ md _ _ (fun _ h => h.1)
      fun _ ⟨hp, k, hk⟩ htt =>
        ⟨hp, k, hk, of_decide_eq_true (decide_of_eval (down_gt_eval hp hk 0) true htt)⟩

/-- `assume r > 0; assert false; assume r < 0; while (true) {}`: no run finishes, and every
    divergent run passes an assumption that fails. -/
private abbrev gapBody : Core.Statements :=
  [Core.Statement.assume "a1" (opE Core.intGtOp rId 0) md,
   Core.Statement.assert "a2" falseE md,
   Core.Statement.assume "a3" (opE Core.intLtOp rId 0) md,
   .loop (.det (.boolConst Core.valueLoc true)) none [] [] md]

/-- **A reachable failing assertion is caught even when no run finishes.**  From an admitted
    entry where `r` holds `1`, `gapBody md` meets no total triple: its run reaches
    `assert false` after the assumption `r > 0`, which holds, although the run later passes the
    failing `assume r < 0` and diverges. -/
theorem reachable_failing_assert_not_total (ρ : Env Core.Expression) (hp : Pinned ρ)
    (hr : ρ.store rId = some (intOf ρ.factory 1))
    (hwf : Core.Logic.BlockInitEnvWF testParams (gapBody md) ρ) :
    ¬ Core.Logic.HoareTotal.Triple π testParams (fun ρ' => ρ' = ρ) (gapBody md)
      (fun _ => True) := by
  intro h
  have hterm := (h ρ rfl hwf).1 (someValuation _)
  have hrun : StepStmtStarE Core.Expression (Core.EvalCommandE π) (.stmts (gapBody md) ρ) _
      (.stmts (gapBody md).tail.tail ρ) :=
    .step _ _ _ _ _ .step_stmts_cons
      (.step _ _ _ _ _ (.step_seq_inner (.step_cmd (.cmd_sem .eval_assume)))
        (.step _ _ _ _ _ .step_seq_done
          (.step _ _ _ _ _ .step_stmts_cons
            (.step _ _ _ _ _ (.step_seq_inner (.step_cmd (.cmd_sem .eval_assert)))
              (.step _ _ _ _ _ .step_seq_done (.refl _))))))
  have hassert := hterm.assertionsHoldIn hrun
  simp only [List.nil_append, List.append_nil, List.cons_append, Trace.AssertionsHoldIn]
    at hassert
  have hpos : Core.Expression.eval ρ.factory ρ.store (opE Core.intGtOp rId 0) =
      some (HasBool.ttVal ρ.factory) := by
    rw [down_gt_eval hp hr 0]
    rfl
  rcases (hassert (Or.inl ⟨hp, hpos⟩)).1 with ⟨_, hex⟩ | ⟨hne, _⟩
  · exact HasBool.ttVal_ne_ffVal _ (Option.some.inj
      (hex.symm.trans (Core.eval_boolConst ρ.factory ρ.store false)))
  · exact hne hp

end Assume

end Strata.HoareTotalTest
