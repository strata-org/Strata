/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Core.Tests.Logic.HoareAfterSupport
import Strata.Transform.LoopInitHoistCoreCorrect

open Imperative
open StrataDDM (Program)

namespace Strata.HoareAfterLoopInitHoistTest

open HoareAfterSupport

/-- The program.  It comes first in the file: the translation records the byte offsets of its
    statements in their metadata, which `sumBody` spells out with `loc`, so an edit above it
    moves them. -/
private def sumPgm : Program :=
#strata
program Core;

procedure SumSquares(n : int, out s : int)
spec {
  ensures int.ge(s, 0);
}
{
  s := 0;
  var i : int := 0;
  while (int.lt(i, n)) {
    var sq : int := int.mul(i, i);
    s := int.add(s, sq);
    i := int.add(i, 1);
  }
};
#end

private def sumPgmAST : Core.Program := cstToAST sumPgm

private abbrev π : String → Option Core.Procedure := sumPgmAST.findProcByString?

/-! # A contract proved after hoisting a loop-body declaration

```
procedure SumSquares(n : int, out s : int)
spec { ensures int.ge(s, 0); }
{
  s := 0;
  var i : int := 0;
  while (int.lt(i, n)) {
    var sq : int := int.mul(i, i);
    s := int.add(s, sq);
    i := int.add(i, 1);
  }
}
```

Each iteration declares `sq` afresh in the loop body's scope.  The Core pass
`Core.LoopInitHoist.loopInitHoist` declares it once before the loop and assigns it in the body:

```
s := 0;
var i : int := 0;
var sq : int;
while (int.lt(i, n)) { sq := int.mul(i, i); s := int.add(s, sq); i := int.add(i, 1); }
```

The while rule with the invariant `s ≥ 0 ∧ i ≥ 0` proves the contract of this body.
`Core.LoopInitHoist.triple` carries the triple back to the original body.  The final
environments of the two bodies agree only on the bindings of the original's
(`EnvStoreAgree`): the hoisted `sq` stays defined after the loop, even when the loop runs no
iteration.  The postcondition reads `s`, which the original body writes without declaring,
so the gate has it defined at entry and every run keeps it defined; the factory is the
entry's in both runs.

The translated body is spelled out as the closed term `sumBody`; the facts about the pass's
output on it, and about its variables, are decided by the kernel (`decide +kernel`).  The facts
that bind the translated program to it (`sum_body_eq`, `sum_decl`, `sum_out`'s run,
`sum_post_expr`, and the procedure lookup and `contractChecksTyped` premises of
`sum_meets_contract`) use `native_decide`: the translation is `partial`, so the kernel cannot
reduce it.
-/

private def sumProc : Core.Procedure := (π "SumSquares").get!

private def nId : Core.Expression.Ident := ⟨"n", ()⟩
private def sId : Core.Expression.Ident := ⟨"s", ()⟩
private def iId : Core.Expression.Ident := ⟨"i", ()⟩
private def sqId : Core.Expression.Ident := ⟨"sq", ()⟩

/-- The guard `int.lt(i, n)`. -/
private abbrev ltE : Core.Expression.Expr := .app Core.valueLoc (.app Core.valueLoc Core.intLtOp (v iId)) (v nId)
/-- `int.mul(i, i)`. -/
private abbrev mulE : Core.Expression.Expr := .app Core.valueLoc (.app Core.valueLoc Core.intMulOp (v iId)) (v iId)
/-- `int.add(s, sq)`. -/
private abbrev addE : Core.Expression.Expr := .app Core.valueLoc (.app Core.valueLoc Core.intAddOp (v sId)) (v sqId)
/-- `int.add(i, 1)`. -/
private abbrev incE : Core.Expression.Expr :=
  .app Core.valueLoc (.app Core.valueLoc Core.intAddOp (v iId)) (.intConst Core.valueLoc 1)

/-- The metadata of the declaration of `sq` and of the loop. -/
private abbrev mdSq : MetaData Core.Expression := loc 708 738
private abbrev mdL : MetaData Core.Expression := loc 681 791

/-- The statements after the loop's declaration of `sq`. -/
private abbrev bodyTail : Core.Statements :=
  [Core.Statement.set sId addE (loc 743 763), Core.Statement.set iId incE (loc 768 787)]

/-- `s := 0`. -/
private abbrev setS0 : Core.Statement := Core.Statement.set sId (.intConst Core.valueLoc 0) (loc 651 658)

/-- `var i : int := 0`. -/
private abbrev initI : Core.Statement :=
  Core.Statement.init iId intLTy (.det (.intConst Core.valueLoc 0)) (loc 661 678)

/-- The translated body. -/
private abbrev sumBody : Core.Statements :=
  [setS0] ++ ([initI] ++ [.loop (.det ltE) none []
    (Core.Statement.init sqId intLTy (.det mulE) mdSq :: bodyTail) mdL])

/-- The translated body really is the prelude followed by the loop. -/
private theorem sum_body_eq : sumProc.body = .structured sumBody := by native_decide

/-! ## The hoisted body -/

/-- The body of the hoisted loop. -/
private abbrev tgtLoopBody : Core.Statements :=
  [Core.Statement.set sqId mulE mdSq] ++ bodyTail

/-- The hoisted body. -/
private abbrev sumTgt : Core.Statements :=
  [setS0] ++ ([initI] ++ ([Core.Statement.init sqId intLTy .nondet mdSq] ++
    [.loop (.det ltE) none [] tgtLoopBody mdL]))

/-- Hoisting turns the body into `sumTgt`. -/
private theorem sum_hoist : Core.hoistLoopPrefixInits sumBody = some sumTgt := by
  decide +kernel

/-- The metadata of the declaration of the procedure. -/
private def sumDeclMd : MetaData Core.Expression :=
  match sumPgmAST.decls[0]? with
  | some (Core.Decl.proc _ md) => md
  | _ => default

/-- The procedure is the first declaration of the program. -/
private theorem sum_decl : sumPgmAST.decls[0]? = some (.proc sumProc sumDeclMd) := by
  native_decide

/-- A run of the Core pass on the program. -/
private def sumRun :=
  Core.LoopInitHoist.loopInitHoist sumPgmAST Core.Transform.CoreTransformState.emp

/-- The program the run returns. -/
private def sumOut : Core.Program := match sumRun.1 with
  | .ok r => r.2
  | .error _ => default

/-- **The Core pass hoists the declaration.**  The run of `Core.LoopInitHoist.loopInitHoist`
    on the program succeeds, and the program it returns has the procedure with the body
    `sumTgt`. -/
theorem sum_out : (∃ c σ', sumRun = (.ok (c, sumOut), σ')) ∧
    Core.Decl.proc { sumProc with body := .structured sumTgt } sumDeclMd ∈ sumOut.decls := by
  have h : (match sumRun.1 with | .ok _ => true | .error _ => false) = true := by
    native_decide
  have hrun : ∃ c σ', sumRun = (.ok (c, sumOut), σ') := by
    unfold sumOut
    revert h
    generalize sumRun = r
    obtain ⟨_ | ⟨c, q⟩, σ'⟩ := r
    · intro h; cases h
    · intro _; exact ⟨c, σ', rfl⟩
  refine ⟨hrun, ?_⟩
  obtain ⟨c, σ', hr⟩ := hrun
  obtain ⟨_, hss, hmem, _⟩ := Core.LoopInitHoist.loopInitHoistPipelinePhase_over.{0} (π := π)
    (s := Core.Transform.CoreTransformState.emp) (s' := σ') (changed := c)
    (by rw [Core.LoopInitHoist.loopInitHoistPipelinePhase_ok]; exact hr)
    (show Core.Program.allStatements Core.Statements.noCalls sumPgmAST = true by native_decide)
    (show Core.Program.allStatements (fun ss =>
      (Imperative.Block.initVars (C := Core.Command) ss).eraseDups ==
        Imperative.Block.initVars (C := Core.Command) ss) sumPgmAST = true by native_decide)
    (List.mem_of_getElem? sum_decl) sum_body_eq
  rw [sum_hoist] at hss
  cases hss
  exact hmem

/-- The postcondition is `int.ge(s, 0)`. -/
private theorem sum_post_expr :
    ∀ lc ∈ sumProc.spec.postconditions.toList, lc.2.expr = ge0 sId :=
  List.forall_of_all_decide (by native_decide)

/-! ## The triple of the hoisted body

The triple is proved for each entry factory `E` over `Core.Factory`: the store facts read
integers of `E`'s model, and the final environments of the two bodies, which have the same
store values, have that factory. -/

section Body

variable (E : Core.Expression.Factory)

/-- `x` holds the integer `k` of `E`. -/
private abbrev Holds (x : Core.Expression.Ident) (k : Int) (ρ : Env Core.Expression) : Prop :=
  ρ.store x = some (intOf E k)

/-- The factory is `E`. -/
private abbrev At (ρ : Env Core.Expression) : Prop := ρ.factory = E

/-- The loop invariant: `s` and `i` hold non-negative integers. -/
private abbrev Inv (ρ : Env Core.Expression) : Prop :=
  At E ρ ∧ ∃ a b, Holds E sId a ρ ∧ Holds E iId b ρ ∧ 0 ≤ a ∧ 0 ≤ b

/-- After `sq := int.mul(i, i)`. -/
private abbrev Squared (ρ : Env Core.Expression) : Prop :=
  At E ρ ∧ ∃ a b, Holds E sId a ρ ∧ Holds E iId b ρ ∧ Holds E sqId (b * b) ρ ∧ 0 ≤ a ∧ 0 ≤ b

/-- The postcondition's store fact: `s` holds a non-negative integer. -/
private abbrev Done (ρ : Env Core.Expression) : Prop :=
  At E ρ ∧ ∃ a, Holds E sId a ρ ∧ 0 ≤ a

/-- `s` is not `i`. -/
private theorem s_ne_i : sId ≠ iId := by decide
/-- `s` is not `sq`. -/
private theorem s_ne_sq : sId ≠ sqId := by decide
/-- `i` is not `sq`. -/
private theorem i_ne_sq : iId ≠ sqId := by decide

variable {E} (hE : E.factory = Core.Factory)
include hE

/-- An iteration of the hoisted loop keeps `Inv`. -/
private theorem loopBody_triple :
    Core.Logic.Hoare.Triple π testParams
      (fun ρ => Inv E ρ ∧ Core.Expression.eval ρ.factory ρ.store ltE =
        some (HasBool.ttVal ρ.factory)) tgtLoopBody (Inv E) := by
  change Core.Logic.Hoare.Triple π testParams _ ([Core.Statement.set sqId mulE mdSq] ++
    ([Core.Statement.set sId addE (loc 743 763)] ++
      [Core.Statement.set iId incE (loc 768 787)])) (Inv E)
  refine Core.Logic.Hoare.seq π testParams (Mid := Squared E) ?_ ?_ (by covered)
  · refine Core.Logic.Hoare.set π testParams _ _ _ _ _
      (fun ρ₀ σ' v ⟨⟨hf, a, b, hs, hi, ha, hb⟩, _⟩ hev hup => ?_)
    rw [hf, Core.eval_intMul (hE ▸ Core.coreFactory_intMul) (Core.eval_fvar_int E hi)
      (Core.eval_fvar_int E hi)] at hev
    cases hev
    cases hup with
    | update _ hnew hoth =>
      exact ⟨hf, a, b, (hoth _ s_ne_sq.symm).trans hs, (hoth _ i_ne_sq.symm).trans hi, hnew, ha,
        hb⟩
  refine Core.Logic.Hoare.seq π testParams (Mid := Inv E) ?_ ?_ (by covered)
  · refine Core.Logic.Hoare.set π testParams _ _ _ _ _
      (fun ρ₀ σ' v ⟨hf, a, b, hs, hi, hsq, ha, hb⟩ hev hup => ?_)
    rw [hf, Core.eval_intAdd (hE ▸ Core.coreFactory_intAdd) (Core.eval_fvar_int E hs)
      (Core.eval_fvar_int E hsq)] at hev
    cases hev
    cases hup with
    | update _ hnew hoth =>
      exact ⟨hf, a + b * b, b, hnew, (hoth _ s_ne_i).trans hi,
        Int.add_nonneg ha (Int.mul_nonneg hb hb), hb⟩
  · refine Core.Logic.Hoare.set π testParams _ _ _ _ _
      (fun ρ₀ σ' v ⟨hf, a, b, hs, hi, ha, hb⟩ hev hup => ?_)
    rw [hf, Core.eval_intAdd (hE ▸ Core.coreFactory_intAdd) (Core.eval_fvar_int E hi)
      (Core.eval_intConst E ρ₀.store 1)] at hev
    cases hev
    cases hup with
    | update _ hnew hoth =>
      exact ⟨hf, a, b + 1, (hoth _ s_ne_i.symm).trans hs, hnew, ha, by omega⟩

/-- **The hoisted body establishes `Done`** from an entry over `E`. -/
private theorem sumTgt_triple :
    Core.Logic.Hoare.Triple π testParams (At E) sumTgt (Done E) := by
  refine Core.Logic.Hoare.seq π testParams (Mid := fun ρ => At E ρ ∧ Holds E sId 0 ρ) ?_ ?_
    (by covered)
  · refine Core.Logic.Hoare.set π testParams _ _ _ _ _ (fun ρ₀ σ' v hf hev hup => ?_)
    rw [hf, Core.eval_intConst] at hev
    cases hev
    cases hup with
    | update _ hnew _ => exact ⟨hf, hnew⟩
  refine Core.Logic.Hoare.seq π testParams
    (Mid := fun ρ => At E ρ ∧ Holds E sId 0 ρ ∧ Holds E iId 0 ρ) ?_ ?_ (by covered)
  · refine Core.Logic.Hoare.init π testParams _ _ _ _ _ _ (fun ρ₀ σ' v ⟨hf, hs⟩ hev hinit => ?_)
    rw [hf, Core.eval_intConst] at hev
    cases hev
    cases hinit with
    | init _ hnew hoth => exact ⟨hf, (hoth _ s_ne_i.symm).trans hs, hnew⟩
  refine Core.Logic.Hoare.seq π testParams (Mid := Inv E) ?_ ?_ (by covered)
  · refine Core.Logic.Hoare.cmd π testParams _ _ _
      (fun ρ₀ σ' emitted ⟨hf, hs, hi⟩ _ hstep => ?_)
    have ⟨_, _, _, _, hoth, he⟩ := EvalCmdE.init_nondet_inv (evalCmdExtE_cmd_iff.mp hstep)
    exact ⟨by rw [he]; trivial, fun _ => ⟨hf, 0, 0, (hoth _ s_ne_sq.symm).trans hs,
      (hoth _ i_ne_sq.symm).trans hi, Int.le_refl 0, Int.le_refl 0⟩⟩
  refine Core.Logic.Hoare.consequence π testParams
    (Core.Logic.Hoare.while_rule π testParams (loopBody_triple hE) (by covered)
      (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide +kernel)))
    (fun _ h => h) (fun _ ⟨⟨hf, a, _, hs, _, ha, _⟩, _⟩ => ⟨hf, a, hs, ha⟩)

end Body

/-! ## Back to the original body -/

/-- `Done E` of the hoisted body's final environment gives it of the original's: `s` is
    defined in the original's, where the two agree, and both have the entry's factory `E`. -/
private theorem done_transport {E : Core.Expression.Factory} {ρ₀ ρ' ρ'' : Env Core.Expression}
    (hpre : ρ₀.factory = E) (hwf : Core.Logic.BlockInitEnvWF testParams sumBody ρ₀)
    (hf : ρ'.factory = ρ₀.factory)
    (hd : ∀ x, (ρ₀.store x).isSome = Bool.true → (ρ'.store x).isSome = Bool.true)
    (hagree : Imperative.Specification.Transform.EnvStoreAgree ρ' ρ'') (hx : Done E ρ'') :
    Done E ρ' := by
  obtain ⟨_, a, hs, ha⟩ := hx
  have hs0 : (ρ₀.store sId).isSome = Bool.true :=
    hwf.readWritesDefined sId (by decide +kernel) (by decide +kernel)
  have heq := hagree sId fun y hy => by rw [List.mem_singleton.mp hy]; exact hd _ hs0
  exact ⟨hf.trans hpre, a, heq.trans hs, ha⟩

/-- **`SumSquares` meets its contract**, from the triple of the hoisted body
    (`Core.LoopInitHoist.triple`), inside the procedure block. -/
theorem sum_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple sumPgmAST testParams "SumSquares" := by
  have hfactory : sumPgmAST.factoryBeforeProcedure "SumSquares" = Core.Factory :=
    Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by decide +kernel)
  rw [Core.Logic.Hoare.Procedure.contractTriple, hfactory]
  refine ⟨sumProc, by native_decide, by native_decide, ?_⟩
  rw [sum_body_eq]
  refine Core.Logic.Hoare.of_forall_entryFactory π _ fun E => ?_
  by_cases hE : E.factory = Core.Factory
  case neg =>
    exact Core.Logic.Hoare.consequence π testParams (Core.Logic.Hoare.false_pre π testParams _ _)
      (fun _ ⟨hpre, hf⟩ => hE (hf ▸ hpre.2.1)) (fun _ h => h)
  have hsrc : Core.Logic.Hoare.Triple π testParams
      (fun ρ => Core.Logic.Hoare.Procedure.contractPre Core.Factory sumProc ρ ∧ ρ.factory = E)
      sumBody (Done E) :=
    Core.LoopInitHoist.triple π testParams sum_hoist
      ⟨by decide +kernel, show List.Nodup _ by decide +kernel⟩
      (fun _ h => h.1.2.1) (fun _ _ _ hp hwf hf hd hag hx => done_transport hp.2 hwf hf hd hag hx)
      (fun ρ₀ ρ' tr hpre hinit hrun => sumTgt_triple hE ρ₀ ρ' tr hpre.2 hinit hrun)
  have hpost : Imperative.Logic.Hoare.PostWF sumBody (Done E) := by
    intro ρ ⟨hf, a, hs, ha⟩
    have hnd : sId ∉ Block.definedVars (P := Core.Expression) (C := Core.Command) sumBody true := by
      decide +kernel
    refine ⟨hf, a, ?_, ha⟩
    simp only [Holds, Imperative.dropVars, ite_eq_right hnd]
    exact hs
  refine Core.Logic.Hoare.consequence π testParams
    (Core.Logic.Hoare.block π testParams hsrc hpost) (fun _ h => h)
    (fun ρ ⟨hf, a, hs, ha⟩ => post_ge0 sum_post_expr (by rw [Pinned, hf]; exact hE)
      (by rw [hf]; exact hs) ha)

end Strata.HoareAfterLoopInitHoistTest
