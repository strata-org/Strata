/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Core.Tests.Logic.HoareAfterSupport
import Strata.Transform.StructuredToUnstructuredPipelineCoreCorrect

open Imperative
open StrataDDM (Program)

namespace Strata.HoareAfterStructuredToUnstructuredPipelineTest

open HoareAfterSupport

/-- The program.  It comes first in the file: the translation records the byte offsets of its
    statements in their metadata, which `drainBody` spells out with `loc`, so an edit above it
    moves them. -/
private def drainPgm : Program :=
#strata
program Core;

procedure Drain(n : int, out r : int)
spec {
  requires int.ge(n, 0);
  ensures int.ge(r, 0);
}
{
  r := n;
  while (int.gt(r, 0)) {
    var step : int := 1;
    if * {
      r := int.sub(r, step);
    }
  }
};
#end

private def drainPgmAST : Core.Program := cstToAST drainPgm

private abbrev π : String → Option Core.Procedure := drainPgmAST.findProcByString?

/-! # A nondeterministic loop's contract, proved on the CFG of the lowering pipeline

```
procedure Drain(n : int, out r : int)
spec { requires int.ge(n, 0); ensures int.ge(r, 0); }
{
  r := n;
  while (int.gt(r, 0)) {
    var step : int := 1;
    if * { r := int.sub(r, step); }
  }
}
```

Each iteration declares `step` and may or may not take it off `r`.  The lowering pipeline
`Core.StructuredToUnstructuredPipeline.s2uPipeline` eliminates the nondeterministic guard
(a fresh Boolean), hoists the two loop-body declarations before the loop, and lowers the
result to the CFG

```
before_loop$_5: { r := n; var step : int; var $__ndelim_ite$_0 : bool; goto loop_entry$_1; }
loop_entry$_1:  { branch (int.gt(r, 0)) goto ite$_4 else goto end$_0; }
ite$_4:         { step := 1; havoc $__ndelim_ite$_0;
                  branch ($__ndelim_ite$_0) goto l$_3 else goto loop_entry$_1; }
l$_3:           { r := int.sub(r, step); goto loop_entry$_1; }
end$_0:         { return; }
```

As in `HoareUnstructured`, the triple of the CFG is proved from its operational semantics with a
configuration invariant (`RunInv`): `r ≥ 0` everywhere, `r > 0` in the loop body, and
`step = 1` once it is set.  `Core.StructuredToUnstructuredPipeline.triple` carries the triple back
to the structured body, at gate parameters reserving the generated prefixes of both lowering
passes: the postcondition reads `r`, which the body writes without declaring, so the gate has it
defined at entry and every run keeps it defined.

The translated body is spelled out as the closed term `drainBody`, and the CFG as the closed
term `drainCFG`; the block lookups of the CFG, the side conditions of the pipeline and the
facts about the body's variables are decided by the kernel (`decide +kernel`).  The facts that
bind the translated program to the body (`drain_body_eq`, `drain_pre_expr`, `drain_post_expr`,
the input typing, and the procedure lookup and `contractChecksTyped` premises of
`drain_meets_contract`) use `native_decide`: the translation is `partial`, so the kernel cannot
reduce it.  So does `drain_cfg`: the kernel cannot decide the equality of the labels the
lowering builds by appending strings.
-/

/-- Gate parameters of the structured body: the generated prefixes of both lowering passes
    reserved. -/
private def srcParams : Core.Logic.InitEnvWFParams :=
  (testParams.extend Imperative.StructuredToUnstructured.prefixesReserved).extend
    Imperative.NondetElim.prefixesReserved

private def drainProc : Core.Procedure := (π "Drain").get!

private def nId : Core.Expression.Ident := ⟨"n", ()⟩
private def rId : Core.Expression.Ident := ⟨"r", ()⟩
private def stepId : Core.Expression.Ident := ⟨"step", ()⟩
private def gId : Core.Expression.Ident := ⟨"$__ndelim_ite$_0", ()⟩

/-- The loop guard `int.gt(r, 0)`. -/
private abbrev gtE : Core.Expression.Expr := .app () (.app () Core.intGtOp (v rId)) (.intConst () 0)
/-- `int.sub(r, step)`. -/
private abbrev subE : Core.Expression.Expr :=
  .app () (.app () Core.intSubOp (v rId)) (v stepId)

/-- The translated body. -/
private abbrev drainBody : Core.Statements :=
  [Core.Statement.set rId (v nId) (loc 713 720),
   .loop (.det gtE) none []
     [Core.Statement.init stepId intLTy (.det (.intConst () 1)) (loc 750 770),
      .ite .nondet [Core.Statement.set rId subE (loc 788 810)] [] (loc 775 816)]
     (loc 723 820)]

/-- The translated body really is the assignment followed by the loop. -/
private theorem drain_body_eq : drainProc.body = .structured drainBody := by native_decide

/-! ## The CFG of the pipeline, spelled out -/

/-- `r := n`. -/
private abbrev setR0 : Core.Command := .cmd (.set rId (.det (v nId)) (loc 713 720))
/-- The hoisted declaration of `step`. -/
private abbrev initStep : Core.Command := .cmd (.init stepId intLTy .nondet (loc 750 770))
/-- The declaration of the fresh guard. -/
private abbrev initG : Core.Command := .cmd (.init gId HasBool.boolTy .nondet (loc 775 816))
/-- `step := 1`, what is left of the declaration of `step` in the loop body. -/
private abbrev setStep : Core.Command := .cmd (.set stepId (.det (.intConst () 1)) (loc 750 770))
/-- The havoc of the fresh guard. -/
private abbrev havocG : Core.Command := .cmd (.set gId .nondet (loc 775 816))
/-- `r := int.sub(r, step)`. -/
private abbrev setSub : Core.Command := .cmd (.set rId (.det subE) (loc 788 810))
/-- The fresh guard, read. -/
private abbrev gE : Core.Expression.Expr := HasFvar.mkTypedFvar gId HasBool.boolTy

private abbrev lEntry : String := "before_loop$_5"
private abbrev lLoop : String := "loop_entry$_1"
private abbrev lIte : String := "ite$_4"
private abbrev lStep : String := "l$_3"
private abbrev lEnd : String := "end$_0"

/-- The CFG the pipeline returns. -/
private abbrev drainCFG : Core.DetCFG :=
  { entry := lEntry
    blocks :=
      [(lEntry, { cmds := [setR0, initStep, initG], transfer := .goto lLoop }),
       (lLoop, { cmds := [], transfer := .condGoto gtE lIte lEnd .empty }),
       (lIte, { cmds := [setStep, havocG], transfer := .condGoto gE lStep lLoop .empty }),
       (lStep, { cmds := [setSub], transfer := .goto lLoop }),
       (lEnd, { cmds := [], transfer := .finish .empty })] }

/-- The pipeline turns the body into `drainCFG`.  The lowering builds its labels by appending
    strings, and the kernel cannot decide the equality of the strings it builds
    (`ByteArray.toList` is defined by well-founded recursion), so this uses `native_decide`. -/
private theorem drain_cfg :
    Core.StructuredToUnstructuredPipeline.s2uPipeline drainBody = some drainCFG := by
  native_decide

/-- The entry block runs `r := n` and declares `step` and the fresh guard, then jumps to the
    loop header. -/
private theorem entry_lookup : drainCFG.blocks.lookup lEntry =
    some { cmds := [setR0, initStep, initG], transfer := .goto lLoop } := by decide +kernel
/-- The loop header has no command and branches on the loop guard to the body or the end. -/
private theorem loop_lookup : drainCFG.blocks.lookup lLoop =
    some { cmds := [], transfer := .condGoto gtE lIte lEnd .empty } := by decide +kernel
/-- The body block sets `step := 1`, havocs the fresh guard and branches on it to the step or
    back to the loop header. -/
private theorem ite_lookup : drainCFG.blocks.lookup lIte =
    some { cmds := [setStep, havocG], transfer := .condGoto gE lStep lLoop .empty } := by
  decide +kernel
/-- The step block takes `step` off `r` and jumps back to the loop header. -/
private theorem step_lookup : drainCFG.blocks.lookup lStep =
    some { cmds := [setSub], transfer := .goto lLoop } := by decide +kernel
/-- The end block has no command and finishes. -/
private theorem end_lookup : drainCFG.blocks.lookup lEnd =
    some { cmds := [], transfer := .finish .empty } := by decide +kernel

/-- The precondition is `int.ge(n, 0)`. -/
private theorem drain_pre_expr :
    ∀ lc ∈ drainProc.spec.preconditions.toList, lc.2.expr = ge0 nId :=
  forall_of_all (by native_decide)

/-- The postcondition is `int.ge(r, 0)`. -/
private theorem drain_post_expr :
    ∀ lc ∈ drainProc.spec.postconditions.toList, lc.2.expr = ge0 rId :=
  forall_of_all (by native_decide)

/-! ## The configuration invariant

The store facts are about integers of the runtime factory `F` of the run. -/

section Run

variable (F : Core.Expression.Factory)

/-- `n` holds a non-negative integer. -/
private abbrev NIs (ρ : Env Core.Expression) : Prop :=
  ∃ k, ρ.store nId = some (intOf F k) ∧ 0 ≤ k

/-- `r` holds a non-negative integer satisfying `p`. -/
private abbrev RIs (p : Int → Prop) (ρ : Env Core.Expression) : Prop :=
  ∃ k, ρ.store rId = some (intOf F k) ∧ 0 ≤ k ∧ p k

/-- `r` holds a positive integer and `step` holds `1`. -/
private abbrev Stepping (ρ : Env Core.Expression) : Prop :=
  RIs F (0 < ·) ρ ∧ ρ.store stepId = some (intOf F 1)

/-- Every configuration reachable from the entry block, with the store facts that hold
    there.  Every configuration pins the runtime factory to `F`. -/
private inductive RunInv : CFGConfig String Core.Command Core.Expression → Prop where
  | atEntry (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : NIs F ρ) :
      RunInv (.atBlock drainCFG lEntry ρ)
  | entryPreR (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : NIs F ρ) :
      RunInv (.inBlock drainCFG lEntry [setR0, initStep, initG] (.goto lLoop) ρ)
  | entryPreStep (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (fun _ => True) ρ) :
      RunInv (.inBlock drainCFG lEntry [initStep, initG] (.goto lLoop) ρ)
  | entryPreG (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (fun _ => True) ρ) :
      RunInv (.inBlock drainCFG lEntry [initG] (.goto lLoop) ρ)
  | entryAtGoto (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (fun _ => True) ρ) :
      RunInv (.inBlock drainCFG lEntry [] (.goto lLoop) ρ)
  | atLoop (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (fun _ => True) ρ) :
      RunInv (.atBlock drainCFG lLoop ρ)
  | loopAtBranch (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (fun _ => True) ρ) :
      RunInv (.inBlock drainCFG lLoop [] (.condGoto gtE lIte lEnd .empty) ρ)
  | atIte (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (0 < ·) ρ) :
      RunInv (.atBlock drainCFG lIte ρ)
  | itePreStep (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (0 < ·) ρ) :
      RunInv (.inBlock drainCFG lIte [setStep, havocG]
        (.condGoto gE lStep lLoop .empty) ρ)
  | itePreG (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : Stepping F ρ) :
      RunInv (.inBlock drainCFG lIte [havocG] (.condGoto gE lStep lLoop .empty) ρ)
  | iteAtBranch (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : Stepping F ρ) :
      RunInv (.inBlock drainCFG lIte [] (.condGoto gE lStep lLoop .empty) ρ)
  | atStep (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : Stepping F ρ) :
      RunInv (.atBlock drainCFG lStep ρ)
  | stepPreSub (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : Stepping F ρ) :
      RunInv (.inBlock drainCFG lStep [setSub] (.goto lLoop) ρ)
  | stepAtGoto (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (fun _ => True) ρ) :
      RunInv (.inBlock drainCFG lStep [] (.goto lLoop) ρ)
  | atEnd (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (fun _ => True) ρ) :
      RunInv (.atBlock drainCFG lEnd ρ)
  | endAtFinish (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (fun _ => True) ρ) :
      RunInv (.inBlock drainCFG lEnd [] (.finish .empty) ρ)
  | terminal (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (fun _ => True) ρ) :
      RunInv (.terminal ρ)

/-- `step` is not `r`. -/
private theorem step_ne_r : stepId ≠ rId := by decide
/-- The fresh guard is not `r`. -/
private theorem g_ne_r : gId ≠ rId := by decide
/-- The fresh guard is not `step`. -/
private theorem g_ne_step : gId ≠ stepId := by decide

variable {F} (hF : F.factory = Core.Factory)
include hF

/-- One step from an invariant configuration stays within `RunInv` and emits no events. -/
private theorem step_preserves {before after : CFGConfig String Core.Command Core.Expression}
    {emitted : List (Event Core.Expression)} (hinv : RunInv F before)
    (hstep : StepCFGE Core.Expression (Core.EvalCommandE π) before emitted after) :
    RunInv F after ∧ emitted = [] := by
  cases hinv with
  | atEntry ρ hf h =>
    cases hstep with
    | fetch hlookup =>
      rw [Option.some.inj (hlookup.symm.trans entry_lookup)]
      exact ⟨.entryPreR ρ hf h, rfl⟩
  | entryPreR ρ hf h =>
    obtain ⟨k, hn, hk⟩ := h
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨w, heval, hres, _, rfl⟩ := set_inv hcmd
      rw [hf, Core.eval_fvar_int F hn] at heval
      cases heval
      exact ⟨.entryPreStep _ hf ⟨k, hres, hk, trivial⟩, rfl⟩
  | entryPreStep ρ hf h =>
    obtain ⟨k, hr, hk, _⟩ := h
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨hoth, rfl⟩ := init_nondet_inv hcmd
      exact ⟨.entryPreG _ hf ⟨k, (hoth _ step_ne_r).trans hr, hk, trivial⟩, rfl⟩
  | entryPreG ρ hf h =>
    obtain ⟨k, hr, hk, _⟩ := h
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨hoth, rfl⟩ := init_nondet_inv hcmd
      exact ⟨.entryAtGoto _ hf ⟨k, (hoth _ g_ne_r).trans hr, hk, trivial⟩, rfl⟩
  | entryAtGoto ρ hf h =>
    cases hstep with
    | goto_true _ => exact ⟨.atLoop ρ hf h, rfl⟩
    | goto_false _ => exact ⟨.atLoop ρ hf h, rfl⟩
  | atLoop ρ hf h =>
    cases hstep with
    | fetch hlookup =>
      rw [Option.some.inj (hlookup.symm.trans loop_lookup)]
      exact ⟨.loopAtBranch ρ hf h, rfl⟩
  | loopAtBranch ρ hf h =>
    obtain ⟨k, hr, hk, _⟩ := h
    have hg : Core.Expression.eval ρ.factory ρ.store gtE =
        some (Lambda.SemValue.ofBool F.model.tcInterp (decide (k > 0))) := by
      rw [hf]
      exact Core.eval_intGt (hF ▸ Core.coreFactory_intGt) (Core.eval_fvar_int F hr)
        (Core.eval_intConst F ρ.store 0)
    cases hstep with
    | goto_true hguard =>
      have h := Option.some.inj (hguard.symm.trans hg)
      rw [hf] at h
      exact ⟨.atIte ρ hf ⟨k, hr, hk,
        of_decide_eq_true (Lambda.SemValue.ofBool_injective h).symm⟩, rfl⟩
    | goto_false _ => exact ⟨.atEnd ρ hf ⟨k, hr, hk, trivial⟩, rfl⟩
  | atIte ρ hf h =>
    cases hstep with
    | fetch hlookup =>
      rw [Option.some.inj (hlookup.symm.trans ite_lookup)]
      exact ⟨.itePreStep ρ hf h, rfl⟩
  | itePreStep ρ hf h =>
    obtain ⟨k, hr, hk, hpos⟩ := h
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨w, heval, hres, hoth, rfl⟩ := set_inv hcmd
      rw [hf, Core.eval_intConst] at heval
      cases heval
      exact ⟨.itePreG _ hf ⟨⟨k, (hoth _ step_ne_r).trans hr, hk, hpos⟩, hres⟩, rfl⟩
  | itePreG ρ hf h =>
    obtain ⟨⟨k, hr, hk, hpos⟩, hs⟩ := h
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨hoth, rfl⟩ := havoc_inv hcmd
      exact ⟨.iteAtBranch _ hf ⟨⟨k, (hoth _ g_ne_r).trans hr, hk, hpos⟩,
        (hoth _ g_ne_step).trans hs⟩, rfl⟩
  | iteAtBranch ρ hf h =>
    cases hstep with
    | goto_true _ => exact ⟨.atStep ρ hf h, rfl⟩
    | goto_false _ =>
      obtain ⟨⟨k, hr, hk, _⟩, _⟩ := h
      exact ⟨.atLoop ρ hf ⟨k, hr, hk, trivial⟩, rfl⟩
  | atStep ρ hf h =>
    cases hstep with
    | fetch hlookup =>
      rw [Option.some.inj (hlookup.symm.trans step_lookup)]
      exact ⟨.stepPreSub ρ hf h, rfl⟩
  | stepPreSub ρ hf h =>
    obtain ⟨⟨k, hr, _, hpos⟩, hs⟩ := h
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨w, heval, hres, _, rfl⟩ := set_inv hcmd
      rw [hf, Core.eval_intSub (hF ▸ Core.coreFactory_intSub)
        (Core.eval_fvar_int F hr) (Core.eval_fvar_int F hs)] at heval
      cases heval
      exact ⟨.stepAtGoto _ hf ⟨k - 1, hres, by omega, trivial⟩, rfl⟩
  | stepAtGoto ρ hf h =>
    cases hstep with
    | goto_true _ => exact ⟨.atLoop ρ hf h, rfl⟩
    | goto_false _ => exact ⟨.atLoop ρ hf h, rfl⟩
  | atEnd ρ hf h =>
    cases hstep with
    | fetch hlookup =>
      rw [Option.some.inj (hlookup.symm.trans end_lookup)]
      exact ⟨.endAtFinish ρ hf h, rfl⟩
  | endAtFinish ρ hf h =>
    cases hstep with
    | finish => exact ⟨.terminal ρ hf h, rfl⟩
  | terminal ρ hf h =>
    cases hstep

end Run

/-! ## The triple of the CFG -/

/-- At the end, over the entry factory `E`: `r` holds a non-negative integer. -/
private abbrev Done (E : Core.Expression.Factory) (ρ : Env Core.Expression) : Prop :=
  ρ.factory = E ∧ ∃ k, ρ.store rId = some (intOf E k) ∧ 0 ≤ k

/-- **The CFG establishes `Done`**, from every entry over a factory `E` over `Core.Factory`
    satisfying the contract's precondition. -/
private theorem drainCFG_triple {E : Core.Expression.Factory} (hE : E.factory = Core.Factory) :
    Core.Logic.Hoare.TripleUnstructured π testParams
      (fun ρ => Core.Logic.Hoare.Procedure.contractPre Core.Factory drainProc ρ ∧ ρ.factory = E)
      drainCFG (Done E) := by
  intro ρ₀ ρ' trace ⟨hpre, hf⟩ hinit hterm
  have hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE π))
      (.atBlock drainCFG drainCFG.entry ρ₀) trace (.terminal ρ') := by
    rcases hterm with h | ⟨_, h⟩ <;> exact h
  obtain ⟨k, hn, hk⟩ := nonneg_of_pre hpre hinit.storeWellDefined (by native_decide)
    drain_pre_expr (by native_decide)
  rw [hf] at hn
  obtain ⟨hfinal, rfl⟩ :=
    run_preserves_of_step (step_preserves hE) (.atEntry ρ₀ hf ⟨k, hn, hk⟩) hrun
  refine ⟨trivial, fun _ => ?_⟩
  cases hfinal with
  | terminal _ hf' h =>
    obtain ⟨k', hr, hk', _⟩ := h
    exact ⟨hf', k', hr, hk'⟩

/-! ## Back to the structured body -/

/-- A name without a `_<digits>` suffix is not generated by a string generator. -/
private theorem not_gen {name pf : String} {σ : StringGenState}
    (hn : String.endsWithUnderscoreDigits name = false)
    (h : name = (StringGenState.gen pf σ).1) : False := by
  have hs := String.endsWithUnderscoreDigits_of_hasUnderscoreDigitSuffix
    (StringGenState.gen_hasUnderscoreDigitSuffix pf σ)
  rw [← h, hn] at hs
  cases hs

/-- **`Drain` meets its contract**, from the triple of its CFG
    (`Core.StructuredToUnstructuredPipeline.triple`), inside the procedure block. -/
theorem drain_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple drainPgmAST srcParams "Drain" := by
  have hfactory : drainPgmAST.factoryBeforeProcedure "Drain" = Core.Factory :=
    Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by decide +kernel)
  rw [Core.Logic.Hoare.Procedure.contractTriple, hfactory]
  refine ⟨drainProc, by native_decide, by native_decide, ?_⟩
  rw [drain_body_eq]
  refine of_forall_factory π fun E => ?_
  by_cases hE : E.factory = Core.Factory
  case neg =>
    exact Core.Logic.Hoare.consequence π srcParams (Core.Logic.Hoare.false_pre π srcParams _ _)
      (fun _ ⟨hpre, hf⟩ => hE (hf ▸ hpre.2.1)) (fun _ h => h)
  have hlabels : Block.getBlockLabels drainBody = [] := by decide +kernel
  have hinits : Block.initVars (C := Core.Command) drainBody = [stepId] := by decide +kernel
  have hvars : Block.definedVars (C := Core.Command) drainBody false ++
      Block.modifiedVars (C := Core.Command) drainBody = [stepId, rId, rId] := by decide +kernel
  have hsrc := Core.StructuredToUnstructuredPipeline.triple π testParams
    (fun _ h _ _ => by simp [testParams] at h) drain_cfg (Post := Done E) (Post' := Done E)
    ⟨by decide +kernel, by decide +kernel, by decide +kernel,
      by rw [Block.uniqueInits, hinits]; simp, by covered,
      ⟨by simp [hlabels], by simp [hlabels]⟩,
      fun name hname hmem => by
        rw [hvars] at hmem
        rcases (Imperative.NondetElim.isGeneratedName_iff _).1 hname with ⟨σ, h⟩ | ⟨σ, h⟩ <;>
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h' | h' | h' <;>
            first
            | (have hn : name = "step" := congrArg (·.name) h'
               subst hn; exact not_gen (by decide) h)
            | (have hn : name = "r" := congrArg (·.name) h'
               subst hn; exact not_gen (by decide) h),
      fun name hname hmem => by
        rw [hinits, List.mem_singleton] at hmem
        have hn : name = "step" := congrArg (·.name) hmem
        subst hn
        rcases hname with ⟨_, _, σ, h⟩ | ⟨_, σ, h⟩ <;> exact not_gen (by decide) h⟩
    (fun _ h => h.1.2.1)
    (fun ρ₀ ρ' ρ'' ⟨_, h0⟩ hwf hf hd hag ⟨_, k, hr, hk⟩ => by
      have hr0 : (ρ₀.store rId).isSome = Bool.true :=
        hwf.readWritesDefined rId (by decide +kernel) (by decide +kernel)
      have heq := hag rId fun y hy => by rw [List.mem_singleton.mp hy]; exact hd _ hr0
      exact ⟨hf.trans h0, k, heq.trans hr, hk⟩)
    (drainCFG_triple hE)
  have hpost : Imperative.Logic.Hoare.PostWF drainBody (Done E) := by
    intro ρ ⟨hf, k, hr, hk⟩
    have hnd :
        rId ∉ Block.definedVars (P := Core.Expression) (C := Core.Command) drainBody true := by
      decide +kernel
    refine ⟨hf, k, ?_, hk⟩
    simp only [Imperative.dropVars, ite_eq_right hnd]
    exact hr
  refine Core.Logic.Hoare.consequence π srcParams (Core.Logic.Hoare.block π srcParams hsrc hpost)
    (fun _ h => h) (fun ρ ⟨hf, k, hr, hk⟩ => post_ge0 drain_post_expr
      (by rw [Pinned, hf]; exact hE) (by rw [hf]; exact hr) hk)

end Strata.HoareAfterStructuredToUnstructuredPipelineTest
