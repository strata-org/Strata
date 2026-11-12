/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Core.Tests.Logic.HoareAfterSupport
import Strata.Transform.StructuredToUnstructuredCoreCorrect

open Imperative
open StrataDDM (Program)

namespace Strata.HoareAfterStructuredToUnstructuredTest

open HoareAfterSupport

/-- The program.  It comes first in the file: the translation records the byte offsets of its
    statements in their metadata, which `cdBody` spells out with `loc`, so an edit above it
    moves them. -/
private def cdPgm : Program :=
#strata
program Core;

procedure Countdown(n : int, out r : int)
spec {
  requires int.ge(n, 0);
  ensures r == 0;
}
{
  r := n;
  while (int.gt(r, 0)) {
    r := int.sub(r, 1);
  }
};
#end

private def cdPgmAST : Core.Program := cstToAST cdPgm

private abbrev π : String → Option Core.Procedure := cdPgmAST.findProcByString?

/-! # A structured loop's contract, proved on the CFG it is lowered to

```
procedure Countdown(n : int, out r : int)
spec { requires int.ge(n, 0); ensures r == 0; }
{ r := n; while (int.gt(r, 0)) { r := int.sub(r, 1); } }
```

`Core.stmtsToCFG` lowers the body to the control-flow graph

```
$__s2u_before_loop$_3: { r := n;              goto $__s2u_loop_entry$_1; }
$__s2u_loop_entry$_1:  { branch (int.gt(r, 0)) goto $__s2u_l$_2 else goto $__s2u_end$_0; }
$__s2u_l$_2:           { r := int.sub(r, 1);  goto $__s2u_loop_entry$_1; }
$__s2u_end$_0:         { return; }
```

There is no proof rule for CFGs.  As in `HoareUnstructured`, the triple of the CFG is proved
from its operational semantics: every configuration a run reaches satisfies an invariant
(`RunInv`) recording, at each program point, what the store holds (`r ≥ 0`, with `r > 0` in the
body and `r = 0` at the end).  `Core.StructuredToUnstructured.triple` carries the triple back to
the structured body, at gate parameters reserving the generated label prefixes.  The final
environments of the two bodies agree on the bindings of the structured one (`EnvStoreAgree`);
the postcondition reads `r`, which the body writes without declaring, so the gate has it
defined at entry and every run keeps it defined.

The translated body is spelled out as the closed term `cdBody`; the block lookups of the CFG
and the side conditions of the lowering are decided by the kernel (`decide +kernel`).  The
facts that bind the translated program to it (`cd_body_eq`, `cd_pre_expr`, `cd_post_expr`, the
input typing, and the procedure lookup and `contractChecksTyped` premises of
`countdown_meets_contract`) use `native_decide`: the translation is `partial`, so the kernel
cannot reduce it.  So does `cd_cfg`: the kernel cannot decide the equality of the labels the
lowering builds by appending strings.
-/

/-- Gate parameters of the structured body: the generated label prefixes reserved. -/
private def srcParams : Core.Logic.InitEnvWFParams :=
  testParams.extend Imperative.StructuredToUnstructured.prefixesReserved

private def cdProc : Core.Procedure := (π "Countdown").get!

private def nId : Core.Expression.Ident := ⟨"n", ()⟩
private def rId : Core.Expression.Ident := ⟨"r", ()⟩

/-- The loop guard `int.gt(r, 0)`. -/
private abbrev gtE : Core.Expression.Expr := .app () (.app () Core.intGtOp (v rId)) (.intConst () 0)
/-- `int.sub(r, 1)`. -/
private abbrev subE : Core.Expression.Expr :=
  .app () (.app () Core.intSubOp (v rId)) (.intConst () 1)

/-- The translated body. -/
private abbrev cdBody : Core.Statements :=
  [Core.Statement.set rId (v nId) (loc 689 696),
   .loop (.det gtE) none [] [Core.Statement.set rId subE (loc 726 745)] (loc 699 749)]

/-- The translated body really is the assignment followed by the loop. -/
private theorem cd_body_eq : cdProc.body = .structured cdBody := by native_decide

/-! ## The lowered CFG, spelled out -/

/-- `r := n`. -/
private abbrev setR0 : Core.Command := .cmd (.set rId (.det (v nId)) (loc 689 696))
/-- `r := int.sub(r, 1)`. -/
private abbrev setSub : Core.Command := .cmd (.set rId (.det subE) (loc 726 745))

private abbrev lEntry : String := "$__s2u_before_loop$_3"
private abbrev lLoop : String := "$__s2u_loop_entry$_1"
private abbrev lBody : String := "$__s2u_l$_2"
private abbrev lEnd : String := "$__s2u_end$_0"

/-- The CFG the lowering returns. -/
private abbrev cdCFG : Core.DetCFG :=
  { entry := lEntry
    blocks :=
      [(lEntry, { cmds := [setR0], transfer := .goto lLoop }),
       (lLoop, { cmds := [], transfer := .condGoto gtE lBody lEnd .empty }),
       (lBody, { cmds := [setSub], transfer := .goto lLoop }),
       (lEnd, { cmds := [], transfer := .finish .empty })] }

/-- The lowering turns the body into `cdCFG`.  The lowering builds its labels by appending
    strings, and the kernel cannot decide the equality of the strings it builds
    (`ByteArray.toList` is defined by well-founded recursion), so this uses `native_decide`. -/
private theorem cd_cfg : Core.stmtsToCFG cdBody = some cdCFG := by native_decide

/-- The entry block runs `r := n` and jumps to the loop header. -/
private theorem entry_lookup : cdCFG.blocks.lookup lEntry =
    some { cmds := [setR0], transfer := .goto lLoop } := by decide +kernel
/-- The loop header has no command and branches on the guard to the body or the end. -/
private theorem loop_lookup : cdCFG.blocks.lookup lLoop =
    some { cmds := [], transfer := .condGoto gtE lBody lEnd .empty } := by decide +kernel
/-- The body block runs the decrement and jumps back to the loop header. -/
private theorem body_lookup : cdCFG.blocks.lookup lBody =
    some { cmds := [setSub], transfer := .goto lLoop } := by decide +kernel
/-- The end block has no command and finishes. -/
private theorem end_lookup : cdCFG.blocks.lookup lEnd =
    some { cmds := [], transfer := .finish .empty } := by decide +kernel

/-- The precondition is `int.ge(n, 0)`. -/
private theorem cd_pre_expr : ∀ lc ∈ cdProc.spec.preconditions.toList, lc.2.expr = ge0 nId :=
  List.forall_of_all_decide (by native_decide)

/-- The postcondition is `r == 0`. -/
private theorem cd_post_expr :
    ∀ lc ∈ cdProc.spec.postconditions.toList, lc.2.expr = .eq () (v rId) (.intConst () 0) :=
  List.forall_of_all_decide (by native_decide)

/-! ## The configuration invariant

The store facts are about integers of the runtime factory `F` of the run. -/

section Run

variable (F : Core.Expression.Factory)

/-- `r` holds a non-negative integer satisfying `p`. -/
private abbrev RIs (p : Int → Prop) (ρ : Env Core.Expression) : Prop :=
  ∃ k, ρ.store rId = some (intOf F k) ∧ 0 ≤ k ∧ p k

/-- Every configuration reachable from the entry block, with the store facts that hold
    there.  Every configuration pins the runtime factory to `F`. -/
private inductive RunInv : CFGConfig String Core.Command Core.Expression → Prop where
  | atEntry (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (h : ∃ k, ρ.store nId = some (intOf F k) ∧ 0 ≤ k) :
      RunInv (.atBlock cdCFG lEntry ρ)
  | entryPreSet (ρ : Env Core.Expression) (hf : ρ.factory = F)
      (h : ∃ k, ρ.store nId = some (intOf F k) ∧ 0 ≤ k) :
      RunInv (.inBlock cdCFG lEntry [setR0] (.goto lLoop) ρ)
  | entryAtGoto (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (fun _ => True) ρ) :
      RunInv (.inBlock cdCFG lEntry [] (.goto lLoop) ρ)
  | atLoop (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (fun _ => True) ρ) :
      RunInv (.atBlock cdCFG lLoop ρ)
  | loopAtBranch (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (fun _ => True) ρ) :
      RunInv (.inBlock cdCFG lLoop [] (.condGoto gtE lBody lEnd .empty) ρ)
  | atBody (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (0 < ·) ρ) :
      RunInv (.atBlock cdCFG lBody ρ)
  | bodyPreSub (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (0 < ·) ρ) :
      RunInv (.inBlock cdCFG lBody [setSub] (.goto lLoop) ρ)
  | bodyAtGoto (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (fun _ => True) ρ) :
      RunInv (.inBlock cdCFG lBody [] (.goto lLoop) ρ)
  | atEnd (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (· = 0) ρ) :
      RunInv (.atBlock cdCFG lEnd ρ)
  | endAtFinish (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (· = 0) ρ) :
      RunInv (.inBlock cdCFG lEnd [] (.finish .empty) ρ)
  | terminal (ρ : Env Core.Expression) (hf : ρ.factory = F) (h : RIs F (· = 0) ρ) :
      RunInv (.terminal ρ)

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
      exact ⟨.entryPreSet ρ hf h, rfl⟩
  | entryPreSet ρ hf h =>
    obtain ⟨k, hn, hk⟩ := h
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨w, heval, -, hres, _, rfl⟩ :=
        EvalCmdE.set_det_inv (evalCmdExtE_cmd_iff.mp hcmd)
      rw [hf, Core.eval_fvar_int F hn] at heval
      cases heval
      exact ⟨.entryAtGoto _ hf ⟨k, hres, hk, trivial⟩, rfl⟩
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
      exact ⟨.atBody ρ hf ⟨k, hr, hk,
        of_decide_eq_true (Lambda.SemValue.ofBool_injective h).symm⟩, rfl⟩
    | goto_false hguard =>
      have h := Option.some.inj (hguard.symm.trans hg)
      rw [hf] at h
      have hle : ¬ k > 0 := of_decide_eq_false (Lambda.SemValue.ofBool_injective h).symm
      exact ⟨.atEnd ρ hf ⟨k, hr, hk, by omega⟩, rfl⟩
  | atBody ρ hf h =>
    cases hstep with
    | fetch hlookup =>
      rw [Option.some.inj (hlookup.symm.trans body_lookup)]
      exact ⟨.bodyPreSub ρ hf h, rfl⟩
  | bodyPreSub ρ hf h =>
    obtain ⟨k, hr, _, hpos⟩ := h
    cases hstep with
    | step_cmd hcmd =>
      obtain ⟨w, heval, -, hres, _, rfl⟩ :=
        EvalCmdE.set_det_inv (evalCmdExtE_cmd_iff.mp hcmd)
      rw [hf, Core.eval_intSub (hF ▸ Core.coreFactory_intSub)
        (Core.eval_fvar_int F hr) (Core.eval_intConst F ρ.store 1)] at heval
      cases heval
      exact ⟨.bodyAtGoto _ hf ⟨k - 1, hres, by omega, trivial⟩, rfl⟩
  | bodyAtGoto ρ hf h =>
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

/-- At the end, over the entry factory `E`: `r` holds `0`. -/
private abbrev Done (E : Core.Expression.Factory) (ρ : Env Core.Expression) : Prop :=
  ρ.factory = E ∧ ρ.store rId = some (intOf E 0)

/-- **The CFG establishes `Done`**, from every entry over a factory `E` over `Core.Factory`
    satisfying the contract's precondition. -/
private theorem cdCFG_triple {E : Core.Expression.Factory} (hE : E.factory = Core.Factory) :
    Core.Logic.Hoare.TripleUnstructured π testParams
      (fun ρ => Core.Logic.Hoare.Procedure.contractPre Core.Factory cdProc ρ ∧ ρ.factory = E)
      cdCFG (Done E) := by
  intro ρ₀ ρ' trace ⟨hpre, hf⟩ hinit hterm
  have hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE π))
      (.atBlock cdCFG cdCFG.entry ρ₀) trace (.terminal ρ') := by
    rcases hterm with h | ⟨_, h⟩ <;> exact h
  obtain ⟨k, hn, hk⟩ := nonneg_of_pre hpre hinit.storeWellDefined (by native_decide)
    cd_pre_expr (by native_decide)
  rw [hf] at hn
  obtain ⟨hfinal, rfl⟩ :=
    ReflTransTrace.invariant_of_silent_step hrun (step_preserves hE) (.atEntry ρ₀ hf ⟨k, hn, hk⟩)
  refine ⟨trivial, fun _ => ?_⟩
  cases hfinal with
  | terminal _ hf' h =>
    obtain ⟨_, hr, _, rfl⟩ := h
    exact ⟨hf', hr⟩

/-! ## Back to the structured body -/

/-- **`Countdown` meets its contract**, from the triple of its CFG
    (`Core.StructuredToUnstructured.triple`), inside the procedure block. -/
theorem countdown_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple cdPgmAST srcParams "Countdown" := by
  have hfactory : cdPgmAST.factoryBeforeProcedure "Countdown" = Core.Factory :=
    Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by decide +kernel)
  rw [Core.Logic.Hoare.Procedure.contractTriple, hfactory]
  refine ⟨cdProc, by native_decide, by native_decide, ?_⟩
  rw [cd_body_eq]
  refine Core.Logic.Hoare.of_forall_entryFactory π _ fun E => ?_
  by_cases hE : E.factory = Core.Factory
  case neg =>
    exact Core.Logic.Hoare.consequence π srcParams (Core.Logic.Hoare.false_pre π srcParams _ _)
      (fun _ ⟨hpre, hf⟩ => hE (hf ▸ hpre.2.1)) (fun _ h => h)
  have hlabels : Block.getBlockLabels cdBody = [] := by decide +kernel
  have hinits : Block.initVars (C := Core.Command) cdBody = [] := by decide +kernel
  have hsrc := Core.StructuredToUnstructured.triple π testParams cd_cfg (Post := Done E)
    (Post' := Done E)
    ⟨by decide +kernel, by decide +kernel, by rw [Block.uniqueInits, hinits]; exact .nil,
      by decide +kernel, by decide +kernel, by decide +kernel, by covered,
      ⟨by simp [hlabels], by simp [hlabels]⟩⟩
    (fun _ h => h.1.2.1)
    (fun ρ₀ ρ' ρ'' ⟨_, h0⟩ hwf hf hd hag ⟨_, hr⟩ => by
      have hr0 : (ρ₀.store rId).isSome = Bool.true :=
        hwf.readWritesDefined rId (by decide +kernel) (by decide +kernel)
      have heq := hag rId fun y hy => by rw [List.mem_singleton.mp hy]; exact hd _ hr0
      exact ⟨hf.trans h0, heq.trans hr⟩)
    (cdCFG_triple hE)
  refine Core.Logic.Hoare.consequence π srcParams
    (Core.Logic.Hoare.block π srcParams hsrc
      (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide +kernel)))
    (fun _ h => h) (fun ρ ⟨hf, hr⟩ => ?_)
  intro label check hmem _ _
  refine .inl ⟨by rw [hf]; exact hE, ?_⟩
  change Core.Expression.eval ρ.factory ρ.store check.expr = some (HasBool.ttVal ρ.factory)
  rw [cd_post_expr _ hmem, hf]
  exact Core.eval_eq_true E (Core.eval_fvar_int E hr) (Core.eval_intConst E ρ.store 0)

end Strata.HoareAfterStructuredToUnstructuredTest
