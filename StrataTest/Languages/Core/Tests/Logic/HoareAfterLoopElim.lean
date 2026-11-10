/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import Strata.Languages.Core.ProgramProps
import Strata.Languages.Core
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.Transform.LoopElimCoreCorrect
import StrataDDM.Integration.Lean.HashCommands

/-! # A loop's contract, proved on its loop-eliminated form

`procedure Count(out y : int) spec { ensures !(int.le(y, 9)); }
 { y := 0; while (int.le(y, 9)) { y := int.add(y, 1); } }`

The contract is proved without a loop invariant or a while rule.  The Core pass
`Core.loopElim`, run on the program, replaces the loop by its passive encoding

```
if (int.le(y, 9)) {
  $__loopElim_arbitrary_iter_facts_loop_0: {
    $__loopElim_havoc_loop_0: { havoc y; }
    assume [$__loopElimAssume_guard_loop_0]: int.le(y, 9);
    y := int.add(y, 1);
  }
  $__loopElim_havoc_loop_0: { havoc y; }
  assume [$__loopElimAssume_not_guard_loop_0]: !(int.le(y, 9));
}
```

and the triple of the procedure's contract over this loop-free body follows from the
structural rules: the `if` either ends with the assumption of the negated guard, which is the
postcondition, or does not enter, where the guard is false.  `Core.LoopElim.triple_coreProgram`
then carries the triple back to the original body, which has no `exit` out of its loop
(`Block.loopExitsLocal`), and the procedure block wraps it.

The steps that inspect the translated procedure, or the output of running the pass on it, use
`native_decide`: `count_decl`, `count_body_eq`, `count_inner_eq`, `count_run`,
`count_out_decl`, `count_post_expr`, and the procedure lookup and `contractChecksTyped`
premises of `count_meets_contract`.  The procedure's statements, expressions and contract come
from `translateStmt`, `translateExpr` and `translateSpec`, which are `partial`, so the kernel
cannot reduce them and `decide +kernel` gets stuck on these steps.  The other side conditions
(the `definedVars` premises of `block_rule` and `postWF_of_definedVars_nil`, the `noCalls` and
`loopExitsLocal` premises) are checked by `decide +kernel` or `simp`.
-/

open Imperative
open StrataDDM (Program)

namespace Strata.HoareAfterLoopElimTest

/-- Translate a DDM concrete-syntax program to the Core AST. -/
private def cstToAST (p : Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- Gate parameters: no reserved fresh-prefixes, and every name counts as declared. -/
private def testParams : Core.Logic.InitEnvWFParams := ⟨[], [], fun _ => true⟩

private def countPgm : Program :=
#strata
program Core;

procedure Count(out y : int)
spec {
  ensures !(int.le(y, 9));
}
{
  y := 0;
  while (int.le(y, 9)) {
    y := int.add(y, 1);
  }
};
#end

private def countPgmAST : Core.Program := cstToAST countPgm

private abbrev π : String → Option Core.Procedure := countPgmAST.findProcByString?

private def countProc : Core.Procedure := (π "Count").get!

private def countY : Core.Expression.Ident := ⟨"y", ()⟩

/-- The metadata of `y := 0`, the loop's guard, measure, invariants, body and metadata, and
    the right-hand side and metadata of the body's assignment, projected out of the AST. -/
private def countParts :
    Imperative.MetaData Core.Expression × Core.Expression.Expr ×
      Option Core.Expression.Expr × List (String × Core.Expression.Expr) ×
      Core.Statements × Imperative.MetaData Core.Expression :=
  match countProc.body with
  | .structured [Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.set _ _ md0)),
                 Imperative.Stmt.loop (.det g) m inv body md1] => (md0, g, m, inv, body, md1)
  | _ => default

private abbrev countGuard : Core.Expression.Expr := countParts.2.1

/-- The body of the loop, `y := int.add(y, 1)`. -/
private abbrev countInner : Core.Statements := countParts.2.2.2.2.1

/-- The metadata of the procedure's declaration. -/
private def countMd : Imperative.MetaData Core.Expression :=
  match countPgmAST.decls with
  | [.proc _ md] => md
  | _ => default

/-- The procedure is the program's only declaration. -/
private theorem count_decl : countPgmAST.decls[0]? = some (.proc countProc countMd) := by
  native_decide

/-- The translated body really is the initialisation followed by the loop. -/
private theorem count_body_eq :
    countProc.body = .structured
      ([Core.Statement.set countY (Lambda.LExpr.const () (.intConst 0)) countParts.1] ++
        [.loop (.det countGuard) countParts.2.2.1 countParts.2.2.2.1 countInner
          countParts.2.2.2.2.2]) := by
  native_decide

/-- The right-hand side and metadata of the loop body's assignment `y := int.add(y, 1)`. -/
private def countInnerParts : Core.Expression.Expr × Imperative.MetaData Core.Expression :=
  match countInner with
  | [Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.set _ (.det e) md))] => (e, md)
  | _ => default

/-- The loop body really is a single assignment. -/
private theorem count_inner_eq :
    countInner = [Core.Statement.set countY countInnerParts.1 countInnerParts.2] := by
  native_decide

/-! ## The loop-eliminated body -/

/-- The havoc block of the encoding. -/
private def havocBlock : Core.Statement :=
  .block "$__loopElim_havoc_loop_0" [.cmd (HasHavoc.havoc countY countParts.2.2.2.2.2)] {}

/-- The first branch of the `if` replacing the loop: one iteration from a havocked `y`, then a
    havoc to the exit store and the assumption of the negated guard. -/
private def countThen : Core.Statements :=
  [.block "$__loopElim_arbitrary_iter_facts_loop_0"
      ([havocBlock] ++
        [.cmd (HasPassiveCmds.assume "$__loopElimAssume_guard_loop_0" countGuard
          countParts.2.2.2.2.2)] ++ countInner) {}] ++
    ([havocBlock] ++
      [.cmd (HasPassiveCmds.assume "$__loopElimAssume_not_guard_loop_0"
        (HasBoolOps.not countGuard) countParts.2.2.2.2.2)])

/-- The procedure body the Core pass returns. -/
private def countTgt : Core.Statements :=
  [Core.Statement.set countY (Lambda.LExpr.const () (.intConst 0)) countParts.1] ++
    [.ite (.det countGuard) countThen [] {}]

/-- A run of the Core pass `Core.loopElim` on the program. -/
private def countRun := Core.loopElim countPgmAST Core.Transform.CoreTransformState.emp

/-- The program the run returns. -/
private def countOut : Core.Program :=
  match countRun.1 with
  | .ok (_, p') => p'
  | .error _ => default

/-- The run succeeds, eliminating the loop. -/
private theorem count_run : ∃ σ', countRun = (.ok (Bool.true, countOut), σ') := by
  have hok : (match countRun.1 with | .ok (b, _) => b | .error _ => Bool.false) = Bool.true := by
    native_decide
  unfold countOut
  revert hok
  generalize countRun = r
  rcases r with ⟨_ | ⟨b, p'⟩, σ'⟩
  · simp
  · intro hb
    subst hb
    exact ⟨σ', rfl⟩

/-- The run replaces the body of the procedure by `countTgt`. -/
private theorem count_out_decl :
    countOut.decls[0]? = some (.proc { countProc with body := .structured countTgt } countMd) := by
  native_decide

/-! ## The triple of the loop-free body -/

/-- The postcondition `!(int.le(y, 9))` is the negated guard. -/
private theorem count_post_expr :
    ∀ lc ∈ countProc.spec.postconditions.toList, lc.2.expr = HasBoolOps.not countGuard := by
  have h : countProc.spec.postconditions.toList.all
      (fun lc => decide (lc.2.expr = HasBoolOps.not countGuard)) = Bool.true := by
    native_decide
  intro lc hlc
  simpa using (List.all_eq_true.1 h) lc hlc

/-- The runtime factory's functions are those of `Core.Factory`. -/
private abbrev Pinned (ρ : Env Core.Expression) : Prop := ρ.factory.factory = Core.Factory

/-- Where the negated guard evaluates to `true`, the postcondition holds. -/
private theorem post_of_not_guard {ρ : Env Core.Expression} (hpin : Pinned ρ)
    (h : Core.Expression.eval ρ.factory ρ.store (HasBoolOps.not countGuard) =
      some (HasBool.ttVal ρ.factory)) :
    Core.Logic.Hoare.Procedure.contractPost Core.Factory countProc ρ := by
  intro label check hmem _ _
  exact .inl ⟨hpin, by rw [count_post_expr _ hmem]; exact h⟩

/-- A havoc keeps the runtime factory. -/
private theorem havoc_pinned (x : Core.Expression.Ident) (md : MetaData Core.Expression)
    {Pre : Env Core.Expression → Prop} (hpre : ∀ ρ, Pre ρ → Pinned ρ) :
    Core.Logic.Hoare.Triple π testParams Pre [.cmd (HasHavoc.havoc x md)] Pinned := by
  refine Core.Logic.Hoare.cmd π testParams _ Pre Pinned
    (fun ρ₀ σ' emitted hρ _ hstep => ?_)
  cases hstep with
  | cmd_sem hbase =>
    cases hbase with
    | eval_set_nondet _ _ _ => exact ⟨True.intro, fun _ => hpre ρ₀ hρ⟩

/-- An assumption keeps the runtime factory and, when reachable, holds. -/
private theorem assume_rule (l : String) (e : Core.Expression.Expr) (md : MetaData Core.Expression)
    {Pre Post : Env Core.Expression → Prop}
    (hpost : ∀ ρ, Pre ρ → Core.Expression.eval ρ.factory ρ.store e =
      some (HasBool.ttVal ρ.factory) → Post ρ) :
    Core.Logic.Hoare.Triple π testParams (fun ρ => Pre ρ ∧ Pinned ρ)
      [.cmd (HasPassiveCmds.assume l e md)] Post := by
  refine Core.Logic.Hoare.cmd π testParams _ _ Post
    (fun ρ₀ σ' emitted hρ _ hstep => ?_)
  cases hstep with
  | cmd_sem hbase =>
    cases hbase with
    | eval_assume =>
      refine ⟨by simp [Trace.AssertionsValid, Trace.AssertionsValidFromP], fun ⟨w, hw⟩ => ?_⟩
      rcases hw _ (List.mem_singleton_self _) with ⟨_, he⟩ | ⟨hne, _⟩
      · exact hpost ρ₀ hρ.1 he
      · exact absurd hρ.2 hne

/-- A block that defines nothing keeps any postcondition through its exit. -/
private theorem block_rule {l : String} {ss : Core.Statements} {md : MetaData Core.Expression}
    {Pre Post : Env Core.Expression → Prop}
    (h : Core.Logic.Hoare.Triple π testParams Pre ss Post)
    (hdefs : Block.definedVars (P := Core.Expression) (C := Core.Command) ss true = []) :
    Core.Logic.Hoare.Triple π testParams Pre [.block l ss md] Post :=
  Core.Logic.Hoare.block π testParams h (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ hdefs)

/-- The havoc block keeps the runtime factory. -/
private theorem havocBlock_pinned {Pre : Env Core.Expression → Prop}
    (hpre : ∀ ρ, Pre ρ → Pinned ρ) :
    Core.Logic.Hoare.Triple π testParams Pre [havocBlock] Pinned :=
  block_rule (havoc_pinned _ _ hpre) (by decide +kernel)

/-- The loop body keeps the runtime factory. -/
private theorem inner_pinned : Core.Logic.Hoare.Triple π testParams Pinned countInner Pinned := by
  rw [count_inner_eq]
  exact Core.Logic.Hoare.set π testParams countY _ _ Pinned Pinned
    (fun _ _ _ hρ _ _ => hρ)

/-- **The loop-free body meets the contract.**  The first branch of the `if` ends with the
    assumption of the negated guard, which is the postcondition; the empty second branch runs
    where the guard is false, so the negated guard is true there. -/
private theorem countTgt_triple :
    Core.Logic.Hoare.Triple π testParams
      (Core.Logic.Hoare.Procedure.contractPre Core.Factory countProc) countTgt
      (Core.Logic.Hoare.Procedure.contractPost Core.Factory countProc) := by
  refine Core.Logic.Hoare.seq π testParams (Mid := Pinned)
    (Core.Logic.Hoare.set π testParams countY _ countParts.1 _ Pinned
      (fun _ _ _ hρ _ _ => hρ.2.1))
    ?_ ⟨trivial, trivial⟩
  refine Core.Logic.Hoare.ite π testParams ?_ ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide +kernel))
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide +kernel))
  · -- One iteration from a havocked `y`, then the exit havoc and the negated guard.
    refine Core.Logic.Hoare.seq π testParams (Mid := Pinned) ?_ ?_ ?_
    · refine block_rule ?_ (by rw [count_inner_eq]; decide +kernel)
      refine Core.Logic.Hoare.seq π testParams (Mid := Pinned) ?_ inner_pinned
        (by simp [havocBlock, Block.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks])
      refine Core.Logic.Hoare.seq π testParams (Mid := Pinned) ?_ ?_
        (by simp [havocBlock, Block.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks])
      · exact havocBlock_pinned fun _ h => h.1
      · exact Core.Logic.Hoare.consequence π testParams
          (assume_rule (Pre := Pinned) (Post := Pinned) _ _ _ fun _ h _ => h)
          (fun _ h => ⟨h, h⟩) (fun _ h => h)
    · refine Core.Logic.Hoare.seq π testParams (Mid := Pinned) (havocBlock_pinned fun _ h => h)
        ?_ (by simp [havocBlock, Block.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks])
      exact Core.Logic.Hoare.consequence π testParams
        (assume_rule (Pre := Pinned) _ _ _ fun _ hpin h => post_of_not_guard hpin h)
        (fun _ h => ⟨h, h⟩) (fun _ h => h)
    · simp [Block.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks, havocBlock, count_inner_eq]
  · -- The loop is not entered: the guard is false, so its negation is true.
    refine Core.Logic.Hoare.consequence π testParams
      (Imperative.Logic.Hoare.skip_block (Core.EvalCommandE π) Core.Logic.BlockInitEnvWF
        testParams _)
      (fun _ h => h) (fun ρ h => post_of_not_guard h.1 ?_)
    have hbool := Core.coreEvaluator_WellFormedSemanticEvalBool ρ.factory
      (h.1 ▸ Core.coreFactory_boolNot)
    exact ((hbool ρ.store countGuard).2.1 h.2)

/-! ## Back to the loop -/

/-- **The loop meets its contract**, from the triple of the body the Core pass returns
    (`Core.LoopElim.triple_coreProgram`). -/
theorem count_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple countPgmAST testParams "Count" := by
  have hfactory : countPgmAST.factoryBeforeProcedure "Count" = Core.Factory :=
    Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by decide +kernel)
  rw [Core.Logic.Hoare.Procedure.contractTriple, hfactory]
  refine ⟨countProc, by native_decide, by native_decide, ?_⟩
  rw [count_body_eq]
  obtain ⟨σ', hrun⟩ := count_run
  obtain ⟨ss', hd, htriple⟩ := Core.LoopElim.triple_coreProgram π testParams hrun count_decl
    count_body_eq
    (by simp [count_inner_eq, Core.Statements.noCalls, Block.allSubstmts_cons,
      Stmt.allSubstmts_loop, Stmt.allSubstmts_cmd, Block.allSubstmts_nil,
      Core.Statement.isNotCall, Core.Statement.set])
    (by simp [count_inner_eq, Block.loopExitsLocal, Stmt.loopExitsLocal,
      Block.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks])
  rw [count_out_decl] at hd
  simp only [Option.some.injEq, Core.Decl.proc.injEq] at hd
  obtain rfl : countTgt = ss' := Imperative.Body.structured.inj (congrArg (·.body) hd.1)
  exact block_rule (htriple (fun _ hpre => hpre.2.1) countTgt_triple)
    (by rw [count_inner_eq]; decide +kernel)

end Strata.HoareAfterLoopElimTest
