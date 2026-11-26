/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import Strata.Languages.Core.ProcedureProps
import Strata.Languages.Core.ProgramProps
import Strata.Languages.Core
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.Transform.LoopElimCoreCorrect
import Strata.Languages.Core.IntEvalProps
import StrataDDM.Integration.Lean.HashCommands
import StrataTest.Languages.Core.Tests.Logic.HoareUtils

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
then carries the triple back to the original body, and the procedure block wraps it.

The steps that inspect the translated procedure, or the output of running the pass on it, use
`native_decide`: `count_decl`, `count_body_eq`, `count_inner_eq`, `count_run`,
`count_out_decl`, `count_post_expr`, and the procedure lookup and `contractChecksTyped`
premises of `count_meets_contract`.  The procedure's statements, expressions and contract come
from `translateStmt`, `translateExpr` and `translateSpec`, which are `partial`, so the kernel
cannot reduce them and `decide +kernel` gets stuck on these steps.  The other side conditions
(the `definedVars` premises of `block_rule` and `postWF_of_definedVars_nil`, and the `noCalls`
premise) are checked by `decide +kernel` or `simp`.

The last section, *A loop left by an `exit`*, checks that loop elimination still transports
triples back when an iteration leaves its loop by an `exit`.
-/

open Imperative
open StrataDDM (Program)

namespace Strata.HoareAfterLoopElimTest

open Strata.HoareUtils (cstToAST testParams Pinned boolFactory someValuation)

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
                 Imperative.Stmt.loop (.det g) m inv body md1] _ => (md0, g, m, inv, body, md1)
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

/-- The right-hand side of the initialisation `y := 0`, whose source location the
translation fixes; extracted from the translated body rather than written out so the
test pins the shape, not the location. -/
private def countInitExpr : Core.Expression.Expr :=
  match countProc.body with
  | .structured (Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.set _ (.det e) _)) :: _)
      _ => e
  | _ => default

/-- The translated body really is the initialisation followed by the loop. -/
private theorem count_body_eq :
    countProc.body = .structured
      ([Core.Statement.set countY (countInitExpr) countParts.1] ++
        [.loop (.det countGuard) countParts.2.2.1 countParts.2.2.2.1 countInner
          countParts.2.2.2.2.2]) false := by
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
  [Core.Statement.set countY (countInitExpr) countParts.1] ++
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
    countOut.decls[0]? = some (.proc { countProc with body := .structured countTgt false } countMd)
        := by
  native_decide

/-! ## The triple of the loop-free body -/

/-- The postcondition `!(int.le(y, 9))` is the negated guard. -/
private theorem count_post_expr :
    ∀ lc ∈ countProc.spec.postconditions.toList,
      Core.eraseLocs lc.2.expr = Core.eraseLocs (HasBoolOps.not countGuard) := by
  have h : countProc.spec.postconditions.toList.all
      (fun lc => decide (Core.eraseLocs lc.2.expr = Core.eraseLocs (HasBoolOps.not countGuard))) = Bool.true := by
    native_decide
  intro lc hlc
  simpa using (List.all_eq_true.1 h) lc hlc

/-- Where the negated guard evaluates to `true`, the postcondition holds. -/
private theorem post_of_not_guard {ρ : Env Core.Expression} (hpin : Pinned ρ)
    (h : Core.Expression.eval ρ.factory ρ.store (HasBoolOps.not countGuard) =
      some (HasBool.ttVal ρ.factory)) :
    Core.Logic.Hoare.Procedure.contractPost Core.Factory countProc ρ := by
  intro label check hmem _ _
  refine .inl ⟨hpin, ?_⟩
  rw [← Core.Expression.eval_eraseLocs, count_post_expr _ hmem, Core.Expression.eval_eraseLocs]
  exact h

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
  refine ⟨countProc, by native_decide,
    Core.Procedure.forall_instance_of_typeArgs_nil (by native_decide) ⟨by native_decide, ?_⟩⟩
  rw [count_body_eq]
  -- The body proof does not use the axioms visible to the procedure.
  refine Core.Logic.Hoare.consequence _ _
    (Pre := Core.Logic.Hoare.Procedure.contractPre Core.Factory countProc) ?_
    (fun _ h => h.1) (fun _ h => h)
  obtain ⟨σ', hrun⟩ := count_run
  obtain ⟨ss', hd, htriple⟩ := Core.LoopElim.triple_coreProgram π testParams hrun count_decl
    count_body_eq
    (by simp [count_inner_eq, Core.Statements.noCalls, Block.allSubstmts_cons,
      Stmt.allSubstmts_loop, Stmt.allSubstmts_cmd, Block.allSubstmts_nil,
      Core.Statement.isNotCall, Core.Statement.set])
  rw [count_out_decl] at hd
  simp only [Option.some.injEq, Core.Decl.proc.injEq] at hd
  obtain rfl : countTgt = ss' := (Imperative.Body.structured.inj (congrArg (·.body) hd.1)).1
  exact block_rule (htriple (fun _ hpre => hpre.2.1) countTgt_triple)
    (by rw [count_inner_eq]; decide +kernel)

/-! ## A loop left by an `exit`

```
block L { while (true) { assert [A]: false; exit L; } }
```

The first iteration fails `A`, then leaves the loop, and the enclosing block, by `exit L`.
Loop elimination replaces the loop by a passive encoding that replays one iteration; a run of
that encoding ending the way the source's does need not run the iteration that fails `A`.  The
Hoare triple of the output still determines the source's, because the triple also checks the
assertions of executions that have not finished, and a finite execution of the output replays
the iteration up to `A`.

- `exitLoop_not_triple`: the source meets no triple from entries over `Core.Factory`: its
  execution that has just run `A` emits an assertion holding in no world.
- `exitLoop_loopElim`: the pass `Block.loopElim` succeeds on the source.
- `exitLoop_output_not_triple`: so its output meets no such triple either, by
  `Core.LoopElim.triple`, which asks nothing about how the loops of the source are left.

The statements are built as Lean terms, so every side condition is checked by
`decide +kernel`.
-/

/-- Empty metadata for every statement. -/
private def md0 : MetaData Core.Expression := #[]

/-- The literal `false`. -/
private def ffE : Core.Expression.Expr := Lambda.LExpr.boolConst Core.valueLoc false

/-- The literal `true`. -/
private def ttE : Core.Expression.Expr := Lambda.LExpr.boolConst Core.valueLoc true

/-- The loop body: assert `false`, then leave the block `L`. -/
private def loopBody : Core.Statements :=
  [Core.Statement.assert "A" ffE md0, Stmt.exit "L" md0]

/-- The loop `while (true) { assert [A]: false; exit L; }`. -/
private def loopStmt : Core.Statement := Stmt.loop (.det ttE) none [] loopBody md0

/-- The source: the loop inside the block `L`. -/
private def src : Core.Statements := [Stmt.block "L" [loopStmt] md0]

/-- The gate parameters of the source: those of the output with the label prefix of the blocks
    loop elimination mints reserved. -/
private def srcParams : Core.Logic.InitEnvWFParams :=
  testParams.extendBlockLabels [Core.loopElimPrefix]

/-- The environment with an empty store over the runtime factory of `model`. -/
private def emptyEnv (model : Lambda.Interp Core.Factory) : Env Core.Expression :=
  { store := fun _ => none, factory := boolFactory model }

/-- The source's gate admits `emptyEnv`: the source names no variable, and its label `L` does
    not start with the reserved prefix. -/
private theorem emptyEnv_blockWF (model : Lambda.Interp Core.Factory) :
    Core.Logic.BlockInitEnvWF srcParams src (emptyEnv model) :=
  Core.Logic.BlockInitEnvWF.of_defUseOk
    (Core.coreFactory_WellFormedSemanticEval _ rfl)
    (fun _ _ hn => by cases hn)
    (by intro n hn
        rw [show Block.definedVars (P := Core.Expression) (C := Core.Command) src false = []
          from by decide +kernel] at hn
        simp at hn)
    (by
      intro n hn p hp
      simp [srcParams, testParams, Imperative.Logic.InitEnvWFParams.extendBlockLabels] at hp)
    (by
      intro n hn p hp
      simp [srcParams, testParams, Imperative.Logic.InitEnvWFParams.extendBlockLabels] at hp)
    (by
      intro l hl p hp
      rw [show Block.labels (P := Core.Expression) (C := Core.Command) src = ["L"]
        from by decide +kernel] at hl
      simp only [List.mem_cons, List.not_mem_nil, or_false, srcParams,
        Imperative.Logic.InitEnvWFParams.extendBlockLabels, testParams, List.append_nil] at hl hp
      subst hl hp
      decide +kernel)
    (by
      show Block.defUseWellFormed (fun _ => false) srcParams.declaredFuncs src = true
      decide +kernel)
    (by intro nm _; rfl)
    (by intro f _; rfl)
    (by
      intro ty hty
      rw [show Block.initTypes (P := Core.Expression) (C := Core.Command) src = []
        from by decide +kernel] at hty
      simp at hty)
    ⟨(fun _ => none : VarTyping Core.Expression), ⟨(fun _ _ hty => nomatch hty),
      (Block.fvarTypesWellAnnotatedB_iff (P := Core.Expression) (C := Core.Command) _ _).1
        (by decide +kernel)⟩⟩
    (by
      intro m hm
      rw [show Block.measures (P := Core.Expression) (C := Core.Command) src = []
        from by decide +kernel] at hm
      simp at hm)

/-- From `emptyEnv`, the source enters the block and the loop, whose guard holds, and runs the
    `assert`, emitting it. -/
private theorem src_prefix (model : Lambda.Interp Core.Factory) :
    StepStmtStarE Core.Expression (Core.EvalCommandE π) (.stmts src (emptyEnv model))
      [Event.assert ⟨(emptyEnv model).factory, (emptyEnv model).store, "A", ffE, md0⟩]
      (.seq (.block (some "L") (emptyEnv model).store
        (.seq (.seq (.block .none (emptyEnv model).store
          (.seq (.terminal (emptyEnv model)) [Stmt.exit "L" md0])) [loopStmt]) [])) []) := by
  have hg : Core.Expression.eval (emptyEnv model).factory (emptyEnv model).store ttE =
      some (HasBool.ttVal (emptyEnv model).factory) :=
    Core.eval_boolConst _ _ true
  refine .step _ [] _ _ _ .step_stmts_cons ?_
  refine .step _ [] _ _ _ (.step_seq_inner .step_block) ?_
  refine .step _ [] _ _ _ (.step_seq_inner (.step_block_body .step_stmts_cons)) ?_
  refine .step _ [] _ _ _
    (.step_seq_inner (.step_block_body (.step_seq_inner (.step_loop_enter hg)))) ?_
  refine .step _ [] _ _ _ (.step_seq_inner (.step_block_body (.step_seq_inner
    (.step_seq_inner (.step_block_body .step_stmts_cons))))) ?_
  exact .step _ _ _ [] _ (.step_seq_inner (.step_block_body (.step_seq_inner (.step_seq_inner
    (.step_block_body (.step_seq_inner
      (.step_cmd (Core.EvalCommandE.cmd_sem Imperative.EvalCmdE.eval_assert))))))) :
      StepStmtE Core.Expression (Core.EvalCommandE π) _ _ _) (.refl _)

/-- **The source meets no triple** from the entries over `Core.Factory` that its gate admits,
    whatever the postcondition: the execution that has just run `A` emits the assertion
    `false`, which holds in no world. -/
theorem exitLoop_not_triple (Post : Env Core.Expression → Prop) :
    ¬ Core.Logic.Hoare.Triple π srcParams Pinned src Post := by
  obtain ⟨model⟩ := Core.factoryInterp_nonempty
  intro h
  have hvalid := (h (emptyEnv model) rfl (emptyEnv_blockWF model)).1 _ _ (src_prefix model)
  rcases hvalid.1 trivial (someValuation _) (fun _ hc => by simp at hc) with
    ⟨_, hex⟩ | ⟨hne, _⟩
  · change Core.Expression.eval (emptyEnv model).factory (emptyEnv model).store ffE =
      some (HasBool.ttVal (emptyEnv model).factory) at hex
    rw [show ffE = Lambda.LExpr.boolConst Core.valueLoc false from rfl,
      Core.eval_boolConst] at hex
    exact HasBool.ttVal_ne_ffVal _ (Option.some.inj hex).symm
  · exact hne rfl

/-- **Loop elimination succeeds on the source.** -/
theorem exitLoop_loopElim : ∃ ss', Imperative.Block.loopElim src = some ss' :=
  Option.isSome_iff_exists.mp (by decide +kernel)

/-- **The output of loop elimination meets no triple either.**  For every output `ss'` of
    `Block.loopElim` on the source, no triple of `ss'` holds from the entries over
    `Core.Factory` that its gate admits, since `Core.LoopElim.triple` would carry it back to the
    source. -/
theorem exitLoop_output_not_triple (Post : Env Core.Expression → Prop) (ss' : Core.Statements)
    (ht : Imperative.Block.loopElim src = some ss') :
    ¬ Core.Logic.Hoare.Triple π testParams Pinned ss' Post := fun h =>
  exitLoop_not_triple Post
    (Core.LoopElim.triple π testParams ht (by decide +kernel) (fun _ h => h) h)

end Strata.HoareAfterLoopElimTest
