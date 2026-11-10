/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import Strata.Languages.Core.ProgramProps
import Strata.Languages.Core
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.Languages.Core.IntEvalProps
import Strata.Transform.InsertLoopInvariantAssertsCoreCorrect
import StrataDDM.Integration.Lean.HashCommands

/-! # A loop's contract, proved on the form with its invariant and measure checked

`procedure Count(out y : int) spec { ensures !(int.le(y, 9)); }
 { y := 0; while (int.le(y, 9)) decreases int.sub(10, y) invariant int.le(y, 10)
   { y := int.add(y, 1); } }`

The pass `Core.insertLoopInvariantAsserts` inserting the checks of the loop's invariant and
measure turns the body into

```
y := 0;
assert [insertLoopInvAssert_entry_invariant_loop_0_0]: int.le(y, 10);
assume [insertLoopInvAssume_entry_invariant_loop_0_0]: int.le(y, 10);
while (int.le(y, 9)) {
  assume [insertLoopInvAssume_invariant_loop_0_0]: int.le(y, 10);
  var $__loop_measure_loop_0 : int := int.sub(10, y);
  assert [insertLoopInvAssert_measure_lb_loop_0]: !(int.lt($__loop_measure_loop_0, 0));
  y := int.add(y, 1);
  assert [insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0]: int.le(y, 10);
  assert [insertLoopInvAssert_measure_decrease_loop_0]:
    int.lt(int.sub(10, y), $__loop_measure_loop_0);
}
assume [insertLoopInvAssume_exit_invariant_loop_0_0]: int.le(y, 10);
assume [insertLoopInvAssume_exit_not_guard_loop_0]: !(int.le(y, 9));
```

whose triple follows from the structural rules and the while rule with the invariant
`y ≤ 10`, the measure checks holding by integer arithmetic.
`Core.InsertLoopInvAsserts.triple_coreProgram` carries the triple back to the original body, at
gate parameters reserving the prefix of the measure snapshot variables
(`InsertLoopInvAsserts.prefixesReserved`), and the block rule wraps it in the procedure block.

The steps that inspect the translated procedure, or the output of running the pass on it, use
`native_decide`: `count_body_eq`, `countRun_ok`, `count_decl`, `count_out_decl`, the four
`*_shape` theorems, `count_post_expr`, and the procedure lookup and `contractChecksTyped`
premises of `count_meets_contract`.  The procedure's statements, expressions and contract come
from `translateStmt`, `translateExpr` and `translateSpec`, which are `partial`, so the kernel
cannot reduce them and `decide +kernel` gets stuck on these steps.  The other side conditions
(the `definedVars` premises, `postWF_of_definedVars_nil` and the `noCalls` premise of
`triple_coreProgram`) are checked by `decide +kernel` or `simp`.
-/

open Imperative
open StrataDDM (Program)

namespace Strata.HoareAfterInsertLoopInvTest

/-- Translate a DDM concrete-syntax program to the Core AST. -/
private def cstToAST (p : Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- Gate parameters: no reserved fresh-prefixes, and every name counts as declared. -/
private def testParams : Core.Logic.InitEnvWFParams := ⟨[], [], fun _ => true⟩

/-- The gate parameters of the source: `testParams` with the prefix of the measure snapshot
    variables reserved. -/
private def srcParams : Core.Logic.InitEnvWFParams :=
  testParams.extend InsertLoopInvAsserts.prefixesReserved

private def countPgm : Program :=
#strata
program Core;

procedure Count(out y : int)
spec {
  ensures !(int.le(y, 9));
}
{
  y := 0;
  while (int.le(y, 9))
    decreases int.sub(10, y)
    invariant int.le(y, 10)
  {
    y := int.add(y, 1);
  }
};
#end

private def countPgmAST : Core.Program := cstToAST countPgm

private abbrev π : String → Option Core.Procedure := countPgmAST.findProcByString?

private def countProc : Core.Procedure := (π "Count").get!

private def countY : Core.Expression.Ident := ⟨"y", ()⟩

/-- The parts of the translated body. -/
private structure Parts where
  /-- The metadata of `y := 0`. -/
  md0 : MetaData Core.Expression
  /-- The guard `int.le(y, 9)`. -/
  guard : Core.Expression.Expr
  /-- The measure `int.sub(10, y)`. -/
  measure : Core.Expression.Expr
  /-- The label of the invariant. -/
  invLabel : String
  /-- The invariant `int.le(y, 10)`. -/
  inv : Core.Expression.Expr
  /-- The right-hand side `int.add(y, 1)` of the body's assignment. -/
  rhs : Core.Expression.Expr
  /-- The metadata of the body's assignment. -/
  md2 : MetaData Core.Expression
  /-- The metadata of the loop. -/
  md1 : MetaData Core.Expression
  deriving Inhabited

/-- The parts of the translated body, projected out of the AST. -/
private def parts : Parts :=
  match countProc.body with
  | .structured [Stmt.cmd (CmdExt.cmd (Cmd.set _ _ md0)),
      Stmt.loop (.det g) (some m) [(l, i)] [Stmt.cmd (CmdExt.cmd (Cmd.set _ (.det e) md2))]
        md1] => ⟨md0, g, m, l, i, e, md2, md1⟩
  | _ => default

/-- The initialisation `y := 0`. -/
private abbrev countInit : Core.Statement :=
  Core.Statement.set countY (Lambda.LExpr.const () (.intConst 0)) parts.md0

/-- The body's assignment `y := int.add(y, 1)`. -/
private abbrev countSet : Core.Statement := Core.Statement.set countY parts.rhs parts.md2

/-- The translated body really is the initialisation followed by the loop. -/
private theorem count_body_eq :
    countProc.body = .structured ([countInit] ++
      [.loop (.det parts.guard) (some parts.measure) [(parts.invLabel, parts.inv)] [countSet]
        parts.md1]) := by
  native_decide

/-! ## The checked body -/

/-- The measure snapshot variable. -/
private abbrev mId : Core.Expression.Ident :=
  InsertLoopInvAsserts.measureIdent (P := Core.Expression) "loop_0"

/-- The metadata of the invariant's checks. -/
private abbrev imd : MetaData Core.Expression := parts.md1.invariantMd 0

/-- The non-negativity check of the measure snapshot. -/
private abbrev lbExpr : Core.Expression.Expr :=
  InsertLoopInvAsserts.lbExpr (P := Core.Expression) "loop_0"

/-- The decrease check of the measure. -/
private abbrev decExpr : Core.Expression.Expr :=
  InsertLoopInvAsserts.decExpr (P := Core.Expression) "loop_0" parts.measure

/-- The body of the checked loop. -/
private def tgtBody : Core.Statements :=
  [.cmd (HasPassiveCmds.assume "insertLoopInvAssume_invariant_loop_0_0" parts.inv imd)] ++
  ([.cmd (HasInit.init mId HasInt.intTy (.det parts.measure) parts.md1)] ++
  ([.cmd (HasPassiveCmds.assert "insertLoopInvAssert_measure_lb_loop_0" lbExpr parts.md1)] ++
  ([countSet] ++
  ([.cmd (HasPassiveCmds.assert
      "insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0" parts.inv imd)] ++
  [.cmd (HasPassiveCmds.assert "insertLoopInvAssert_measure_decrease_loop_0" decExpr
      parts.md1)]))))

/-- The statements after `y := 0` of the checked body. -/
private def tgtLoop : Core.Statements :=
  [.cmd (HasPassiveCmds.assert "insertLoopInvAssert_entry_invariant_loop_0_0" parts.inv imd)] ++
  ([.cmd (HasPassiveCmds.assume "insertLoopInvAssume_entry_invariant_loop_0_0" parts.inv imd)] ++
  ([.loop (.det parts.guard) none [] tgtBody parts.md1] ++
  ([.cmd (HasPassiveCmds.assume "insertLoopInvAssume_exit_invariant_loop_0_0" parts.inv imd)] ++
  [.cmd (HasPassiveCmds.assume "insertLoopInvAssume_exit_not_guard_loop_0"
      (HasBoolOps.not parts.guard) parts.md1)])))

/-- The run of the Core pass on the program, from the empty transformation state. -/
private def countRun :=
  Core.insertLoopInvariantAsserts countPgmAST Core.Transform.CoreTransformState.emp

/-- The program the Core pass returns. -/
private def countOut : Core.Program := match countRun.1 with
  | .ok r => r.2
  | .error _ => default

/-- The Core pass succeeds on the program. -/
private theorem countRun_ok : ∃ c σ', countRun = (.ok (c, countOut), σ') := by
  have h : (match countRun.1 with | .ok _ => true | .error _ => false) = true := by
    native_decide
  unfold countOut
  revert h
  generalize countRun = r
  obtain ⟨_ | ⟨c, q⟩, σ'⟩ := r
  · intro h; cases h
  · intro _; exact ⟨c, σ', rfl⟩

/-- The metadata of the declaration of the procedure. -/
private def countDeclMd : MetaData Core.Expression :=
  match countPgmAST.decls[0]? with
  | some (Core.Decl.proc _ md) => md
  | _ => default

/-- The procedure is the first declaration of the program. -/
private theorem count_decl : countPgmAST.decls[0]? = some (.proc countProc countDeclMd) := by
  native_decide

/-- The Core pass turns the procedure body into `countInit` followed by `tgtLoop`. -/
private theorem count_out_decl : countOut.decls[0]? =
    some (.proc { countProc with body := .structured ([countInit] ++ tgtLoop) } countDeclMd) := by
  native_decide

/-! ## Evaluating the conditions -/

/-- The integer type, as variables are annotated with it. -/
private abbrev intMono : Lambda.LMonoTy := .tcons "int" []

/-- The guard is `int.le(y, 9)` in `Core.Factory`'s operator form. -/
private theorem guard_shape :
    parts.guard = .app () (.app () Core.intLeOp (.fvar () countY (some intMono)))
      (.intConst () 9) := by native_decide

/-- The invariant is `int.le(y, 10)` in `Core.Factory`'s operator form. -/
private theorem inv_shape :
    parts.inv = .app () (.app () Core.intLeOp (.fvar () countY (some intMono)))
      (.intConst () 10) := by native_decide

/-- The measure is `int.sub(10, y)` in `Core.Factory`'s operator form. -/
private theorem measure_shape :
    parts.measure = .app () (.app () Core.intSubOp (.intConst () 10))
      (.fvar () countY (some intMono)) := by native_decide

/-- The increment is `int.add(y, 1)` in `Core.Factory`'s operator form. -/
private theorem rhs_shape :
    parts.rhs = .app () (.app () Core.intAddOp (.fvar () countY (some intMono)))
      (.intConst () 1) := by native_decide

/-- The runtime factory's functions are those of `Core.Factory`. -/
private abbrev Pinned (ρ : Env Core.Expression) : Prop := ρ.factory.factory = Core.Factory

/-- The integer `n` under the runtime factory `f`. -/
private abbrev int (f : Core.Expression.Factory) (n : Int) : Core.Expression.Val :=
  Lambda.SemValue.ofInt f.model.tcInterp n

section Eval

variable {f : Core.Expression.Factory} (hf : f.factory = Core.Factory) {σ : Core.CoreStore}
include hf

/-- With `y ↦ n`, the guard evaluates to `n ≤ 9`. -/
private theorem guard_eval {n : Int} (hy : σ countY = some (int f n)) :
    Core.Expression.eval f σ parts.guard =
      some (Lambda.SemValue.ofBool f.model.tcInterp (decide (n ≤ 9))) := by
  rw [guard_shape]
  exact Core.eval_intLe (hf ▸ Core.coreFactory_intLe) (Core.eval_fvar_int f hy)
    (Core.eval_intConst f σ 9)

/-- With `y ↦ n` and `n ≤ 10`, the invariant evaluates to `true`. -/
private theorem inv_eval {n : Int} (hy : σ countY = some (int f n)) (hn : n ≤ 10) :
    Core.Expression.eval f σ parts.inv = some (HasBool.ttVal f) := by
  rw [inv_shape, Core.eval_intLe (hf ▸ Core.coreFactory_intLe) (Core.eval_fvar_int f hy)
    (Core.eval_intConst f σ 10), decide_eq_true hn]
  rfl

/-- With `y ↦ n`, the measure evaluates to `10 - n`. -/
private theorem measure_eval {n : Int} (hy : σ countY = some (int f n)) :
    Core.Expression.eval f σ parts.measure = some (int f (10 - n)) := by
  rw [measure_shape]
  exact Core.eval_intSub (hf ▸ Core.coreFactory_intSub) (Core.eval_intConst f σ 10)
    (Core.eval_fvar_int f hy)

/-- With `y ↦ n`, the increment evaluates to `n + 1`. -/
private theorem rhs_eval {n : Int} (hy : σ countY = some (int f n)) :
    Core.Expression.eval f σ parts.rhs = some (int f (n + 1)) := by
  rw [rhs_shape]
  exact Core.eval_intAdd (hf ▸ Core.coreFactory_intAdd) (Core.eval_fvar_int f hy)
    (Core.eval_intConst f σ 1)

/-- With the snapshot holding a non-negative `k`, its non-negativity check evaluates to
    `true`. -/
private theorem lb_eval {k : Int} (hm : σ mId = some (int f k)) (hk : 0 ≤ k) :
    Core.Expression.eval f σ lbExpr = some (HasBool.ttVal f) := by
  have hbool := Core.coreEvaluator_WellFormedSemanticEvalBool f (hf ▸ Core.coreFactory_boolNot)
  refine (hbool σ _).2.1 ((Core.eval_intLt (hf ▸ Core.coreFactory_intLt)
    (Core.eval_fvar_int f hm) (Core.eval_intConst f σ 0)).trans ?_)
  rw [decide_eq_false (by omega)]
  rfl

/-- With `y ↦ n` and the snapshot holding `k > 10 - n`, the decrease check evaluates to
    `true`. -/
private theorem dec_eval {n k : Int} (hy : σ countY = some (int f n))
    (hm : σ mId = some (int f k)) (hk : 10 - n < k) :
    Core.Expression.eval f σ decExpr = some (HasBool.ttVal f) := by
  refine (Core.eval_intLt (hf ▸ Core.coreFactory_intLt) (measure_eval hf hy)
    (Core.eval_fvar_int f hm)).trans ?_
  rw [decide_eq_true hk]
  rfl

end Eval

/-! ## Rules for the commands of the checked body -/

/-- The statements before the next ones exit to no label. -/
local macro "covered" : tactic =>
  `(tactic| simp [Block.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks])

/-- An assumption keeps a precondition that pins the runtime factory. -/
private theorem assume_keep (l : String) (e : Core.Expression.Expr)
    (md : MetaData Core.Expression) {Pre : Env Core.Expression → Prop} :
    Core.Logic.Hoare.Triple π testParams Pre [.cmd (HasPassiveCmds.assume l e md)] Pre := by
  refine Core.Logic.Hoare.cmd π testParams _ Pre Pre (fun ρ₀ σ' emitted hρ _ hstep => ?_)
  cases hstep with
  | cmd_sem hbase =>
    cases hbase with
    | eval_assume =>
      exact ⟨by simp [Trace.AssertionsValid, Trace.AssertionsValidFromP], fun _ => hρ⟩

/-- An assumption keeps the runtime factory and, when reachable, holds. -/
private theorem assume_rule (l : String) (e : Core.Expression.Expr)
    (md : MetaData Core.Expression) {Pre Post : Env Core.Expression → Prop}
    (hpin : ∀ ρ, Pre ρ → Pinned ρ)
    (hpost : ∀ ρ, Pre ρ → Core.Expression.eval ρ.factory ρ.store e =
      some (HasBool.ttVal ρ.factory) → Post ρ) :
    Core.Logic.Hoare.Triple π testParams Pre [.cmd (HasPassiveCmds.assume l e md)] Post := by
  refine Core.Logic.Hoare.cmd π testParams _ _ Post (fun ρ₀ σ' emitted hρ _ hstep => ?_)
  cases hstep with
  | cmd_sem hbase =>
    cases hbase with
    | eval_assume =>
      refine ⟨by simp [Trace.AssertionsValid, Trace.AssertionsValidFromP], fun ⟨w, hw⟩ => ?_⟩
      rcases hw _ (List.mem_singleton_self _) with ⟨_, he⟩ | ⟨hne, _⟩
      · exact hpost ρ₀ hρ he
      · exact absurd (hpin ρ₀ hρ) hne

/-- An assertion that evaluates to `true` under a precondition pinning the runtime factory is
    valid, and keeps the precondition. -/
private theorem assert_rule (l : String) (e : Core.Expression.Expr)
    (md : MetaData Core.Expression) {Pre : Env Core.Expression → Prop}
    (hpin : ∀ ρ, Pre ρ → Pinned ρ)
    (hv : ∀ ρ, Pre ρ → Core.Expression.eval ρ.factory ρ.store e =
      some (HasBool.ttVal ρ.factory)) :
    Core.Logic.Hoare.Triple π testParams Pre [.cmd (HasPassiveCmds.assert l e md)] Pre := by
  refine Core.Logic.Hoare.cmd π testParams _ Pre Pre (fun ρ₀ σ' emitted hρ _ hstep => ?_)
  cases hstep with
  | cmd_sem hbase =>
    cases hbase with
    | eval_assert =>
      exact ⟨⟨fun _ _ _ => .inl ⟨hpin ρ₀ hρ, hv ρ₀ hρ⟩, trivial⟩, fun _ => hρ⟩

/-! ## The triple of the checked body -/

/-- `y` holds the integer `n`. -/
private abbrev YIs (n : Int) (ρ : Env Core.Expression) : Prop :=
  ρ.store countY = some (int ρ.factory n)

/-- `$__loop_measure_loop_0` holds the integer `k`. -/
private abbrev MIs (k : Int) (ρ : Env Core.Expression) : Prop :=
  ρ.store mId = some (int ρ.factory k)

/-- The loop invariant of the while rule: `y` holds an integer at most `10`. -/
private abbrev Inv (ρ : Env Core.Expression) : Prop :=
  Pinned ρ ∧ ∃ n, YIs n ρ ∧ n ≤ 10

/-- At the start of an iteration: `y` holds an integer at most `9`. -/
private abbrev Iter (ρ : Env Core.Expression) : Prop :=
  Pinned ρ ∧ ∃ n, YIs n ρ ∧ n ≤ 9

/-- After the measure snapshot: it holds `10 - n` where `y` holds `n`. -/
private abbrev Snap (ρ : Env Core.Expression) : Prop :=
  Pinned ρ ∧ ∃ n, YIs n ρ ∧ MIs (10 - n) ρ ∧ n ≤ 9

/-- After the increment: `y` holds `n + 1` where the snapshot holds `10 - n`. -/
private abbrev Incr (ρ : Env Core.Expression) : Prop :=
  Pinned ρ ∧ ∃ n, YIs (n + 1) ρ ∧ MIs (10 - n) ρ ∧ n ≤ 9

/-- The measure snapshot variable is not `y`. -/
private theorem mId_ne_y : mId ≠ countY := by decide

/-- The body of the checked loop keeps the invariant. -/
private theorem tgtBody_triple :
    Core.Logic.Hoare.Triple π testParams
      (fun ρ => Inv ρ ∧ Core.Expression.eval ρ.factory ρ.store parts.guard =
        some (HasBool.ttVal ρ.factory)) tgtBody Inv := by
  refine Core.Logic.Hoare.consequence π testParams (Pre := Iter) (Post := Incr) ?_
    (fun ρ ⟨⟨hp, n, hy, _⟩, hg⟩ => ⟨hp, n, hy, ?_⟩)
    (fun ρ ⟨hp, n, hy, _, hn⟩ => ⟨hp, n + 1, hy, by omega⟩)
  · refine Core.Logic.Hoare.seq π testParams (assume_keep _ _ _) ?_ (by covered)
    refine Core.Logic.Hoare.seq π testParams (Mid := Snap) ?_ ?_ (by covered)
    · refine Core.Logic.Hoare.init π testParams _ _ _ _ _ _
        (fun ρ₀ σ' v ⟨hp, n, hy, hn⟩ hev hinit => ?_)
      cases hinit with
      | init _ hnew hoth =>
        rw [measure_eval hp hy] at hev
        cases hev
        exact ⟨hp, n, (hoth _ mId_ne_y).trans hy, hnew, hn⟩
    refine Core.Logic.Hoare.seq π testParams
      (assert_rule _ _ _ (fun _ h => h.1) fun ρ ⟨hp, n, _, hm, hn⟩ => lb_eval hp hm (by omega))
      ?_ (by covered)
    refine Core.Logic.Hoare.seq π testParams (Mid := Incr) ?_ ?_ (by covered)
    · refine Core.Logic.Hoare.set π testParams _ _ _ _ _
        (fun ρ₀ σ' v ⟨hp, n, hy, hm, hn⟩ hev hup => ?_)
      cases hup with
      | update _ hnew hoth =>
        rw [rhs_eval hp hy] at hev
        cases hev
        exact ⟨hp, n, hnew, (hoth _ mId_ne_y.symm).trans hm, hn⟩
    refine Core.Logic.Hoare.seq π testParams
      (assert_rule _ _ _ (fun _ h => h.1) fun ρ ⟨hp, n, hy, _, hn⟩ =>
        inv_eval hp hy (by omega)) ?_ (by covered)
    exact assert_rule _ _ _ (fun _ h => h.1) fun ρ ⟨hp, n, hy, hm, _⟩ =>
      dec_eval hp hy hm (by omega)
  · have h := hg
    rw [guard_eval hp hy] at h
    exact of_decide_eq_true (Lambda.SemValue.ofBool_injective (Option.some.inj h))

/-- The postcondition `!(int.le(y, 9))` is the negated guard. -/
private theorem count_post_expr :
    ∀ lc ∈ countProc.spec.postconditions.toList, lc.2.expr = HasBoolOps.not parts.guard := by
  have h : countProc.spec.postconditions.toList.all
      (fun lc => decide (lc.2.expr = HasBoolOps.not parts.guard)) = Bool.true := by
    native_decide
  intro lc hlc
  simpa using (List.all_eq_true.1 h) lc hlc

/-- **The checked body meets the contract.** -/
private theorem countTgt_triple :
    Core.Logic.Hoare.Triple π testParams
      (Core.Logic.Hoare.Procedure.contractPre Core.Factory countProc) ([countInit] ++ tgtLoop)
      (Core.Logic.Hoare.Procedure.contractPost Core.Factory countProc) := by
  refine Core.Logic.Hoare.seq π testParams (Mid := fun ρ => Pinned ρ ∧ YIs 0 ρ) ?_ ?_
    (by covered)
  · refine Core.Logic.Hoare.set π testParams _ _ _ _ _
      (fun ρ₀ σ' v hρ hev hup => ?_)
    cases hup with
    | update _ hnew _ =>
      rw [show (Lambda.LExpr.const () (.intConst 0) : Core.Expression.Expr) = .intConst () 0
        from rfl, Core.eval_intConst] at hev
      cases hev
      exact ⟨hρ.2.1, hnew⟩
  refine Core.Logic.Hoare.seq π testParams
    (assert_rule _ _ _ (fun _ h => h.1) fun ρ ⟨hp, hy⟩ => inv_eval hp hy (by omega)) ?_
    (by covered)
  refine Core.Logic.Hoare.seq π testParams (assume_keep _ _ _) ?_ (by covered)
  refine Core.Logic.Hoare.seq π testParams (Mid := fun ρ => Inv ρ ∧
      Core.Expression.eval ρ.factory ρ.store parts.guard = some (HasBool.ffVal ρ.factory))
    ?_ ?_ (by simp [tgtBody, Block.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks])
  · refine Core.Logic.Hoare.consequence π testParams
      (Core.Logic.Hoare.while_rule π testParams tgtBody_triple
        (by simp [tgtBody, Block.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks]) ?_)
      (fun ρ ⟨hp, hy⟩ => ⟨hp, 0, hy, by omega⟩) (fun _ h => h)
    intro ρ ⟨hp, n, hy, hn⟩
    refine ⟨hp, n, ?_, hn⟩
    have hd : countY ∉ Block.definedVars (P := Core.Expression) (C := Core.Command)
        tgtBody true := by decide +kernel
    change (if countY ∈ Block.definedVars (P := Core.Expression) (C := Core.Command) tgtBody true
      then none else ρ.store countY) = _
    simp only [hd, ↓reduceIte]
    exact hy
  refine Core.Logic.Hoare.seq π testParams (assume_keep _ _ _) ?_ (by covered)
  refine assume_rule _ _ _ (fun _ h => h.1.1) fun ρ ⟨⟨hp, _⟩, _⟩ he => ?_
  intro label check hmem _ _
  exact .inl ⟨hp, by rw [count_post_expr _ hmem]; exact he⟩

/-! ## Back to the loop -/

/-- **The loop meets its contract**, from the triple of the body the Core pass returns
    (`Core.InsertLoopInvAsserts.triple_coreProgram`), inside the procedure block. -/
theorem count_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple countPgmAST srcParams "Count" := by
  have hfactory : countPgmAST.factoryBeforeProcedure "Count" = Core.Factory :=
    Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by decide +kernel)
  rw [Core.Logic.Hoare.Procedure.contractTriple, hfactory]
  refine ⟨countProc, by native_decide, by native_decide, ?_⟩
  obtain ⟨_, _, hrun⟩ := countRun_ok
  obtain ⟨ss', hd, htriple⟩ := Core.InsertLoopInvAsserts.triple_coreProgram π testParams
    (fun _ h => by simp [testParams] at h) Core.CoreGenState.wf_emp hrun count_decl count_body_eq
    (by simp [Core.Statements.noCalls, Block.allSubstmts_cons, Stmt.allSubstmts_loop,
      Stmt.allSubstmts_cmd, Block.allSubstmts_nil, Core.Statement.isNotCall])
  rw [count_out_decl] at hd
  have hss' : ss' = [countInit] ++ tgtLoop := by
    injection hd with hd
    injection hd with hd
    have hb := congrArg (fun q : Core.Procedure => q.body) hd
    injection hb with hb
    exact hb.symm
  subst hss'
  rw [count_body_eq]
  exact Core.Logic.Hoare.block π srcParams (htriple (fun _ hpre => hpre.2.1) countTgt_triple)
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide +kernel))

end Strata.HoareAfterInsertLoopInvTest
