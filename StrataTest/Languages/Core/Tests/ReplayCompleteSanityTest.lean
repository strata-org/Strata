/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.InterpreterCallComplete
import Strata.Languages.Core.InterpreterComplete
import Strata.Languages.Core.InstWellFormedSemanticsEval
import all Strata.Languages.Core.Interpreter
import all Strata.Languages.Core.InterpreterReplay
import all Strata.DL.Imperative.InterpreterCall
import all Strata.DL.Imperative.InterpreterCallComplete
import all Strata.DL.Imperative.StmtCFGCallSemantics
import Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Imperative.Stmt
import all Strata.Languages.Core.InterpreterCallSound
import all Strata.Languages.Core.StatementSemantics
import all Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.InterpreterSound
import all Strata.Languages.Core.InterpreterSound
import Strata.Languages.Core.InterpreterReplayTactics
import Strata.Languages.Core.InterpreterProps
import Strata.Languages.Core.Logic.FactoryInterp
import Strata.Languages.Core.FactoryWF
import Strata.Languages.Core.InterpreterDomainProps

/-! # The premises of `core_replayComplete` and `core_replaySound` are satisfiable

Two concrete instances:
- `wGenuine`: `call w()` whose callee body is `assert fail : false`, a run that resolves no
  choice, with an empty oracle; every premise of `core_replayComplete` is discharged, over Core's
  factory modeled by `Core.factoryInterp` (`M0`);
- `hGenuine`: `if * then call h()` whose callee body is `init b : bool := *; assert neg : b`,
  a run that takes the then-branch of a nondeterministic `ite` in the caller and has the
  callee's nondeterministic `init` write `ff`, replayed with the oracle `[tt, ff]`; every premise
  of `core_replayComplete` is discharged at `M0`. Every value the engine commits for `b` is the
  literal `false` up to metadata because over Core's factory every runtime value denoting a
  Boolean is a Boolean literal (`denotes_boolConst`).

One instance with every premise of `core_replaySound` discharged: a call configuration
`call w(x; y)` over Core's factory whose callee body is `b := a` (`replaySound_wit`). -/

namespace ReplayCompleteSanityTest

open Core Imperative

private def md : MetaData Expression := #[]
private def ffE : Expression.Expr := .boolConst () false

/-- Core's factory, modeled by its interpretation `Core.factoryInterp`: the factory the
    counterexamples below are replayed at. -/
private noncomputable def M0 : Expression.Factory :=
  ⟨Core.Factory, Core.factoryInterp, fun _ => .bool⟩

/-! ## A run that resolves no choice -/

/-- The literal `false` evaluates to `ffVal` on every store. -/
private theorem ffE_denote (F : Expression.Factory) (σ : SemanticStore Expression) :
    Expression.eval F σ ffE = some (HasBool.ffVal F) :=
  Lambda.LExpr.denoteEval_boolConst

/-- The engine's evaluator leaves the literal `false` unchanged at every fuel. -/
private theorem ffE_eval (n : Nat) (F : Lambda.Factory CoreLParams) (σr : RStore Expression) :
    Lambda.LExpr.eval n F σr ffE = (ffE, .value true) :=
  Lambda.eval_value_identity n F σr ffE (Lambda.isValue_const_true ..)

/-- The callee: no formals, no spec clauses, body `assert fail : false`. -/
def wProc : Procedure :=
  { header := { name := ⟨"w", ()⟩, typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [.cmd (.cmd (.assert "fail" ffE md))] }

/-- The procedure table: `"w"` resolves to `wProc`. -/
def wPi : String → Option Procedure := fun n => if n = "w" then some wProc else none

/-- The caller environment: the empty store over Core's factory. -/
def wEnv : Imperative.IEnv Expression :=
  .ofStore (fun _ => none) Core.Factory

/-- The counterexample: the call, with an empty oracle. -/
def wCex : CexA Expression Command :=
  { cfg := .stmts [.cmd (.call "w" [] md)] wEnv, oracle := [] }

/-- The target: the callee's assert. -/
def wTarget : AssertId Expression := { label := "fail", md := md }

/-- The reference semantics has a run of `wCex.cfg`, stopped right after the call, that resolves
    no nondeterministic choice and emits an assert event of the callee's `assert fail : false`
    whose condition the reference evaluator and the engine evaluate to false
    (`Calls.assertFailureE`). -/
private theorem wRun (F : Expression.Factory) :
    ∃ evs final, Calls.RunChoices wPi (wCex.cfg.abs F) evs final [] ∧
      ∃ ev ∈ evs, Calls.assertFailureE wTarget ev := by
  refine ⟨_, _, ⟨1, fun rest =>
    .step _ _ _ _ _ (.step_det .step_stmts_cons)
    (.step _ _ _ _ _ (.step_seq_inner (.step_cmd (.inr (.inl
      ⟨"w", wProc, [], md, _, _, _, _, rfl, rfl, rfl,
        ⟨[], [], .eval_none, .read_none, ⟨_, _, .init_none, .init_none, rfl⟩⟩,
        .step _ _ _ _ _ (.step_det .step_block)
          (.step _ _ _ _ _ (.step_det (.step_block_body .step_stmts_cons))
          (.step _ _ _ _ _ (.step_block_body (.step_seq_inner (.step_cmd
            ⟨_, rfl, .eval_assert, .inl ⟨rfl, rfl⟩⟩)))
          (.step _ _ _ _ _ (.step_det (.step_block_body .step_seq_done))
          (.step _ _ _ _ _ (.step_det (.step_block_body .step_stmts_nil))
          (.step _ _ _ _ _ (.step_det .step_block_done) (.refl _)))))),
        ⟨List.nodup_nil, [], .read_none, .update_none, .nil⟩, rfl, nofun,
        fun _ _ _ _ _ _ h _ => by cases h; rfl⟩))))
    (.refl _))⟩, .assert ⟨F,
      Calls.withOldSnapshots (Calls.inoutParams wProc.header) emptyStore, "fail", ffE, md⟩,
    by simp [Calls.defaultAssertEvents, wProc, IEnv.abs], rfl, rfl, ffE_denote F _,
    fun σr v _ hv => ⟨0, ffE, evalBounded_eq_some_iff.2 ⟨evalTypedDomain_const .., ffE_eval ..,
      typeCheckWith_const .., rfl⟩, denotes_literal ((ffE_denote F _).trans
        ((ffE_denote F _).symm.trans hv))⟩,
    fun σr n r _ h => (Prod.mk.inj ((ffE_eval ..).symm.trans
      (evalBounded_eq_some_iff.1 h).2.1)).1 ▸ rfl⟩

/-- Replaying `wCex` with its own (empty) oracle reaches the callee's failing assert at every
    sufficiently large fuel and call-depth limit, so the replay verdict is `genuine`. -/
theorem wGenuine :
    ∃ f0, ∀ fuel d, f0 ≤ fuel → f0 ≤ d → genuine wPi wTarget fuel wCex d := by
  obtain ⟨_, _, hrun, hfail⟩ := wRun M0
  exact core_replayComplete wPi wTarget wCex
    (show IConfig.Denoting M0 (.stmts _ wEnv) from ⟨by simp [wEnv, IEnv.ofStore,
      RStore.Denoting, IStore.get, IStore.ofStore, InterpLang.writesFind?_empty], rfl⟩)
    trivial hrun [] List.nil_prefix ⟨rfl, nofun⟩ nofun hfail

/-! ## A run that resolves a nondeterministic guard and a nondeterministic `init` -/

private def bId : Expression.Ident := ⟨"b", ()⟩
private def bE : Expression.Expr := .fvar () bId none

/-- The callee: no formals, no spec clauses, body `init b : bool := *; assert neg : b`. -/
def hProc : Procedure :=
  { header := { name := ⟨"h", ()⟩, typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [.cmd (.cmd (.init bId HasBool.boolTy .nondet md)),
      .cmd (.cmd (.assert "neg" bE md))] }

/-- The procedure table: `"h"` resolves to `hProc`. -/
def hPi : String → Option Procedure := fun n => if n = "h" then some hProc else none

/-- The caller environment: the empty store over Core's factory. -/
def hEnv : Imperative.IEnv Expression :=
  .ofStore (fun _ => none) Core.Factory

/-- The counterexample: `if * then call h()`, with the oracle `[tt, ff]`: `tt` takes the
    then-branch, `ff` is the value the callee's `init b` writes. -/
def hCex : CexA Expression Command :=
  { cfg := .stmts [.ite .nondet [.cmd (.call "h" [] md)] [] md] hEnv,
    oracle := [HasBool.tt, HasBool.ff] }

/-- The target: the callee's assert. -/
def hTarget : AssertId Expression := { label := "neg", md := md }

/-- A runtime value denoting `ffVal` over Core's factory is the literal `false` up to metadata. -/
private theorem ff_of_denotes (F : Expression.Factory) (hF : F.factory = Core.Factory)
    (r : Expression.Expr) (hd : InterpLang.Denotes F r (HasBool.ffVal F)) :
    InterpLang.eqModuloMeta r HasBool.ff := by
  obtain ⟨m, c, rfl⟩ := denotes_boolConst (hF ▸ Factory_constrsNotBool) hd rfl
  cases c
  · rfl
  · exact (HasBool.ttVal_ne_ffVal (P := Expression) F (Option.some.inj
      ((Lambda.LExpr.denoteEval_boolConst (T := CoreLParams)).symm.trans
        (denotes_iff.1 hd).2.2))).elim

/-- Every value the engine commits for `b` is the value `b` holds in the runtime store. -/
private theorem bE_eval (F : Lambda.Factory CoreLParams) (σr : RStore Expression) (n : Nat)
    (r : Expression.Expr) (h : evalBounded n F σr bE = some r) : σr bId = some r := by
  have h2 := (evalBounded_eq_some_iff.1 h).2.1
  have hbv : Lambda.LExpr.isValue F (.fvar () bId none : Expression.Expr) = false := by
    rw [Lambda.LExpr.isValue.eq_def]; rfl
  cases n <;> cases hσ : σr bId <;>
    simp_all [Lambda.LExpr.eval, Lambda.LExpr.evalCore, Lambda.Factory.callOfLFunc,
      Lambda.getLFuncCall, Lambda.getLFuncCall.go, bE]

/-- The callee's entry frame. -/
private def hFrame : SemanticStore Expression :=
  Calls.withOldSnapshots (Calls.inoutParams hProc.header) emptyStore

/-- The callee's store after `init b : bool := *` writes `ffVal F`. -/
def hStore (F : Expression.Factory) : SemanticStore Expression :=
  SemanticStore.update hFrame bId (HasBool.ffVal F)

/-- The reference evaluator evaluates `b` to `ffVal` on `hStore F`. -/
private theorem hAssert_denote (F : Expression.Factory) :
    Expression.eval F (hStore F) bE = some (HasBool.ffVal F) :=
  Lambda.LExpr.denoteEval_fvar (by simp [hStore, SemanticStore.update]) rfl

/-- Over Core's factory, on every runtime store denoting `hStore F`, the engine evaluates `b` at
    fuel 1 to the runtime value of `b`, which denotes `ffVal`. -/
private theorem hAssert_eval (F : Expression.Factory) (hF : F.factory = Core.Factory)
    (σr : RStore Expression) (hS : StoreDenotes F σr (hStore F)) :
    ∃ r, evalBounded 1 F.factory σr bE = some r ∧ InterpLang.Denotes F r (HasBool.ffVal F) := by
  have hb : hStore F bId = some (HasBool.ffVal F) := by simp [hStore, SemanticStore.update]
  obtain ⟨rb, hr⟩ : ∃ rb, σr bId = some rb :=
    Option.ne_none_iff_exists'.1 fun h => by simp [(hS.1 bId).2 h] at hb
  have hd := hS.2 bId rb _ hr hb
  obtain ⟨m, c, rfl⟩ := denotes_boolConst (hF ▸ Factory_constrsNotBool) hd rfl
  refine ⟨_, evalBounded_eq_some_iff.2 ⟨(evalTypedDomain_iff hS _).2 ⟨_, hAssert_denote F⟩, ?_,
    rfl, evalOpsChecked_fvar hr rfl⟩, hd⟩
  have hbv : Lambda.LExpr.isValue F.factory (.fvar () bId none : Expression.Expr) = false := by
    rw [Lambda.LExpr.isValue.eq_def]; rfl
  simp [Lambda.LExpr.eval, Lambda.LExpr.evalCore, hbv, Lambda.Factory.callOfLFunc,
    Lambda.getLFuncCall, Lambda.getLFuncCall.go, bE, hr, Lambda.LExpr.boolConst,
    Lambda.isValue_const_true]

/-- The reference semantics has a run of `hCex.cfg`, stopped right after the call, that takes the
    then-branch, has the callee's `init b` write `ff`, and emits an assert event of the callee's
    `assert neg : b` whose condition the reference evaluator and the engine evaluate to false
    (`Calls.assertFailureE`); the nondeterministic choices it resolves are, in order,
    `[ttVal, ffVal]`. -/
private theorem hRun (F : Expression.Factory) (hF : F.factory = Core.Factory) :
    ∃ evs final, Calls.RunChoices hPi
      (hCex.cfg.abs F) evs final [HasBool.ttVal F, HasBool.ffVal F] ∧
      ∃ ev ∈ evs, Calls.assertFailureE hTarget ev := by
  refine ⟨_, _, ⟨1, fun rest =>
    .step _ _ _ _ _ (.step_det .step_stmts_cons)
    (.step _ _ _ _ _ (.step_seq_inner .step_ite_then)
    (.step _ _ _ _ _ (.step_det (.step_seq_inner (.step_block_body .step_stmts_cons)))
    (.step _ _ _ _ _ (.step_seq_inner (.step_block_body (.step_seq_inner (.step_cmd (.inr (.inl
      ⟨"h", hProc, [], md, _, _, _, _, rfl, rfl, rfl,
        ⟨[], [], .eval_none, .read_none, ⟨_, _, .init_none, .init_none, rfl⟩⟩,
        .step _ _ _ _ _ (.step_det .step_block)
            (.step _ _ _ _ _ (.step_det (.step_block_body .step_stmts_cons))
            (.step _ _ _ _ _ (.step_block_body (.step_seq_inner (.step_cmd
              ⟨_, rfl, .eval_init_nondet (v := HasBool.ffVal F) rfl
                (HasBool.boolIsValOfTy _).2 (HasBool.boolIsValOfTy _).2
                (coreEvaluator_WellFormedSemanticEvalVar _),
                .inr ⟨bId, HasBool.ffVal F, rfl, by simp [SemanticStore.update],
                  .inl ⟨_, _, rfl⟩⟩⟩)))
            (.step _ _ _ _ _ (.step_det (.step_block_body .step_seq_done))
            (.step _ _ _ _ _ (.step_det (.step_block_body .step_stmts_cons))
            (.step _ _ _ _ _ (.step_block_body (.step_seq_inner (.step_cmd
              ⟨_, rfl, .eval_assert, .inl ⟨rfl, rfl⟩⟩)))
            (.step _ _ _ _ _ (.step_det (.step_block_body .step_seq_done))
            (.step _ _ _ _ _ (.step_det (.step_block_body .step_stmts_nil))
            (.step _ _ _ _ _ (.step_det .step_block_done) (.refl _))))))))),
        ⟨List.nodup_nil, [], .read_none, .update_none, .nil⟩, rfl, nofun,
        fun _ _ _ _ _ _ h _ => by cases h; rfl⟩))))))
    (.refl _))))⟩, .assert ⟨F, hStore F, "neg", bE, md⟩,
    by simp [Calls.defaultAssertEvents, hProc, IEnv.abs, hStore, hFrame], rfl, rfl,
    hAssert_denote F,
    ⟨fun σr v hS hv => ⟨1, Option.some.inj ((hAssert_denote F).symm.trans hv) ▸
      hAssert_eval F hF σr hS⟩,
    fun σr n r hS h => ff_of_denotes F hF r
      (hS.2 bId r _ (bE_eval _ σr n r h) (by simp [hStore, SemanticStore.update]))⟩⟩

/-- Replaying `hCex` with its own oracle `[tt, ff]` reaches the callee's failing assert at every
    sufficiently large fuel and call-depth limit, so the replay verdict is `genuine`. -/
theorem hGenuine :
    ∃ f0, ∀ fuel d, f0 ≤ fuel → f0 ≤ d → genuine hPi hTarget fuel hCex d := by
  obtain ⟨_, _, hrun, hfail⟩ := hRun M0 rfl
  refine core_replayComplete hPi hTarget hCex
    (show IConfig.Denoting M0 (.stmts _ hEnv) from ⟨by simp [hEnv, IEnv.ofStore,
      RStore.Denoting, IStore.get, IStore.ofStore, InterpLang.writesFind?_empty], rfl⟩)
    trivial hrun [HasBool.tt, HasBool.ff] (List.prefix_refl _) ⟨rfl, ?_⟩ ?_ hfail
  · refine List.forall_mem_cons.2 ⟨?_, List.forall_mem_cons.2 ⟨?_, nofun⟩⟩
    · exact ⟨InterpLangBool.denote_tt M0, Lambda.isValue_const_true .., fun _ => rfl,
        fun h => (HasBool.ttVal_ne_ffVal (P := Expression) M0 h).elim⟩
    · exact ⟨InterpLangBool.denote_ff M0, Lambda.isValue_const_true ..,
        fun h => (HasBool.ttVal_ne_ffVal (P := Expression) M0 h.symm).elim, fun _ => rfl⟩
  · refine List.forall_mem_cons.2 ⟨?_, List.forall_mem_cons.2 ⟨?_, nofun⟩⟩
    all_goals rintro σ ty ⟨-, hty⟩
    all_goals simp only [InterpLang.ops, replayValueOps, valueHasType, hty]
    all_goals rfl

/-! ## A configuration satisfying the premises of `core_replaySound` -/

namespace CallSideConditionWitness

private def vid (s : String) : Expression.Ident := ⟨s, ()⟩
private def rd (s : String) : Expression.Expr := .fvar () (vid s) none
private def mdE : Imperative.MetaData Expression := {}

/-- The callee: input `a`, output `b`, body `b := a`, no spec clauses. -/
def wCallee : Procedure :=
  { header :=
      { name := vid "w", typeArgs := [],
        inputs := [(vid "a", Lambda.LMonoTy.bool)],
        outputs := [(vid "b", Lambda.LMonoTy.bool)] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [.cmd (.cmd (.set (vid "b") (.det (rd "a")) mdE))] }

/-- The procedure table: `"w"` resolves to `wCallee`, every other name to nothing. -/
def wPi : String → Option Procedure := fun n => if n = "w" then some wCallee else none

/-- The call site: one strict input actual and one output actual. -/
def wCall : Command := .call "w" [.inArg (rd "x"), .outArg (vid "y")] mdE

attribute [local simp] Block.allCmds.eq_1 Block.allCmds.eq_2 Stmt.allCmds.eq_1
  Calls.CmdCallOk Calls.StrictActual Calls.getInputExprs CallArg.getInputExprs CallArg.getLhs ListMap.keys
  Procedure.Header.getOutputOnlyParams HasFvar.getFvar HasFvars.getFvars

/-- Every procedure of the witness table is well-formed for call-aware replay: its frame-binding
    formals are pairwise distinct, and its structured body is exit-covered and has well-formed
    call sites. -/
private theorem procsOk_wPi : ProcsOk wPi := by
  simp [ProcsOk, ProcOk, wPi, wCallee, vid, Block.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks]

/-- The witness caller environment: the empty store over Core's concrete factory. -/
def wEnv : Imperative.IEnv Expression :=
  .ofStore (fun _ => none) Core.Factory

/-- The witness configuration: the call, about to be executed. -/
def wCfg : IConfig Expression Command := .stmt (.cmd wCall) wEnv

/-- The witness configuration satisfies the invariant Core call-aware replay soundness runs
    under: the store holds only values and is typed, and the configuration has well-formed call
    sites. -/
private theorem coreCfgInv_wCfg (F : Expression.Factory) : CoreCfgInv wPi (wCfg.abs F) :=
  ⟨by simp only [wCfg, wEnv, IConfig.abs, IEnv.abs, IEnv.ofStore, Config.storeWellDefined]
      intro x v h
      simp [InterpLang.absStore, IStore.get, IStore.ofStore, InterpLang.writesFind?_empty] at h,
    by simp [wCfg, IConfig.abs, Config.allCmds, wCall, rd, Calls.TypedActual],
    by simp [wCfg, wEnv, IConfig.abs, IEnv.abs, IEnv.ofStore, InterpLang.absStore,
      Config.storeTyped, StoreTyped]⟩

/-- The witness counterexample: the call configuration and no oracle values. -/
def wCex : CexA Expression Command :=
  { cfg := wCfg, oracle := [] }

/-- The witness replay fuel. -/
def wFuel : Nat := 100

/-- No target assertion id occurs in a procedure of the witness table: the callee has no spec
    clauses and its body has no `assert` or `cover`. -/
private theorem targetNotInProcs_wPi (target : AssertId Expression) :
    TargetNotInProcs wPi target := by
  simp [Calls.TargetNotInProcs, wPi, wCallee, Calls.ChecksAvoidTarget, Calls.cmdAvoidsTarget,
    Calls.checksAtCall]

/-- Replay soundness holds at the witness, at every modeled factory over `Core.Factory`: for
    every target, if replaying `wCex` returns `genuine`, then the reference semantics has a run
    from `wCfg` emitting an event that fails the target assertion. -/
theorem replaySound_wit
    (F : Expression.Factory) (hF : F.factory = Core.Factory)
    (target : AssertId Expression) :
    ReplaySound wPi target wFuel F wCex :=
  core_replaySound wPi target wFuel wCex procsOk_wPi F (hF ▸ evalFactoryWF_coreFactory)
    (factoryWF_coreFactory F hF)
    (show IConfig.Denoting F wCfg from ⟨by simp [wEnv, IEnv.ofStore, RStore.Denoting, IStore.get,
      IStore.ofStore, InterpLang.writesFind?_empty], hF.symm⟩) trivial (coreCfgInv_wCfg F)
    (targetNotInProcs_wPi _) defaultMaxCallDepth

end CallSideConditionWitness

end ReplayCompleteSanityTest
