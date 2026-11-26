/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Core.Tests.Logic.HoareTotal
import Strata.Languages.Core.Logic.HoareCall
import Strata.DL.Imperative.BigStep.Adequacy
import Strata.Transform.DeadDefElimProps
import Strata.Languages.Core.Analysis.ProcedureCorrectnessProps

open Imperative
open Imperative.BigStep

namespace Strata.HoareTotalCallTest

open HoareUtils HoareTotalTest

/-! # A total-correctness call to a looping procedure

`HoareTotal.Procedure.call_of_contract` applied to `call z := CountUp()`, where `CountUp` is
the counting loop of `HoareTotal.lean`, proved there to meet its total-correctness contract
(`countUp_meets_contract_total`).  From an entry where `z` holds an integer, the call
terminates with `z` holding `10` (`countUp_call_total`). The same call to `CountUp` declared
without a body, an abstract callee, gives the same result from the contract alone
(`countUpAbs_call_total`).

Besides the callee's contract, the rule asks for facts about every run of the callee's body:
it writes only the output `y` (`up_body_frame`) and leaves `y` holding an integer
(`up_body_outputs`, `up_run_yInt`).  Both are proved over the big-step semantics
(`Imperative.BigStep.BRun`), to which a call-free Core run converts
(`Imperative.BigStep.star_brun`); the loop is handled by induction on its big-step run
(`upStmt_yInt`, `upLoopBody_yInt`).  A final callee store meeting the contract has `y` holding
`10` (`y10_of_post`), which the call writes back into `z`.

A call is one step, so the call terminates with valid assertions when it can execute: it has a
callee entry store (`up_callEntry`), a finished run of the body from it (`up_bodyRun`), and a
write-back from every such run.  The finished run comes from `CountUp`'s total-correctness
contract: its body terminates with valid assertions, and since it has no `assume`, every step
keeps its assumptions true in any world (`step_detSets_emits_nil`), so
`EventLang.MustTerminateAndAssertsValid.reaches_final` gives a finished execution.

The facts about `CountUp`'s signature, the absence of calls and definitions in its body, and the
type annotations in it use `native_decide`: the translation is `partial`, so the kernel cannot
reduce it. -/

/-- The procedures of the test program, by name. -/
private abbrev π : String → Option Core.Procedure := countPgmAST.findProcByString?

/-- The procedure `CountUp`. -/
private abbrev upProc : Core.Procedure := procOf countPgmAST "CountUp"

/-- The caller's variable receiving `CountUp`'s output. -/
private def zId : Core.Expression.Ident := ⟨"z", ()⟩

/-- The arguments of `call z := CountUp()`. -/
private def upCall : List (Imperative.CallArg Core.Expression) := [.outArg zId]

/-- `CountUp` is found by name. -/
private theorem up_find : π "CountUp" = some upProc := by native_decide
/-- A call to `CountUp` without type arguments runs `upProc`, which has no type parameters. -/
private theorem up_callee : Calls.typeInstantiatedCallee π "CountUp" none = some upProc :=
  (Core.Procedure.typeInstantiatedCallee_of_typeArgs_nil up_find (by native_decide)).2 ⟨rfl, rfl⟩

/-! ## Facts about `CountUp`'s signature -/

/-- `CountUp`'s only output is `y`, of type `int`. -/
private theorem up_outputs : upProc.header.outputs.toList = [(yId, Lambda.LMonoTy.int)] := by
  native_decide

/-- The names of `CountUp`'s outputs are `[y]`. -/
private theorem up_outKeys : ListMap.keys upProc.header.outputs = [yId] := by native_decide

/-- `CountUp` has no input formals. -/
private theorem up_inputParams :
    Imperative.ProcedureHeader.inputParams (P := Core.Expression) upProc.header = [] := by
  native_decide

/-- `CountUp`'s only output-only formal is `y`. -/
private theorem up_outOnly :
    Imperative.Calls.outputOnlyParams (P := Core.Expression) upProc.header = [yId] := by
  native_decide

/-- `CountUp` has no inout formals. -/
private theorem up_inout :
    Imperative.Calls.inoutParams (P := Core.Expression) upProc.header = [] := by
  native_decide

/-- `CountUp`'s output formals, as the call reads them back, are `[y]`. -/
private theorem up_outputParams :
    Imperative.ProcedureHeader.outputParams (P := Core.Expression) upProc.header = [yId] := by
  native_decide

/-! ## Every run of the body -/

/-- `y` holds an integer of the factory `f` in the store `σ`. -/
private abbrev YInt (f : Core.Expression.Factory) (σ : Core.CoreStore) : Prop :=
  ∃ w, σ yId = some w ∧ HasVal.valueOfTy f w intLTy

/-- An assignment to `y` that runs from a store where `y` holds an integer leaves `y` holding
    an integer: the value assigned has the type of the value `y` held. -/
private theorem yInt_of_set {f : Core.Expression.Factory} {σ σ' : Core.CoreStore}
    {e : Core.Expression.Expr} {md : Imperative.MetaData Core.Expression}
    {evs : List (Event Core.Expression)}
    (h : EvalE f σ (.cmd (.set yId (.det e) md)) σ' evs) (hy : YInt f σ) : YInt f σ' := by
  obtain ⟨w, hw, hwt⟩ := hy
  change EvalCmdE Core.Expression f σ (.set yId (.det e) md) σ' evs at h
  cases h with
  | eval_set _ hupd htyped _ =>
    obtain ⟨old, ty, hold, holdt, hvt⟩ := htyped
    rw [hw] at hold
    cases hold
    obtain rfl := Core.valueOfTy_unique holdt hwt
    cases hupd with
    | update _ hnew _ => exact ⟨_, hnew, hvt⟩

/-- The assignment in the body of `CountUp`'s loop. -/
private abbrev upSet : Core.Statement :=
  Core.Statement.set yId (opE Core.intAddOp yId 1) (loc 649 668)

/-- Leaving a scope keeps `y` holding an integer when `y` was bound on entry. -/
private theorem yInt_projectStore {f : Core.Expression.Factory} {σp σ : Core.CoreStore}
    (hp : YInt f σp) (h : YInt f σ) : YInt f (Imperative.projectStore σp σ) := by
  obtain ⟨_, hp0, -⟩ := hp
  obtain ⟨w, hw, hwt⟩ := h
  refine ⟨w, ?_, hwt⟩
  unfold Imperative.projectStore
  rw [hp0]
  exact hw

mutual
/-- Every run of `CountUp`'s loop, or of the assignment in its body, from a store where `y`
    holds an integer ends with `y` holding an integer. -/
private theorem upStmt_yInt {f : Core.Expression.Factory} :
    ∀ {s : Core.Statement} {σ : Core.CoreStore} {evs : List (Event Core.Expression)}
      {o : Outcome Core.Expression},
      BRunS f s σ evs o → s = upLoop ∨ s = upSet → YInt f σ → YInt f o.store
  | _, _, _, _, .cmd hc, hs, hy => by
    rcases hs with hs | hs
    · cases hs
    · obtain rfl := Stmt.cmd.inj hs
      exact yInt_of_set hc hy
  | _, _, _, _, .loop_exit _, _, hy => hy
  | _, _, _, _, .loop_iter _ hb hrest, hs, hy => by
    have hl : _ = upLoop := hs.resolve_right (fun h => by cases h)
    exact upStmt_yInt hrest (.inl hl)
      (yInt_projectStore hy (upLoopBody_yInt hb (.inl (Stmt.loop.inj hl).2.2.2.1) hy))
  | _, _, _, _, .loop_break _ hb, hs, hy => by
    have hl : _ = upLoop := hs.resolve_right (fun h => by cases h)
    exact yInt_projectStore hy (upLoopBody_yInt hb (.inl (Stmt.loop.inj hl).2.2.2.1) hy)
  | _, _, _, _, .ite_true _ _, hs, _ | _, _, _, _, .ite_false _ _, hs, _
  | _, _, _, _, .ite_nondet_true _, hs, _ | _, _, _, _, .ite_nondet_false _, hs, _
  | _, _, _, _, .block _, hs, _ | _, _, _, _, .exit, hs, _ | _, _, _, _, .typeDecl, hs, _ => by
    rcases hs with hs | hs <;> cases hs

/-- Every run of the body of `CountUp`'s loop, or of its empty rest, from a store where `y`
    holds an integer ends with `y` holding an integer. -/
private theorem upLoopBody_yInt {f : Core.Expression.Factory} :
    ∀ {ss : Core.Statements} {σ : Core.CoreStore} {evs : List (Event Core.Expression)}
      {o : Outcome Core.Expression},
      BRun f ss σ evs o → ss = upLoopBody ∨ ss = [] → YInt f σ → YInt f o.store
  | _, _, _, _, .nil, _, hy => hy
  | _, _, _, _, .cons_normal h1 h2, hs, hy => by
    have hl : _ = upLoopBody := hs.resolve_right (fun h => by cases h)
    exact upLoopBody_yInt h2 (.inr (List.cons.inj hl).2)
      (upStmt_yInt h1 (.inr (List.cons.inj hl).1) hy)
  | _, _, _, _, .cons_exit h1, hs, hy => by
    have hl : _ = upLoopBody := hs.resolve_right (fun h => by cases h)
    exact upStmt_yInt h1 (.inr (List.cons.inj hl).1) hy
end

/-- A pair in the zip of a list with itself has equal components. -/
private theorem eq_of_mem_zip_self {ks : List Core.Expression.Ident}
    {a b : Core.Expression.Ident} (h : (a, b) ∈ ks.zip ks) : a = b := by
  induction ks with
  | nil => simp at h
  | cons k ks ih =>
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · rfl
    · exact ih h

/-- `y := 0` leaves `y` holding an integer, and runs only from a store where `y` is bound. -/
private theorem yInt_of_set0 {f : Core.Expression.Factory} {σ σ' : Core.CoreStore}
    {md : Imperative.MetaData Core.Expression} {evs : List (Event Core.Expression)}
    (h : EvalE f σ (.cmd (.set yId (.det (.intConst Core.valueLoc 0)) md)) σ' evs) :
    (σ yId).isSome ∧ YInt f σ' := by
  change EvalCmdE Core.Expression f σ (.set yId (.det (.intConst Core.valueLoc 0)) md) σ' evs
    at h
  cases h with
  | eval_set heval hupd htyped _ =>
    obtain rfl := Option.some.inj (heval.symm.trans (Core.eval_intConst _ _ 0))
    obtain ⟨old, ty, hold, -, hvt⟩ := htyped
    obtain rfl := Core.valueOfTy_unique hvt (⟨rfl, rfl⟩ : HasVal.valueOfTy f (intOf f 0) intLTy)
    cases hupd with
    | update _ hnew _ => exact ⟨by simp [hold], _, hnew, hvt⟩

/-- Every run of `CountUp`'s body starts from a store where `y` is bound and ends with `y`
    holding an integer. -/
private theorem upBody_yInt {f : Core.Expression.Factory} {σ : Core.CoreStore}
    {evs : List (Event Core.Expression)} {o : Outcome Core.Expression}
    (h : BRun f upBody σ evs o) : (σ yId).isSome ∧ YInt f o.store := by
  change BRun f [Core.Statement.set yId (.intConst Core.valueLoc 0) (loc 612 619), upLoop] σ evs o
    at h
  cases h with
  | cons_normal h1 h2 =>
    cases h1 with
    | cmd hset =>
      obtain ⟨hdef, hy⟩ := yInt_of_set0 hset
      refine ⟨hdef, ?_⟩
      cases h2 with
      | cons_normal h3 h4 => cases h4; exact upStmt_yInt h3 (.inl rfl) hy
      | cons_exit h3 => exact upStmt_yInt h3 (.inl rfl) hy
  | cons_exit h1 => cases h1

/-- A block statement runs its body: its outcome is the body's, leaving the block. -/
private theorem block_inv {f : Core.Expression.Factory} {l : String}
    {ss : Core.Statements} {md : Imperative.MetaData Core.Expression} {σ : Core.CoreStore}
    {evs : List (Event Core.Expression)} {o' : Outcome Core.Expression}
    (h : BRunS f (.block l ss md) σ evs o') : ∃ o, BRun f ss σ evs o ∧ o' = o.block l σ := by
  cases h with
  | block hb => exact ⟨_, hb, rfl⟩

/-- A run of `CountUp`'s body, as the procedure block it runs in, from `σ` emitting `evs` and
    ending in `σ'` is a big-step run of that block from `σ` to `σ'`. -/
private theorem up_brun {σ : Core.CoreStore} {f : Core.Expression.Factory}
    {σ' : Core.CoreStore} {evs : List (Event Core.Expression)}
    (h : Core.CoreBodyExecE π (.structured upBody false) ⟨σ, f⟩ σ' evs) :
    BRun f [Stmt.block "" upBody #[]] σ evs (.normal σ') := by
  cases h with
  | structured hrun =>
    rename_i ρ'
    have hnc : Core.Statements.noCalls [Stmt.block "" upBody #[]] = true := by native_decide
    exact star_brun.1 (Core.DeadDefElim.star_evalE
      (Imperative.stmtRun_to_singletonE (Core.EvalCommandE π) hrun) hnc)

/-- **Every run of `CountUp`'s body writes only its output `y`.** -/
private theorem up_body_frame :
    ∀ proc, Calls.typeInstantiatedCallee π "CountUp" none = some proc →
      Core.Logic.Hoare.Procedure.bodyFrame π proc := by
  intro proc hlk
  obtain rfl : proc = upProc := Option.some.inj (hlk.symm.trans up_callee)
  intro σe f σx evs hbody
  rw [up_body_eq] at hbody
  have hb := up_brun hbody
  show Imperative.invStoresExcept σe σx (ListMap.keys upProc.header.outputs)
  rw [up_outKeys]
  intro vs hdisj k1 k2 hmem
  obtain rfl := eq_of_mem_zip_self hmem
  have hne : k1 ∉ [yId] := hdisj (List.of_mem_zip hmem).1
  show σe k1 = σx k1
  by_cases hs : (σe k1).isSome
  · simp only [List.mem_singleton] at hne
    exact (brun_frame hb k1 hs (by
      simp [Block.modifiedVars, Stmt.modifiedVars, HasVarsImp.modifiedVars, CmdExt.modifiedVars,
        Cmd.modifiedVars, hne])).symm
  · have hnone : σe k1 = none := Option.not_isSome_iff_eq_none.mp hs
    rw [hnone]
    cases hx : σx k1 with
    | none => rfl
    | some _ =>
      rcases brun_sub hb k1 (by show (σx k1).isSome; rw [hx]; rfl) with h | h
      · exact absurd h hs
      · simp [Block.definedVars, Stmt.definedVars] at h

/-- Every run of `CountUp`'s body ends with `y` holding an integer of the runtime factory. -/
private theorem up_run_yInt {σe σx : Core.CoreStore} {f : Core.Expression.Factory}
    {evs : List (Event Core.Expression)}
    (hbody : Core.CoreBodyExecE π upProc.body ⟨σe, f⟩ σx evs) : YInt f σx := by
  rw [up_body_eq] at hbody
  -- The block runs `y := 0` and then the loop, and projects the result on `σe`.
  cases up_brun hbody with
  | cons_normal hblk hnil =>
    cases hnil
    obtain ⟨o, hbo, ho⟩ := block_inv hblk
    obtain ⟨hdef, w, hw, hwt⟩ := upBody_yInt hbo
    have hσx := congrArg Outcome.store ho
    rw [Outcome.block_store] at hσx
    refine ⟨w, ?_, hwt⟩
    simp only [Outcome.store] at hσx
    rw [hσx]
    unfold Imperative.projectStore
    rw [ite_eq_left hdef]
    exact hw

/-- **Every run of `CountUp`'s body leaves its output `y` holding an integer.** -/
private theorem up_body_outputs :
    ∀ proc, Calls.typeInstantiatedCallee π "CountUp" none = some proc →
      Core.Logic.Hoare.Procedure.bodyOutputsTyped
        (countPgmAST.factoryBeforeProcedure "CountUp") π proc := by
  intro proc hlk
  obtain rfl : proc = upProc := Option.some.inj (hlk.symm.trans up_callee)
  intro σe f σx evs _ _ hbody
  obtain ⟨w, hw, hwt⟩ := up_run_yInt hbody
  intro id ty hmem
  rw [up_outputs] at hmem
  simp only [List.mem_singleton, Prod.mk.injEq] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  obtain ⟨-, hmono⟩ := hwt
  simp only [Lambda.LTy.toMonoType?, Option.some.injEq] at hmono
  exact ⟨w, hw, hmono.symm⟩

/-! ## The call `call z := CountUp()` -/

/-- Caller precondition: the runtime factory is over `Core.Factory` and `z` holds an integer. -/
private def CallPre (ρ : Env Core.Expression) : Prop :=
  Pinned ρ ∧ ∃ k, ρ.store zId = some (intOf ρ.factory k)

/-- Caller postcondition: the runtime factory is over `Core.Factory` and `z` holds `10`. -/
private def CallPost (ρ : Env Core.Expression) : Prop :=
  Pinned ρ ∧ ρ.store zId = some (intOf ρ.factory 10)

/-- `CountUp`'s entry store for the call when `z` holds `w`: `y` holds `w`, nothing else is
    bound. -/
private abbrev entryStore (w : Core.Expression.Val) : Core.CoreStore :=
  SemanticStore.update Imperative.emptyStore yId w

/-- The call's callee entry store is `entryStore w`, where `w` is the value `z` holds. -/
private theorem up_callEntry_inv {fac : Core.Expression.Factory} {σ σAO : Core.CoreStore}
    (h : Core.CallEntry fac σ upProc upCall σAO) :
    ∃ w, σ zId = some w ∧ HasVal.value fac w ∧ σAO = entryStore w := by
  obtain ⟨inputVals, outOnlyVals, hEE, hRV, σA, σIO, hIA, hIO, hSnap⟩ := h
  rw [show Imperative.Calls.getInputExprs upCall = [] from rfl] at hEE
  rw [show Imperative.CallArg.getOutArgs upCall = [zId] from rfl] at hRV
  rw [up_inputParams] at hIA
  rw [up_outOnly] at hIO
  rw [up_inout] at hSnap
  cases hEE
  cases hRV with
  | read_some hz hval hRV2 =>
    cases hRV2
    cases hIA
    cases hIO with
    | init_some hiy hIO2 =>
      cases hIO2
      refine ⟨_, hz, hval, ?_⟩
      rw [hSnap]
      funext k
      cases hiy with
      | init _ hnew hother =>
        simp only [Imperative.Calls.withOldSnapshots, SemanticStore.update]
        by_cases hk : k = yId
        · subst hk; simpa using hnew
        · rw [ite_eq_right hk]; exact hother k (Ne.symm hk)

/-- From an entry where `z` holds the value `w`, the call has the callee entry store
    `entryStore w`. -/
private theorem up_callEntry {fac : Core.Expression.Factory} {σ : Core.CoreStore}
    {w : Core.Expression.Val} (hz : σ zId = some w) (hw : HasVal.value fac w) :
    Core.CallEntry fac σ upProc upCall (entryStore w) := by
  refine ⟨[], [w], .eval_none, .read_some hz hw .read_none, Imperative.emptyStore,
    entryStore w, ?_, ?_, ?_⟩
  · rw [up_inputParams]; exact .init_none
  · rw [up_outOnly]; exact .init_some (InitState.of_update rfl) .init_none
  · rw [up_inout]; rfl

/-- A final store of `CountUp` meeting its contract, with `y` holding an integer, has `y`
    holding `10`. -/
private theorem y10_of_post {ρ' : Env Core.Expression} (hp : Pinned ρ')
    (hpost : Core.Logic.Hoare.Procedure.contractPost Core.Factory upProc ρ')
    (hout : Core.Logic.Hoare.Procedure.outputAsPredicate upProc ρ') :
    ρ'.store yId = some (intOf ρ'.factory 10) := by
  obtain ⟨v, hv, hvt⟩ := hout yId Lambda.LMonoTy.int (by rw [up_outputs]; simp)
  obtain ⟨⟨label, check⟩, hmem, hattr⟩ : ∃ lc ∈ upProc.spec.postconditions.toList,
      lc.2.attr = Core.Procedure.CheckAttr.Default := by native_decide
  rcases hpost label check hmem hattr (someValuation _) with ⟨_, hex⟩ | ⟨hne, _⟩
  · change Core.Expression.eval ρ'.factory ρ'.store check.expr =
      some (HasBool.ttVal ρ'.factory) at hex
    rw [up_post_expr _ hmem] at hex
    obtain ⟨w, hw, hwtc⟩ := Lambda.LExpr.denoteEval_defines hex yId
      (by simp [Lambda.LExpr.LExpr.getVars])
    rw [hv] at hw
    cases hw
    obtain ⟨i, hi⟩ := Lambda.SemValue.exists_ofInt hvt
    have hvi : ρ'.store yId = some (intOf ρ'.factory i) := by rw [hv, hi, hwtc]
    by_cases h10 : i = 10
    · subst h10; exact hvi
    · exfalso
      have hff : Core.Expression.eval ρ'.factory ρ'.store (eqInt yId 10) =
          some (Lambda.SemValue.ofBool ρ'.factory.model.tcInterp false) :=
        Core.eval_eq_false ρ'.factory (Core.eval_fvar_int _ hvi) (Core.eval_intConst _ _ 10) rfl
          (fun h => h10 (Lambda.SemValue.ofInt_injective h))
      rw [hex] at hff
      exact HasBool.ttVal_ne_ffVal _ (Option.some.inj hff)
  · exact absurd hp hne

/-- The typing that gives `y` the integer type and no other variable a type. -/
private abbrev yTyping : VarTyping Core.Expression :=
  fun n => if n = yId then some intLTy else none

/-- `yTyping` annotates every list of occurrences of `y` at the integer type. -/
private theorem annotates_y {occs : List (Core.Expression.Ident × Core.Expression.Ty)}
    (h : ∀ p ∈ occs, p = (yId, intLTy)) : VarTyping.annotates yTyping occs := by
  intro x ty hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (h _ hm)
  simp

/-- The gate of `CountUp`'s body holds at an entry over `Core.Factory` that binds only `y`, to
    an integer. -/
private theorem up_blockWF {ρ : Env Core.Expression} (hfac : Pinned ρ) {k : Int}
    (hy : ρ.store yId = some (intOf ρ.factory k)) (hother : ∀ n, n ≠ yId → ρ.store n = none) :
    Core.Logic.BlockInitEnvWF testParams [Stmt.block "" upBody #[]] ρ := by
  have hdef : (fun n => (ρ.store n).isSome) = (fun n => decide (n = yId)) := by
    funext n
    by_cases h : n = yId
    · subst h; simp [hy]
    · simp [hother n h, h]
  refine Core.Logic.BlockInitEnvWF.of_defUseOk (Core.coreFactory_WellFormedSemanticEval _ hfac)
    (fun n v hn => ?_) (fun n hn => ?_) (fun _ _ p hp => by simp [testParams] at hp)
    (fun _ _ p hp => by simp [testParams] at hp) (fun _ _ p hp => by simp [testParams] at hp)
    (by
      show Block.defUseWellFormed (fun n => (ρ.store n).isSome) testParams.declaredFuncs
        [Stmt.block "" upBody #[]] = true
      rw [hdef]
      native_decide)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun ty hty => ?_) ⟨yTyping, fun x ty hx => ?_, ?_⟩
    (fun m hm => ?_)
  · by_cases h : n = yId
    · subst h; rw [hy] at hn; cases hn; rfl
    · rw [hother n h] at hn; cases hn
  · rw [show Block.definedVars (P := Core.Expression) (C := Core.Command)
      [Stmt.block "" upBody #[]] false = [] from by native_decide] at hn
    simp at hn
  · rw [show Block.initTypes (P := Core.Expression) (C := Core.Command)
      [Stmt.block "" upBody #[]] = [] from by native_decide] at hty
    simp at hty
  · by_cases h : x = yId
    · subst h
      simp only [yTyping, ite_true, Option.some.injEq] at hx
      subst hx
      exact ⟨_, hy, rfl, rfl⟩
    · simp [yTyping, h] at hx
  · -- The body defines nothing, so every statement is checked against `yTyping`.
    have hext : ∀ s : Core.Statement, Stmt.typedDefinedVars s = [] →
        yTyping.extend (Stmt.typedDefinedVars s) = yTyping := fun s hs => by
      funext n; simp [VarTyping.extend, hs]
    refine ⟨?_, trivial⟩
    change Stmt.fvarTypesWellAnnotated yTyping
        (Core.Statement.set yId (.intConst Core.valueLoc 0) (loc 612 619)) ∧
      Block.fvarTypesWellAnnotated (yTyping.extend (Stmt.typedDefinedVars
        (Core.Statement.set yId (.intConst Core.valueLoc 0) (loc 612 619)))) [upLoop]
    rw [hext _ (by native_decide)]
    refine ⟨annotates_y (by native_decide), ⟨annotates_y (by native_decide),
      annotates_y (by native_decide), annotates_y (by native_decide), ?_, trivial⟩, trivial⟩
    exact annotates_y (by native_decide)
  · rw [show Block.measures (P := Core.Expression) (C := Core.Command)
      [Stmt.block "" upBody #[]] = [] from by native_decide] at hm
    simp at hm

/-- At the call's callee entry, which binds only `y`, to an integer `k`, `CountUp`'s contract
    precondition and the gate of its body hold. -/
private theorem up_entry {f : Core.Expression.Factory} (hfac : f.factory = Core.Factory)
    (k : Int) :
    Core.Logic.Hoare.Procedure.contractPre (countPgmAST.factoryBeforeProcedure "CountUp") upProc
        ⟨entryStore (intOf f k), f⟩ ∧
      Core.Logic.BlockInitEnvWF testParams [Stmt.block "" upBody #[]]
        ⟨entryStore (intOf f k), f⟩ := by
  have hfactory : countPgmAST.factoryBeforeProcedure "CountUp" = Core.Factory :=
    Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)
  have hy : entryStore (intOf f k) yId = some (intOf f k) := by simp [SemanticStore.update]
  have hother : ∀ n, n ≠ yId → entryStore (intOf f k) n = none := fun n hn => by
    simp [SemanticStore.update, hn, Imperative.emptyStore]
  refine ⟨⟨?_, hfac.trans hfactory.symm, ?_, ?_, ?_⟩, up_blockWF hfac hy hother⟩
  · intro label check hmem
    rw [show upProc.spec.preconditions.toList = [] from by native_decide] at hmem
    simp at hmem
  · intro id hid
    rw [show ListMap.keys upProc.header.getInoutParams = [] from by native_decide] at hid
    simp at hid
  · intro id ty hmem
    rw [show upProc.header.inputs.toList = [] from by native_decide] at hmem
    simp at hmem
  · intro id ty hmem
    rw [up_outputs, List.mem_singleton] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact ⟨_, hy, rfl⟩

/-- A deterministic assignment. -/
private def isDetSet : Core.Command → Bool
  | .cmd (.set _ (.det _) _) => true
  | _ => false

/-- A step of a configuration whose commands are all deterministic assignments emits no
    event. -/
private theorem step_detSets_emits_nil {c c' : Config Core.Expression Core.Command}
    {emitted : List (Event Core.Expression)}
    (hs : StepStmtE Core.Expression (Core.EvalCommandE π) c emitted c')
    (hQ : c.allCmds isDetSet) : emitted = [] := by
  induction hs with
  | @step_cmd cmd _ _ _ hcmd =>
    simp only [Config.allCmds, Stmt.allCmds] at hQ
    cases cmd with
    | cmd c =>
      cases c with
      | set x e md =>
        cases e with
        | det e =>
          cases hcmd with
          | cmd_sem hbase => cases hbase; rfl
        | nondet => simp [isDetSet] at hQ
      | _ => simp [isDetSet] at hQ
    | call => simp [isDetSet] at hQ
  | step_seq_inner _ ih => exact ih hQ.1
  | step_block_body _ ih => exact ih hQ
  | _ => rfl

/-- From the callee entry `entryStore (intOf f k)`, some run of `CountUp`'s body finishes:
    the body terminates with valid assertions, and it has no `assume` that could fail. -/
private theorem up_bodyRun {f : Core.Expression.Factory} (hfac : f.factory = Core.Factory)
    (k : Int) :
    ∃ σEnd bodyEvents,
      Core.CoreBodyExecE π upProc.body ⟨entryStore (intOf f k), f⟩ σEnd bodyEvents := by
  obtain ⟨hpre, hwf⟩ := up_entry hfac k
  have hterm := (Core.Logic.Hoare.Procedure.contractTripleTotal_iff countPgmAST testParams
    "CountUp").mp countUp_meets_contract_total |>.2
  obtain ⟨proc, hproc, hterms⟩ := hterm
  obtain rfl : proc = upProc := Option.some.inj (hproc.symm.trans up_find)
  have hterm := hterms [] upProc
    ((Core.Procedure.instantiateTypes_of_typeArgs_nil (by native_decide)).2 ⟨rfl, rfl⟩)
  rw [up_body_eq] at hterm ⊢
  have hQ : Config.allCmds isDetSet
      (.stmts [Stmt.block "" upBody #[]] ⟨entryStore (intOf f k), f⟩) := by
    show Block.allCmds isDetSet [Stmt.block "" upBody #[]] = true
    native_decide
  obtain ⟨trace, ρ', hfinal⟩ := (hterm _ ⟨hpre,
      _root_.Core.Specification.axiomsBeforeProcedureDecl_of_noAxioms (by native_decide) _⟩
    hwf (someValuation _)).reaches_final (fun c => Config.allCmds isDetSet c) hQ
    fun _ _ _ hQc hs => by
      refine ⟨stepStmtE_preserves_allCmds (Core.EvalCommandE π) hs hQc, ?_⟩
      rw [step_detSets_emits_nil hs hQc]
      exact fun _ h => nomatch h
  rcases singletonRun_to_stmtRunE (Core.EvalCommandE π) hfinal with hrun | ⟨lbl, hexit⟩
  · exact ⟨_, _, .structured hrun⟩
  · exact absurd hexit (exitsCoveredByBlocks_noEscapeE (Core.EvalCommandE π) _
      (by simp [Stmt.exitsCoveredByBlocks, Block.exitsCoveredByBlocks]) _ lbl ρ')

/-- **`call z := CountUp()` meets a total-correctness triple**: from an entry where `z`
    holds an integer, the call terminates with `z` holding `10`. -/
theorem countUp_call_total :
    Core.Logic.HoareTotal.Triple π testParams CallPre
      [Core.Statement.call "CountUp" none upCall .empty] CallPost
      (factory := countPgmAST.factoryBeforeProcedure "CountUp") := by
  have hfactory : countPgmAST.factoryBeforeProcedure "CountUp" = Core.Factory :=
    Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)
  refine Core.Logic.HoareTotal.Procedure.call_of_contract countPgmAST testParams "CountUp"
    upCall .empty CallPre CallPost
    (Core.Logic.Hoare.Procedure.contractTriple_of_contractTripleTotal
      countUp_meets_contract_total)
    ⟨_, up_callee⟩ up_body_frame up_body_outputs ?_
    (fun _ _ _ _ _ _ _ =>
      _root_.Core.Specification.axiomsBeforeProcedureDecl_of_noAxioms (by native_decide) _)
    ?_ ?_ ?_ ?_
    (fun _ _ _ _ _ hlk ho _ => by
      rw [Option.some.inj (hlk.symm.trans up_callee), up_body_eq] at ho; cases ho)
  · -- hentry: the contract precondition and the body's gate hold at the callee entry.
    intro ρ₀ proc σAO ⟨hfac, k, hz⟩ _ hlk hce
    obtain rfl : proc = upProc := Option.some.inj (hlk.symm.trans up_callee)
    obtain ⟨w, hzw, _, rfl⟩ := up_callEntry_inv hce
    obtain rfl : w = intOf ρ₀.factory k := Option.some.inj (hzw.symm.trans hz)
    rw [up_body_eq]
    simp only [Imperative.Body.isOpaque, Bool.false_eq_true, ↓reduceIte]
    exact up_entry hfac k
  · -- hexit: the write-back puts `10` into `z`.
    intro ρ₀ proc ρ' σ' σAO ⟨hfac, _⟩ _ hlk hpost hout hρ' _ _ hcx
    obtain rfl : proc = upProc := Option.some.inj (hlk.symm.trans up_callee)
    rw [hfactory] at hpost
    have hy := y10_of_post (show Pinned ρ' by rw [Pinned, hρ']; exact hfac) hpost hout
    rw [hρ'] at hy
    obtain ⟨_, vals, hRV, hUpd, -⟩ := hcx
    rw [up_outputParams] at hRV
    cases hRV with
    | read_some hy' _ hRV2 =>
      cases hRV2
      obtain rfl := Option.some.inj (hy'.symm.trans hy)
      cases hUpd with
      | update_some hu hUpd2 =>
        cases hUpd2
        cases hu with
        | update _ hnew _ => exact ⟨hfac, hnew⟩
  · -- hcallEntry: the call has a callee entry store.
    intro ρ₀ proc ⟨_, k, hz⟩ hwf hlk
    obtain rfl : proc = upProc := Option.some.inj (hlk.symm.trans up_callee)
    exact ⟨_, up_callEntry hz (hwf.storeWellDefined zId _ hz)⟩
  · -- hbodyRun: some run of the body finishes from the callee entry.
    intro ρ₀ proc σAO ⟨hfac, k, hz⟩ _ hlk _ hce
    obtain rfl : proc = upProc := Option.some.inj (hlk.symm.trans up_callee)
    obtain ⟨w, hzw, _, rfl⟩ := up_callEntry_inv hce
    obtain rfl : w = intOf ρ₀.factory k := Option.some.inj (hzw.symm.trans hz)
    exact up_bodyRun hfac k
  · -- hcallExit: every finished run of the body has a write-back into `z`, since it leaves
    -- `y` holding an integer.
    intro ρ₀ proc σAO σEnd bodyEvents ⟨_, k, hz⟩ _ hlk _ hb
    obtain rfl : proc = upProc := Option.some.inj (hlk.symm.trans up_callee)
    obtain ⟨w, hw, hwt⟩ := up_run_yInt hb
    refine ⟨SemanticStore.update ρ₀.store zId w,
      by simp [upCall, Imperative.CallArg.getLhs], [w], ?_, ?_, ?_⟩
    · rw [up_outputParams]; exact .read_some hw hwt.1 .read_none
    · exact .update_some (UpdateState.of_update hz) .update_none
    · exact .cons ⟨_, intLTy, hz, ⟨rfl, rfl⟩, hwt⟩ .nil

/-! ## A call to an abstract callee

The same call, in a program where `CountUp` keeps its contract but has no body (`absPgmAST`).
The callee is then abstract, so the call runs its contract: it havocs `y` and assumes
`ensures y == 10`. `HoareTotal.Procedure.call_of_contract` derives `z == 10` from that contract
alone (`countUpAbs_call_total`); the premises about the body's runs hold vacuously, and the
write-back from the callee entry store is the only fact the call needs to run. -/

/-- `CountUp` without a body. -/
private abbrev absProc : Core.Procedure := { upProc with body := .abstract }

/-- `countPgmAST` with `CountUp` replaced by `absProc`. -/
private def absPgmAST : Core.Program :=
  { decls := countPgmAST.decls.map fun d => match d with
      | .proc q md => if q.header.name.name = "CountUp" then .proc absProc md else d
      | d => d }

/-- The procedures of `absPgmAST`, by name. -/
private abbrev πA : String → Option Core.Procedure := absPgmAST.findProcByString?

/-- `CountUp` is found by name in `absPgmAST`, without its body. -/
private theorem abs_find : πA "CountUp" = some absProc := by native_decide

/-- A call to `CountUp` without type arguments runs `absProc`. -/
private theorem abs_callee : Calls.typeInstantiatedCallee πA "CountUp" none = some absProc :=
  (Core.Procedure.typeInstantiatedCallee_of_typeArgs_nil abs_find (by native_decide)).2 ⟨rfl, rfl⟩

/-- `absPgmAST` declares no function, so its factory before `CountUp` is `Core.Factory`. -/
private theorem abs_factory : absPgmAST.factoryBeforeProcedure "CountUp" = Core.Factory :=
  Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)

/-- **`call z := CountUp()` to the abstract `CountUp` meets a total-correctness triple**: from
    an entry where `z` holds an integer, the call terminates with `z` holding `10`, by
    `CountUp`'s contract alone. -/
theorem countUpAbs_call_total :
    Core.Logic.HoareTotal.Triple πA testParams CallPre
      [Core.Statement.call "CountUp" none upCall .empty] CallPost
      (factory := absPgmAST.factoryBeforeProcedure "CountUp") := by
  have hfactory : countPgmAST.factoryBeforeProcedure "CountUp" = Core.Factory :=
    Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)
  have hop : Imperative.ProcedureHeader.outputParams (P := Core.Expression) absProc.header =
      [yId] := up_outputParams
  refine Core.Logic.HoareTotal.Procedure.call_of_contract absPgmAST testParams "CountUp"
    upCall .empty CallPre CallPost
    ⟨absProc, abs_find, fun tys proc hinst => ?_⟩ ⟨_, abs_callee⟩
    (fun proc hlk _ _ _ _ hb => by
      obtain rfl := Option.some.inj (hlk.symm.trans abs_callee)
      cases hb)
    (fun proc hlk _ _ _ _ _ _ hb => by
      obtain rfl := Option.some.inj (hlk.symm.trans abs_callee)
      cases hb)
    ?_
    (fun _ _ _ _ _ _ _ =>
      _root_.Core.Specification.axiomsBeforeProcedureDecl_of_noAxioms (by native_decide) _)
    ?_ ?_
    (fun _ proc _ _ _ hlk ho _ => by
      obtain rfl := Option.some.inj (hlk.symm.trans abs_callee)
      cases ho)
    (fun _ proc _ _ _ _ _ hlk _ hb => by
      obtain rfl := Option.some.inj (hlk.symm.trans abs_callee)
      cases hb)
    ?_
  · -- hcontract: `absProc` has no type parameters, its contract type-checks, and an abstract
    -- body asks for nothing.
    obtain ⟨rfl, rfl⟩ :=
      (Core.Procedure.instantiateTypes_of_typeArgs_nil (by native_decide)).1 hinst
    exact ⟨by native_decide, trivial⟩
  · -- hentry: the contract precondition holds at the callee entry, as for `CountUp`.
    intro ρ₀ proc σAO ⟨hfac, k, hz⟩ _ hlk hce
    obtain rfl := Option.some.inj (hlk.symm.trans abs_callee)
    obtain ⟨w, hzw, _, rfl⟩ := up_callEntry_inv hce
    obtain rfl : w = intOf ρ₀.factory k := Option.some.inj (hzw.symm.trans hz)
    have hpre := (up_entry hfac k).1
    rw [hfactory] at hpre
    rw [abs_factory]
    exact ⟨hpre, trivial⟩
  · -- hexit: the assumed postcondition puts `10` into `y`, which the write-back copies to `z`.
    intro ρ₀ proc ρ' σ' σAO ⟨hfac, _⟩ _ hlk hpost hout hρ' _ _ hcx
    obtain rfl := Option.some.inj (hlk.symm.trans abs_callee)
    rw [abs_factory] at hpost
    have hy := y10_of_post (show Pinned ρ' by rw [Pinned, hρ']; exact hfac) hpost hout
    rw [hρ'] at hy
    obtain ⟨_, vals, hRV, hUpd, -⟩ := hcx
    rw [hop] at hRV
    cases hRV with
    | read_some hy' _ hRV2 =>
      cases hRV2
      obtain rfl := Option.some.inj (hy'.symm.trans hy)
      cases hUpd with
      | update_some hu hUpd2 =>
        cases hUpd2
        cases hu with
        | update _ hnew _ => exact ⟨hfac, hnew⟩
  · -- hcallEntry: the call has a callee entry store.
    intro ρ₀ proc ⟨_, k, hz⟩ hwf hlk
    obtain rfl := Option.some.inj (hlk.symm.trans abs_callee)
    exact ⟨_, up_callEntry hz (hwf.storeWellDefined zId _ hz)⟩
  · -- hcallExitOpaque: the entry store, where `y` holds `z`'s integer, writes back into `z`.
    intro ρ₀ proc σAO ⟨_, k, hz⟩ _ hlk _ hce
    obtain rfl := Option.some.inj (hlk.symm.trans abs_callee)
    obtain ⟨w, hzw, _, rfl⟩ := up_callEntry_inv hce
    obtain rfl : w = intOf ρ₀.factory k := Option.some.inj (hzw.symm.trans hz)
    refine ⟨SemanticStore.update ρ₀.store zId (intOf ρ₀.factory k),
      by simp [upCall, Imperative.CallArg.getLhs], [intOf ρ₀.factory k], ?_, ?_, ?_⟩
    · rw [hop]; exact .read_some (by simp [SemanticStore.update]) rfl .read_none
    · exact .update_some (UpdateState.of_update hz) .update_none
    · exact .cons ⟨_, intLTy, hz, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ .nil

end Strata.HoareTotalCallTest
