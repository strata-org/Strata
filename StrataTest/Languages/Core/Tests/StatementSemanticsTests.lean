/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.StatementSemanticsProps
import all Strata.Languages.Core.StatementSemantics
import all Strata.Languages.Core.Statement
import all Strata.Languages.Core.Procedure
import all Strata.Util.ListMap

/-!
# Core call-semantics tests

This module checks collision-free initialization of input, inout, and output-only
formals; selection of call-site contract clauses; chronological contract and
body events from `EvalCommandE` and `EvalCommandContractE`; and nested
executable call-body evaluation.

Jump to the "MAIN TESTS" section to look at the top-level tests in this file.
Lines before "MAIN TESTS" are auxiliary lemmas and definitions.

Each `example` is an anonymous theorem. `UniqueResult R σ result` combines a
concrete derivation `R σ result` with a universal inversion property: every
derivation of `R` has both `σ` as its output store and `result` as its observation.
Thus the examples establish that the displayed store and event trace are the
only possible result, rather than merely one reachable result.
Examples with output havoc keep their abstract contract derivations separate
because that relation is intentionally nondeterministic.
-/

namespace Core.StatementSemanticsTests

open Imperative

private def intVal (n : Int) : Expression.Expr := .intConst () n
/-- The integer `n` as a value of the factory `fac`. -/
private def intV (fac : Expression.Factory) (n : Int) : Expression.Val :=
  ⟨fac.model.tcInterp, .int, (n : Int)⟩
private def calleeY : Expression.Ident := ⟨"y", ()⟩
private def callerResult : Expression.Ident := ⟨"result", ()⟩

private def assertEvent (fac : Expression.Factory) (σ : CoreStore)
    (label : String) (expr : Expression.Expr) : Event Expression :=
  .assert { factory := fac, store := σ, label, expr, metadata := .empty }

private def assumeEvent (fac : Expression.Factory) (σ : CoreStore)
    (label : String) (expr : Expression.Expr) : Event Expression :=
  .assume { factory := fac, store := σ, label, expr, metadata := .empty }

private def oneInputProc (y : Expression.Ident) (ty : Lambda.LMonoTy) : Procedure :=
  { header :=
      { name := ⟨"callee", ()⟩
        typeArgs := []
        inputs := [(y, ty)]
        outputs := [] }
    spec := { preconditions := [], postconditions := [] }
    body := .structured [] }

private def oneOutputProc (y : Expression.Ident) (ty : Lambda.LMonoTy) : Procedure :=
  { header :=
      { name := ⟨"callee", ()⟩
        typeArgs := []
        inputs := []
        outputs := [(y, ty)] }
    spec := { preconditions := [], postconditions := [] }
    body := .structured [] }

private def oneInoutProc (y : Expression.Ident) (ty : Lambda.LMonoTy) : Procedure :=
  { header :=
      { name := ⟨"callee", ()⟩
        typeArgs := []
        inputs := [(y, ty)]
        outputs := [(y, ty)] }
    spec := { preconditions := [], postconditions := [] }
    body := .structured [] }

private def oldCalleeY : Expression.Ident := CoreIdent.mkOld calleeY.name

private def oldYIs7 : Expression.Expr :=
  Lambda.LExpr.eq ()
    (Lambda.LExpr.fvar () oldCalleeY (some .int)) (intVal 7)

private def oneInoutOldProc : Procedure :=
  { oneInoutProc calleeY .int with
    spec := { preconditions := [], postconditions := [("old", { expr := oldYIs7 })] } }

private def oneInputContractProc (y : Expression.Ident) (ty : Lambda.LMonoTy)
    (pre post : Expression.Expr) : Procedure :=
  { header := (oneInputProc y ty).header
    spec :=
      { preconditions := [("pre", { expr := pre })]
        postconditions := [("post", { expr := post })] }
    body := .structured [] }

private def oneInputContractBodyProc (y : Expression.Ident) (ty : Lambda.LMonoTy)
    (pre post bodyCheck : Expression.Expr) : Procedure :=
  { oneInputContractProc y ty pre post with
    body := .structured [Statement.assert "body" bodyCheck .empty] }

private def passingBodyProc : Procedure :=
  oneInputContractBodyProc calleeY .int HasBool.tt HasBool.tt HasBool.tt

private def failingBodyProc : Procedure :=
  oneInputContractBodyProc calleeY .int HasBool.tt HasBool.tt HasBool.ff

/-! ## Reusable construction lemmas

The examples below take no semantic witnesses as hypotheses. Procedure lookup,
literal evaluation, frame initialization, empty and single-assert body execution,
contract checks, havoc, reads, and updates are all constructed from the concrete
fixtures above. The remaining universally quantified parameters (`fac` and
`σ`) keep store-independent scenarios general; they do not assume semantic
facts.

-/

/-- A procedure environment resolving the single name `"callee"` to `p`, and no
    other name. -/
private def calleeEnv (p : Procedure) : String → Option Procedure :=
  fun n => if n = "callee" then some p else none

/-- `calleeEnv p` resolves the name `"callee"` to `p`. -/
private theorem calleeEnv_callee (p : Procedure) :
    calleeEnv p "callee" = some p := by
  simp [calleeEnv]

/-- The callee-local frame store for a one-parameter callee whose sole formal
    `calleeY` is bound to `v`: `emptyStore` extended with `calleeY ↦ v`. -/
private def calleeFrame (v : Expression.Val) : CoreStore :=
  updatedState emptyStore calleeY v

/-- The callee frame after snapshotting the incoming value of its inout formal. -/
private def inoutFrame (v : Expression.Val) : CoreStore :=
  withOldSnapshots [calleeY] (calleeFrame v)

/-- The collision-free frame of a one-inout callee binds both the current formal
    and its `old` snapshot to the incoming value. -/
private theorem initCallFrame_oneInout (v : Expression.Val) :
    InitCallFrame (oneInoutProc calleeY .int) [v] [] (inoutFrame v) := by
  unfold InitCallFrame
  refine ⟨calleeFrame v, calleeFrame v, ?_, ?_, ?_⟩
  · show InitStates emptyStore [calleeY] [v] (calleeFrame v)
    exact .init_some (updatedStateInit rfl) .init_none
  · simpa [oneInoutProc, Calls.outputOnlyParams, ProcedureHeader.inputParams,
      ProcedureHeader.outputParams, ListMap.keys, List.contains_eq_mem] using
      (InitStates.init_none : InitStates (calleeFrame v) [] [] (calleeFrame v))
  · simp [inoutFrame, oneInoutProc, Calls.inoutParams, ProcedureHeader.inputParams,
      ProcedureHeader.outputParams, ListMap.keys, List.contains_eq_mem]

/-- Reading the inout actual from the caller evaluates to its stored value. -/
private theorem evalExpressions_inout
    (fac : Expression.Factory) (v : Expression.Val) (hv : HasVal.value fac v) :
    EvalExpressions fac (calleeFrame v)
      [Lambda.LExpr.fvar () calleeY none] [v] := by
  apply EvalExpressions.eval_some
  · simp [SemanticStore.varsDefined, HasFvars.getFvars, Lambda.LExpr.LExpr.getVars,
      calleeFrame, updatedState]
  · exact Lambda.LExpr.denoteEval_fvar (T := CoreLParams)
      (by simp [calleeFrame, updatedState]) hv
  · exact .eval_none

/-- An integer literal has no free variables and evaluates to its value, in any
    factory and store. -/
private theorem evalExpressions_intVal
    (fac : Expression.Factory) (σ : CoreStore) (n : Int) :
    EvalExpressions fac σ [intVal n] [intV fac n] := by
  apply EvalExpressions.eval_some
  · simp [SemanticStore.varsDefined, intVal, HasFvars.getFvars, Lambda.LExpr.LExpr.getVars]
  · exact Lambda.LExpr.denoteEval_intConst (T := CoreLParams)
  · exact EvalExpressions.eval_none

/-- Snapshotting an empty list leaves the store unchanged. -/
private theorem withOldSnapshots_nil (σ : CoreStore) : withOldSnapshots [] σ = σ := rfl

/-- The collision-free frame of a one-input callee binds its input formal
    `calleeY` to the evaluated argument, leaving `calleeFrame v`. -/
private theorem initCallFrame_oneInput (ty : Lambda.LMonoTy) (v : Expression.Val) :
    InitCallFrame (oneInputProc calleeY ty) [v] [] (calleeFrame v) := by
  refine ⟨calleeFrame v, calleeFrame v, ?_, ?_, ?_⟩
  · show InitStates emptyStore [calleeY] [v] (calleeFrame v)
    exact InitStates.init_some (updatedStateInit rfl) InitStates.init_none
  · show InitStates (calleeFrame v) [] [] (calleeFrame v)
    exact InitStates.init_none
  · show calleeFrame v = withOldSnapshots [] (calleeFrame v)
    exact (withOldSnapshots_nil _).symm

/-- The collision-free frame of a one-output-only callee copies the caller value
    `v` into the output formal `calleeY`, leaving `calleeFrame v`. -/
private theorem initCallFrame_oneOutput (ty : Lambda.LMonoTy) (v : Expression.Val) :
    InitCallFrame (oneOutputProc calleeY ty) [] [v] (calleeFrame v) := by
  refine ⟨emptyStore, calleeFrame v, ?_, ?_, ?_⟩
  · show InitStates emptyStore [] [] emptyStore
    exact InitStates.init_none
  · show InitStates emptyStore [calleeY] [v] (calleeFrame v)
    exact InitStates.init_some (updatedStateInit rfl) InitStates.init_none
  · show calleeFrame v = withOldSnapshots [] (calleeFrame v)
    exact (withOldSnapshots_nil _).symm

/-- An empty structured body emits no events and leaves its store and factory
    unchanged. -/
private theorem emptyBodyExecE
    (π : String → Option Procedure)

    (σ : CoreStore) (fac : Expression.Factory) :
    CoreBodyExecE π (.structured []) ⟨σ, fac⟩ σ [] := by
  have hstar : CoreStepStarE π
      (.stmt (Stmt.block "" [] #[]) ⟨σ, fac⟩) []
      (.terminal ⟨projectStore σ σ, fac⟩) := by
    refine ReflTransTrace.step _ [] _ [] _
      (StepStmtE.step_block) ?_
    refine ReflTransTrace.step _ [] _ [] _
      (StepStmtE.step_block_body (StepStmtE.step_stmts_nil)) ?_
    refine ReflTransTrace.step _ [] _ [] _
      (StepStmtE.step_block_done) ?_
    exact ReflTransTrace.refl _
  have h := CoreBodyExecE.structured (π := π) (ss := [])
    (ρ := ⟨σ, fac⟩) (ρ' := ⟨projectStore σ σ, fac⟩) hstar
  simpa [projectStore_self] using h

/-- Reading the slot just written by `calleeFrame` returns the written value,
    provided that it is a value of the factory. -/
private theorem readValues_calleeFrame
    (fac : Expression.Factory) (v : Expression.Val) (hv : HasVal.value fac v) :
    ReadValues fac (calleeFrame v) [calleeY] [v] := by
  have hlk : (calleeFrame v) calleeY = some v := by
    have hinit : InitState Expression emptyStore calleeY v (calleeFrame v) :=
      updatedStateInit rfl
    cases hinit with
    | init _ hsome _ => exact hsome
  exact ReadValues.read_some hlk hv ReadValues.read_none

/-- Writing a slot's current value back to itself leaves the store unchanged. -/
private theorem updateStates_id_single
    {σ : CoreStore} {y : Expression.Ident} {v : Expression.Val}
    (h : σ y = some v) : UpdateStates σ [y] [v] σ :=
  .update_some (.update h h (fun _ _ => rfl)) .update_none

/-! ### Concrete Boolean-literal and assert-body helpers

These examples specialize clause and body expressions to the Boolean literals
`true` and `false`, then construct their evaluations with the helpers below.
The helpers hold in every runtime factory, so the examples quantify over one.

-/

/-- A Boolean literal evaluates to its value in any factory and store. -/
private theorem eval_boolConst (fac : Expression.Factory) (σ : CoreStore) (b : Bool) :
    Expression.eval fac σ (Lambda.LExpr.boolConst () b)
      = some (Lambda.SemValue.ofBool fac.model.tcInterp b) :=
  Lambda.LExpr.denoteEval_boolConst

/-- An integer literal is a value in every factory. -/
private theorem intVal_value (fac : Expression.Factory) (n : Int) :
    HasVal.value fac (intV fac n) :=
  rfl

/-- An integer has Core's monomorphic integer type. -/
private theorem intVal_valueOfTy (fac : Expression.Factory) (n : Int) :
    HasVal.valueOfTy fac (intV fac n) (Lambda.LTy.forAll [] .int) :=
  ⟨rfl, rfl⟩

/-- Boolean `true` is not a Core integer value. -/
private theorem true_not_int (fac : Expression.Factory) :
    ¬ HasVal.valueOfTy fac (HasBool.ttVal fac) (Lambda.LTy.forAll [] .int) := by
  simp [HasVal.valueOfTy, HasBool.ttVal, Lambda.SemValue.ofBool, Lambda.LTy.toMonoType?,
    Lambda.LSort.toMonoTy, Lambda.LMonoTy.int]

/-- The current inout formal keeps its incoming value in the snapshotted frame. -/
private theorem inoutFrame_current {fac : Expression.Factory} :
    inoutFrame (intV fac 7) calleeY = some (intV fac 7) := by
  simp [inoutFrame, Calls.withOldSnapshots, calleeFrame, updatedState,
    calleeY, HasOldIdent.mkOld, CoreIdent.mkOld, CoreIdent.oldStr]

/-- Havocing the integer inout slot preserves its integer type. -/
private theorem havocVars_inout_int_typed (fac : Expression.Factory) {σ' : CoreStore}
    (h : HavocVars fac (inoutFrame (intV fac 7)) [calleeY] σ') :
    ∃ v, σ' calleeY = some v ∧
      HasVal.valueOfTy fac v (Lambda.LTy.forAll [] .int) := by
  cases h with
  | update_some hup hstored htail =>
    cases htail
    obtain ⟨previous, ty, hprevious, hpTy, hvTy⟩ := hstored
    have hprev : previous = intV fac 7 :=
      Option.some.inj (hprevious.symm.trans inoutFrame_current)
    subst previous
    have hvInt := LawfulHasVal.valueOfTy_congr fac (intV fac 7) _
      (Lambda.LTy.forAll [] .int) ty (intVal_valueOfTy fac 7) hpTy hvTy
    cases hup with
    | update _ hx _ => exact ⟨_, hx, hvInt⟩

/-- Havocing an integer slot cannot replace it with Boolean `true`. -/
private theorem havocVars_inout_not_true (fac : Expression.Factory) :
    ¬ HavocVars fac (inoutFrame (intV fac 7)) [calleeY]
      (updatedState (inoutFrame (intV fac 7)) calleeY (HasBool.ttVal fac)) := by
  intro h
  obtain ⟨v, hv, hvTy⟩ := havocVars_inout_int_typed fac h
  have htrue : updatedState (inoutFrame (intV fac 7)) calleeY (HasBool.ttVal fac) calleeY =
      some (HasBool.ttVal fac) := by simp [updatedState]
  have : v = (HasBool.ttVal fac) := Option.some.inj (hv.symm.trans htrue)
  subst v
  exact true_not_int fac hvTy

/-- The old identifier reads the inout formal's incoming value. -/
private theorem inoutFrame_old {fac : Expression.Factory} :
    inoutFrame (intV fac 7) oldCalleeY = some (intV fac 7) := by
  simp [inoutFrame, Calls.withOldSnapshots, oldCalleeY, calleeY, calleeFrame,
    updatedState, HasOldIdent.mkOld, CoreIdent.mkOld, CoreIdent.oldStr]

/-- The old-value postcondition holds whenever the old slot contains seven. -/
private theorem oldYIs7_eval (fac : Expression.Factory) (σ : CoreStore)
    (hold : σ oldCalleeY = some (intV fac 7)) :
    Expression.eval fac σ oldYIs7 = some (HasBool.ttVal fac) := by
  exact Lambda.LExpr.denoteEval_eq_true (T := CoreLParams)
    (Lambda.LExpr.denoteEval_fvar hold rfl) Lambda.LExpr.denoteEval_intConst

/-- A one-assert body `{ assert [label]: e }`
    leaves its store and factory unchanged and emits exactly the single captured
    assert event, for any condition `e` (event semantics never evaluates it, so no
    truth-value or well-formedness premise is needed). -/
private theorem assertBodyExecE
    (π : String → Option Procedure)

    (fac : Expression.Factory) (σ : CoreStore)
    (label : String) (e : Expression.Expr) :
    CoreBodyExecE π (.structured [Statement.assert label e .empty]) ⟨σ, fac⟩ σ
      [assertEvent fac σ label e] := by
  let ρ : Env Expression := ⟨σ, fac⟩
  have hcmdE : EvalCommandE π fac σ
      (CmdExt.cmd (Cmd.assert label e .empty)) σ [assertEvent fac σ label e] :=
    EvalCommandE.cmd_sem EvalCmdE.eval_assert
  have hstar : CoreStepStarE π
      (.stmt (Stmt.block "" [Statement.assert label e .empty] #[]) ρ)
      [assertEvent fac σ label e]
      (.terminal ⟨projectStore σ σ, fac⟩) := by
    refine ReflTransTrace.step _ [] _ _ _
      (StepStmtE.step_block) ?_
    refine ReflTransTrace.step _ [] _ _ _
      (StepStmtE.step_block_body (StepStmtE.step_stmts_cons)) ?_
    refine ReflTransTrace.step _ [assertEvent fac σ label e] _ _ _
      (StepStmtE.step_block_body (StepStmtE.step_seq_inner (StepStmtE.step_cmd hcmdE))) ?_
    refine ReflTransTrace.step _ [] _ _ _
      (StepStmtE.step_block_body (StepStmtE.step_seq_done)) ?_
    refine ReflTransTrace.step _ [] _ _ _
      (StepStmtE.step_block_body (StepStmtE.step_stmts_nil)) ?_
    refine ReflTransTrace.step _ [] _ _ _
      (StepStmtE.step_block_done) ?_
    exact ReflTransTrace.refl _
  have h := CoreBodyExecE.structured (π := π)
    (ss := [Statement.assert label e .empty]) (ρ := ⟨σ, fac⟩)
    (ρ' := ⟨projectStore σ σ, fac⟩) hstar
  simpa [projectStore_self] using h

/-- Two executions of the same one-assert event body have identical stores,
factories, and traces. -/
private theorem assertBodyExecEUnique
    {π : String → Option Procedure}

    {fac : Expression.Factory} {σ end₁ end₂ : CoreStore}
    {label : String} {e : Expression.Expr}
    {emitted₁ emitted₂ : Trace Expression}
    (h₁ : CoreBodyExecE π (.structured [Statement.assert label e .empty])
      ⟨σ, fac⟩ end₁ emitted₁)
    (h₂ : CoreBodyExecE π (.structured [Statement.assert label e .empty])
      ⟨σ, fac⟩ end₂ emitted₂) :
    end₁ = end₂ ∧ emitted₁ = emitted₂ :=
  h₁.singleton_cmd_unique EvalCommandE.assert_unique h₂

/-- `R` produces the expected observation at `expected`, and every derivation of
`R` produces that same output store and observation. -/
private def UniqueResult {α : Type _} (R : CoreStore → α → Prop)
    (expected : CoreStore) (observation : α) : Prop :=
  R expected observation ∧
    ∀ σ' result, R σ' result → σ' = expected ∧ result = observation

/-- Two executions of the same empty event body have identical stores,
factories, and traces. -/
private theorem emptyBodyExecEUnique
    {π : String → Option Procedure}

    {fac : Expression.Factory} {σ end₁ end₂ : CoreStore}
    {emitted₁ emitted₂ : Trace Expression}
    (h₁ : CoreBodyExecE π (.structured []) ⟨σ, fac⟩ end₁ emitted₁)
    (h₂ : CoreBodyExecE π (.structured []) ⟨σ, fac⟩ end₂ emitted₂) :
    end₁ = end₂ ∧ emitted₁ = emitted₂ := by
  obtain ⟨hstore₁, hemitted₁⟩ := h₁.empty_unique π σ end₁ fac emitted₁
  obtain ⟨hstore₂, hemitted₂⟩ := h₂.empty_unique π σ end₂ fac emitted₂
  exact ⟨hstore₁.trans hstore₂.symm, hemitted₁.trans hemitted₂.symm⟩

/-- Package an event call witness with pairwise store-and-trace determinism. -/
private theorem uniqueEvalCommandE
    {π : String → Option Procedure}

    {fac : Expression.Factory} {σ expected : CoreStore} {n : String}
    {p : Procedure} {args : List (CallArg Expression)}
    {md : MetaData Expression} {emitted : Trace Expression}
    (hLookup : π n = some p)
    (hBodyUnique : ∀ {frame end₁ end₂ : CoreStore}
      {bodyEvents₁ bodyEvents₂ : Trace Expression},
      CoreBodyExecE π p.body ⟨frame, fac⟩ end₁ bodyEvents₁ →
      CoreBodyExecE π p.body ⟨frame, fac⟩ end₂ bodyEvents₂ →
      end₁ = end₂ ∧ bodyEvents₁ = bodyEvents₂)
    (h : EvalCommandE π fac σ (.call n args md) expected emitted) :
    UniqueResult (EvalCommandE π fac σ (.call n args md)) expected emitted :=
  ⟨h, fun _ _ h' => h'.call_unique_of_body_unique hLookup hBodyUnique h⟩

/-- Package a no-output event contract call witness with pairwise
store-and-trace determinism. -/
private theorem uniqueEvalCommandContractE
    {π : String → Option Procedure} {fac : Expression.Factory}
    {σ expected : CoreStore} {n : String} {p : Procedure}
    {args : List (CallArg Expression)} {md : MetaData Expression}
    {emitted : Trace Expression}
    (hLookup : π n = some p) (hOutputs : ListMap.keys p.header.outputs = [])
    (h : EvalCommandContractE π fac σ (.call n args md) expected emitted) :
    UniqueResult (EvalCommandContractE π fac σ (.call n args md)) expected emitted :=
  ⟨h, fun _ _ h' => h'.call_unique_of_outputs_nil hLookup hOutputs h⟩

/-=============================================================================
                                    MAIN TESTS
=============================================================================-/

/-! ## Example 1.
    Executable calls use the collision-free frame and return through the original
    caller store when there are no outputs.

Core-style pseudocode:
```core
procedure Callee(y : int) { };
procedure Caller() {
  var y : int := 1;
  call Callee(2);
  assert y == 1; // No callee output is written back to the caller.
};
```
-/
example

    (fac : Expression.Factory) (σ : CoreStore) :
    -- Both semantics have a unique complete result: `σ` plus no events.
    UniqueResult
      (EvalCommandE (calleeEnv (oneInputProc calleeY .int)) fac σ
        (.call "callee" [.inArg (intVal 2)] .empty)) σ [] ∧
    UniqueResult
      (EvalCommandContractE (calleeEnv (oneInputProc calleeY .int)) fac σ
        (.call "callee" [.inArg (intVal 2)] .empty)) σ [] := by
  refine ⟨?_, ?_⟩
  · apply uniqueEvalCommandE (calleeEnv_callee _) emptyBodyExecEUnique
    simpa [defaultAssertEvents, Calls.defaultAssertEvents, Calls.checksAtCall,
      MetaData.setCallSiteFileRange_empty, ListMap.toList, oneInputProc] using
      EvalCommandE.call_sem (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal fac σ 2, .read_none, initCallFrame_oneInput .int (intV fac 2)⟩
        (emptyBodyExecE _ _ _)
            ⟨(by simp [Imperative.CallArg.getLhs]), _, .read_none, .update_none, .nil⟩
  · apply uniqueEvalCommandContractE (calleeEnv_callee _) (by rfl)
    simpa [defaultAssertEvents, Calls.defaultAssertEvents, Calls.checksAtCall,
      MetaData.setCallSiteFileRange_empty, ListMap.toList, assumeEvents,
      Calls.assumeEvents, oneInputProc] using
      EvalCommandContractE.call_sem (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal fac σ 2, .read_none, initCallFrame_oneInput .int (intV fac 2)⟩
        .update_none ⟨(by simp [Imperative.CallArg.getLhs]), _, .read_none, .update_none, .nil⟩

/-! ## Example 2.
    An inout actual may have the same identifier as the callee formal. The frame
    copies the incoming value once and keeps it under `old y`, even when contract
    semantics later havocs the current value.

Core-style pseudocode:
```core
procedure Callee(inout y : int)
spec {
  ensures old(y) == 7;
} { };
procedure Caller() {
  var y : int := 7;
  call Callee(inout y);
};
```
-/

private def inoutResultStore (fac : Expression.Factory) : CoreStore :=
  updatedState (calleeFrame (intV fac 7)) calleeY (intV fac 9)

example

    (fac : Expression.Factory) :
    -- Concrete semantics uniquely determines both `y = 7` and its displayed
    -- trace. Contract semantics is intentionally
    -- nondeterministic and exhibits the allowed `y = 9` choice below.
    UniqueResult
      (EvalCommandE (calleeEnv oneInoutOldProc) fac (calleeFrame (intV fac 7))
        (.call "callee" [.inoutArg calleeY] .empty))
      (calleeFrame (intV fac 7))
      [assertEvent fac (inoutFrame (intV fac 7)) "old" oldYIs7] ∧
    EvalCommandContractE (calleeEnv oneInoutOldProc) fac
      (calleeFrame (intV fac 7))
      (.call "callee" [.inoutArg calleeY] .empty)
      (inoutResultStore fac)
      [assumeEvent fac
        (updatedState (inoutFrame (intV fac 7)) calleeY (intV fac 9))
        "old" oldYIs7] := by
  have hframe : InitCallFrame oneInoutOldProc [intV fac 7] []
      (inoutFrame (intV fac 7)) := by
    simpa [oneInoutOldProc, Calls.InitCallFrame] using initCallFrame_oneInout (intV fac 7)
  have hentry : CallEntry fac (calleeFrame (intV fac 7)) oneInoutOldProc
      [.inoutArg calleeY] (inoutFrame (intV fac 7)) := by
    unfold CallEntry
    refine ⟨[intV fac 7], [], ?_, .read_none, hframe⟩
    simpa [Calls.getInputExprs, HasFvar.mkFvar] using
      evalExpressions_inout fac (intV fac 7) (intVal_value fac 7)
  have hcaller : calleeFrame (intV fac 7) calleeY = some (intV fac 7) := by
    simp [calleeFrame, updatedState]
  have hread : ReadValues fac (inoutFrame (intV fac 7)) [calleeY] [intV fac 7] :=
    .read_some inoutFrame_current (intVal_value fac 7) .read_none
  have hexit : CallExit fac (calleeFrame (intV fac 7)) oneInoutOldProc
      [.inoutArg calleeY] (inoutFrame (intV fac 7)) (calleeFrame (intV fac 7)) := by
    refine ⟨(by simp [Imperative.CallArg.getLhs]), [intV fac 7], ?_, updateStates_id_single hcaller,
      .cons ⟨_, Lambda.LTy.forAll [] .int, hcaller, intVal_valueOfTy fac 7, intVal_valueOfTy fac 7⟩
          .nil⟩
    simpa [oneInoutOldProc, oneInoutProc, ProcedureHeader.outputParams, ListMap.keys] using hread
  let σO := updatedState (inoutFrame (intV fac 7)) calleeY (intV fac 9)
  have hupd : UpdateState Expression (inoutFrame (intV fac 7)) calleeY
      (intV fac 9) σO := updatedStateUpdate inoutFrame_current
  have hhavoc : HavocVars fac (inoutFrame (intV fac 7)) [calleeY] σO :=
    .update_some hupd
      ⟨intV fac 7, Lambda.LTy.forAll [] .int, inoutFrame_current,
        intVal_valueOfTy fac 7, intVal_valueOfTy fac 9⟩
      .update_none
  have hcurrentO : σO calleeY = some (intV fac 9) := by
    cases hupd with | update _ h _ => exact h
  have holdO : σO oldCalleeY = some (intV fac 7) := by
    cases hupd with
    | update _ _ hother =>
      rw [hother oldCalleeY]
      · exact inoutFrame_old
      · simpa [oldCalleeY] using CoreIdent.ne_mkOld calleeY
  have hreadO : ReadValues fac σO [calleeY] [intV fac 9] :=
    .read_some hcurrentO (intVal_value fac 9) .read_none
  have hcallerUpdate : UpdateStates (calleeFrame (intV fac 7)) [calleeY]
      [intV fac 9] (inoutResultStore fac) :=
    .update_some (updatedStateUpdate hcaller) .update_none
  have hexitO : CallExit fac (calleeFrame (intV fac 7)) oneInoutOldProc
      [.inoutArg calleeY] σO (inoutResultStore fac) := by
    refine ⟨(by simp [Imperative.CallArg.getLhs]), [intV fac 9], ?_, hcallerUpdate,
      .cons ⟨_, Lambda.LTy.forAll [] .int, hcaller, intVal_valueOfTy fac 7,
        intVal_valueOfTy fac 9⟩ .nil⟩
    simpa [oneInoutOldProc, oneInoutProc, ProcedureHeader.outputParams, ListMap.keys] using hreadO
  refine ⟨?_, ?_⟩
  · apply uniqueEvalCommandE (calleeEnv_callee _) emptyBodyExecEUnique
    simpa [MetaData.empty, defaultAssertEvents, Calls.defaultAssertEvents, Calls.checksAtCall,
      MetaData.setCallSiteFileRange_empty, ListMap.toList,
      assertEvent, oneInoutOldProc] using
      EvalCommandE.call_sem (calleeEnv_callee _) hentry
        (emptyBodyExecE _ _ _) hexit
  · simpa [MetaData.empty, defaultAssertEvents, Calls.defaultAssertEvents, Calls.checksAtCall,
      MetaData.setCallSiteFileRange_empty, ListMap.toList,
      assumeEvents, Calls.assumeEvents, assumeEvent,
      oneInoutOldProc, σO] using
      EvalCommandContractE.call_sem (calleeEnv_callee _) hentry hhavoc hexitO

/-! ## Example 3.
    Executable calls copy caller `out` values into output-only formals without
    introducing another nondeterministic value before the body. Concretized: the
    caller holds `result ↦ 7`, and the contract abstraction havocs the output to a
    *different* value `9`; every premise is built internally.

Core-style pseudocode:
```core
procedure Callee(out y : int) {
  // y initially equals result's value (7) immediately before the call.
};
procedure Caller() {
  var result : int := 7;
  call Callee(out result);
  // Concrete: copies 7 into Callee.y, writes 7 back — result stays 7.
  // Contract: *havocs* y to 9 and writes 9 back — result becomes 9.
};
```
-/

/-- Caller store binding `result ↦ 7` immediately before the output-copy call. -/
private def copyCallerStore (fac : Expression.Factory) : CoreStore := updatedState emptyStore
    callerResult (intV fac 7)

/-- Caller store after the contract abstraction writes its (different) abstract
    result `9` back into `result`. -/
private def copyResultStore (fac : Expression.Factory) : CoreStore := updatedState
    (copyCallerStore fac) callerResult (intV fac 9)

example

    (fac : Expression.Factory) :
    -- Concrete semantics uniquely determines `(copyCallerStore fac)` together with
    -- success/no events. Contract semantics is intentionally nondeterministic
    -- and demonstrates the allowed `(copyResultStore fac)` choice.
    UniqueResult
      (EvalCommandE (calleeEnv (oneOutputProc calleeY .int)) fac (copyCallerStore fac)
        (.call "callee" [.outArg callerResult] .empty)) (copyCallerStore fac) [] ∧
    EvalCommandContractE (calleeEnv (oneOutputProc calleeY .int)) fac
        (copyCallerStore fac)
        (.call "callee" [.outArg callerResult] .empty)
        (copyResultStore fac) [] := by

  have hcaller : (copyCallerStore fac) callerResult = some (intV fac 7) := by
    have hinit : InitState Expression emptyStore callerResult (intV fac 7) (copyCallerStore fac) :=
      updatedStateInit rfl
    cases hinit with | init _ hsome _ => exact hsome
  have hcopied : ReadValues fac (copyCallerStore fac) [callerResult] [intV fac 7] :=
    .read_some hcaller (intVal_value fac 7) .read_none
  have hframe := initCallFrame_oneOutput .int (intV fac 7)
  have hresult := readValues_calleeFrame fac (intV fac 7) (intVal_value fac 7)
  have hentry : CallEntry fac (copyCallerStore fac) (oneOutputProc calleeY .int)
      [.outArg callerResult] (calleeFrame (intV fac 7)) :=
    ⟨_, _, .eval_none, hcopied, hframe⟩
  have hexit : CallExit fac (copyCallerStore fac) (oneOutputProc calleeY .int)
      [.outArg callerResult] (calleeFrame (intV fac 7)) (copyCallerStore fac) :=
    ⟨(by simp [Imperative.CallArg.getLhs]), _, hresult, updateStates_id_single hcaller,
      .cons ⟨_, Lambda.LTy.forAll [] .int, hcaller, intVal_valueOfTy fac 7, intVal_valueOfTy fac 7⟩
          .nil⟩
  -- The frame binds `calleeY ↦ 7`; the contract abstraction havocs it to 9.
  have hframeLk : (calleeFrame (intV fac 7)) calleeY = some (intV fac 7) := by
    have hinit : InitState Expression emptyStore calleeY (intV fac 7) (calleeFrame (intV fac 7)) :=
      updatedStateInit rfl
    cases hinit with | init _ hsome _ => exact hsome
  have hupd : UpdateState Expression (calleeFrame (intV fac 7)) calleeY (intV fac 9)
      (updatedState (calleeFrame (intV fac 7)) calleeY (intV fac 9)) := updatedStateUpdate hframeLk
  have hhavoc : HavocVars fac (calleeFrame (intV fac 7)) [calleeY]
      (updatedState (calleeFrame (intV fac 7)) calleeY (intV fac 9)) :=
    .update_some hupd
      ⟨intV fac 7, Lambda.LTy.forAll [] .int, hframeLk,
        intVal_valueOfTy fac 7, intVal_valueOfTy fac 9⟩
      .update_none
  have hσO : (updatedState (calleeFrame (intV fac 7)) calleeY (intV fac 9)) calleeY = some
      (intV fac 9) := by
    cases hupd with | update _ hsome _ => exact hsome
  have hcontractResult : ReadValues fac
      (updatedState (calleeFrame (intV fac 7)) calleeY (intV fac 9))
      [calleeY] [intV fac 9] := .read_some hσO (intVal_value fac 9) .read_none
  have hcontractUpdate : UpdateStates (copyCallerStore fac) [callerResult] [intV fac 9]
      (copyResultStore fac) :=
    .update_some (updatedStateUpdate hcaller) .update_none
  refine ⟨?_, ?_⟩
  · apply uniqueEvalCommandE (calleeEnv_callee _) emptyBodyExecEUnique
    simpa [defaultAssertEvents, Calls.defaultAssertEvents, Calls.checksAtCall,
      MetaData.setCallSiteFileRange_empty, ListMap.toList, oneOutputProc] using
      EvalCommandE.call_sem (calleeEnv_callee _) hentry
        (emptyBodyExecE _ _ _) hexit
  · simpa [defaultAssertEvents, Calls.defaultAssertEvents, Calls.checksAtCall,
      MetaData.setCallSiteFileRange_empty, ListMap.toList, assumeEvents,
      Calls.assumeEvents, oneOutputProc] using
      EvalCommandContractE.call_sem (calleeEnv_callee _)
        ⟨_, _, .eval_none, hcopied, hframe⟩
        hhavoc ⟨(by simp [Imperative.CallArg.getLhs]), _, hcontractResult, hcontractUpdate,
        .cons ⟨_, Lambda.LTy.forAll [] .int, hcaller, intVal_valueOfTy fac 7,
          intVal_valueOfTy fac 9⟩ .nil⟩

/-! ## Example 4.
    A contract-bearing procedure with one body assertion is interpreted by all
    two event call relations. Specialized to the exact literals
    `pre = post = bodyCheck = true` of the pseudocode, so every premise — the
    literal argument's evaluation, both contract clauses, and the executing
    `assert true` body — is discharged internally with no hypotheses.

Core-style pseudocode:
```core
procedure Callee(y : int)
spec {
  requires [pre]: true;
  ensures [post]: true;
} {
  assert [body]: true;
};
procedure Caller() {
  call Callee(0);
};
```
-/
example

    (fac : Expression.Factory) (σ : CoreStore) :
    -- Both no-output calls have the displayed store-observation pair as
    -- their unique complete result; traces distinguish checks from abstraction.
    UniqueResult
      (EvalCommandE (calleeEnv passingBodyProc) fac σ
        (.call "callee" [.inArg (intVal 0)] .empty)) σ
      [assertEvent fac (calleeFrame (intV fac 0)) "pre" HasBool.tt,
       assertEvent fac (calleeFrame (intV fac 0)) "body" HasBool.tt,
       assertEvent fac (calleeFrame (intV fac 0)) "post" HasBool.tt] ∧
    UniqueResult
      (EvalCommandContractE (calleeEnv passingBodyProc) fac σ
        (.call "callee" [.inArg (intVal 0)] .empty)) σ
      [assertEvent fac (calleeFrame (intV fac 0)) "pre" HasBool.tt,
       assumeEvent fac (calleeFrame (intV fac 0)) "post" HasBool.tt] := by

  have hframe : InitCallFrame (passingBodyProc)
      [intV fac 0] [] (calleeFrame (intV fac 0)) := initCallFrame_oneInput (ty := .int) (intV fac 0)
  have hbodyE := assertBodyExecE (calleeEnv (passingBodyProc))
    fac (calleeFrame (intV fac 0)) "body" HasBool.tt
  refine ⟨?_, ?_⟩
  · apply uniqueEvalCommandE (calleeEnv_callee _) (fun h₁ h₂ => by
      simpa [passingBodyProc, oneInputContractBodyProc] using
        assertBodyExecEUnique h₁ h₂)
    simpa [MetaData.empty, passingBodyProc, defaultAssertEvents, Calls.defaultAssertEvents,
      Calls.checksAtCall, MetaData.setCallSiteFileRange_empty,
      ListMap.toList, assertEvent,
      oneInputContractBodyProc, oneInputContractProc] using
      EvalCommandE.call_sem (callArgs := [.inArg (intVal 0)]) (md := .empty) (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal fac σ 0, .read_none, hframe⟩
        hbodyE ⟨(by simp [Imperative.CallArg.getLhs]), _, .read_none, .update_none, .nil⟩
  · apply uniqueEvalCommandContractE (calleeEnv_callee _) (by rfl)
    simpa [MetaData.empty, passingBodyProc, defaultAssertEvents, Calls.defaultAssertEvents,
      Calls.checksAtCall, MetaData.setCallSiteFileRange_empty,
      ListMap.toList, assumeEvents, Calls.assumeEvents,
      assertEvent, assumeEvent, oneInputContractBodyProc, oneInputContractProc] using
      EvalCommandContractE.call_sem (callArgs := [.inArg (intVal 0)]) (md := .empty)
        (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal fac σ 0, .read_none, hframe⟩
        .update_none ⟨(by simp [Imperative.CallArg.getLhs]), _, .read_none, .update_none, .nil⟩

/-- ## Example 5.
    Executable call, FAIL path: a false (`ff`) Default postcondition is emitted as
    an assertion event after the successful body. Specialized to the literals
    `pre = true`, `post = false`. Contract semantics emits the same postcondition
    as an assumption event instead.

Core-style pseudocode:
```core
procedure Callee(y : int)
spec {
  requires [pre]: true;
  ensures [post]: false;
} { };
procedure Caller() {
  call Callee(0); // The post assertion fails after the successful body.
};
```
-/
example

    (fac : Expression.Factory) (σ : CoreStore) :
    -- The unique results retain `σ` and report the displayed events.
    UniqueResult
      (EvalCommandE
        (calleeEnv (oneInputContractProc calleeY .int HasBool.tt HasBool.ff))
        fac σ (.call "callee" [.inArg (intVal 0)] .empty)) σ
      [assertEvent fac (calleeFrame (intV fac 0)) "pre" HasBool.tt,
       assertEvent fac (calleeFrame (intV fac 0)) "post" HasBool.ff] ∧
    UniqueResult
      (EvalCommandContractE
        (calleeEnv (oneInputContractProc calleeY .int HasBool.tt HasBool.ff))
        fac σ (.call "callee" [.inArg (intVal 0)] .empty)) σ
      [assertEvent fac (calleeFrame (intV fac 0)) "pre" HasBool.tt,
       assumeEvent fac (calleeFrame (intV fac 0)) "post" HasBool.ff] := by

  have hframe : InitCallFrame (oneInputContractProc calleeY .int HasBool.tt HasBool.ff)
      [intV fac 0] [] (calleeFrame (intV fac 0)) := initCallFrame_oneInput (ty := .int) (intV fac 0)
  refine ⟨?_, ?_⟩
  · apply uniqueEvalCommandE (calleeEnv_callee _) emptyBodyExecEUnique
    simpa [MetaData.empty, defaultAssertEvents, Calls.defaultAssertEvents, Calls.checksAtCall,
      MetaData.setCallSiteFileRange_empty, ListMap.toList,
      assertEvent, oneInputContractProc] using
      EvalCommandE.call_sem (callArgs := [.inArg (intVal 0)]) (md := .empty) (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal fac σ 0, .read_none, hframe⟩
        (emptyBodyExecE _ _ _)
            ⟨(by simp [Imperative.CallArg.getLhs]), _, .read_none, .update_none, .nil⟩
  · apply uniqueEvalCommandContractE (calleeEnv_callee _) (by rfl)
    simpa [MetaData.empty, defaultAssertEvents, Calls.defaultAssertEvents, Calls.checksAtCall,
      MetaData.setCallSiteFileRange_empty, ListMap.toList,
      assumeEvents, Calls.assumeEvents, assertEvent, assumeEvent,
      oneInputContractProc] using
      EvalCommandContractE.call_sem (callArgs := [.inArg (intVal 0)]) (md := .empty)
        (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal fac σ 0, .read_none, hframe⟩
        .update_none ⟨(by simp [Imperative.CallArg.getLhs]), _, .read_none, .update_none, .nil⟩

/-- ## Example 6.
    Executable call, FAIL path: a failing body assertion is emitted between
    passing pre- and postconditions. The body is the genuine one-assert body
    `assert false`, executed via `assertBodyExecE`. The contract
    relation never executes that body, so its trace has no body event.

Core-style pseudocode:
```core
procedure Callee(y : int)
spec {
  requires [pre]: true;
  ensures [post]: true;
} {
  assert [body]: false;
};
procedure Caller() {
  call Callee(0); // The body assertion fails; both contract checks pass.
};
```
-/
example

    (fac : Expression.Factory) (σ : CoreStore) :
    -- Both displayed store-observation pairs are unique; the concrete trace
    -- has the body assertion, while contract semantics abstracts it away.
    UniqueResult
      (EvalCommandE (calleeEnv failingBodyProc) fac σ
        (.call "callee" [.inArg (intVal 0)] .empty)) σ
      [assertEvent fac (calleeFrame (intV fac 0)) "pre" HasBool.tt,
       assertEvent fac (calleeFrame (intV fac 0)) "body" HasBool.ff,
       assertEvent fac (calleeFrame (intV fac 0)) "post" HasBool.tt] ∧
    UniqueResult
      (EvalCommandContractE (calleeEnv failingBodyProc) fac σ
        (.call "callee" [.inArg (intVal 0)] .empty)) σ
      [assertEvent fac (calleeFrame (intV fac 0)) "pre" HasBool.tt,
       assumeEvent fac (calleeFrame (intV fac 0)) "post" HasBool.tt] := by

  have hframe : InitCallFrame (failingBodyProc)
      [intV fac 0] [] (calleeFrame (intV fac 0)) := initCallFrame_oneInput (ty := .int) (intV fac 0)
  have hbodyE := assertBodyExecE (calleeEnv (failingBodyProc))
    fac (calleeFrame (intV fac 0)) "body" HasBool.ff
  refine ⟨?_, ?_⟩
  · apply uniqueEvalCommandE (calleeEnv_callee _) (fun h₁ h₂ => by
      simpa [failingBodyProc, oneInputContractBodyProc] using
        assertBodyExecEUnique h₁ h₂)
    simpa [MetaData.empty, defaultAssertEvents, Calls.defaultAssertEvents, Calls.checksAtCall,
      MetaData.setCallSiteFileRange_empty, ListMap.toList,
      assertEvent, failingBodyProc,
      oneInputContractBodyProc, oneInputContractProc] using
      EvalCommandE.call_sem (callArgs := [.inArg (intVal 0)]) (md := .empty) (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal fac σ 0, .read_none, hframe⟩
        hbodyE ⟨(by simp [Imperative.CallArg.getLhs]), _, .read_none, .update_none, .nil⟩
  · apply uniqueEvalCommandContractE (calleeEnv_callee _) (by rfl)
    simpa [MetaData.empty, defaultAssertEvents, Calls.defaultAssertEvents, Calls.checksAtCall,
      MetaData.setCallSiteFileRange_empty, ListMap.toList,
      assumeEvents, Calls.assumeEvents, assertEvent, assumeEvent,
      failingBodyProc, oneInputContractBodyProc, oneInputContractProc] using
      EvalCommandContractE.call_sem (callArgs := [.inArg (intVal 0)]) (md := .empty)
        (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal fac σ 0, .read_none, hframe⟩
        .update_none ⟨(by simp [Imperative.CallArg.getLhs]), _, .read_none, .update_none, .nil⟩

/-- ## Example 7.
    Contract call, FAIL path: a false (`ff`) Default precondition is emitted as an
    assertion event by both relations. The contract relation emits the
    postcondition as an assumption rather than an assertion.

Core-style pseudocode:
```core
procedure Callee(y : int)
spec {
  requires [pre]: false;
  ensures [post]: true;
} { };
procedure Caller() {
  call Callee(0); // Failure comes from pre; post is checked/assumed and passes.
};
```
-/
example

    (fac : Expression.Factory) (σ : CoreStore) :
    -- Both displayed store-observation pairs are unique. Both relations report
    -- the false precondition; traces distinguish check/assume.
    UniqueResult
      (EvalCommandE
        (calleeEnv (oneInputContractProc calleeY .int HasBool.ff HasBool.tt))
        fac σ (.call "callee" [.inArg (intVal 0)] .empty)) σ
      [assertEvent fac (calleeFrame (intV fac 0)) "pre" HasBool.ff,
       assertEvent fac (calleeFrame (intV fac 0)) "post" HasBool.tt] ∧
    UniqueResult
      (EvalCommandContractE
        (calleeEnv (oneInputContractProc calleeY .int HasBool.ff HasBool.tt))
        fac σ (.call "callee" [.inArg (intVal 0)] .empty)) σ
      [assertEvent fac (calleeFrame (intV fac 0)) "pre" HasBool.ff,
       assumeEvent fac (calleeFrame (intV fac 0)) "post" HasBool.tt] := by

  have hframe : InitCallFrame (oneInputContractProc calleeY .int HasBool.ff HasBool.tt)
      [intV fac 0] [] (calleeFrame (intV fac 0)) := initCallFrame_oneInput (ty := .int) (intV fac 0)
  refine ⟨?_, ?_⟩
  · apply uniqueEvalCommandE (calleeEnv_callee _) emptyBodyExecEUnique
    simpa [MetaData.empty, defaultAssertEvents, Calls.defaultAssertEvents, Calls.checksAtCall,
      MetaData.setCallSiteFileRange_empty, ListMap.toList,
      assertEvent, oneInputContractProc] using
      EvalCommandE.call_sem (callArgs := [.inArg (intVal 0)]) (md := .empty) (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal fac σ 0, .read_none, hframe⟩
        (emptyBodyExecE _ _ _)
            ⟨(by simp [Imperative.CallArg.getLhs]), _, .read_none, .update_none, .nil⟩
  · apply uniqueEvalCommandContractE (calleeEnv_callee _) (by rfl)
    simpa [MetaData.empty, defaultAssertEvents, Calls.defaultAssertEvents, Calls.checksAtCall,
      MetaData.setCallSiteFileRange_empty, ListMap.toList,
      assumeEvents, Calls.assumeEvents, assertEvent, assumeEvent,
      oneInputContractProc] using
      EvalCommandContractE.call_sem (callArgs := [.inArg (intVal 0)]) (md := .empty)
        (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal fac σ 0, .read_none, hframe⟩
        .update_none ⟨(by simp [Imperative.CallArg.getLhs]), _, .read_none, .update_none, .nil⟩

private def noArgProc (name : String) (body : Statements) : Procedure :=
  { header :=
      { name := ⟨name, ()⟩, typeArgs := [], inputs := [], outputs := [] }
    spec := { preconditions := [], postconditions := [] }
    body := .structured body }

private def leafProc : Procedure := noArgProc "leaf" []
private def middleProc : Procedure :=
  noArgProc "middle" [.cmd (.call "leaf" [] .empty)]

private def nestedProcEnv (name : String) : Option Procedure :=
  if name == "leaf" then some leafProc
  else if name == "middle" then some middleProc
  else none

/-- Initializing an argument-less procedure's call frame yields the empty store. -/
private theorem emptyFrame (name : String) (body : Statements) :
    InitCallFrame (noArgProc name body) [] [] emptyStore := by
  unfold InitCallFrame noArgProc
  exact ⟨emptyStore, emptyStore, .init_none, .init_none,
    (withOldSnapshots_nil _).symm⟩

/-- ## Example 8.
    A top-level executable call runs through the middle procedure's nested leaf
    call; the contract semantics abstracts the same top-level call. Both leave
    the empty caller store unchanged.

Core-style pseudocode:
```core
procedure Leaf() { };
procedure Middle() {
  call Leaf();
};
procedure Caller() {
  call Middle();
  // Executable semantics enters Middle and Leaf; contract semantics skips both.
};
```
-/
example

    (fac : Expression.Factory) :
    -- Concrete semantics executes both nested bodies while contract semantics
    -- abstracts the outer call. Every relation uniquely returns `emptyStore`
    -- with an empty trace.
    UniqueResult
      (EvalCommandE nestedProcEnv fac emptyStore (.call "middle" [] .empty))
      emptyStore [] ∧
    UniqueResult
      (EvalCommandContractE nestedProcEnv fac emptyStore (.call "middle" [] .empty))
      emptyStore [] := by
  -- Leaf has no contract clauses and an empty body, so its call emits no events.
  have hleafE : EvalCommandE nestedProcEnv fac emptyStore
      (.call "leaf" [] .empty) emptyStore [] := by
    simpa [defaultAssertEvents, Calls.defaultAssertEvents, Calls.checksAtCall,
      MetaData.setCallSiteFileRange_empty, ListMap.toList, leafProc,
      noArgProc] using
      EvalCommandE.call_sem (π := nestedProcEnv) (by simp [nestedProcEnv, leafProc])
        ⟨_, _, .eval_none, .read_none, emptyFrame "leaf" []⟩
        (emptyBodyExecE nestedProcEnv emptyStore fac)
        ⟨(by simp [Imperative.CallArg.getLhs]), _, .read_none, .update_none, .nil⟩
  let ρ : Env Expression := ⟨emptyStore, fac⟩
  -- Modelled on `assertBodyExecE`: middle's body is a single leaf call that emits no events, so the body emits no events.
  have hmiddleBodyE : CoreBodyExecE nestedProcEnv middleProc.body
      ⟨emptyStore, fac⟩ emptyStore [] := by
    unfold middleProc noArgProc
    change CoreBodyExecE nestedProcEnv
      (.structured [.cmd (.call "leaf" [] .empty)]) ⟨emptyStore, fac⟩ emptyStore []
    have hstar : CoreStepStarE nestedProcEnv
        (.stmt (Stmt.block "" [.cmd (.call "leaf" [] .empty)] #[]) ρ) []
        (.terminal ⟨projectStore emptyStore emptyStore, fac⟩) := by
      refine ReflTransTrace.step _ [] _ _ _
        (StepStmtE.step_block) ?_
      refine ReflTransTrace.step _ [] _ _ _
        (StepStmtE.step_block_body (StepStmtE.step_stmts_cons)) ?_
      refine ReflTransTrace.step _ [] _ _ _
        (StepStmtE.step_block_body (StepStmtE.step_seq_inner (StepStmtE.step_cmd hleafE))) ?_
      refine ReflTransTrace.step _ [] _ _ _
        (StepStmtE.step_block_body (StepStmtE.step_seq_done)) ?_
      refine ReflTransTrace.step _ [] _ _ _
        (StepStmtE.step_block_body (StepStmtE.step_stmts_nil)) ?_
      refine ReflTransTrace.step _ [] _ _ _
        (StepStmtE.step_block_done) ?_
      exact ReflTransTrace.refl _
    have h := CoreBodyExecE.structured (π := nestedProcEnv)
      (ss := [.cmd (.call "leaf" [] .empty)]) (ρ := ⟨emptyStore, fac⟩)
      (ρ' := ⟨projectStore emptyStore emptyStore, fac⟩) hstar
    simpa [projectStore_self] using h
  have hmiddleBodyEUnique : ∀ {frame end₁ end₂ : CoreStore}
      {emitted₁ emitted₂ : Trace Expression},
      CoreBodyExecE nestedProcEnv middleProc.body ⟨frame, fac⟩ end₁ emitted₁ →
      CoreBodyExecE nestedProcEnv middleProc.body ⟨frame, fac⟩ end₂ emitted₂ →
      end₁ = end₂ ∧ emitted₁ = emitted₂ := by
    intro frame end₁ end₂ emitted₁ emitted₂ h₁ h₂
    change CoreBodyExecE nestedProcEnv
      (.structured [.cmd (.call "leaf" [] .empty)]) ⟨frame, fac⟩ end₁ emitted₁ at h₁
    change CoreBodyExecE nestedProcEnv
      (.structured [.cmd (.call "leaf" [] .empty)]) ⟨frame, fac⟩ end₂ emitted₂ at h₂
    exact h₁.singleton_cmd_unique
      (fun hcmd₁ hcmd₂ => hcmd₁.call_unique_of_body_unique (p := leafProc)
        (by simp [nestedProcEnv, leafProc]) emptyBodyExecEUnique hcmd₂) h₂
  refine ⟨?_, ?_⟩
  · apply uniqueEvalCommandE (p := middleProc) (by simp [nestedProcEnv, middleProc]) hmiddleBodyEUnique
    simpa [defaultAssertEvents, Calls.defaultAssertEvents, Calls.checksAtCall,
      MetaData.setCallSiteFileRange_empty, ListMap.toList, middleProc,
      noArgProc] using
      EvalCommandE.call_sem (by simp [nestedProcEnv, middleProc])
        ⟨_, _, .eval_none, .read_none, emptyFrame "middle" [.cmd (.call "leaf" [] .empty)]⟩
        hmiddleBodyE ⟨(by simp [Imperative.CallArg.getLhs]), _, .read_none, .update_none, .nil⟩
  · apply uniqueEvalCommandContractE (p := middleProc)
      (by simp [nestedProcEnv, middleProc]) (by rfl)
    simpa [defaultAssertEvents, Calls.defaultAssertEvents, Calls.checksAtCall,
      MetaData.setCallSiteFileRange_empty, ListMap.toList, assumeEvents,
      Calls.assumeEvents, middleProc, noArgProc] using
      EvalCommandContractE.call_sem (by simp [nestedProcEnv, middleProc])
        ⟨_, _, .eval_none, .read_none, emptyFrame "middle" [.cmd (.call "leaf" [] .empty)]⟩
        .update_none ⟨(by simp [Imperative.CallArg.getLhs]), _, .read_none, .update_none, .nil⟩

/-! ## The typing restrictions reject ill-typed entries and write-backs -/

/-- The Boolean `b` as a value of the factory `fac`. -/
private def boolV (fac : Expression.Factory) (b : Bool) : Expression.Val :=
  ⟨fac.model.tcInterp, .bool, b⟩

/-- An integer value has no Boolean type. -/
private theorem intV_not_bool (fac : Expression.Factory) (n : Int) (b : Bool)
    (ty : Expression.Ty) (hint : HasVal.valueOfTy fac (intV fac n) ty)
    (hbool : HasVal.valueOfTy fac (boolV fac b) ty) :
    False := by
  exact absurd (hint.2.symm.trans hbool.2) (by simp only [intV, boolV, Option.some.injEq]; decide)

/-- No typing meets the annotation check for a store holding an integer at `x` and a body that
    reads `x` annotated as Boolean. -/
example (fac : Expression.Factory) :
    ¬ ∃ Γ, StoreHasTyping fac (updatedState emptyStore callerResult (intV fac 0)) Γ ∧
      Block.fvarTypesWellAnnotated Γ
        [Statement.assert "p" (.fvar () callerResult (some .bool)) #[]] := by
  rintro ⟨Γ, hσ, hw, -⟩
  have hx : Γ callerResult = some (.forAll [] .bool) :=
    hw _ _ List.mem_cons_self
  obtain ⟨v, hv, hty⟩ := hσ _ _ hx
  simp only [updatedState, decide_true, ↓reduceIte, Option.some.injEq] at hv
  subst hv
  simp only [HasVal.valueOfTy, intV, Lambda.LTy.toMonoType?, Option.some.injEq, true_and] at hty
  exact absurd hty (by decide)

/-- No call exit writes a Boolean output of the callee back to a caller variable holding an
    integer. -/
example (fac : Expression.Factory) (σ' : CoreStore) :
    ¬ CallExit fac (updatedState emptyStore callerResult (intV fac 0))
      (oneOutputProc calleeY .bool) [.outArg callerResult] (calleeFrame (boolV fac true)) σ' := by
  rintro ⟨-, outs, hread, -, hrel⟩
  change ReadValues fac (calleeFrame (boolV fac true)) [calleeY] outs at hread
  cases hread with
  | read_some hy _ hrest =>
    cases hrest
    simp only [calleeFrame, updatedState, decide_true, ↓reduceIte, Option.some.injEq] at hy
    subst hy
    cases hrel with
    | cons hst _ =>
      obtain ⟨prev, ty, hprev, hpty, hvty⟩ := hst
      simp only [updatedState, decide_true, ↓reduceIte, Option.some.injEq] at hprev
      subst hprev
      exact intV_not_bool fac 0 true ty hpty hvty

end Core.StatementSemanticsTests
