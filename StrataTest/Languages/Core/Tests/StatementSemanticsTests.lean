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
formals; selection and evaluation of call-site contract clauses; failure
aggregation for executable and contract calls; chronological contract and body
events from `EvalCommandE` and `EvalCommandContractE`; and nested executable
call-body evaluation.

Jump to the "MAIN TESTS" section to look at the top-level tests in this file.
Lines before "MAIN TESTS" are auxiliary lemmas and definitions.

Each `example` is an anonymous theorem. `UniqueResult R σ result` combines a
concrete derivation `R σ result` with a universal inversion property: every
derivation of `R` has both `σ` as its output store and `result` as its observation.
Thus the examples establish that the displayed store, failure flag, and event
trace are the only possible result, rather than merely one reachable result.
Examples with output havoc keep their abstract contract derivations separate
because that relation is intentionally nondeterministic.

The final Boolean of `EvalCommand` is the `hasFailure` result, while
`EvalCommandE` and `EvalCommandContractE` replace it with the chronological
event trace.
-/

namespace Core.StatementSemanticsTests

open Imperative

private def intVal (n : Int) : Expression.Expr := .intConst () n
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
fixtures above. The remaining universally quantified parameters (`φ`, `fac`, and
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
private def calleeFrame (v : Expression.Expr) : CoreStore :=
  updatedState emptyStore calleeY v

/-- The callee frame after snapshotting the incoming value of its inout formal. -/
private def inoutFrame (v : Expression.Expr) : CoreStore :=
  withOldSnapshots [calleeY] (calleeFrame v)

/-- The collision-free frame of a one-inout callee binds both the current formal
    and its `old` snapshot to the incoming value. -/
private theorem initCallFrame_oneInout (v : Expression.Expr) :
    InitCallFrame (oneInoutProc calleeY .int) [v] [] (inoutFrame v) := by
  unfold InitCallFrame
  refine ⟨calleeFrame v, calleeFrame v, ?_, ?_, ?_⟩
  · show InitStates emptyStore [calleeY] [v] (calleeFrame v)
    exact .init_some (updatedStateInit rfl) .init_none
  · simpa [oneInoutProc, Procedure.Header.getOutputOnlyParams,
      ListMap.keys_eq_map_fst, List.contains_eq_mem] using
      (InitStates.init_none : InitStates (calleeFrame v) [] [] (calleeFrame v))
  · simp [inoutFrame, oneInoutProc, Procedure.Header.getInoutParams,
      getInoutParams, ListMap.keys_eq_map_fst, List.contains_eq_mem]

/-- Reading the inout actual from the caller evaluates to its stored value. -/
private theorem evalExpressions_inout
    (fac : Expression.Factory) (v : Expression.Expr) (hv : HasVal.value fac v) :
    EvalExpressions fac (calleeFrame v)
      [Lambda.LExpr.fvar () calleeY none] [v] := by
  apply EvalExpressions.eval_some
  · simp [isDefined, HasFvars.getFvars, Lambda.LExpr.LExpr.getVars,
      calleeFrame, updatedState]
  · exact Lambda.evalFully_fvar_of_value fac (calleeFrame v) () calleeY none v
      (by simp [calleeFrame, updatedState]) hv
  · exact .eval_none

/-- An integer literal has no free variables and evaluates to itself, so a
    singleton argument list of one literal evaluates to itself in any factory and
    store. -/
private theorem evalExpressions_intVal
    (fac : Expression.Factory) (σ : CoreStore) (n : Int) :
    EvalExpressions fac σ [intVal n] [intVal n] := by
  apply EvalExpressions.eval_some
  · simp [isDefined, intVal, HasFvars.getFvars, Lambda.LExpr.LExpr.getVars]
  · exact Lambda.evalFully_const fac σ () (.intConst n)
  · exact EvalExpressions.eval_none

/-- Snapshotting an empty list leaves the store unchanged. -/
private theorem withOldSnapshots_nil (σ : CoreStore) : withOldSnapshots [] σ = σ := rfl

/-- The collision-free frame of a one-input callee binds its input formal
    `calleeY` to the evaluated argument, leaving `calleeFrame v`. -/
private theorem initCallFrame_oneInput (ty : Lambda.LMonoTy) (v : Expression.Expr) :
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
private theorem initCallFrame_oneOutput (ty : Lambda.LMonoTy) (v : Expression.Expr) :
    InitCallFrame (oneOutputProc calleeY ty) [] [v] (calleeFrame v) := by
  refine ⟨emptyStore, calleeFrame v, ?_, ?_, ?_⟩
  · show InitStates emptyStore [] [] emptyStore
    exact InitStates.init_none
  · show InitStates emptyStore [calleeY] [v] (calleeFrame v)
    exact InitStates.init_some (updatedStateInit rfl) InitStates.init_none
  · show calleeFrame v = withOldSnapshots [] (calleeFrame v)
    exact (withOldSnapshots_nil _).symm

/-- An empty structured body leaves its store and factory unchanged and reports
    no failure, for any environment, closure extension, store, and factory. -/
private theorem emptyBodyExec
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (σ : CoreStore) (fac : Expression.Factory) :
    CoreBodyExec π φ (.structured []) σ fac σ fac false := by
  let ρ : Env Expression := ⟨σ, fac, false⟩
  have hstmts : StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
      (.stmts [] ρ) (.terminal ρ) := .step _ _ _ .step_stmts_nil (.refl _)
  have hcore : CoreStepStar π φ
      (.stmt (Stmt.block "" [] #[]) ρ) (.terminal ⟨projectStore σ σ, fac, false⟩) := by
    apply StepStmtStar_to_CoreStepStar
    refine .step _ _ _ .step_block ?_
    refine ReflTrans_Transitive _ _ _ _
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
        _ _ (some "") σ fac hstmts) ?_
    exact ReflTrans.step _ _ _ StepStmt.step_block_done (ReflTrans.refl _)
  have h := CoreBodyExec.structured (ss := []) (σ := σ) (fac := fac)
    (ρ' := ⟨projectStore σ σ, fac, false⟩) hcore
  simpa [projectStore_self] using h

/-- Event analogue of `emptyBodyExec`: an empty structured body emits no events
    and leaves its store and factory unchanged. -/
private theorem emptyBodyExecE
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (σ : CoreStore) (fac : Expression.Factory) :
    CoreBodyExecE π φ (.structured []) σ fac σ fac [] := by
  have hstar : CoreStepStarE π φ
      (.stmt (Stmt.block "" [] #[]) ⟨σ, fac, false⟩) []
      (.terminal ⟨projectStore σ σ, fac, false⟩) := by
    refine ReflTransTrace.step _ [] _ [] _
      (StepStmtE.step_admin StepStmt.step_block) ?_
    refine ReflTransTrace.step _ [] _ [] _
      (StepStmtE.step_block_body (StepStmtE.step_admin StepStmt.step_stmts_nil)) ?_
    refine ReflTransTrace.step _ [] _ [] _
      (StepStmtE.step_admin StepStmt.step_block_done) ?_
    exact ReflTransTrace.refl _
  have h := CoreBodyExecE.structured (π := π) (φ := φ) (ss := []) (σ := σ)
    (fac := fac) (ρ' := ⟨projectStore σ σ, fac, false⟩) hstar
  simpa [projectStore_self] using h

/-- Reading the slot just written by `calleeFrame` returns the written value,
    provided that value is canonical in the factory. -/
private theorem readValues_calleeFrame
    (fac : Expression.Factory) (v : Expression.Expr) (hv : HasVal.value fac v) :
    ReadValues fac (calleeFrame v) [calleeY] [v] := by
  have hlk : (calleeFrame v) calleeY = some v := by
    have hinit : InitState Expression emptyStore calleeY v (calleeFrame v) :=
      updatedStateInit rfl
    cases hinit with
    | init _ hsome _ => exact hsome
  exact ReadValues.read_some hlk hv ReadValues.read_none

/-- Writing a slot's current value back to itself leaves the store unchanged. -/
private theorem updateStates_id_single
    {σ : CoreStore} {y : Expression.Ident} {v : Expression.Expr}
    (h : σ y = some v) : UpdateStates σ [y] [v] σ :=
  .update_some (.update h h (fun _ _ => rfl)) .update_none

/-! ### Concrete Boolean-literal and assert-body helpers

These examples specialize clause and body expressions to the Boolean literals
`true` and `false`, then construct their evaluations with the helpers below.
Only an executed body assertion needs `WellFormedSemanticEvalBool`, which is why
those examples use `Core.Factory`.

-/

/-- A Boolean literal evaluates to itself in any factory and store: a constant is
    its own value, so no well-formedness assumption is required. -/
private theorem eval_boolConst (fac : Expression.Factory) (σ : CoreStore) (b : Bool) :
    Expression.eval fac σ (Lambda.LExpr.boolConst () b)
      = some (Lambda.LExpr.boolConst () b) :=
  Lambda.evalFully_const fac σ () (Lambda.LConst.boolConst b)

/-- A Boolean literal has no free variables, so any store trivially defines all
    of them. -/
private theorem isDefined_boolConst (σ : CoreStore) (b : Bool) :
    isDefined σ (HasFvars.getFvars (Lambda.LExpr.boolConst () b)) := by
  simp [isDefined, HasFvars.getFvars, Lambda.LExpr.LExpr.getVars]

/-- An integer literal is a canonical value in every factory. -/
private theorem intVal_value (fac : Expression.Factory) (n : Int) :
    HasVal.value fac (intVal n) :=
  show Lambda.LExpr.isCanonicalValue fac (intVal n) = true from
    Lambda.isCanonicalValue_const_true fac () (Lambda.LConst.intConst n)

/-- The current inout formal keeps its incoming value in the snapshotted frame. -/
private theorem inoutFrame_current :
    inoutFrame (intVal 7) calleeY = some (intVal 7) := by
  simp [inoutFrame, withOldSnapshots, calleeFrame, updatedState,
    calleeY, CoreIdent.mkOld, CoreIdent.oldStr]

/-- The old identifier reads the inout formal's incoming value. -/
private theorem inoutFrame_old :
    inoutFrame (intVal 7) oldCalleeY = some (intVal 7) := by
  simp [inoutFrame, withOldSnapshots, oldCalleeY, calleeY, calleeFrame,
    updatedState, CoreIdent.mkOld, CoreIdent.oldStr]

/-- The old-value postcondition holds whenever the old slot contains seven. -/
private theorem oldYIs7_eval (fac : Expression.Factory) (σ : CoreStore)
    (hold : σ oldCalleeY = some (intVal 7)) :
    Expression.eval fac σ oldYIs7 = some HasBool.tt := by
  exact Lambda.evalFully_eq_self fac σ () _ _ (intVal 7)
    (Lambda.evalFully_fvar_of_value fac σ () oldCalleeY
      (some .int) _ hold (intVal_value fac 7))
    (Lambda.evalFully_const fac σ () (.intConst 7))

/-- The old-value postcondition's sole free variable is defined whenever the old
    slot contains seven. -/
private theorem oldYIs7_defined (σ : CoreStore)
    (hold : σ oldCalleeY = some (intVal 7)) :
    isDefined σ (HasFvars.getFvars oldYIs7) := by
  have h := congrArg Option.isSome hold
  simpa [oldYIs7, intVal, isDefined, HasFvars.getFvars,
    Lambda.LExpr.LExpr.getVars] using h

/-- Failure-flag execution of a one-assert body `{ assert [label]: e }` from `σ`:
    an assert never changes the store or factory, so the run terminates back at
    `σ`/`fac` and reports exactly the assert's own outcome. The Boolean value `bv`
    of `e` (in `fac`) selects that outcome — passing (`bv = true`) reports no
    failure and failing (`bv = false`) reports failure `!bv`. It discharges body
    execution for concrete assert-only bodies without any opaque `CoreBodyExec`
    hypothesis. -/
private theorem assertBodyExec
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (fac : Expression.Factory) (σ : CoreStore)
    (label : String) (e : Expression.Expr) (bv : Bool)
    (hwf : WellFormedSemanticEvalBool (P := Expression) fac)
    (heval : Expression.eval fac σ e = some (Lambda.LExpr.boolConst () bv)) :
    CoreBodyExec π φ (.structured [Statement.assert label e .empty]) σ fac σ fac (!bv) := by
  let ρ : Env Expression := ⟨σ, fac, false⟩
  have hcmd : EvalCommand π φ fac σ (CmdExt.cmd (Cmd.assert label e .empty)) σ (!bv) := by
    refine EvalCommand.cmd_sem ?_
    cases bv with
    | true => exact EvalCmd.eval_assert_pass heval hwf
    | false => exact EvalCmd.eval_assert_fail heval hwf
  have hstmts : StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
      (.stmts [Statement.assert label e .empty] ρ) (.terminal ⟨σ, fac, !bv⟩) := by
    refine .step _ _ _ .step_stmts_cons ?_
    refine .step _ _ _ (.step_seq_inner (.step_cmd hcmd)) ?_
    refine .step _ _ _ .step_seq_done ?_
    exact .step _ _ _ .step_stmts_nil (.refl _)
  have hcore : CoreStepStar π φ
      (.stmt (Stmt.block "" [Statement.assert label e .empty] #[]) ρ)
      (.terminal ⟨projectStore σ σ, fac, !bv⟩) := by
    apply StepStmtStar_to_CoreStepStar
    refine .step _ _ _ .step_block ?_
    refine ReflTrans_Transitive _ _ _ _
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
        _ _ (some "") σ fac hstmts) ?_
    exact ReflTrans.step _ _ _ StepStmt.step_block_done (ReflTrans.refl _)
  have h := CoreBodyExec.structured (ss := [Statement.assert label e .empty])
    (σ := σ) (fac := fac) (ρ' := ⟨projectStore σ σ, fac, !bv⟩) hcore
  simpa [projectStore_self] using h

/-- Event analogue of `assertBodyExec`: a one-assert body `{ assert [label]: e }`
    leaves its store and factory unchanged and emits exactly the single captured
    assert event, for any condition `e` (event semantics never evaluates it, so no
    truth-value or well-formedness premise is needed). -/
private theorem assertBodyExecE
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (fac : Expression.Factory) (σ : CoreStore)
    (label : String) (e : Expression.Expr) :
    CoreBodyExecE π φ (.structured [Statement.assert label e .empty]) σ fac σ fac
      [assertEvent fac σ label e] := by
  let ρ : Env Expression := ⟨σ, fac, false⟩
  have hcmdE : EvalCommandE π φ fac σ
      (CmdExt.cmd (Cmd.assert label e .empty)) σ [assertEvent fac σ label e] :=
    EvalCommandE.cmd_sem EvalCmdE.eval_assert
  have hstar : CoreStepStarE π φ
      (.stmt (Stmt.block "" [Statement.assert label e .empty] #[]) ρ)
      [assertEvent fac σ label e]
      (.terminal ⟨projectStore σ σ, fac, false⟩) := by
    refine ReflTransTrace.step _ [] _ _ _
      (StepStmtE.step_admin StepStmt.step_block) ?_
    refine ReflTransTrace.step _ [] _ _ _
      (StepStmtE.step_block_body (StepStmtE.step_admin StepStmt.step_stmts_cons)) ?_
    refine ReflTransTrace.step _ [assertEvent fac σ label e] _ _ _
      (StepStmtE.step_block_body (StepStmtE.step_seq_inner (StepStmtE.step_cmd hcmdE))) ?_
    refine ReflTransTrace.step _ [] _ _ _
      (StepStmtE.step_block_body (StepStmtE.step_admin StepStmt.step_seq_done)) ?_
    refine ReflTransTrace.step _ [] _ _ _
      (StepStmtE.step_block_body (StepStmtE.step_admin StepStmt.step_stmts_nil)) ?_
    refine ReflTransTrace.step _ [] _ _ _
      (StepStmtE.step_admin StepStmt.step_block_done) ?_
    exact ReflTransTrace.refl _
  have h := CoreBodyExecE.structured (π := π) (φ := φ)
    (ss := [Statement.assert label e .empty]) (σ := σ) (fac := fac)
    (ρ' := ⟨projectStore σ σ, fac, false⟩) hstar
  simpa [projectStore_self] using h


/-- Two executions of the same one-assert body have identical stores, factories,
and failure results. -/
private theorem assertBodyExecUnique
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac : Expression.Factory} {σ end₁ end₂ : CoreStore}
    {label : String} {e : Expression.Expr}
    {endFac₁ endFac₂ : Expression.Factory} {failed₁ failed₂ : Bool}
    (h₁ : CoreBodyExec π φ (.structured [Statement.assert label e .empty])
      σ fac end₁ endFac₁ failed₁)
    (h₂ : CoreBodyExec π φ (.structured [Statement.assert label e .empty])
      σ fac end₂ endFac₂ failed₂) :
    end₁ = end₂ ∧ endFac₁ = endFac₂ ∧ failed₁ = failed₂ :=
  h₁.singleton_cmd_unique EvalCommand.assert_unique h₂

/-- Two executions of the same one-assert event body have identical stores,
factories, and traces. -/
private theorem assertBodyExecEUnique
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac : Expression.Factory} {σ end₁ end₂ : CoreStore}
    {label : String} {e : Expression.Expr}
    {endFac₁ endFac₂ : Expression.Factory}
    {emitted₁ emitted₂ : Trace Expression}
    (h₁ : CoreBodyExecE π φ (.structured [Statement.assert label e .empty])
      σ fac end₁ endFac₁ emitted₁)
    (h₂ : CoreBodyExecE π φ (.structured [Statement.assert label e .empty])
      σ fac end₂ endFac₂ emitted₂) :
    end₁ = end₂ ∧ endFac₁ = endFac₂ ∧ emitted₁ = emitted₂ :=
  h₁.singleton_cmd_unique EvalCommandE.assert_unique h₂

/-- `R` produces the expected observation at `expected`, and every derivation of
`R` produces that same output store and observation. -/
private def UniqueResult {α : Type} (R : CoreStore → α → Prop)
    (expected : CoreStore) (observation : α) : Prop :=
  R expected observation ∧
    ∀ σ' result, R σ' result → σ' = expected ∧ result = observation

/-- Two executions of the same empty concrete body have identical stores,
factories, and failure results. -/
private theorem emptyBodyExecUnique
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac : Expression.Factory} {σ end₁ end₂ : CoreStore}
    {endFac₁ endFac₂ : Expression.Factory} {failed₁ failed₂ : Bool}
    (h₁ : CoreBodyExec π φ (.structured []) σ fac end₁ endFac₁ failed₁)
    (h₂ : CoreBodyExec π φ (.structured []) σ fac end₂ endFac₂ failed₂) :
    end₁ = end₂ ∧ endFac₁ = endFac₂ ∧ failed₁ = failed₂ := by
  obtain ⟨hstore₁, hfac₁, hfailed₁⟩ := h₁.empty_unique π φ σ end₁ fac endFac₁ failed₁
  obtain ⟨hstore₂, hfac₂, hfailed₂⟩ := h₂.empty_unique π φ σ end₂ fac endFac₂ failed₂
  exact ⟨hstore₁.trans hstore₂.symm, hfac₁.trans hfac₂.symm,
    hfailed₁.trans hfailed₂.symm⟩

/-- Two executions of the same empty event body have identical stores,
factories, and traces. -/
private theorem emptyBodyExecEUnique
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac : Expression.Factory} {σ end₁ end₂ : CoreStore}
    {endFac₁ endFac₂ : Expression.Factory}
    {emitted₁ emitted₂ : Trace Expression}
    (h₁ : CoreBodyExecE π φ (.structured []) σ fac end₁ endFac₁ emitted₁)
    (h₂ : CoreBodyExecE π φ (.structured []) σ fac end₂ endFac₂ emitted₂) :
    end₁ = end₂ ∧ endFac₁ = endFac₂ ∧ emitted₁ = emitted₂ := by
  obtain ⟨hstore₁, hfac₁, hemitted₁⟩ := h₁.empty_unique π φ σ end₁ fac endFac₁ emitted₁
  obtain ⟨hstore₂, hfac₂, hemitted₂⟩ := h₂.empty_unique π φ σ end₂ fac endFac₂ emitted₂
  exact ⟨hstore₁.trans hstore₂.symm, hfac₁.trans hfac₂.symm,
    hemitted₁.trans hemitted₂.symm⟩

/-- Package a concrete call witness with pairwise store-and-failure
determinism. -/
private theorem uniqueEvalCommand
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac : Expression.Factory} {σ expected : CoreStore} {n : String}
    {p : Procedure} {args : List (CallArg Expression)}
    {md : MetaData Expression} {failed : Bool}
    (hLookup : π n = some p)
    (hBodyUnique : ∀ {frame end₁ end₂ : CoreStore}
      {endFac₁ endFac₂ : Expression.Factory} {bodyFailed₁ bodyFailed₂ : Bool},
      CoreBodyExec π φ p.body frame fac end₁ endFac₁ bodyFailed₁ →
      CoreBodyExec π φ p.body frame fac end₂ endFac₂ bodyFailed₂ →
      end₁ = end₂ ∧ endFac₁ = endFac₂ ∧ bodyFailed₁ = bodyFailed₂)
    (h : EvalCommand π φ fac σ (.call n args md) expected failed) :
    UniqueResult (EvalCommand π φ fac σ (.call n args md)) expected failed :=
  ⟨h, fun _ _ h' => h'.call_unique_of_body_unique hLookup hBodyUnique h⟩

/-- Package an event call witness with pairwise store-and-trace determinism. -/
private theorem uniqueEvalCommandE
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac : Expression.Factory} {σ expected : CoreStore} {n : String}
    {p : Procedure} {args : List (CallArg Expression)}
    {md : MetaData Expression} {emitted : Trace Expression}
    (hLookup : π n = some p)
    (hBodyUnique : ∀ {frame end₁ end₂ : CoreStore}
      {endFac₁ endFac₂ : Expression.Factory} {bodyEvents₁ bodyEvents₂ : Trace Expression},
      CoreBodyExecE π φ p.body frame fac end₁ endFac₁ bodyEvents₁ →
      CoreBodyExecE π φ p.body frame fac end₂ endFac₂ bodyEvents₂ →
      end₁ = end₂ ∧ endFac₁ = endFac₂ ∧ bodyEvents₁ = bodyEvents₂)
    (h : EvalCommandE π φ fac σ (.call n args md) expected emitted) :
    UniqueResult (EvalCommandE π φ fac σ (.call n args md)) expected emitted :=
  ⟨h, fun _ _ h' => h'.call_unique_of_body_unique hLookup hBodyUnique h⟩

/-- Package a no-output abstract contract call witness with pairwise
store-and-failure determinism. -/
private theorem uniqueEvalCommandContract
    {π : String → Option Procedure} {fac : Expression.Factory}
    {σ expected : CoreStore} {n : String} {p : Procedure}
    {args : List (CallArg Expression)} {md : MetaData Expression} {failed : Bool}
    (hLookup : π n = some p) (hOutputs : ListMap.keys p.header.outputs = [])
    (h : EvalCommandContract π fac σ (.call n args md) expected failed) :
    UniqueResult (EvalCommandContract π fac σ (.call n args md)) expected failed :=
  ⟨h, fun _ _ h' => h'.call_unique_of_outputs_nil hLookup hOutputs h⟩

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
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (fac : Expression.Factory) (σ : CoreStore) :
    -- All four semantics have a unique complete result: `σ` plus success
    -- (`false`) for failure semantics, or `σ` plus no events for traces.
    UniqueResult
      (EvalCommand (calleeEnv (oneInputProc calleeY .int)) φ fac σ
        (.call "callee" [.inArg (intVal 2)] .empty)) σ false ∧
    UniqueResult
      (EvalCommandE (calleeEnv (oneInputProc calleeY .int)) φ fac σ
        (.call "callee" [.inArg (intVal 2)] .empty)) σ [] ∧
    UniqueResult
      (EvalCommandContract (calleeEnv (oneInputProc calleeY .int)) fac σ
        (.call "callee" [.inArg (intVal 2)] .empty)) σ false ∧
    UniqueResult
      (EvalCommandContractE (calleeEnv (oneInputProc calleeY .int)) fac σ
        (.call "callee" [.inArg (intVal 2)] .empty)) σ [] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply uniqueEvalCommand (calleeEnv_callee _) emptyBodyExecUnique
    exact EvalCommand.call_sem (calleeEnv_callee _)
      ⟨_, _, evalExpressions_intVal fac σ 2, .read_none, initCallFrame_oneInput .int (intVal 2)⟩
      .eval_none (emptyBodyExec _ _ _ _) .eval_none ⟨_, .read_none, .update_none⟩
  · apply uniqueEvalCommandE (calleeEnv_callee _) emptyBodyExecEUnique
    simpa [defaultAssertEvents, oneInputProc] using
      EvalCommandE.call_sem (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal fac σ 2, .read_none, initCallFrame_oneInput .int (intVal 2)⟩
        (emptyBodyExecE _ _ _ _) ⟨_, .read_none, .update_none⟩
  · apply uniqueEvalCommandContract (calleeEnv_callee _) (by rfl)
    exact EvalCommandContract.call_sem (calleeEnv_callee _)
      ⟨_, _, evalExpressions_intVal fac σ 2, .read_none, initCallFrame_oneInput .int (intVal 2)⟩
      .eval_none .update_none (by trivial) ⟨_, .read_none, .update_none⟩
  · apply uniqueEvalCommandContractE (calleeEnv_callee _) (by rfl)
    simpa [defaultAssertEvents, assumeEvents, oneInputProc] using
      EvalCommandContractE.call_sem (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal fac σ 2, .read_none, initCallFrame_oneInput .int (intVal 2)⟩
        .update_none ⟨_, .read_none, .update_none⟩

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

private def inoutResultStore : CoreStore :=
  updatedState (calleeFrame (intVal 7)) calleeY (intVal 9)

example
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (fac : Expression.Factory) :
    -- Concrete semantics uniquely determines both `y = 7` and its displayed
    -- failure/trace observation. Contract semantics is intentionally
    -- nondeterministic and exhibits the allowed `y = 9` choice below.
    UniqueResult
      (EvalCommand (calleeEnv oneInoutOldProc) φ fac (calleeFrame (intVal 7))
        (.call "callee" [.inoutArg calleeY] .empty))
      (calleeFrame (intVal 7)) false ∧
    UniqueResult
      (EvalCommandE (calleeEnv oneInoutOldProc) φ fac (calleeFrame (intVal 7))
        (.call "callee" [.inoutArg calleeY] .empty))
      (calleeFrame (intVal 7))
      [assertEvent fac (inoutFrame (intVal 7)) "old" oldYIs7] ∧
    EvalCommandContract (calleeEnv oneInoutOldProc) fac
      (calleeFrame (intVal 7))
      (.call "callee" [.inoutArg calleeY] .empty)
      inoutResultStore false ∧
    EvalCommandContractE (calleeEnv oneInoutOldProc) fac
      (calleeFrame (intVal 7))
      (.call "callee" [.inoutArg calleeY] .empty)
      inoutResultStore
      [assumeEvent fac
        (updatedState (inoutFrame (intVal 7)) calleeY (intVal 9))
        "old" oldYIs7] := by
  have hframe : InitCallFrame oneInoutOldProc [intVal 7] []
      (inoutFrame (intVal 7)) := by
    simpa [oneInoutOldProc, InitCallFrame] using initCallFrame_oneInout (intVal 7)
  have hentry : CallEntry fac (calleeFrame (intVal 7)) oneInoutOldProc
      [.inoutArg calleeY] (inoutFrame (intVal 7)) := by
    unfold CallEntry
    refine ⟨[intVal 7], [], ?_, .read_none, hframe⟩
    simpa [CallArg.getInputExprs] using
      evalExpressions_inout fac (intVal 7) (intVal_value fac 7)
  have hcaller : calleeFrame (intVal 7) calleeY = some (intVal 7) := by
    simp [calleeFrame, updatedState]
  have hread : ReadValues fac (inoutFrame (intVal 7)) [calleeY] [intVal 7] :=
    .read_some inoutFrame_current (intVal_value fac 7) .read_none
  have hexit : CallExit fac (calleeFrame (intVal 7)) oneInoutOldProc
      [.inoutArg calleeY] (inoutFrame (intVal 7)) (calleeFrame (intVal 7)) := by
    refine ⟨[intVal 7], ?_, updateStates_id_single hcaller⟩
    simpa [oneInoutOldProc, oneInoutProc, ListMap.keys] using hread
  let σO := updatedState (inoutFrame (intVal 7)) calleeY (intVal 9)
  have hupd : UpdateState Expression (inoutFrame (intVal 7)) calleeY
      (intVal 9) σO := updatedStateUpdate inoutFrame_current
  have hhavoc : HavocVars fac (inoutFrame (intVal 7)) [calleeY] σO :=
    .update_some hupd (intVal_value fac 9) .update_none
  have hcurrentO : σO calleeY = some (intVal 9) := by
    cases hupd with | update _ h _ => exact h
  have holdO : σO oldCalleeY = some (intVal 7) := by
    cases hupd with
    | update _ _ hother =>
      rw [hother oldCalleeY]
      · exact inoutFrame_old
      · simpa [oldCalleeY] using CoreIdent.ne_mkOld calleeY
  have hreadO : ReadValues fac σO [calleeY] [intVal 9] :=
    .read_some hcurrentO (intVal_value fac 9) .read_none
  have hcallerUpdate : UpdateStates (calleeFrame (intVal 7)) [calleeY]
      [intVal 9] inoutResultStore :=
    .update_some (updatedStateUpdate hcaller) .update_none
  have hexitO : CallExit fac (calleeFrame (intVal 7)) oneInoutOldProc
      [.inoutArg calleeY] σO inoutResultStore := by
    refine ⟨[intVal 9], ?_, hcallerUpdate⟩
    simpa [oneInoutOldProc, oneInoutProc, ListMap.keys] using hreadO
  have hassume : AssumeExprs fac σO [oldYIs7] := by
    exact ⟨oldYIs7_defined σO holdO, oldYIs7_eval fac σO holdO⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply uniqueEvalCommand (calleeEnv_callee _) emptyBodyExecUnique
    exact EvalCommand.call_sem (calleeEnv_callee _) hentry .eval_none
      (emptyBodyExec _ _ _ _) (.eval_pass
        (oldYIs7_defined _ inoutFrame_old)
        (oldYIs7_eval fac _ inoutFrame_old) .eval_none) hexit
  · apply uniqueEvalCommandE (calleeEnv_callee _) emptyBodyExecEUnique
    simpa [MetaData.empty, defaultAssertEvents, assertEvent, oneInoutOldProc] using
      EvalCommandE.call_sem (calleeEnv_callee _) hentry
        (emptyBodyExecE _ _ _ _) hexit
  · exact EvalCommandContract.call_sem (calleeEnv_callee _) hentry
      .eval_none hhavoc hassume hexitO
  · simpa [MetaData.empty, defaultAssertEvents, assumeEvents, assumeEvent, oneInoutOldProc,
      σO] using
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
private def copyCallerStore : CoreStore := updatedState emptyStore callerResult (intVal 7)

/-- Caller store after the contract abstraction writes its (different) abstract
    result `9` back into `result`. -/
private def copyResultStore : CoreStore := updatedState copyCallerStore callerResult (intVal 9)

example
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (fac : Expression.Factory) :
    -- Concrete semantics uniquely determines `copyCallerStore` together with
    -- success/no events. Contract semantics is intentionally nondeterministic
    -- and demonstrates the allowed `copyResultStore` choice.
    UniqueResult
      (EvalCommand (calleeEnv (oneOutputProc calleeY .int)) φ fac copyCallerStore
        (.call "callee" [.outArg callerResult] .empty)) copyCallerStore false ∧
    UniqueResult
      (EvalCommandE (calleeEnv (oneOutputProc calleeY .int)) φ fac copyCallerStore
        (.call "callee" [.outArg callerResult] .empty)) copyCallerStore [] ∧
    EvalCommandContract (calleeEnv (oneOutputProc calleeY .int)) fac
        copyCallerStore
        (.call "callee" [.outArg callerResult] .empty)
        copyResultStore false ∧
    EvalCommandContractE (calleeEnv (oneOutputProc calleeY .int)) fac
        copyCallerStore
        (.call "callee" [.outArg callerResult] .empty)
        copyResultStore [] := by

  have hcaller : copyCallerStore callerResult = some (intVal 7) := by
    have hinit : InitState Expression emptyStore callerResult (intVal 7) copyCallerStore :=
      updatedStateInit rfl
    cases hinit with | init _ hsome _ => exact hsome
  have hcopied : ReadValues fac copyCallerStore [callerResult] [intVal 7] :=
    .read_some hcaller (intVal_value fac 7) .read_none
  have hframe := initCallFrame_oneOutput .int (intVal 7)
  have hresult := readValues_calleeFrame fac (intVal 7) (intVal_value fac 7)
  have hentry : CallEntry fac copyCallerStore (oneOutputProc calleeY .int)
      [.outArg callerResult] (calleeFrame (intVal 7)) :=
    ⟨_, _, .eval_none, hcopied, hframe⟩
  have hexit : CallExit fac copyCallerStore (oneOutputProc calleeY .int)
      [.outArg callerResult] (calleeFrame (intVal 7)) copyCallerStore :=
    ⟨_, hresult, updateStates_id_single hcaller⟩
  -- The frame binds `calleeY ↦ 7`; the contract abstraction havocs it to 9.
  have hframeLk : (calleeFrame (intVal 7)) calleeY = some (intVal 7) := by
    have hinit : InitState Expression emptyStore calleeY (intVal 7) (calleeFrame (intVal 7)) :=
      updatedStateInit rfl
    cases hinit with | init _ hsome _ => exact hsome
  have hupd : UpdateState Expression (calleeFrame (intVal 7)) calleeY (intVal 9)
      (updatedState (calleeFrame (intVal 7)) calleeY (intVal 9)) := updatedStateUpdate hframeLk
  have hhavoc : HavocVars fac (calleeFrame (intVal 7)) [calleeY]
      (updatedState (calleeFrame (intVal 7)) calleeY (intVal 9)) :=
    .update_some hupd (intVal_value fac 9) .update_none
  have hσO : (updatedState (calleeFrame (intVal 7)) calleeY (intVal 9)) calleeY = some (intVal 9) := by
    cases hupd with | update _ hsome _ => exact hsome
  have hcontractResult : ReadValues fac (updatedState (calleeFrame (intVal 7)) calleeY (intVal 9))
      [calleeY] [intVal 9] := .read_some hσO (intVal_value fac 9) .read_none
  have hcontractUpdate : UpdateStates copyCallerStore [callerResult] [intVal 9] copyResultStore :=
    .update_some (updatedStateUpdate hcaller) .update_none
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply uniqueEvalCommand (calleeEnv_callee _) emptyBodyExecUnique
    exact EvalCommand.call_sem (calleeEnv_callee _) hentry
      .eval_none (emptyBodyExec _ _ _ _) .eval_none hexit
  · apply uniqueEvalCommandE (calleeEnv_callee _) emptyBodyExecEUnique
    simpa [defaultAssertEvents, oneOutputProc] using
      EvalCommandE.call_sem (calleeEnv_callee _) hentry
        (emptyBodyExecE _ _ _ _) hexit
  · exact EvalCommandContract.call_sem (calleeEnv_callee _)
      ⟨_, _, .eval_none, hcopied, hframe⟩
      .eval_none hhavoc (by trivial) ⟨_, hcontractResult, hcontractUpdate⟩
  · simpa [defaultAssertEvents, assumeEvents, oneOutputProc] using
      EvalCommandContractE.call_sem (calleeEnv_callee _)
        ⟨_, _, .eval_none, hcopied, hframe⟩
        hhavoc ⟨_, hcontractResult, hcontractUpdate⟩

/-! ## Example 4.
    A contract-bearing procedure with one body assertion is interpreted by all
    four call relations. Specialized to `Core.Factory` and the exact literals
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
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (σ : CoreStore) :
    -- All four no-output calls have the displayed store-observation pair as
    -- their unique complete result; traces distinguish checks from abstraction.
    UniqueResult
      (EvalCommand (calleeEnv passingBodyProc) φ Core.Factory σ
        (.call "callee" [.inArg (intVal 0)] .empty)) σ false ∧
    UniqueResult
      (EvalCommandE (calleeEnv passingBodyProc) φ Core.Factory σ
        (.call "callee" [.inArg (intVal 0)] .empty)) σ
      [assertEvent Core.Factory (calleeFrame (intVal 0)) "pre" HasBool.tt,
       assertEvent Core.Factory (calleeFrame (intVal 0)) "body" HasBool.tt,
       assertEvent Core.Factory (calleeFrame (intVal 0)) "post" HasBool.tt] ∧
    UniqueResult
      (EvalCommandContract (calleeEnv passingBodyProc) Core.Factory σ
        (.call "callee" [.inArg (intVal 0)] .empty)) σ false ∧
    UniqueResult
      (EvalCommandContractE (calleeEnv passingBodyProc) Core.Factory σ
        (.call "callee" [.inArg (intVal 0)] .empty)) σ
      [assertEvent Core.Factory (calleeFrame (intVal 0)) "pre" HasBool.tt,
       assumeEvent Core.Factory (calleeFrame (intVal 0)) "post" HasBool.tt] := by

  have hframe : InitCallFrame (passingBodyProc)
      [intVal 0] [] (calleeFrame (intVal 0)) := initCallFrame_oneInput (ty := .int) (intVal 0)
  -- The one body assertion is `assert true`, so the concrete body run succeeds.
  have hbody := assertBodyExec (calleeEnv (passingBodyProc))
    φ Core.Factory (calleeFrame (intVal 0)) "body" HasBool.tt true
    coreFactory_WellFormedSemanticEvalBool (eval_boolConst Core.Factory (calleeFrame (intVal 0)) true)
  have hbodyE := assertBodyExecE (calleeEnv (passingBodyProc))
    φ Core.Factory (calleeFrame (intVal 0)) "body" HasBool.tt
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply uniqueEvalCommand (calleeEnv_callee _) (fun h₁ h₂ => by
      simpa [passingBodyProc, oneInputContractBodyProc] using
        assertBodyExecUnique h₁ h₂)
    exact EvalCommand.call_sem (calleeEnv_callee _)
      ⟨_, _, evalExpressions_intVal Core.Factory σ 0, .read_none, hframe⟩
      (.eval_pass (isDefined_boolConst _ true) (eval_boolConst _ _ true) .eval_none) hbody
      (.eval_pass (isDefined_boolConst _ true) (eval_boolConst _ _ true) .eval_none)
      ⟨_, .read_none, .update_none⟩
  · apply uniqueEvalCommandE (calleeEnv_callee _) (fun h₁ h₂ => by
      simpa [passingBodyProc, oneInputContractBodyProc] using
        assertBodyExecEUnique h₁ h₂)
    simpa [MetaData.empty, passingBodyProc, defaultAssertEvents, assertEvent, oneInputContractBodyProc,
      oneInputContractProc] using
      EvalCommandE.call_sem (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal Core.Factory σ 0, .read_none, hframe⟩
        hbodyE ⟨_, .read_none, .update_none⟩
  · apply uniqueEvalCommandContract (calleeEnv_callee _) (by rfl)
    exact EvalCommandContract.call_sem (calleeEnv_callee _)
      ⟨_, _, evalExpressions_intVal Core.Factory σ 0, .read_none, hframe⟩
      (.eval_pass (isDefined_boolConst _ true) (eval_boolConst _ _ true) .eval_none) .update_none
      ⟨isDefined_boolConst _ true, eval_boolConst _ _ true⟩ ⟨_, .read_none, .update_none⟩
  · apply uniqueEvalCommandContractE (calleeEnv_callee _) (by rfl)
    simpa [MetaData.empty, passingBodyProc, defaultAssertEvents, assumeEvents, assertEvent, assumeEvent,
      oneInputContractBodyProc,
      oneInputContractProc] using
      EvalCommandContractE.call_sem (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal Core.Factory σ 0, .read_none, hframe⟩
        .update_none ⟨_, .read_none, .update_none⟩

/-- ## Example 5.
    Executable call, FAIL path: a false (`ff`) Default postcondition makes the
    aggregate failure flag `true` (the `postFailed` disjunct). Specialized to the
    literals `pre = true`, `post = false`. Failure-flag contract semantics has no
    derivation here, because it *assumes* the postcondition rather than checking
    it, and `false` cannot be assumed.

Core-style pseudocode:
```core
procedure Callee(y : int)
spec {
  requires [pre]: true;
  ensures [post]: false;
} { };
procedure Caller() {
  call Callee(0); // postFailed = true after the successful body.
};
```
-/
example
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (fac : Expression.Factory) (σ : CoreStore) :
    -- The unique concrete results retain `σ` and report the displayed failure
    -- flag or events. Failure-flag contract semantics has no run.
    UniqueResult
      (EvalCommand
        (calleeEnv (oneInputContractProc calleeY .int HasBool.tt HasBool.ff))
        φ fac σ (.call "callee" [.inArg (intVal 0)] .empty)) σ true ∧
    UniqueResult
      (EvalCommandE
        (calleeEnv (oneInputContractProc calleeY .int HasBool.tt HasBool.ff))
        φ fac σ (.call "callee" [.inArg (intVal 0)] .empty)) σ
      [assertEvent fac (calleeFrame (intVal 0)) "pre" HasBool.tt,
       assertEvent fac (calleeFrame (intVal 0)) "post" HasBool.ff] ∧
    (∀ σ' failed,
      ¬ EvalCommandContract (calleeEnv (oneInputContractProc calleeY .int HasBool.tt HasBool.ff)) fac
        σ
        (.call "callee" [.inArg (intVal 0)] .empty)
        σ' failed) ∧
    UniqueResult
      (EvalCommandContractE
        (calleeEnv (oneInputContractProc calleeY .int HasBool.tt HasBool.ff))
        fac σ (.call "callee" [.inArg (intVal 0)] .empty)) σ
      [assertEvent fac (calleeFrame (intVal 0)) "pre" HasBool.tt,
       assumeEvent fac (calleeFrame (intVal 0)) "post" HasBool.ff] := by

  have hframe : InitCallFrame (oneInputContractProc calleeY .int HasBool.tt HasBool.ff)
      [intVal 0] [] (calleeFrame (intVal 0)) := initCallFrame_oneInput (ty := .int) (intVal 0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply uniqueEvalCommand (calleeEnv_callee _) emptyBodyExecUnique
    exact EvalCommand.call_sem (calleeEnv_callee _)
      ⟨_, _, evalExpressions_intVal fac σ 0, .read_none, hframe⟩
      (.eval_pass (isDefined_boolConst _ true) (eval_boolConst _ _ true) .eval_none)
      (emptyBodyExec _ _ _ _)
      (.eval_fail (isDefined_boolConst _ false) (eval_boolConst _ _ false) .eval_none)
      ⟨_, .read_none, .update_none⟩
  · apply uniqueEvalCommandE (calleeEnv_callee _) emptyBodyExecEUnique
    simpa [MetaData.empty, defaultAssertEvents, assertEvent, oneInputContractProc] using
      EvalCommandE.call_sem (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal fac σ 0, .read_none, hframe⟩
        (emptyBodyExecE _ _ _ _) ⟨_, .read_none, .update_none⟩
  · -- Inverting the contract rule exposes its assumption of `post`, but `post`
    -- evaluates to `ff`, so no such derivation exists.
    intro σ' failed h
    cases h with
    | call_sem hlookup _ _ _ hassume _ =>
      simp [calleeEnv] at hlookup
      subst hlookup
      simp [oneInputContractProc, Procedure.Spec.getCheckExprs, ListMap.values,
        AssumeExprs] at hassume
      have hff : (Lambda.LExpr.boolConst () false : Expression.Expr)
          = Lambda.LExpr.boolConst () true :=
        Option.some.inj ((eval_boolConst fac _ false).symm.trans hassume.2)
      simp [Lambda.LExpr.boolConst] at hff
  · apply uniqueEvalCommandContractE (calleeEnv_callee _) (by rfl)
    simpa [MetaData.empty, defaultAssertEvents, assumeEvents, assertEvent, assumeEvent,
      oneInputContractProc] using
      EvalCommandContractE.call_sem (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal fac σ 0, .read_none, hframe⟩
        .update_none ⟨_, .read_none, .update_none⟩

/-- ## Example 6.
    Executable call, FAIL path: a failing body (`bodyFailed = true`) makes the
    aggregate failure flag `true` (the `bodyFailed` disjunct), even with passing
    pre- and postconditions. The body is the genuine one-assert body
    `assert false`, executed on `Core.Factory` via `assertBodyExec` — not an
    impossible failure of an empty body. The contract relations never execute that
    body, so they report success on the very same call.

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
  call Callee(0); // bodyFailed = true; both contract checks pass.
};
```
-/
example
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (σ : CoreStore) :
    -- All four displayed store-observation pairs are unique; concrete failure
    -- comes from the body assertion, while contract semantics abstracts it away.
    UniqueResult
      (EvalCommand (calleeEnv failingBodyProc) φ Core.Factory σ
        (.call "callee" [.inArg (intVal 0)] .empty)) σ true ∧
    UniqueResult
      (EvalCommandE (calleeEnv failingBodyProc) φ Core.Factory σ
        (.call "callee" [.inArg (intVal 0)] .empty)) σ
      [assertEvent Core.Factory (calleeFrame (intVal 0)) "pre" HasBool.tt,
       assertEvent Core.Factory (calleeFrame (intVal 0)) "body" HasBool.ff,
       assertEvent Core.Factory (calleeFrame (intVal 0)) "post" HasBool.tt] ∧
    UniqueResult
      (EvalCommandContract (calleeEnv failingBodyProc) Core.Factory σ
        (.call "callee" [.inArg (intVal 0)] .empty)) σ false ∧
    UniqueResult
      (EvalCommandContractE (calleeEnv failingBodyProc) Core.Factory σ
        (.call "callee" [.inArg (intVal 0)] .empty)) σ
      [assertEvent Core.Factory (calleeFrame (intVal 0)) "pre" HasBool.tt,
       assumeEvent Core.Factory (calleeFrame (intVal 0)) "post" HasBool.tt] := by

  have hframe : InitCallFrame (failingBodyProc)
      [intVal 0] [] (calleeFrame (intVal 0)) := initCallFrame_oneInput (ty := .int) (intVal 0)
  -- The one body assertion is `assert false`, so the concrete body run fails.
  have hbody := assertBodyExec (calleeEnv (failingBodyProc))
    φ Core.Factory (calleeFrame (intVal 0)) "body" HasBool.ff false
    coreFactory_WellFormedSemanticEvalBool (eval_boolConst Core.Factory (calleeFrame (intVal 0)) false)
  have hbodyE := assertBodyExecE (calleeEnv (failingBodyProc))
    φ Core.Factory (calleeFrame (intVal 0)) "body" HasBool.ff
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply uniqueEvalCommand (calleeEnv_callee _) (fun h₁ h₂ => by
      simpa [failingBodyProc, oneInputContractBodyProc] using
        assertBodyExecUnique h₁ h₂)
    exact EvalCommand.call_sem (calleeEnv_callee _)
      ⟨_, _, evalExpressions_intVal Core.Factory σ 0, .read_none, hframe⟩
      (.eval_pass (isDefined_boolConst _ true) (eval_boolConst _ _ true) .eval_none) hbody
      (.eval_pass (isDefined_boolConst _ true) (eval_boolConst _ _ true) .eval_none)
      ⟨_, .read_none, .update_none⟩
  · apply uniqueEvalCommandE (calleeEnv_callee _) (fun h₁ h₂ => by
      simpa [failingBodyProc, oneInputContractBodyProc] using
        assertBodyExecEUnique h₁ h₂)
    simpa [MetaData.empty, defaultAssertEvents, assertEvent, failingBodyProc, oneInputContractBodyProc,
      oneInputContractProc] using
      EvalCommandE.call_sem (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal Core.Factory σ 0, .read_none, hframe⟩
        hbodyE ⟨_, .read_none, .update_none⟩
  · apply uniqueEvalCommandContract (calleeEnv_callee _) (by rfl)
    exact EvalCommandContract.call_sem (calleeEnv_callee _)
      ⟨_, _, evalExpressions_intVal Core.Factory σ 0, .read_none, hframe⟩
      (.eval_pass (isDefined_boolConst _ true) (eval_boolConst _ _ true) .eval_none) .update_none
      ⟨isDefined_boolConst _ true, eval_boolConst _ _ true⟩ ⟨_, .read_none, .update_none⟩
  · apply uniqueEvalCommandContractE (calleeEnv_callee _) (by rfl)
    simpa [MetaData.empty, defaultAssertEvents, assumeEvents, assertEvent, assumeEvent, failingBodyProc,
      oneInputContractBodyProc, oneInputContractProc] using
      EvalCommandContractE.call_sem (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal Core.Factory σ 0, .read_none, hframe⟩
        .update_none ⟨_, .read_none, .update_none⟩

/-- ## Example 7.
    Contract call, FAIL path: a false (`ff`) Default precondition makes the
    failure flag `true` under both failure-flag relations. The contract flag is
    `preFailed` only: the postcondition is assumed rather than checked, so it
    cannot contribute a failure.

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
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (fac : Expression.Factory) (σ : CoreStore) :
    -- All four displayed store-observation pairs are unique. Both failure
    -- relations report the false precondition; traces distinguish check/assume.
    UniqueResult
      (EvalCommand
        (calleeEnv (oneInputContractProc calleeY .int HasBool.ff HasBool.tt))
        φ fac σ (.call "callee" [.inArg (intVal 0)] .empty)) σ true ∧
    UniqueResult
      (EvalCommandE
        (calleeEnv (oneInputContractProc calleeY .int HasBool.ff HasBool.tt))
        φ fac σ (.call "callee" [.inArg (intVal 0)] .empty)) σ
      [assertEvent fac (calleeFrame (intVal 0)) "pre" HasBool.ff,
       assertEvent fac (calleeFrame (intVal 0)) "post" HasBool.tt] ∧
    UniqueResult
      (EvalCommandContract
        (calleeEnv (oneInputContractProc calleeY .int HasBool.ff HasBool.tt))
        fac σ (.call "callee" [.inArg (intVal 0)] .empty)) σ true ∧
    UniqueResult
      (EvalCommandContractE
        (calleeEnv (oneInputContractProc calleeY .int HasBool.ff HasBool.tt))
        fac σ (.call "callee" [.inArg (intVal 0)] .empty)) σ
      [assertEvent fac (calleeFrame (intVal 0)) "pre" HasBool.ff,
       assumeEvent fac (calleeFrame (intVal 0)) "post" HasBool.tt] := by

  have hframe : InitCallFrame (oneInputContractProc calleeY .int HasBool.ff HasBool.tt)
      [intVal 0] [] (calleeFrame (intVal 0)) := initCallFrame_oneInput (ty := .int) (intVal 0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply uniqueEvalCommand (calleeEnv_callee _) emptyBodyExecUnique
    exact EvalCommand.call_sem (calleeEnv_callee _)
      ⟨_, _, evalExpressions_intVal fac σ 0, .read_none, hframe⟩
      (.eval_fail (isDefined_boolConst _ false) (eval_boolConst _ _ false) .eval_none)
      (emptyBodyExec _ _ _ _)
      (.eval_pass (isDefined_boolConst _ true) (eval_boolConst _ _ true) .eval_none)
      ⟨_, .read_none, .update_none⟩
  · apply uniqueEvalCommandE (calleeEnv_callee _) emptyBodyExecEUnique
    simpa [MetaData.empty, defaultAssertEvents, assertEvent, oneInputContractProc] using
      EvalCommandE.call_sem (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal fac σ 0, .read_none, hframe⟩
        (emptyBodyExecE _ _ _ _) ⟨_, .read_none, .update_none⟩
  · apply uniqueEvalCommandContract (calleeEnv_callee _) (by rfl)
    exact EvalCommandContract.call_sem (calleeEnv_callee _)
      ⟨_, _, evalExpressions_intVal fac σ 0, .read_none, hframe⟩
      (.eval_fail (isDefined_boolConst _ false) (eval_boolConst _ _ false) .eval_none) .update_none
      ⟨isDefined_boolConst _ true, eval_boolConst _ _ true⟩ ⟨_, .read_none, .update_none⟩
  · apply uniqueEvalCommandContractE (calleeEnv_callee _) (by rfl)
    simpa [MetaData.empty, defaultAssertEvents, assumeEvents, assertEvent, assumeEvent,
      oneInputContractProc] using
      EvalCommandContractE.call_sem (calleeEnv_callee _)
        ⟨_, _, evalExpressions_intVal fac σ 0, .read_none, hframe⟩
        .update_none ⟨_, .read_none, .update_none⟩

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
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (fac : Expression.Factory) :
    -- Concrete semantics executes both nested bodies while contract semantics
    -- abstracts the outer call. Every relation uniquely returns `emptyStore`
    -- with its displayed success flag or empty trace.
    UniqueResult
      (EvalCommand nestedProcEnv φ fac emptyStore (.call "middle" [] .empty))
      emptyStore false ∧
    UniqueResult
      (EvalCommandE nestedProcEnv φ fac emptyStore (.call "middle" [] .empty))
      emptyStore [] ∧
    UniqueResult
      (EvalCommandContract nestedProcEnv fac emptyStore (.call "middle" [] .empty))
      emptyStore false ∧
    UniqueResult
      (EvalCommandContractE nestedProcEnv fac emptyStore (.call "middle" [] .empty))
      emptyStore [] := by
  have hleaf : EvalCommand nestedProcEnv φ fac emptyStore
      (.call "leaf" [] .empty) emptyStore false := by
    exact EvalCommand.call_sem (by simp [nestedProcEnv, leafProc])
      ⟨_, _, .eval_none, .read_none, emptyFrame "leaf" []⟩
      .eval_none (emptyBodyExec nestedProcEnv φ emptyStore fac) .eval_none
      ⟨_, .read_none, .update_none⟩
  -- Event analogue of `hleaf`: leaf has no contract clauses and an empty body,
  -- so its call emits no events.
  have hleafE : EvalCommandE nestedProcEnv φ fac emptyStore
      (.call "leaf" [] .empty) emptyStore [] := by
    simpa [defaultAssertEvents, leafProc, noArgProc] using
      EvalCommandE.call_sem (π := nestedProcEnv) (by simp [nestedProcEnv, leafProc])
        ⟨_, _, .eval_none, .read_none, emptyFrame "leaf" []⟩
        (emptyBodyExecE nestedProcEnv φ emptyStore fac)
        ⟨_, .read_none, .update_none⟩
  let ρ : Env Expression := ⟨emptyStore, fac, false⟩
  have hmiddleStmts : StepStmtStar Expression (EvalCommand nestedProcEnv φ) (EvalPureFunc φ)
      (.stmts [.cmd (.call "leaf" [] .empty)] ρ) (.terminal ρ) := by
    refine .step _ _ _ .step_stmts_cons ?_
    refine .step _ _ _ (.step_seq_inner (.step_cmd hleaf)) ?_
    exact .step _ _ _ .step_seq_done (.step _ _ _ .step_stmts_nil (.refl _))
  have hmiddleBody : CoreBodyExec nestedProcEnv φ middleProc.body
      emptyStore fac emptyStore fac false := by
    unfold middleProc noArgProc
    change CoreBodyExec nestedProcEnv φ
      (.structured [.cmd (.call "leaf" [] .empty)]) emptyStore fac emptyStore fac false
    have hcore : CoreStepStar nestedProcEnv φ
        (.stmt (.block "" [.cmd (.call "leaf" [] .empty)] .empty) ρ) (.terminal ρ) := by
      apply StepStmtStar_to_CoreStepStar
      refine .step _ _ _ .step_block ?_
      refine ReflTrans_Transitive _ _ _ _
        (block_inner_star Expression (EvalCommand nestedProcEnv φ) (EvalPureFunc φ)
          _ _ (some "") emptyStore fac hmiddleStmts) ?_
      exact ReflTrans.step _ _ _ StepStmt.step_block_done (ReflTrans.refl _)
    exact CoreBodyExec.structured (ss := [.cmd (.call "leaf" [] .empty)])
      (σ := emptyStore) (fac := fac) (ρ' := ρ) hcore
  -- Event analogue of `hmiddleBody`, modelled on `assertBodyExecE`: middle's body
  -- is a single leaf call that emits no events, so the body emits no events.
  have hmiddleBodyE : CoreBodyExecE nestedProcEnv φ middleProc.body
      emptyStore fac emptyStore fac [] := by
    unfold middleProc noArgProc
    change CoreBodyExecE nestedProcEnv φ
      (.structured [.cmd (.call "leaf" [] .empty)]) emptyStore fac emptyStore fac []
    have hstar : CoreStepStarE nestedProcEnv φ
        (.stmt (Stmt.block "" [.cmd (.call "leaf" [] .empty)] #[]) ρ) []
        (.terminal ⟨projectStore emptyStore emptyStore, fac, false⟩) := by
      refine ReflTransTrace.step _ [] _ _ _
        (StepStmtE.step_admin StepStmt.step_block) ?_
      refine ReflTransTrace.step _ [] _ _ _
        (StepStmtE.step_block_body (StepStmtE.step_admin StepStmt.step_stmts_cons)) ?_
      refine ReflTransTrace.step _ [] _ _ _
        (StepStmtE.step_block_body (StepStmtE.step_seq_inner (StepStmtE.step_cmd hleafE))) ?_
      refine ReflTransTrace.step _ [] _ _ _
        (StepStmtE.step_block_body (StepStmtE.step_admin StepStmt.step_seq_done)) ?_
      refine ReflTransTrace.step _ [] _ _ _
        (StepStmtE.step_block_body (StepStmtE.step_admin StepStmt.step_stmts_nil)) ?_
      refine ReflTransTrace.step _ [] _ _ _
        (StepStmtE.step_admin StepStmt.step_block_done) ?_
      exact ReflTransTrace.refl _
    have h := CoreBodyExecE.structured (π := nestedProcEnv) (φ := φ)
      (ss := [.cmd (.call "leaf" [] .empty)]) (σ := emptyStore) (fac := fac)
      (ρ' := ⟨projectStore emptyStore emptyStore, fac, false⟩) hstar
    simpa [projectStore_self] using h
  have hmiddleBodyUnique : ∀ {frame end₁ end₂ : CoreStore}
      {endFac₁ endFac₂ : Expression.Factory} {failed₁ failed₂ : Bool},
      CoreBodyExec nestedProcEnv φ middleProc.body frame fac end₁ endFac₁ failed₁ →
      CoreBodyExec nestedProcEnv φ middleProc.body frame fac end₂ endFac₂ failed₂ →
      end₁ = end₂ ∧ endFac₁ = endFac₂ ∧ failed₁ = failed₂ := by
    intro frame end₁ end₂ endFac₁ endFac₂ failed₁ failed₂ h₁ h₂
    change CoreBodyExec nestedProcEnv φ
      (.structured [.cmd (.call "leaf" [] .empty)]) frame fac end₁ endFac₁ failed₁ at h₁
    change CoreBodyExec nestedProcEnv φ
      (.structured [.cmd (.call "leaf" [] .empty)]) frame fac end₂ endFac₂ failed₂ at h₂
    exact h₁.singleton_cmd_unique
      (fun hcmd₁ hcmd₂ => hcmd₁.call_unique_of_body_unique (p := leafProc)
        (by simp [nestedProcEnv, leafProc]) emptyBodyExecUnique hcmd₂) h₂
  have hmiddleBodyEUnique : ∀ {frame end₁ end₂ : CoreStore}
      {endFac₁ endFac₂ : Expression.Factory} {emitted₁ emitted₂ : Trace Expression},
      CoreBodyExecE nestedProcEnv φ middleProc.body frame fac end₁ endFac₁ emitted₁ →
      CoreBodyExecE nestedProcEnv φ middleProc.body frame fac end₂ endFac₂ emitted₂ →
      end₁ = end₂ ∧ endFac₁ = endFac₂ ∧ emitted₁ = emitted₂ := by
    intro frame end₁ end₂ endFac₁ endFac₂ emitted₁ emitted₂ h₁ h₂
    change CoreBodyExecE nestedProcEnv φ
      (.structured [.cmd (.call "leaf" [] .empty)]) frame fac end₁ endFac₁ emitted₁ at h₁
    change CoreBodyExecE nestedProcEnv φ
      (.structured [.cmd (.call "leaf" [] .empty)]) frame fac end₂ endFac₂ emitted₂ at h₂
    exact h₁.singleton_cmd_unique
      (fun hcmd₁ hcmd₂ => hcmd₁.call_unique_of_body_unique (p := leafProc)
        (by simp [nestedProcEnv, leafProc]) emptyBodyExecEUnique hcmd₂) h₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply uniqueEvalCommand (p := middleProc) (by simp [nestedProcEnv, middleProc]) hmiddleBodyUnique
    exact EvalCommand.call_sem (by simp [nestedProcEnv, middleProc])
      ⟨_, _, .eval_none, .read_none, emptyFrame "middle" [.cmd (.call "leaf" [] .empty)]⟩
      .eval_none hmiddleBody .eval_none ⟨_, .read_none, .update_none⟩
  · apply uniqueEvalCommandE (p := middleProc) (by simp [nestedProcEnv, middleProc]) hmiddleBodyEUnique
    simpa [defaultAssertEvents, middleProc, noArgProc] using
      EvalCommandE.call_sem (by simp [nestedProcEnv, middleProc])
        ⟨_, _, .eval_none, .read_none, emptyFrame "middle" [.cmd (.call "leaf" [] .empty)]⟩
        hmiddleBodyE ⟨_, .read_none, .update_none⟩
  · apply uniqueEvalCommandContract (p := middleProc)
      (by simp [nestedProcEnv, middleProc]) (by rfl)
    exact EvalCommandContract.call_sem (by simp [nestedProcEnv, middleProc])
      ⟨_, _, .eval_none, .read_none, emptyFrame "middle" [.cmd (.call "leaf" [] .empty)]⟩
      .eval_none .update_none (by trivial) ⟨_, .read_none, .update_none⟩
  · apply uniqueEvalCommandContractE (p := middleProc)
      (by simp [nestedProcEnv, middleProc]) (by rfl)
    simpa [defaultAssertEvents, assumeEvents, middleProc, noArgProc] using
      EvalCommandContractE.call_sem (by simp [nestedProcEnv, middleProc])
        ⟨_, _, .eval_none, .read_none, emptyFrame "middle" [.cmd (.call "leaf" [] .empty)]⟩
        .update_none ⟨_, .read_none, .update_none⟩

end Core.StatementSemanticsTests
