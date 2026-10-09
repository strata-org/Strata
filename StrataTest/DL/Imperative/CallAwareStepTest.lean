/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Imperative.CallAwareSemantics
import Strata.DL.Imperative.CFGSemanticsProps
import Strata.Languages.Core.StatementSemanticsProps
import all Strata.DL.Imperative.StmtCallSemantics
import all Strata.Languages.Core.StatementSemantics
import all Strata.Languages.Core.Procedure
import all Strata.Util.ListMap

/-! # Tests for the call-aware event-trace CFG and Kleene relations

Concrete derivations of `StepCFGExtStarE` and `StepKleeneExtStarE` at Core's
`Expression`, in which the single command is a call to a procedure `callee` with
no formals, one non-free precondition `pre`, one non-free postcondition `post`
(both the literal `true`), and a body consisting of the single statement
`assert body: true`.  The call steps through `EvalCmdExtE.call_sem`; its trace is
the `pre` assertion event, then the body's `body` assertion event, then the `post`
assertion event, each captured at the callee's (empty) frame.  One CFG derivation
builds the call step through Core's abbreviations `EvalCommandE` /
`CoreBodyExecE` and their Core-premise constructors. -/

namespace CallAwareStepTest

open Imperative Core

/-- The callee's only body statement: `assert body: true`. -/
private def bodyStmt : Statement := .cmd (.cmd (.assert "body" HasBool.tt .empty))

/-- The callee: no formals, precondition `pre : true`, postcondition `post : true`,
    body `[bodyStmt]`. -/
private def callee : Procedure :=
  { header := { name := ⟨"callee", ()⟩, typeArgs := [], inputs := [], outputs := [] }
    spec := { preconditions := [("pre", { expr := HasBool.tt })],
              postconditions := [("post", { expr := HasBool.tt })] }
    body := .structured [bodyStmt] }

/-- A procedure environment resolving only `"callee"`. -/
private def calleeEnv : String → Option Procedure :=
  fun n => if n = "callee" then some callee else none

/-- The call command `call callee()`. -/
private def callCmd : Command := .call "callee" [] .empty

/-- The assertion event of label `label` and condition `true`, captured at the
    empty store and factory `fac`. -/
private def trueEvent (fac : Expression.Factory) (label : String) : Event Expression :=
  .assert { factory := fac, store := emptyStore, label := label, expr := HasBool.tt,
            metadata := .empty }

/-- The trace of `callCmd`: precondition, body, postcondition. -/
private def callTrace (fac : Expression.Factory) : Trace Expression :=
  [trueEvent fac "pre", trueEvent fac "body", trueEvent fac "post"]

/-- The callee body, wrapped as `BigStepE` wraps it, runs from the empty frame to
    termination, emitting the `body` assertion event. -/
private theorem body_run (δ : ExtendFactory Expression) (fac : Expression.Factory) :
    StepStmtExtStarE calleeEnv δ
      (.stmt (Stmt.block "" [bodyStmt] #[]) ⟨emptyStore, fac, false⟩)
      [trueEvent fac "body"]
      (.terminal ⟨emptyStore, fac, false⟩) :=
  .step _ [] _ _ _ (.step_admin .step_block) <|
  .step _ [] _ _ _ (.step_block_body (.step_admin .step_stmts_cons)) <|
  .step _ [trueEvent fac "body"] _ _ _
    (.step_block_body (.step_seq_inner (.step_cmd (.cmd_sem .eval_assert)))) <|
  .step _ [] _ _ _ (.step_block_body (.step_admin .step_seq_done)) <|
  .step _ [] _ _ _ (.step_block_body (.step_admin .step_stmts_nil)) <|
  .step _ [] _ [] _ (.step_admin .step_block_done) (.refl _)

/-- `callCmd` takes any store `σ` to itself, emitting `callTrace fac`. -/
private theorem callCmd_sem (δ : ExtendFactory Expression) (fac : Expression.Factory)
    (σ : CoreStore) :
    EvalCmdExtE calleeEnv δ fac σ callCmd σ (callTrace fac) := by
  have hbody : BigStepE calleeEnv δ callee.body emptyStore fac emptyStore fac
      [trueEvent fac "body"] :=
    .structured (ρ' := ⟨emptyStore, fac, false⟩) (body_run δ fac)
  have h := EvalCmdExtE.call_sem (n := "callee") (callArgs := []) (md := .empty)
    (π := calleeEnv) (δ := δ) (fac := fac) (σ := σ) (σ' := σ) (σAO := emptyStore)
    (by simp [calleeEnv])
    ⟨[], [], .eval_none, .read_none, ⟨emptyStore, emptyStore, .init_none, .init_none, rfl⟩⟩
    hbody ⟨[], .read_none, .update_none⟩
  simpa [Calls.defaultAssertEvents, callee, callCmd, callTrace, trueEvent, MetaData.empty]
    using h

/-- The same call step, derived through Core's abbreviations: `CoreBodyExecE.structured`
    and `EvalCommandE.call_sem` with Core's `CallEntry` / `CallExit` premises. -/
private theorem callCmd_semCore
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (fac : Expression.Factory) (σ : CoreStore) :
    EvalCommandE calleeEnv φ fac σ callCmd σ (callTrace fac) := by
  have hbody : CoreBodyExecE calleeEnv φ callee.body emptyStore fac emptyStore fac
      [trueEvent fac "body"] :=
    CoreBodyExecE.structured (ρ' := ⟨emptyStore, fac, false⟩) (body_run _ fac)
  have h := EvalCommandE.call_sem (n := "callee") (callArgs := []) (md := .empty)
    (π := calleeEnv) (φ := φ) (fac := fac) (σ := σ) (σ' := σ) (σAO := emptyStore)
    (by simp [calleeEnv])
    ⟨[], [], .eval_none, .read_none, ⟨emptyStore, emptyStore, .init_none, .init_none, rfl⟩⟩
    hbody ⟨[], .read_none, .update_none⟩
  simpa [Calls.defaultAssertEvents, callee, callCmd, callTrace, trueEvent, MetaData.empty]
    using h

/-- A one-block CFG whose block `"entry"` runs `callCmd` and then finishes. -/
private def callCFG : CFG String (DetBlock String Command Expression) :=
  { entry := "entry"
    blocks := [("entry", { cmds := [callCmd], transfer := .finish .empty })] }

/-- The CFG run fetches `"entry"`, steps the call, and finishes: the store and
    failure flag are unchanged and the trace is the call's pre / body / post events. -/
example (δ : ExtendFactory Expression) (fac : Expression.Factory) (σ : CoreStore)
    (f : Bool) :
    StepCFGExtStarE calleeEnv δ fac callCFG
      (.atBlock "entry" σ f) (callTrace fac) (.terminal σ f) :=
  .step _ [] _ (callTrace fac) _ (.fetch rfl) <|
  .step _ (callTrace fac) _ [] _ (.step_cmd (callCmd_sem δ fac σ)) <|
  .step _ [] _ [] _ .finish (.refl _)

/-- The same CFG run at Core's `EvalPureFunc φ`, with the call step from
    `callCmd_semCore`. -/
example (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (fac : Expression.Factory) (σ : CoreStore) (f : Bool) :
    StepCFGExtStarE calleeEnv (EvalPureFunc φ) fac callCFG
      (.atBlock "entry" σ f) (callTrace fac) (.terminal σ f) :=
  .step _ [] _ (callTrace fac) _ (.fetch rfl) <|
  .step _ (callTrace fac) _ [] _ (.step_cmd (callCmd_semCore φ fac σ)) <|
  .step _ [] _ [] _ .finish (.refl _)

/-- The Kleene command `callCmd` runs to `.terminal` with the same environment,
    emitting the call's pre / body / post events. -/
example (δ : ExtendFactory Expression) (ρ : Env Expression) :
    StepKleeneExtStarE calleeEnv δ
      (.stmt (.cmd callCmd) ρ) (callTrace ρ.factory) (.terminal ρ) := by
  have h := StepKleeneE.step_cmd (P := Expression) (EvalCmd := EvalCmdExtE calleeEnv δ)
    (ρ := ρ) (callCmd_sem δ ρ.factory ρ.store)
  simpa using ReflTransTrace.step _ _ _ [] _ h (.refl _)

end CallAwareStepTest
