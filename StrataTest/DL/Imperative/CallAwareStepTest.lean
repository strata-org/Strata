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
private theorem body_run (fac : Expression.Factory) :
    StepStmtExtStarE calleeEnv
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
private theorem callCmd_sem (fac : Expression.Factory)
    (σ : CoreStore) :
    EvalCmdExtE calleeEnv fac σ callCmd σ (callTrace fac) := by
  have hbody : BigStepE calleeEnv callee.body ⟨emptyStore, fac, false⟩ emptyStore
      [trueEvent fac "body"] :=
    .structured (ρ' := ⟨emptyStore, fac, false⟩) (body_run fac)
  have h := EvalCmdExtE.call_sem (n := "callee") (callArgs := []) (md := .empty)
    (π := calleeEnv) (fac := fac) (σ := σ) (σ' := σ) (σAO := emptyStore)
    (by simp [calleeEnv])
    ⟨[], [], .eval_none, .read_none, ⟨emptyStore, emptyStore, .init_none, .init_none, rfl⟩⟩
    hbody ⟨[], .read_none, .update_none⟩
  simpa [Calls.defaultAssertEvents, callee, callCmd, callTrace, trueEvent, MetaData.empty]
    using h

/-- The same call step, derived through Core's abbreviations: `CoreBodyExecE.structured`
    and `EvalCommandE.call_sem` with Core's `CallEntry` / `CallExit` premises. -/
private theorem callCmd_semCore
    (fac : Expression.Factory) (σ : CoreStore) :
    EvalCommandE calleeEnv fac σ callCmd σ (callTrace fac) := by
  have hbody : CoreBodyExecE calleeEnv callee.body ⟨emptyStore, fac, false⟩ emptyStore
      [trueEvent fac "body"] :=
    CoreBodyExecE.structured (ρ' := ⟨emptyStore, fac, false⟩) (body_run fac)
  have h := EvalCommandE.call_sem (n := "callee") (callArgs := []) (md := .empty)
    (π := calleeEnv) (fac := fac) (σ := σ) (σ' := σ) (σAO := emptyStore)
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
example (fac : Expression.Factory) (σ : CoreStore)
    (f : Bool) :
    StepCFGExtStarE calleeEnv fac callCFG
      (.atBlock "entry" σ f) (callTrace fac) (.terminal σ f) :=
  .step _ [] _ (callTrace fac) _ (.fetch rfl) <|
  .step _ (callTrace fac) _ [] _ (.step_cmd (callCmd_sem fac σ)) <|
  .step _ [] _ [] _ .finish (.refl _)

/-- The same CFG run derived through Core's abbreviations, with the call step from
    `callCmd_semCore`. -/
example (fac : Expression.Factory) (σ : CoreStore) (f : Bool) :
    StepCFGExtStarE calleeEnv fac callCFG
      (.atBlock "entry" σ f) (callTrace fac) (.terminal σ f) :=
  .step _ [] _ (callTrace fac) _ (.fetch rfl) <|
  .step _ (callTrace fac) _ [] _ (.step_cmd (callCmd_semCore fac σ)) <|
  .step _ [] _ [] _ .finish (.refl _)

/-- The Kleene command `callCmd` runs to `.terminal` with the same environment,
    emitting the call's pre / body / post events. -/
example (ρ : Env Expression) :
    StepKleeneExtStarE calleeEnv
      (.stmt (.cmd callCmd) ρ) (callTrace ρ.factory) (.terminal ρ) := by
  have h := StepKleeneE.step_cmd (P := Expression) (EvalCmd := EvalCmdExtE calleeEnv)
    (ρ := ρ) (callCmd_sem ρ.factory ρ.store)
  simpa using ReflTransTrace.step _ _ _ [] _ h (.refl _)

end CallAwareStepTest
