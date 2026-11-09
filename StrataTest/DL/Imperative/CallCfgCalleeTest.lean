/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Imperative.CallAwareSemantics
import Strata.DL.Imperative.CFGSemanticsProps
import Strata.DL.Imperative.StmtCFGCallSemanticsProps
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.Languages.Core.StatementSemanticsProps
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.StmtCFGCallSemantics
import all Strata.DL.Imperative.StmtSemantics
import all Strata.Languages.Core.Procedure
import all Strata.Languages.Core.StatementSemantics
import all Strata.Util.ListMap
import Strata.Languages.Core.DDMTransform.Translate
import StrataDDM.Integration.Lean.HashCommands
meta import Strata.Languages.Core.DDMTransform.Translate

/-! # Tests for calls to procedures with a CFG body

Concrete derivations, at Core's `Expression`, of a call `call callee(out x)` whose
callee `callee` has one output formal `y : bool`, no specification clauses, and a
CFG body with the single block `"entry"`:
`init t : bool := *; y := *; assert body: true; finish`.
The derivations choose `true` for both nondeterministic values.  From the caller
store `x ↦ false`, the callee frame is `y ↦ false`; the body halts at
`y ↦ true, t ↦ true`, the call's final callee store drops the body-local `t`, and
the caller ends at `x ↦ true`.  The call is run from a structured statement, from
a caller CFG, and from a procedure whose body is that caller CFG.

The callee and both callers are also written as a Core program in DDM syntax,
`calleeProgram`.  The derivations are about hand-built ASTs; `#guard` checks pin
that the DDM translation of `calleeProgram`, with its metadata erased, is exactly
those ASTs, so the derivations hold for the parsed program up to metadata.  (The
translation is a `partial` function, so this equality is checked by evaluation,
not by `rfl`.) -/

namespace CallCfgCalleeTest

open Imperative Core

/-- The caller variable `x`. -/
private def xId : CoreIdent := ⟨"x", ()⟩
/-- The callee's output formal `y`. -/
private def yId : CoreIdent := ⟨"y", ()⟩
/-- The callee's body-local variable `t`. -/
private def tId : CoreIdent := ⟨"t", ()⟩

/-- The store `σ` with `k` bound to `v`. -/
private def bind (σ : CoreStore) (k : CoreIdent) (v : Expression.Val) : CoreStore :=
  fun i => if i = k then some v else σ i

/-- Binding an unbound slot `k` of `σ` to `v` initializes it. -/
private theorem initState_bind {σ : CoreStore} {k : CoreIdent} {v : Expression.Val}
    (h : σ k = none) : InitState Expression σ k v (bind σ k v) :=
  .init h (by simp [bind]) fun _ hk => by simp [bind, Ne.symm hk]

/-- Binding a bound slot `k` of `σ` to `v` updates it. -/
private theorem updateState_bind {σ : CoreStore} {k : CoreIdent} {v v' : Expression.Val}
    (h : σ k = some v') : UpdateState Expression σ k v (bind σ k v) :=
  .update h (by simp [bind]) fun _ hk => by simp [bind, Ne.symm hk]

/-- The Boolean value `true` of the factory `fac`. -/
private abbrev ttV (fac : Expression.Factory) : Expression.Val := HasBool.ttVal fac
/-- The Boolean value `false` of the factory `fac`. -/
private abbrev ffV (fac : Expression.Factory) : Expression.Val := HasBool.ffVal fac

/-- The caller store before the call: `x ↦ false`. -/
private def σ0 (fac : Expression.Factory) : CoreStore := bind emptyStore xId (ffV fac)
/-- The callee entry frame: `y ↦ false`. -/
private def frame (fac : Expression.Factory) : CoreStore := bind emptyStore yId (ffV fac)
/-- The callee store after `init t`: `y ↦ false, t ↦ true`. -/
private def σ1 (fac : Expression.Factory) : CoreStore := bind (frame fac) tId (ttV fac)
/-- The callee store at the `assert`: `y ↦ true, t ↦ true`. -/
private def σ2 (fac : Expression.Factory) : CoreStore := bind (σ1 fac) yId (ttV fac)

/-- The callee's CFG body. -/
private def calleeCFG : DetCFG Expression Command :=
  { entry := "entry"
    blocks := [("entry",
      { cmds := [.cmd (.init tId HasBool.boolTy .nondet .empty),
                 .cmd (.set yId .nondet .empty),
                 .cmd (.assert "body" HasBool.tt .empty)]
        transfer := .finish .empty })] }

/-- The callee: output `y : bool`, no specification clauses, body `calleeCFG`. -/
private def callee : Procedure :=
  { header := { name := ⟨"callee", ()⟩, typeArgs := [], inputs := [],
                outputs := [(yId, .tcons "bool" [])] }
    spec := { preconditions := [], postconditions := [] }
    body := .cfg calleeCFG }

/-- A procedure environment resolving only `"callee"`. -/
private def calleeEnv : String → Option Procedure :=
  fun n => if n = "callee" then some callee else none

/-- The call command `call callee(out x)`. -/
private def callCmd : Command := .call "callee" [.outArg xId] .empty

/-- The `body` assertion event, captured at the store `σ2` and factory `fac`. -/
private def bodyEvent (fac : Expression.Factory) : Event Expression :=
  .assert { factory := fac, store := (σ2 fac), label := "body", expr := HasBool.tt,
            metadata := .empty }

/-- The callee body runs from `frame` to `finish` at `σ2`, emitting `bodyEvent`. -/
private theorem calleeCFG_run (fac : Expression.Factory) :
    StepCFGExtStarE calleeEnv
      (.atBlock calleeCFG "entry" ⟨(frame fac), fac⟩) [bodyEvent fac]
      (.terminal ⟨(σ2 fac), fac⟩) :=
  have hwf := coreEvaluator_WellFormedSemanticEvalVar fac
  have hy : (σ1 fac) yId = some (ffV fac) := by simp [σ1, frame, bind, tId, yId]
  .step _ [] _ _ _ (.fetch rfl) <|
  .step _ [] _ _ _ (.step_cmd (.cmd_sem (.eval_init_unconstrained
    (initState_bind (v := (ttV fac)) (by simp [frame, bind, emptyStore, tId, yId]))
    (HasBool.boolIsValOfTy fac).1 hwf))) <|
  .step _ [] _ _ _ (.step_cmd (.cmd_sem (.eval_set_nondet
    (updateState_bind (v := (ttV fac)) hy)
    ⟨(ffV fac), HasBool.boolTy, hy, (HasBool.boolIsValOfTy fac).2,
      (HasBool.boolIsValOfTy fac).1⟩ hwf))) <|
  .step _ [bodyEvent fac] _ _ _ (.step_cmd (.cmd_sem .eval_assert)) <|
  .step _ [] _ [] _ .finish (.refl _)

/-- `callCmd` takes `σ0` to `x ↦ true`, emitting the callee's `bodyEvent`. -/
private theorem callCmd_sem (fac : Expression.Factory) :
    EvalCmdExtE calleeEnv fac (σ0 fac) callCmd (bind (σ0 fac) xId (ttV fac)) [bodyEvent fac] := by
  have hbody : BigStepE calleeEnv callee.body ⟨(frame fac), fac⟩
      (projectStore (frame fac) (σ2 fac))
      [bodyEvent fac] :=
    .cfg (calleeCFG_run fac)
  have h := EvalCmdExtE.call_sem (n := "callee") (callArgs := [.outArg xId]) (md := .empty)
    (π := calleeEnv) (fac := fac) (σ := (σ0 fac)) (σAO := (frame fac))
    (by simp [calleeEnv])
    ⟨[], [(ffV fac)], .eval_none,
      .read_some (by simp [σ0, bind]) (HasBool.boolIsVal fac).2 .read_none,
      ⟨emptyStore, (frame fac), .init_none, .init_some (initState_bind rfl) .init_none, rfl⟩⟩
    hbody
    ⟨(by simp [Imperative.CallArg.getLhs]), [(ttV fac)],
      .read_some (by simp [projectStore, frame, σ2, bind, yId])
        (HasBool.boolIsVal fac).1 .read_none,
      .update_some (updateState_bind (v' := (ffV fac)) (by simp [σ0, bind])) .update_none,
      .cons ⟨(ffV fac), HasBool.boolTy, (by simp [σ0, bind]), (HasBool.boolIsValOfTy fac).2,
        (HasBool.boolIsValOfTy fac).1⟩ .nil⟩
  simpa [Calls.defaultAssertEvents, Calls.checksAtCall, callee, callCmd] using h

/-- The call's callee body ends with the body-local `t` dropped and `y ↦ true`. -/
example (fac : Expression.Factory) :
    projectStore (frame fac) (σ2 fac) tId = none ∧
      projectStore (frame fac) (σ2 fac) yId = some (ttV fac) := by
  simp [projectStore, frame, σ2, bind, emptyStore, tId, yId]

/-- A structured caller: the statement `call callee(out x)` runs from `x ↦ false` to
    `x ↦ true`, emitting the callee's `bodyEvent`. -/
example (fac : Expression.Factory) :
    StepStmtExtStarE calleeEnv (.stmt (.cmd callCmd) ⟨(σ0 fac), fac⟩) [bodyEvent fac]
      (.terminal ⟨bind (σ0 fac) xId (ttV fac), fac⟩) := by
  have h := StepStmtE.step_cmd (P := Expression) (ρ := ⟨(σ0 fac), fac⟩)
    (callCmd_sem fac)
  simpa using ReflTransTrace.step _ _ _ [] _ h (.refl _)

/-- A caller CFG whose block `"entry"` runs `callCmd` and then finishes. -/
private def callerCFG : DetCFG Expression Command :=
  { entry := "entry"
    blocks := [("entry", { cmds := [callCmd], transfer := .finish .empty })] }

/-- The caller CFG runs from `x ↦ false` to `finish` at `x ↦ true`. -/
private theorem callerCFG_run (fac : Expression.Factory) :
    StepCFGExtStarE calleeEnv
      (.atBlock callerCFG "entry" ⟨(σ0 fac), fac⟩) [bodyEvent fac]
      (.terminal ⟨bind (σ0 fac) xId (ttV fac), fac⟩) :=
  .step _ [] _ _ _ (.fetch rfl) <|
  .step _ [bodyEvent fac] _ [] _ (.step_cmd (callCmd_sem fac)) <|
  .step _ [] _ [] _ .finish (.refl _)

/-- A CFG caller procedure body: `callerCFG` as a `BigStepE` body run from `x ↦ false`
    ends at `x ↦ true`. -/
example (fac : Expression.Factory) :
    BigStepE calleeEnv (.cfg callerCFG) ⟨(σ0 fac), fac⟩ (bind (σ0 fac) xId (ttV fac))
      [bodyEvent fac] := by
  have h := BigStepE.cfg (ρ := ⟨(σ0 fac), fac⟩) (callerCFG_run fac)
  have hσ : projectStore (σ0 fac) (bind (σ0 fac) xId (ttV fac)) = bind (σ0 fac) xId (ttV fac) := by
    funext i
    by_cases hi : i = xId <;> simp [projectStore, σ0, bind, emptyStore, hi]
  rwa [hσ] at h

/-! ## The procedures in DDM syntax -/

/-- The callee and the two callers in Core's DDM syntax. -/
private def calleeProgram :=
#strata
program Core;
procedure callee(out y : bool)
cfg entry {
  entry: {
    var t : bool;
    havoc y;
    assert [body]: true;
    return;
  }
};
procedure structuredCaller(out x : bool)
{
  call callee(out x);
};
procedure cfgCaller(out x : bool)
cfg entry {
  entry: {
    call callee(out x);
    return;
  }
};
#end

/-- A command with its metadata erased. -/
private def eraseCmdMd : Command → Command
  | .cmd (.init x ty e _) => .cmd (.init x ty e .empty)
  | .cmd (.set x e _) => .cmd (.set x e .empty)
  | .cmd (.assert l b _) => .cmd (.assert l b .empty)
  | .cmd (.assume l b _) => .cmd (.assume l b .empty)
  | .cmd (.cover l b _) => .cmd (.cover l b .empty)
  | .call f args _ => .call f args .empty

/-- A procedure body with the metadata of its commands, its transfers and its
    top-level statements erased. -/
private def eraseBodyMd : Procedure.Body → Procedure.Body
  | .cfg g => .cfg { g with blocks := g.blocks.map fun (l, b) =>
      (l, { cmds := b.cmds.map eraseCmdMd, transfer := b.transfer.stripMetaData }) }
  | .structured ss => .structured (ss.map fun
      | .cmd c => .cmd (eraseCmdMd c)
      | s => s.stripMetaData)

/-- The procedures of the DDM translation of `calleeProgram`, with their bodies'
    metadata erased. -/
private def parsedProcedures : List Procedure :=
  (Strata.TransM.run default (Strata.translateProgram calleeProgram)).fst.decls.filterMap
    fun | .proc p _ => some { p with body := eraseBodyMd p.body } | _ => none

-- The translation of `calleeProgram` reports no errors.
#guard (Strata.TransM.run default (Strata.translateProgram calleeProgram)).snd.isEmpty

-- The parsed `callee` is the hand-built `callee`.
#guard parsedProcedures[0]? == some callee

-- The parsed structured caller's body is the statement `call callee(out x)`.
#guard (parsedProcedures[1]?.map (·.body)) == some (.structured [.cmd callCmd])

-- The parsed CFG caller's body is `callerCFG`.
#guard (parsedProcedures[2]?.map (·.body)) == some (.cfg callerCFG)

end CallCfgCalleeTest
