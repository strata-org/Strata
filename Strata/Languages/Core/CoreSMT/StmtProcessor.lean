/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.CoreSMT.State
import Strata.Languages.Core.CoreSMT.ExprTranslator
import Strata.Languages.Core.CoreSMT.IsCoreSMT
import Strata.Languages.Core.Verifier

/-!
# Statement Processor for CoreSMT Verifier

Processes CoreSMT statements by translating them to SMT solver commands.
Each statement type maps to specific SMT-LIB operations:
- assume → assert
- init with expr → define-fun
- init without expr → declare-fun
- assert → check-sat of negation (push/pop)
- cover → check-sat (push/pop)
- block → push/pop
- funcDecl → declare-fun or define-fun
- havoc → declare-fun (fresh)
-/

namespace Strata.Core.CoreSMT

open Core
open Strata.SMT
open Lambda
open Imperative

/-- Outcome of a CoreSMT verification check -/
inductive CheckOutcome where
  | pass        -- Proved (unsat when checking negation)
  | fail        -- Counterexample found (sat when checking negation)
  | unknown     -- Solver couldn't determine
  | refuted     -- Provably false (unsat when checking the assertion itself)
  | error (msg : String)
  deriving Repr, DecidableEq, Inhabited

instance : Std.ToFormat CheckOutcome where
  format
    | .pass => "✅ pass"
    | .fail => "❌ fail"
    | .unknown => "🟡 unknown"
    | .refuted => "🔴 refuted"
    | .error msg => s!"🚨 error: {msg}"

/-- Result of a single verification check -/
structure CheckResult where
  label : String
  outcome : CheckOutcome
  isCover : Bool := false
  deriving Repr, Inhabited

/-- Helper: translate an expression to SMT term, throwing IO error on failure -/
private def translateOrThrow (E : Core.Env) (e : Core.Expression.Expr)
    (ctx : Core.SMT.Context) : IO (Term × Core.SMT.Context) := do
  match translateExpr E e ctx with
  | .ok r => return r
  | .error msg => throw (IO.userError s!"Translation error: {msg}")

/-- Helper: translate a type to SMT TermType, throwing IO error on failure -/
private def translateTypeOrThrow (E : Core.Env) (ty : Core.Expression.Ty)
    (ctx : Core.SMT.Context) : IO (TermType × Core.SMT.Context) := do
  match translateType E ty ctx with
  | .ok r => return r
  | .error msg => throw (IO.userError s!"Type translation error: {msg}")

/-- Proof check: check-sat of negation using push/pop -/
private def proveCheck (state : CoreSMTState) (E : Core.Env)
    (label : String) (expr : Core.Expression.Expr)
    (smtCtx : Core.SMT.Context) : IO (CheckResult × Core.SMT.Context) := do
  let (term, smtCtx) ← translateOrThrow E expr smtCtx
  state.solver.push
  state.solver.assert (Factory.not term)
  let decision ← state.solver.checkSat
  state.solver.pop
  let outcome := match decision with
    | .unsat   => CheckOutcome.pass
    | .sat     => CheckOutcome.fail
    | .unknown => CheckOutcome.unknown
  return ({ label, outcome, isCover := false }, smtCtx)

/-- Cover check: check-sat of expression using push/pop -/
private def coverCheck (state : CoreSMTState) (E : Core.Env)
    (label : String) (expr : Core.Expression.Expr)
    (smtCtx : Core.SMT.Context) : IO (CheckResult × Core.SMT.Context) := do
  let (term, smtCtx) ← translateOrThrow E expr smtCtx
  state.solver.push
  state.solver.assert term
  let decision ← state.solver.checkSat
  state.solver.pop
  let outcome := match decision with
    | .sat     => CheckOutcome.pass      -- Reachable
    | .unsat   => CheckOutcome.fail      -- Unreachable
    | .unknown => CheckOutcome.unknown
  return ({ label, outcome, isCover := true }, smtCtx)

mutual
/-- Process a single CoreSMT statement. Returns updated state, SMT context,
    and an optional check result (for assert/cover). -/
partial def processStatement (state : CoreSMTState) (E : Core.Env)
    (stmt : Core.Statement) (smtCtx : Core.SMT.Context)
    : IO (CoreSMTState × Core.SMT.Context × Option CheckResult) := do
  if !isCoreSMTStmt stmt then
    return (state, smtCtx, some { label := "non-CoreSMT", outcome := .error "Statement not in CoreSMT subset" })
  match stmt with
  | Core.Statement.assume _label expr _ =>
    let (term, smtCtx) ← translateOrThrow E expr smtCtx
    state.solver.assert term
    let state := state.addItem (.assumption expr)
    return (state, smtCtx, none)

  | Core.Statement.init name ty (some expr) _ =>
    let (term, smtCtx) ← translateOrThrow E expr smtCtx
    let (smtTy, smtCtx) ← translateTypeOrThrow E ty smtCtx
    state.solver.defineFun name.name [] smtTy term
    let state := state.addItem (.varDef name.name smtTy term)
    return (state, smtCtx, none)

  | Core.Statement.init name ty none _ =>
    let (smtTy, smtCtx) ← translateTypeOrThrow E ty smtCtx
    state.solver.declareFun name.name [] smtTy
    let state := state.addItem (.varDecl name.name smtTy)
    return (state, smtCtx, none)

  | Core.Statement.assert label expr _ =>
    let (result, smtCtx) ← proveCheck state E label expr smtCtx
    return (state.incResultCount, smtCtx, some result)

  | Core.Statement.cover label expr _ =>
    let (result, smtCtx) ← coverCheck state E label expr smtCtx
    return (state.incResultCount, smtCtx, some result)

  | .cmd (.cmd (.havoc name _)) =>
    -- For havoc, declare a fresh unconstrained variable
    -- We need the type from context; for now declare as uninterpreted
    let state := state.addItem (.varDecl name.name .int)
    state.solver.declareFun name.name [] .int
    return (state, smtCtx, none)

  | .block _label stmts _ =>
    let state ← state.push
    let (state, smtCtx, results) ← processStatements state E stmts smtCtx
    let state ← state.pop
    -- Return the last check result if any
    return (state, smtCtx, results.getLast?)

  | .funcDecl decl _ =>
    let inputTypes ← decl.inputs.foldlM (fun acc (_, ty) => do
      let (smtTy, _) ← translateTypeOrThrow E ty smtCtx
      return acc ++ [smtTy]) []
    let (outTy, smtCtx) ← translateTypeOrThrow E decl.output smtCtx
    match decl.body with
    | none =>
      state.solver.declareFun decl.name.name inputTypes outTy
      let state := state.addItem (.funcDecl decl.name.name inputTypes outTy)
      return (state, smtCtx, none)
    | some body =>
      let (bodyTerm, smtCtx) ← translateOrThrow E body smtCtx
      let args := decl.inputs.map fun (name, ty) =>
        match translateType E ty smtCtx with
        | .ok (smtTy, _) => (name.name, smtTy)
        | .error _ => (name.name, TermType.int)
      state.solver.defineFun decl.name.name args outTy bodyTerm
      let state := state.addItem (.funcDef decl.name.name args outTy bodyTerm)
      return (state, smtCtx, none)

  | _ => return (state, smtCtx, some { label := "unknown", outcome := .error "Unexpected statement" })

/-- Process a list of CoreSMT statements sequentially -/
partial def processStatements (state : CoreSMTState) (E : Core.Env)
    (stmts : List Core.Statement) (smtCtx : Core.SMT.Context)
    : IO (CoreSMTState × Core.SMT.Context × List CheckResult) := do
  let mut state := state
  let mut smtCtx := smtCtx
  let mut results : List CheckResult := []
  for stmt in stmts do
    let (state', smtCtx', result) ← processStatement state E stmt smtCtx
    state := state'
    smtCtx := smtCtx'
    match result with
    | some r => results := results ++ [r]
    | none => pure ()
    -- If not accumulating errors and we got a failure, stop
    if !state.config.accumulateErrors then
      match result with
      | some r =>
        if r.outcome != .pass then
          return (state, smtCtx, results)
      | none => pure ()
  return (state, smtCtx, results)
end

end Strata.Core.CoreSMT
