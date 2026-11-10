/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.InterpreterEval
meta import Strata.Languages.Core.InterpreterReplay

/-! # Behavioral tests of `EvalM` (`runCoreEval`, `runCoreEvalWith`) at each assert/assume policy,
    and of the call-depth limit -/

meta section

namespace InterpreterEvalTest

open Core Lambda Imperative

private def id (name : String) : CoreIdent := ⟨name, ()⟩
private def int (n : Int) : Expression.Expr := .intConst () n
private def md : MetaData Expression := #[]
private def xVar : Expression.Expr := .fvar () (id "x") (some .int)

private def setX (v : Int) : Statement :=
  .cmd (.cmd (.set (id "x") (.det (int v)) md))
private def assertX (label : String) (rhs : Int) : Statement :=
  .cmd (.cmd (.assert label (.eq () xVar (int rhs)) md))

/-- Caller env with `x` predefined to `1`. -/
private def env0 : Imperative.IEnv Expression :=
  .ofStore (fun n => if n == id "x" then some (int 1) else none) Core.Factory
private def π : String → Option Procedure := fun _ => none

/-- Read `x` from the final store of an `EvalM` run. -/
private def finalX (stmts : List Statement) : Option Expression.Expr :=
  (runCoreEvalStore π 100 (.stmts stmts env0)).bind (fun s => s (id "x"))

-- Passing assert: the run continues, so the following `set x := 2` takes effect.
#guard finalX [assertX "ap" 1, setX 2] == some (int 2)
#guard runCoreEvalFailedLabel π 100 (.stmts [assertX "ap" 1, setX 2] env0) == none

-- Failing assert (`x == 2` while `x = 1`): the run halts with the store frozen (`x = 1`), so
-- the following `set x := 3` is not applied.
#guard finalX [assertX "af" 2, setX 3] == some (int 1)
#guard runCoreEvalFailedLabel π 100 (.stmts [assertX "af" 2, setX 3] env0) == some "af"

-- Only the first false assertion halts: the second failing assert is never reached.
#guard runCoreEvalFailedLabel π 100
  (.stmts [assertX "first" 9, assertX "second" 8] env0) == some "first"

/-! ## The four `assertPolicy × assumePolicy` configurations -/

private def assumeX (label : String) (rhs : Int) : Statement :=
  .cmd (.cmd (.assume label (.eq () xVar (int rhs)) md))
private def coverX (label : String) : Statement :=
  .cmd (.cmd (.cover label (.eq () xVar (int 1)) md))

private def opts (ap : AssertPolicy) (sp : AssumePolicy) : EvalOpts :=
  { fuel := 100, assertPolicy := ap, assumePolicy := sp }

/-- Read `x` from the final store of a run at the given policies. -/
private def finalXWith (ap : AssertPolicy) (sp : AssumePolicy)
    (stmts : List Statement) : Option Expression.Expr :=
  match runCoreEvalWith π (opts ap sp) 100 (.stmts stmts env0) with
  | (.ok cfg', _) => cfg'.getEnv.store.get (id "x")
  | (.error (.assertFailed arg), _) => arg.store (id "x")
  | (.error (.stuck _), _) => none
  | (.error (.assumeDidNotReduceToBool _), _) => none
  | (.error .nondetChoiceUnsupported, _) => none

/-- The labels of the failures a run collected, most recent first. -/
private def collectedWith (ap : AssertPolicy) (sp : AssumePolicy)
    (stmts : List Statement) : List String :=
  (runCoreEvalWith π (opts ap sp) 100 (.stmts stmts env0)).2.assertFailures.map (·.1)

/-- The reason a run at the given policies stopped as stuck, or `none` if it did not. -/
private def stuckWith (ap : AssertPolicy) (sp : AssumePolicy)
    (stmts : List Statement) : Option StopReason :=
  match (runCoreEvalWith π (opts ap sp) 100 (.stmts stmts env0)).1 with
  | .error (.stuck reason) => some reason
  | _ => none

-- `.halt`: the failing assert stops the run (`set x := 3` not applied).
#guard finalXWith .halt .ignore [assertX "af" 2, setX 3] == some (int 1)
-- `.collect`: the failing assert is recorded and the run continues.
#guard finalXWith .collect .ignore [assertX "af" 2, setX 3] == some (int 3)
#guard collectedWith .collect .ignore [assertX "af" 2, setX 3] == ["af"]
-- Under `.collect` every independent failure is collected, most-recent-first.
#guard collectedWith .collect .ignore [assertX "a1" 2, setX 2, assertX "a2" 5] == ["a2", "a1"]
-- Under `.halt` nothing is collected: the run stops at the failure.
#guard collectedWith .halt .ignore [assertX "a1" 2, setX 2, assertX "a2" 5] == []

-- `.ignore`: a false assume is skipped, so the run continues.
#guard finalXWith .halt .ignore [assumeX "as" 99, setX 4] == some (int 4)
-- `.enforce`: a false assume stops the run; a true one does not.
#guard finalXWith .halt .enforce [assumeX "as" 99, setX 4] == none
#guard stuckWith .halt .enforce [assumeX "as" 99, setX 4] ==
  some (.assumptionFalseUnderReplay "as")
#guard finalXWith .halt .enforce [assumeX "as" 1, setX 4] == some (int 4)

-- The fourth configuration: collecting failures while enforcing assumes.
#guard finalXWith .collect .enforce [assertX "af" 2, setX 3] == some (int 3)
#guard finalXWith .collect .enforce [assumeX "as" 99, setX 3] == none
#guard stuckWith .collect .enforce [assumeX "as" 99, setX 3] ==
  some (.assumptionFalseUnderReplay "as")

-- `cover` is recorded and the run continues under every configuration.
#guard finalXWith .halt .ignore [coverX "c", setX 5] == some (int 5)
#guard finalXWith .collect .enforce [coverX "c", setX 5] == some (int 5)

/-! A self-recursive procedure nests one call per unit of fuel.  Below the call-depth limit
`defaultMaxCallDepth` (1000) it stops when the fuel runs out; at a fuel of 1,000,000, far above
the limit, it stops when the limit is exceeded, under `EvalM` (`runCoreEval`) and under replay
(`replayWithM`), without exhausting the native stack. -/

/-- `call S()`. -/
private def callS : Statement := .cmd (CmdExt.call "S" [] md)

/-- `procedure S() { call S(); }`. -/
private def sProc : Procedure :=
  { header := { name := id "S", typeArgs := [], inputs := [], outputs := [] }
    spec := { preconditions := [], postconditions := [] }
    body := .structured [callS] }

/-- The callee table resolving `S`. -/
private def πS : String → Option Procedure := fun n => if n == "S" then some sProc else none

#guard (match (runCoreEval πS 100 (.stmts [callS] env0)).1 with
  | .error (.stuck .replayFuelExhausted) => true
  | _ => false)

#guard (match (runCoreEval πS 1000000 (.stmts [callS] env0)).1 with
  | .error (.stuck .callDepthExceeded) => true
  | _ => false)

#guard replayWithM { cfg := .stmts [callS] env0, oracle := [] } { label := "none", md := md }
    1000000 πS == .cantValidate .callDepthExceeded

end InterpreterEvalTest

end -- meta section
