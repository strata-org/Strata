/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core.InterpreterReachCheck
import Strata.Languages.Core.Logic.FactoryInterp
import Strata.Languages.Core.InterpreterReplay
import Strata.DL.Imperative.InterpreterConfig
import Strata.DL.Imperative.StmtCFGCallSemantics
import Strata.DL.Imperative.StmtSemantics
import Strata.DL.Imperative.CmdSemantics
import Strata.Util.ListMap
import Strata.DL.Imperative.Stmt

/-! # The static criterion of computable evaluation on examples

* The fragment check (`Core.inFragment`) over `Core.Factory` accepts integer arithmetic and
  comparisons on variables, conditionals, equalities and the Boolean connectives, and rejects a
  division (its concrete evaluator is undefined on a zero divisor), a quantifier, a map read and
  an operator annotated with a type that is not an instance of its signature.
* `wGenuine_of_fragment`: the program `call w()`, whose callee body is `assert fail : false`,
  passes the static criterion (`Core.programInFragment`), so the replay completeness corollary for
  deterministic programs of the fragment
  (`Core.core_replayComplete_of_deterministic_programInFragment`) gives `genuine` from a bare
  reference run, every hypothesis beyond the criterion being discharged. -/

namespace ReachFragmentTest

open Core Imperative Lambda

/-- The integer type. -/
private def intTy : LMonoTy := .int
/-- The Boolean type. -/
private def boolTy : LMonoTy := .bool

/-- The variable `x : int`. -/
private def xE : Expression.Expr := .fvar () ⟨"x", ()⟩ (some intTy)
/-- The variable `y : int`. -/
private def yE : Expression.Expr := .fvar () ⟨"y", ()⟩ (some intTy)
/-- An integer literal. -/
private def lit (i : Int) : Expression.Expr := .intConst () i

/-- A binary operator applied to two arguments, annotated with the type `a → a → b`. -/
private def bin (name : String) (a b : LMonoTy) (x y : Expression.Expr) : Expression.Expr :=
  .app () (.app () (.op () ⟨name, ()⟩ (some (.arrow a (.arrow a b)))) x) y

/-- `x + 1 < y`. -/
private def e1 : Expression.Expr :=
  bin "Int.Lt" intTy boolTy (bin "Int.Add" intTy intTy xE (lit 1)) yE

/-- `if x < y then x - y else y * 2`. -/
private def e2 : Expression.Expr :=
  .ite () (bin "Int.Lt" intTy boolTy xE yE) (bin "Int.Sub" intTy intTy xE yE)
    (bin "Int.Mul" intTy intTy yE (lit 2))

/-- `(x == y) && (x <= y)`. -/
private def e3 : Expression.Expr :=
  bin "Bool.And" boolTy boolTy (.eq () xE yE) (bin "Int.Le" intTy boolTy xE yE)

/-- `x div 0`. -/
private def e4 : Expression.Expr := bin "Int.Div" intTy intTy xE (lit 0)

/-- `∀ z : int. z == z`. -/
private def e5 : Expression.Expr :=
  .quant () .all "z" (some intTy) (.bvar () 0) (.eq () (.bvar () 0) (.bvar () 0))

/-- `x + 1` with the operator annotated `bool → bool → bool`, not an instance of `Int.Add`'s
    signature. -/
private def e6 : Expression.Expr := bin "Int.Add" boolTy boolTy xE (lit 1)

#guard inFragment Core.Factory e1
#guard inFragment Core.Factory e2
#guard inFragment Core.Factory e3
#guard !inFragment Core.Factory e4
#guard !inFragment Core.Factory e5
#guard !inFragment Core.Factory e6

/-- Core's factory, modeled by its interpretation `Core.factoryInterp`. -/
private noncomputable def M0 : Expression.Factory :=
  ⟨Core.Factory, Core.factoryInterp, fun _ => .bool⟩

/-- Empty metadata. -/
private def md : MetaData Expression := #[]
/-- The literal `false`. -/
private def ffE : Expression.Expr := .boolConst () false

/-- The callee: no formals, no spec clauses, body `assert fail : false`. -/
def wProc : Procedure :=
  { header := { name := ⟨"w", ()⟩, typeArgs := [], inputs := [], outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [.cmd (.cmd (.assert "fail" ffE md))] }

/-- The procedure table: `"w"` resolves to `wProc`. -/
def wPi : String → Option Procedure := fun n => if n = "w" then some wProc else none

/-- The caller environment: the empty store over Core's factory. -/
def wEnv : Imperative.IEnv Expression := .ofStore (fun _ => none) Core.Factory

/-- The counterexample: the call, with an empty oracle. -/
def wCex : CexA Expression Command :=
  { cfg := .stmts [.cmd (.call "w" [] md)] wEnv, oracle := [] }

/-- The target: the callee's assert. -/
def wTarget : AssertId Expression := { label := "fail", md := md }

/-- A bare reference run of `wCex.cfg`, stopped right after the call, emits the callee's failing
    assertion. -/
private theorem wRefRun :
    ∃ evs final, CoreStepStarE wPi (wCex.cfg.abs M0) evs final ∧
      ∃ ev ∈ evs, RefFailure wTarget ev :=
  ⟨_, _, .step _ _ _ _ _ .step_stmts_cons
    (.step _ _ _ _ _ (.step_seq_inner (.step_cmd (.call_sem (n := "w") (p := wProc)
      (σAO := Calls.withOldSnapshots (Calls.inoutParams wProc.header) emptyStore) rfl
      ⟨[], [], .eval_none, .read_none, ⟨_, _, .init_none, .init_none, rfl⟩⟩
      (.structured (.step _ _ _ _ _ .step_block
        (.step _ _ _ _ _ (.step_block_body .step_stmts_cons)
        (.step _ _ _ _ _ (.step_block_body (.step_seq_inner (.step_cmd (.cmd_sem .eval_assert))))
        (.step _ _ _ _ _ (.step_block_body .step_seq_done)
        (.step _ _ _ _ _ (.step_block_body .step_stmts_nil)
        (.step _ _ _ _ _ .step_block_done (.refl _))))))))
      ⟨List.nodup_nil, [], .read_none, .update_none, .nil⟩)))
    (.refl _)),
    .assert ⟨M0, Calls.withOldSnapshots (Calls.inoutParams wProc.header) emptyStore, "fail", ffE,
      md⟩, by simp [Calls.defaultAssertEvents, wProc, Calls.checksAtCall, IEnv.abs],
    rfl, rfl, LExpr.denoteEval_boolConst⟩

/-- **Replay completeness for `wCex` from the static criterion**: replaying `wCex` with its own
    (empty) oracle reaches the callee's failing assert at every sufficiently large fuel and
    call-depth limit; the criterion is checked by `decide`. -/
theorem wGenuine_of_fragment :
    ∃ f0, ∀ fuel d, f0 ≤ fuel → f0 ≤ d → genuine wPi wTarget fuel wCex d := by
  obtain ⟨_, _, hrun, hfail⟩ := wRefRun
  refine core_replayComplete_of_deterministic_programInFragment wPi [wProc]
    (fun n p h => ?_) (fragmentFactoryWF_coreFactory M0 rfl) wTarget wCex
    (show IConfig.Denoting M0 (.stmts _ wEnv) from ⟨by simp [wEnv, IEnv.ofStore,
      RStore.Denoting, IStore.get, IStore.ofStore, InterpLang.writesFind?_empty], rfl⟩)
    trivial ((programInFragment_iff _ _ _).2 ⟨?_, ?_⟩) ⟨rfl, fun x v h => ?_⟩ ?_ hrun hfail
  · unfold wPi at h
    split at h <;> simp_all
  · simp [wCex, IConfig.abs, ConfigInFragment, BlockInFragment, StmtInFragment, CmdInFragment,
      Calls.getInputExprs]
  · simp only [List.mem_singleton, forall_eq]
    refine ⟨⟨_, rfl, ?_⟩, by simp [wProc, ListMap.toList], by simp [wProc, ListMap.toList]⟩
    exact ⟨.const () _, trivial⟩
  · simp [wEnv, IEnv.abs, InterpLang.absStore, IEnv.ofStore, IStore.get,
      IStore.ofStore, InterpLang.writesFind?_empty] at h
  · refine ⟨?_, fun n p ss hp hss => ?_⟩
    · refine ⟨?_, ?_⟩ <;> simp only [wCex, IConfig.abs, Config.noNondetGuards, Config.allCmds]
      · unfold Block.noNondetGuards Stmt.noNondetGuards Block.noNondetGuards
        rfl
      · unfold Block.allCmds Stmt.allCmds Block.allCmds
        rfl
    · unfold wPi at hp
      split at hp
      · cases hp
        cases hss
        refine ⟨?_, ?_⟩
        · unfold Block.noNondetGuards Stmt.noNondetGuards Block.noNondetGuards
          rfl
        · unfold Block.allCmds Stmt.allCmds Block.allCmds
          rfl
      · cases hp

end ReachFragmentTest
