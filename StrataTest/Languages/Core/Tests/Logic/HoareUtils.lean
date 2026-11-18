/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core
public import Strata.Languages.Core.StatementSemantics
public import Strata.Languages.Core.Logic.TraceInterpUsingDenote
public import Strata.Languages.Core.Logic.ContractToHoareTripleProps
public import Strata.Languages.Core.Logic.InterpreterHoareRelation
public import Strata.Languages.Core.ProgramProps
public import Strata.Languages.Core.InstWellFormedSemanticsEval
public import Strata.Languages.Core.IntEvalProps
public import Strata.DL.Imperative.CFGSemanticsProps
public import Strata.DL.Imperative.StmtSemanticsProps
public import Strata.DL.Imperative.StmtCFGCallSemanticsProps
public import Strata.DL.Lambda.FactoryProps
public import Strata.Util.ListUtilsProps
public import Strata.Util.RelationsProps
public import StrataDDM.Integration.Lean.HashCommands

/-! # Shared fixtures of the Core Hoare-logic tests

The tests under `Tests/Logic/` write Core programs in DDM syntax, translate them, and prove facts
about them in `Core.Logic.Hoare`. This file holds the fixtures they share; lemmas that are not
about these fixtures belong in the library's `*Props` files.

* Programs: `cstToAST` translates a program, normalizing its expression locations
  (`eraseProgLocs`), `typeCheckedAST` also type-checks it, and
  `procOf`/`bodyOf` read a procedure and its body; `fuel` is the concrete evaluator's fuel for
  the bodies `Core.runLits` runs.
* Running bodies: `contract_by_run` proves a contract by running the body, and
  `BodyTerminates`/`bodyTerminates_of_progresses` state and prove that a body terminates.
* Gates and models: the gate parameters `testParams`, the runtime factory of a model
  (`boolFactory`) and a world over any factory (`someValuation`).
* Spelled-out terms: the source-location metadata `loc` the translation attaches to a node, with
  which a test spells out a translated body as a closed Core term (so that facts about a pass's
  output on it are decided by the kernel), and `intMono`, `intLTy`, `v`.
* Store and contract facts: `Pinned`, `intOf`, the condition `ge0`, its value (`ge0_eval`) and
  the contract facts it gives (`nonneg_of_pre`, `post_ge0`).
* Empty bodies: `blockWF_nil`, `run_procBlock_nil` and `reachable_nil` run an empty body, and
  `oldInoutAsPredicate_of_no_inout`, `preAsPredicate_of_no_pre` discharge the parts of a
  contract precondition a procedure has no clause for.
* The `covered` tactic for the `exitsCoveredByBlocks` side condition of the sequencing rule.
-/

public section

open Imperative
open StrataDDM (Program)

namespace Strata.HoareUtils

/-! ## Programs -/

/-- Expression source locations are normalized to `Core.valueLoc` so the tests' exact
    structural comparisons hold; execution ignores locations, so this changes nothing the
    evaluator observes. -/
@[expose] def eraseProgLocs (pr : Core.Program) : Core.Program :=
  { pr with decls := pr.decls.map fun d => match d with
      | .proc proc md => .proc (Core.Procedure.mapExprs Core.eraseLocs proc) md
      | .ax a md => .ax { a with e := Core.eraseLocs a.e } md
      | .distinct name es md => .distinct name (es.map Core.eraseLocs) md
      | other => other }

/-- Translate a DDM concrete-syntax program to the Core AST, with expression source
    locations normalized to `Core.valueLoc`. -/
@[expose] def cstToAST (p : Program) : Core.Program :=
  eraseProgLocs (TransM.run Inhabited.default (translateProgram p)).fst

/-- The type-checked Core program of `p`, whose operators carry their instantiated types. -/
@[expose] def typeCheckedAST (p : Program) : Core.Program :=
  match Core.typeCheck { Core.VerifyOptions.default with verbose := .quiet } (cstToAST p) with
  | .ok p => p
  | .error _ => default

/-- The procedure of `p` named `n`. -/
@[expose] def procOf (p : Core.Program) (n : String) : Core.Procedure :=
  (p.findProcByString? n).get!

/-- The body of the procedure of `p` named `n`. -/
@[expose] def bodyOf (p : Core.Program) (n : String) : Core.Statements :=
  match (procOf p n).body with
  | .structured ss => ss
  | .cfg _ => []

/-- Fuel for the concrete evaluator, ample for the tests' bodies. -/
@[expose] def fuel : Nat := 200

/-! ## Gates and models -/

/-- Gate parameters: no reserved fresh-prefixes, and every name counts as declared. -/
@[expose] def testParams : Core.Logic.InitEnvWFParams := ⟨[], [], [], fun _ => true⟩

/-- The runtime factory of the model `model`, reading every residual type variable at
`bool`. -/
abbrev boolFactory {F : Lambda.Factory Core.CoreLParams} (model : Lambda.Interp F) :
    Core.Expression.Factory :=
  { factory := F, model := model, tyVarVal := fun _ => .bool }

/-- A world over any Core expression factory: off-factory conditions never hold. -/
@[expose] def someValuation (factory : Lambda.Factory Core.CoreLParams) :
    Core.Logic.DenoteValuation factory where
  offFactoryHolds := fun _ => False

/-! ## Running straight-line bodies

The `HoareUsing*` tests prove a body's contract and its termination by running it with
`Core.runLits`; `contract_by_run` and `bodyTerminates_of_progresses` package those proofs. -/

/-- The body of procedure `n` of `p` terminates from every environment over `Core.Factory`
    whose store binds every output to a value of its type and leaves undeclared the names the
    body declares. -/
abbrev BodyTerminates (p : Core.Program) (n : String) : Prop :=
  ∀ (π : String → Option Core.Procedure) (ρ : Env Core.Expression),
    ρ.factory.factory = Core.Factory →
    Core.LitDecls.Holds ρ.factory ρ.store (procOf p n).header.outputs →
    (∀ x ∈ Block.definedVars (bodyOf p n) true, ρ.store x = none) →
    (Core.Logic.EventLang.coreBlock π).Terminates (bodyOf p n) ρ

/-- A body that `Core.runLits` runs with every write at the type of its target terminates. -/
theorem bodyTerminates_of_progresses {p : Core.Program} {n : String}
    (h : Core.runLitsProgresses fuel [] (procOf p n).header.outputs (bodyOf p n) = true) :
    BodyTerminates p n :=
  fun π _ hF hout hlocals => Core.runLits_terminates π h hF hout hlocals

/-- `contract_by_run p n` proves `Procedure.contractTriple p testParams n` by running the body
    of procedure `n` with `Core.runLits`, deciding each premise of
    `Procedure.contractTriple_of_meetsContractOnLits` by `native_decide`. -/
macro "contract_by_run " p:term:max n:term:max : term =>
  `(Core.Logic.Hoare.Procedure.contractTriple_of_meetsContractOnLits $p
      Strata.HoareUtils.testParams $n (Strata.HoareUtils.procOf $p $n)
      (Strata.HoareUtils.bodyOf $p $n) Strata.HoareUtils.fuel
      (by native_decide) (by native_decide) (by native_decide)
      (Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide))
      (by native_decide))

/-! ## Spelled-out terms -/

/-- The metadata the translation attaches to a node spanning the bytes `a` to `b` of the test
    file. -/
@[expose] def loc (a b : Nat) : MetaData Core.Expression :=
  #[⟨.label "provenance", .provenance (.loc (.file "") ⟨⟨a⟩, ⟨b⟩⟩)⟩]

/-- The integer type, as variables are annotated with it. -/
abbrev intMono : Lambda.LMonoTy := .tcons "int" []

/-- The integer type, as a declaration gives it. -/
abbrev intLTy : Lambda.LTy := .forAll [] intMono

/-- An integer-annotated variable. -/
abbrev v (x : Core.Expression.Ident) : Core.Expression.Expr :=
  .fvar Core.valueLoc x (some intMono)

/-! ## Store and contract facts -/

/-- `int.ge(x, 0)`. -/
abbrev ge0 (x : Core.Expression.Ident) : Core.Expression.Expr :=
  .app Core.valueLoc (.app Core.valueLoc Core.intGeOp (v x)) (.intConst Core.valueLoc 0)

/-- The runtime factory's functions are those of `Core.Factory`. -/
abbrev Pinned (ρ : Env Core.Expression) : Prop := ρ.factory.factory = Core.Factory

/-- The integer `k` under the runtime factory `f`. -/
abbrev intOf (f : Core.Expression.Factory) (k : Int) : Core.Expression.Val :=
  Lambda.SemValue.ofInt f.model.tcInterp k

/-- With `x ↦ k` under a factory over `Core.Factory`, `int.ge(x, 0)` evaluates to `k ≥ 0`. -/
theorem ge0_eval {f : Core.Expression.Factory} (hf : f.factory = Core.Factory)
    {σ : Core.CoreStore} {x : Core.Expression.Ident} {k : Int}
    (hx : σ x = some (intOf f k)) :
    Core.Expression.eval f σ (ge0 x) =
      some (Lambda.SemValue.ofBool f.model.tcInterp (decide (k ≥ 0))) :=
  Core.eval_intGe (hf ▸ Core.coreFactory_intGe) (Core.eval_fvar_int f hx)
    (Core.eval_intConst f σ 0)

/-- **A non-negative integer input from the contract.**  For a procedure whose preconditions,
    of which there is one at least, are all `int.ge(x, 0)` for an input `x` of type `int`: an
    entry satisfying the contract's precondition, with a well-formed store, has `x` hold a
    non-negative integer of its runtime factory. -/
theorem nonneg_of_pre {proc : Core.Procedure} {ρ : Env Core.Expression}
    {x : Core.Expression.Ident}
    (h : Core.Logic.Hoare.Procedure.contractPre Core.Factory proc ρ)
    (hwf : WellFormedStore ρ.store ρ.factory)
    (hx : (x, Lambda.LMonoTy.int) ∈ proc.header.inputs.toList)
    (hpre : ∀ lc ∈ proc.spec.preconditions.toList, lc.2.expr = ge0 x)
    (hne : proc.spec.preconditions.toList ≠ []) :
    ∃ k, ρ.store x = some (intOf ρ.factory k) ∧ 0 ≤ k := by
  obtain ⟨hreq, hp, _, hin⟩ := h
  obtain ⟨k, hk⟩ := Core.Logic.Hoare.Procedure.inputAsPredicate_int hwf hin x hx
  obtain ⟨⟨l, c⟩, hmem⟩ := List.exists_mem_of_ne_nil _ hne
  rcases hreq l c hmem ⟨fun _ => False⟩ with ⟨_, he⟩ | ⟨hnf, _⟩
  · change Core.Expression.eval ρ.factory ρ.store c.expr = some (HasBool.ttVal ρ.factory) at he
    rw [hpre _ hmem, ge0_eval hp hk] at he
    exact ⟨k, hk, of_decide_eq_true (Lambda.SemValue.ofBool_injective (Option.some.inj he))⟩
  · exact absurd hp hnf

/-- **The contract's postcondition `int.ge(x, 0)`.**  For a procedure whose postconditions are
    all `int.ge(x, 0)`: an environment over `Core.Factory` where `x` holds a non-negative integer
    of its runtime factory satisfies the contract's postcondition. -/
theorem post_ge0 {proc : Core.Procedure} {ρ : Env Core.Expression} {x : Core.Expression.Ident}
    {k : Int} (hpost : ∀ lc ∈ proc.spec.postconditions.toList, lc.2.expr = ge0 x)
    (hp : Pinned ρ) (hx : ρ.store x = some (intOf ρ.factory k)) (hk : 0 ≤ k) :
    Core.Logic.Hoare.Procedure.contractPost Core.Factory proc ρ := by
  intro label check hmem _ _
  refine .inl ⟨hp, ?_⟩
  change Core.Expression.eval ρ.factory ρ.store check.expr = some (HasBool.ttVal ρ.factory)
  rw [hpost _ hmem, ge0_eval hp hx, decide_eq_true hk]
  rfl

/-! ## Empty bodies and contracts without clauses

What the tests that refute a contract need of an empty body: it runs, from any
well-formed environment over `Core.Factory`, back to that environment with no event. -/

/-- The block condition is immediate for an empty body: every clause that mentions
    the statements is vacuous, a runtime factory over `Core.Factory` is well-formed, and
    the store holds only values. -/
theorem blockWF_nil (ρ : Imperative.Env Core.Expression)
    (hfac : ρ.factory.factory = Core.Factory)
    (hsv : Imperative.WellFormedStore ρ.store ρ.factory) :
    Core.Logic.BlockInitEnvWF testParams [Imperative.Stmt.block "" [] #[]] ρ :=
  Core.Logic.blockInitEnvWF_procBlock_nil (Core.coreFactory_WellFormedSemanticEval _ hfac)
    hsv rfl (fun _ _ => rfl)

/-- An empty body, wrapped as the procedure block a body actually runs in, returns to
    its own environment: entering and leaving the block projects the store through
    itself.  Stated over the *event* step relation, the run emits no events. -/
theorem run_procBlock_nil (π : String → Option Core.Procedure)
    (ρ : Imperative.Env Core.Expression) (l : String)
    (md : Imperative.MetaData Core.Expression) :
    Imperative.StepStmtStarE Core.Expression (Core.EvalCommandE π)
      (.stmts [Imperative.Stmt.block l [] md] ρ) [] (.terminal ρ) := by
  have heq : ({ ρ with store := Imperative.projectStore ρ.store ρ.store }
      : Imperative.Env Core.Expression) = ρ := by
    simp [Imperative.projectStore_self]
  refine .step _ [] _ [] _ .step_stmts_cons ?_
  refine .step _ [] _ [] _ (.step_seq_inner .step_block) ?_
  refine .step _ [] _ [] _ (.step_seq_inner (.step_block_body .step_stmts_nil)) ?_
  refine .step _ [] _ [] _ (.step_seq_inner .step_block_done) ?_
  refine .step _ [] _ [] _ .step_seq_done ?_
  rw [heq]
  exact .step _ [] _ [] _ .step_stmts_nil (.refl _)

/-- The empty trace is reachable. -/
theorem reachable_nil (F : Lambda.Factory Core.CoreLParams) :
    Trace.Reachable Core.Expression (Core.Logic.DenoteBasedInterp F) [] :=
  ⟨someValuation F, fun _ hc => absurd hc (by simp)⟩

/-- A procedure with no inout parameters satisfies `oldInoutAsPredicate` vacuously: its
    `getInoutParams` keys are empty, so there is no `old`/current pair to relate. -/
theorem oldInoutAsPredicate_of_no_inout (proc : Core.Procedure)
    (ρ : Imperative.Env Core.Expression)
    (h : ListMap.keys proc.header.getInoutParams = []) :
    Core.Logic.Hoare.Procedure.oldInoutAsPredicate proc ρ := by
  intro id hid; rw [h] at hid; simp at hid

/-- A procedure with no `requires` satisfies the semantic precondition vacuously. -/
theorem preAsPredicate_of_no_pre (factory : Lambda.Factory Core.CoreLParams)
    (proc : Core.Procedure) (ρ : Imperative.Env Core.Expression)
    (h : proc.spec.preconditions.toList = []) :
    Core.Logic.Hoare.Procedure.preAsPredicate factory proc ρ := by
  intro label check hmem; rw [h] at hmem; simp at hmem

/-! ## Tactics -/

/-- The statements before the next ones exit to no label. -/
macro "covered" : tactic =>
  `(tactic| simp [Block.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks])

end Strata.HoareUtils

end -- public section
