/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import Strata.Languages.Core.ProgramProps
import Strata.Languages.Core
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.Languages.Core.IntEvalProps
import Strata.DL.Imperative.CFGSemanticsProps
import StrataDDM.Integration.Lean.HashCommands

/-! # Shared helpers of the `HoareAfter*` tests

The `HoareAfter<Pass>` tests run a Core pass on a translated program, prove a Hoare triple of
its output and transport it back with the pass's `triple` theorem.  This file holds what they
share:

* `cstToAST`, the gate parameters `testParams`, and the source-location metadata `loc` the
  translation attaches to a statement, with which a test spells out the translated body as a
  closed Core term (so that facts about the pass's output on it are decided by the kernel);
* store facts (`Pinned`, `intOf`, the condition `ge0`) and the contract facts they give
  (`input_int`, `nonneg_of_pre`, `post_ge0`);
* rules for reasoning about triples (`with_wf`, `of_forall_factory`) and the `covered`
  tactic for the `exitsCoveredByBlocks` side condition of the sequencing rule;
* inversions of command steps (`set_inv`, `init_nondet_inv`, `havoc_inv`) and the induction
  of a CFG configuration invariant along a run (`run_preserves_of_step`).
-/

open Imperative
open StrataDDM (Program)

namespace Strata.HoareAfterSupport

/-- Translate a DDM concrete-syntax program to the Core AST. -/
def cstToAST (p : Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- Gate parameters: no reserved fresh-prefixes, and every name counts as declared. -/
def testParams : Core.Logic.InitEnvWFParams := ⟨[], [], fun _ => true⟩

/-- The metadata the translation attaches to a node spanning the bytes `a` to `b` of the test
    file. -/
def loc (a b : Nat) : MetaData Core.Expression :=
  #[⟨.label "provenance", .provenance (.loc (.file "") ⟨⟨a⟩, ⟨b⟩⟩)⟩]

/-- The integer type, as variables are annotated with it. -/
abbrev intMono : Lambda.LMonoTy := .tcons "int" []

/-- The integer type, as a declaration gives it. -/
abbrev intLTy : Lambda.LTy := .forAll [] intMono

/-- An integer-annotated variable. -/
abbrev v (x : Core.Expression.Ident) : Core.Expression.Expr := .fvar () x (some intMono)

/-- `int.ge(x, 0)`. -/
abbrev ge0 (x : Core.Expression.Ident) : Core.Expression.Expr :=
  .app () (.app () Core.intGeOp (v x)) (.intConst () 0)

/-- The runtime factory's functions are those of `Core.Factory`. -/
abbrev Pinned (ρ : Env Core.Expression) : Prop := ρ.factory.factory = Core.Factory

/-- The integer `k` under the runtime factory `f`. -/
abbrev intOf (f : Core.Expression.Factory) (k : Int) : Core.Expression.Val :=
  Lambda.SemValue.ofInt f.model.tcInterp k

/-- The statements before the next ones exit to no label. -/
macro "covered" : tactic =>
  `(tactic| simp [Block.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks])

/-- Every element of a list satisfies a decidable predicate when the list's `all` check of it
    passes. -/
theorem forall_of_all {α : Type} {l : List α} {p : α → Prop} [DecidablePred p]
    (h : l.all (fun x => decide (p x)) = Bool.true) : ∀ x ∈ l, p x :=
  fun x hx => of_decide_eq_true ((List.all_eq_true.1 h) x hx)

section Triples

variable (π : String → Option Core.Procedure)

/-- A triple whose precondition also has the entry store well formed holds without it: every
    entry the triple admits satisfies the gate, which carries that fact. -/
theorem with_wf {params : Core.Logic.InitEnvWFParams} {Pre Post : Env Core.Expression → Prop}
    {ss : Core.Statements}
    (h : Core.Logic.Hoare.Triple π params
      (fun ρ => Pre ρ ∧ WellFormedStore ρ.store ρ.factory) ss Post) :
    Core.Logic.Hoare.Triple π params Pre ss Post :=
  fun ρ₀ ρ' tr hpre hinit hrun => h ρ₀ ρ' tr ⟨hpre, hinit.storeWellDefined⟩ hinit hrun

/-- A triple holding from the entries over each runtime factory holds. -/
theorem of_forall_factory {params : Core.Logic.InitEnvWFParams}
    {Pre Post : Env Core.Expression → Prop} {ss : Core.Statements}
    (h : ∀ E, Core.Logic.Hoare.Triple π params (fun ρ => Pre ρ ∧ ρ.factory = E) ss Post) :
    Core.Logic.Hoare.Triple π params Pre ss Post :=
  fun ρ₀ ρ' tr hpre hinit hrun => h ρ₀.factory ρ₀ ρ' tr ⟨hpre, rfl⟩ hinit hrun

end Triples

/-! ## Contract facts -/

/-- An input of type `int` holds an integer of the runtime factory at an entry with a well-formed
    store satisfying the procedure's input typing. -/
theorem input_int {proc : Core.Procedure} {ρ : Env Core.Expression}
    (hwf : WellFormedStore ρ.store ρ.factory)
    (hin : Core.Logic.Hoare.Procedure.inputAsPredicate proc ρ) (x : Core.Expression.Ident)
    (hx : (x, Lambda.LMonoTy.int) ∈ proc.header.inputs.toList) :
    ∃ k, ρ.store x = some (intOf ρ.factory k) := by
  obtain ⟨w, hw, hty⟩ := hin x _ hx
  obtain ⟨k, hk⟩ := Lambda.SemValue.exists_ofInt hty
  exact ⟨k, by rw [hw, hk, hwf x w hw]⟩

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
  obtain ⟨k, hk⟩ := input_int hwf hin x hx
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

/-! ## Command steps and CFG runs -/

section Steps

variable {π : String → Option Core.Procedure}

/-- Inversion of a deterministic `set x := e` step: the value written is the one `e` evaluates
    to, every other variable keeps its value, and nothing is emitted. -/
theorem set_inv {fac : Core.Expression.Factory}
    {σ σ' : SemanticStore Core.Expression} {x : Core.Expression.Ident}
    {e : Core.Expression.Expr} {md : MetaData Core.Expression} {emitted}
    (h : Core.EvalCommandE π fac σ (.cmd (.set x (.det e) md)) σ' emitted) :
    ∃ w, Core.Expression.eval fac σ e = some w ∧ σ' x = some w ∧
      (∀ y, x ≠ y → σ' y = σ y) ∧ emitted = [] := by
  rcases h with ⟨hbase⟩
  cases hbase with
  | eval_set heval hupdate _ _ =>
    cases hupdate with
    | update _ hres hother => exact ⟨_, heval, hres, hother, rfl⟩

/-- Inversion of a havoc step: every other variable keeps its value, and nothing is
    emitted. -/
theorem havoc_inv {fac : Core.Expression.Factory}
    {σ σ' : SemanticStore Core.Expression} {x : Core.Expression.Ident}
    {md : MetaData Core.Expression} {emitted}
    (h : Core.EvalCommandE π fac σ (.cmd (.set x .nondet md)) σ' emitted) :
    (∀ y, x ≠ y → σ' y = σ y) ∧ emitted = [] := by
  rcases h with ⟨hbase⟩
  cases hbase with
  | eval_set_nondet hupdate _ _ =>
    cases hupdate with
    | update _ _ hother => exact ⟨hother, rfl⟩

/-- Inversion of a nondeterministic `init x` step: every other variable keeps its value, and
    nothing is emitted. -/
theorem init_nondet_inv {fac : Core.Expression.Factory}
    {σ σ' : SemanticStore Core.Expression} {x : Core.Expression.Ident}
    {ty : Lambda.LTy} {md : MetaData Core.Expression} {emitted}
    (h : Core.EvalCommandE π fac σ (.cmd (.init x ty .nondet md)) σ' emitted) :
    (∀ y, x ≠ y → σ' y = σ y) ∧ emitted = [] := by
  rcases h with ⟨hbase⟩
  cases hbase with
  | eval_init_unconstrained hinit _ _ =>
    cases hinit with
    | init _ _ hother => exact ⟨hother, rfl⟩

/-- **A configuration invariant of CFG runs.**  For an invariant of CFG configurations that every
    step from a configuration satisfying it keeps, emitting nothing: every run from a
    configuration satisfying it ends in one satisfying it, with the empty trace. -/
theorem run_preserves_of_step {Inv : CFGConfig String Core.Command Core.Expression → Prop}
    (hstep : ∀ {before after emitted}, Inv before →
      StepCFGE Core.Expression (Core.EvalCommandE π) before emitted after →
      Inv after ∧ emitted = [])
    {start final : CFGConfig String Core.Command Core.Expression}
    {trace : List (Event Core.Expression)} (hinv : Inv start)
    (hrun : ReflTransTrace (StepCFGE Core.Expression (Core.EvalCommandE π)) start trace final) :
    Inv final ∧ trace = [] := by
  induction hrun with
  | refl _ => exact ⟨hinv, rfl⟩
  | step _ _ _ _ _ h _ ih =>
    obtain ⟨hnext, rfl⟩ := hstep hinv h
    obtain ⟨hfinal, rfl⟩ := ih hnext
    exact ⟨hfinal, rfl⟩

end Steps

end Strata.HoareAfterSupport
