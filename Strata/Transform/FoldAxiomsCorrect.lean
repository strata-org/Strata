/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.FoldAxioms
public import Strata.Languages.Core.PipelinePhase
public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Lambda.Denote.Assumptions
import all Strata.Transform.FoldAxioms
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.Transform.Simplify.Expr
import all Strata.Languages.Core.PipelinePhase

/-! # Axiom folding is model-preserving

`foldAxiomsPhase` folds each axiom without bound variables with `Simplify.fold`, keeping
the original when the fold leaves a beta redex. It folds with the folding factory and fuel
of the context `runCtx program F0`, where `F0` is the factory `Simplify.programFactory
program` returns. A run keeps every procedure, and, wherever that fold keeps values
(`AxiomFoldSound`) and on axioms whose operators are consistent with the folding factory
(`GroundAxiomsOps`), each axiom has in every well-formed store a counterpart in the output
with its value, where it has one: every model of the input is a model of the output
(`foldAxiomsPhase_modelPreserving`). In particular, where the input's axioms without bound
variables evaluate to `true`, so do the output's (`groundAxiomsHold_fold`).

Folding keeps values only one way: it can give a value to an expression that has none, as
it folds `1 + 2` to `3` when the operator `+` carries no type annotation, which leaves the
original without a value (`fold_gives_value`). So a model of the output need not be one of
the input. And folding keeps values only on operators annotated at instances of their
signatures (`Lambda.OpsConsistentR`): `Int.Add` annotated at `int → int → bool` denotes a
Boolean, which folding replaces by an integer (`fold_mistyped`).

`AxiomFoldSound` is stated, not proved. Expressions evaluate by their denotation under a
model of the runtime factory, while `Simplify.fold` rewrites with the fuel-based reducer
`LExpr.eval` and the concrete evaluators of the folding factory. Proving it needs the
reducer to be sound for the denotation: each step it takes, and each concrete evaluator of
the folding factory, keeps the denotation under the runtime factory's model, and keeps the
term well typed.

TODO: state the result as `SemanticallyEquivalent` of `Strata/Transform/Specification.lean`
over `EventLang.coreBlock`, once that semantics reads the program's axioms; bodies are
unchanged, so only the axioms the entry store must satisfy differ.

Key theorems: `foldAxiomsPhase_run`, `foldAxiomsPhase_modelPreserving`,
`groundAxiomsHold_fold`, `fold_gives_value`, `fold_mistyped`. -/

namespace Core
namespace FoldAxioms

open Imperative

public section


/-- The simplification context a run of `foldAxiomsPhase` (or of
    `equalitySimplificationPhase`) on `program` builds from the factory `F0` that
    `Simplify.programFactory program` returns; the run folds with its `foldFactory` and
    `evalFuel`. -/
abbrev runCtx (program : Program) (F0 : Lambda.Factory CoreLParams) : Simplify.Ctx :=
  Simplify.Ctx.ofFactory F0 (Simplify.lambdaCarriers program)

/-- **Folding an axiom is sound**: on an expression whose operators are consistent with the
    folding factory `F`, `Simplify.fold` keeps the value the expression has under the runtime
    factory `Fs`, in every well-formed store. It carries the link between the model of `Fs`
    and `F`, as `EqualitySimplification.FoldSound` does.

    TODO: derive it from `eval_denote_sound`, which needs reduction from the empty environment
    to keep the free variables of `e` and their annotations, so that the store still defines
    and annotates the result alike (`Step.freeVars_subset`, `StepStar.getVars_nil`), closed
    function bodies (`Factory.Closed`), concrete evaluators that add no free variable
    (`Factory.EvalFreeVars`), the empty environment's well-formedness (`noValuesStepWF`), and
    the folding factory well formed and interpreted by the model of `Fs` as the program's
    factory is (`IsMapOf.factoryWF`, `IsMapOf.interpConsistent`). -/
@[expose] def AxiomFoldSound (F : Lambda.Factory CoreLParams) (Fs : Expression.Factory)
    (fuel : Nat) : Prop :=
  ∀ σ e v, Lambda.OpsConsistentR F e → WellFormedStore σ Fs →
    Expression.eval Fs σ e = some v → Expression.eval Fs σ (Simplify.fold F fuel e) = some v

/-- `1 + 2` with the operator `+` (`Int.Add`) left without a type annotation: an expression
    with no value under the denotational semantics, which folding reduces to `3`. -/
@[expose] def unannotatedSum : Expression.Expr :=
  .app () (.app () (.op () ⟨"Int.Add", ()⟩ none) (.intConst () 1)) (.intConst () 2)

/-- **Folding can give a value to an expression that has none.** In every runtime factory and
    store, `unannotatedSum` has no value, since an operator without a type annotation has no
    type, while the literal `3` has one; and `Simplify.fold Core.Factory 100` folds the first
    to the second. So folding keeps values only one way, which is why `AxiomFoldSound` and
    the soundness conditions of equality simplification are stated for expressions that have
    a value. -/
theorem fold_gives_value (Fs : Expression.Factory) (σ : SemanticStore Expression) :
    Expression.eval Fs σ unannotatedSum = none ∧
      Expression.eval Fs σ (.intConst () 3) = some (Lambda.SemValue.ofInt Fs.model.tcInterp 3) := by
  refine ⟨?_, Lambda.LExpr.denoteEval_intConst⟩
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro v h
  obtain ⟨-, τ, hτ, -⟩ := (Lambda.LExpr.denoteEval_eq_some_iff (T := CoreLParams)).mp h
  simp only [unannotatedSum, Lambda.LExpr.annotateFvars] at hτ
  cases hτ with
  | app hfn _ =>
    cases hfn with
    | app hop _ => cases hop

/-- `1 + 2` with the operator `+` (`Int.Add`) annotated at `int → int → bool`, a type its
    signature `int → int → int` does not have. Its operator is not consistent with Core's
    factory, and it denotes a Boolean, while `Simplify.fold Core.Factory 100` folds it to the
    integer `3`. -/
@[expose] def mistypedSum : Expression.Expr :=
  let int : Lambda.LMonoTy := .tcons "int" []
  .app () (.app () (.op () ⟨"Int.Add", ()⟩
      (some (.tcons "arrow" [int, .tcons "arrow" [int, .tcons "bool" []]])))
    (.intConst () 1)) (.intConst () 2)

/-- **An operator annotated at a type its signature lacks has a value of that type.** In every
    runtime factory and store, `mistypedSum` has a value other than the integer `3`, to which
    `Simplify.fold Core.Factory 100` folds it. So folding keeps values only on expressions
    whose operators are consistent with the folding factory, which is why `AxiomFoldSound`
    asks for it. -/
theorem fold_mistyped (Fs : Expression.Factory) (σ : SemanticStore Expression) :
    ∃ v, Expression.eval Fs σ mistypedSum = some v ∧
      v ≠ Lambda.SemValue.ofInt Fs.model.tcInterp 3 := by
  refine ⟨_, (Lambda.LExpr.denoteEval_eq_some_iff (T := CoreLParams)).mpr
    ⟨fun x hx => by simp [mistypedSum, Lambda.LExpr.LExpr.getVars] at hx, .bool,
      .app (.app .op .const) .const, rfl, rfl⟩, fun h => ?_⟩
  have := congrArg Lambda.SemValue.sort h
  unfold Lambda.LExpr.denoteEvalResult at this
  simp [Lambda.SemValue.ofInt, Lambda.LMonoTy.substTyVars, Lambda.LMonoTy.substTyVars.map] at this

/-- A folded axiom has the value of the original, where that has one, wherever folding is
    sound. -/
private theorem foldAxiom_eval {F : Lambda.Factory CoreLParams} {Fs : Expression.Factory}
    {fuel : Nat} (hfold : AxiomFoldSound F Fs fuel)
    {σ : SemanticStore Expression} (hσ : WellFormedStore σ Fs) {e : Expression.Expr}
    (ho : Lambda.OpsConsistentR F e) {v : Expression.Val}
    (he : Expression.eval Fs σ e = some v) :
    Expression.eval Fs σ (FoldAxioms.foldAxiom F fuel e) = some v := by
  unfold FoldAxioms.foldAxiom
  dsimp only
  split
  · exact hfold σ e v ho hσ he
  · exact he

/-- A run of `foldAxiomsPhase` on `program` from the state `s` computes the factory `F0` of
    `program`, keeps every procedure, and replaces each axiom without bound variables by its
    fold with the folding factory and fuel of `runCtx program F0`: each axiom of the output
    is an axiom of the input or the fold of one, and each axiom of the input is in the
    output or folded there. -/
theorem foldAxiomsPhase_run {program out : Program} {s s' : Transform.CoreTransformState}
    {b : Bool} (h : (Core.foldAxiomsPhase.transform program).run s = (.ok (b, out), s')) :
    ∃ F0 s1, (Simplify.programFactory program).run s = (.ok F0, s1) ∧
      (∀ q md, Decl.proc q md ∈ program.decls → Decl.proc q md ∈ out.decls) ∧
      (∀ a' md, Decl.ax a' md ∈ out.decls → ∃ a, Decl.ax a md ∈ program.decls ∧
        (a' = a ∨ (a.e.hasBVar = false ∧ a'.e = FoldAxioms.foldAxiom
          (runCtx program F0).foldFactory (runCtx program F0).evalFuel a.e))) ∧
      (∀ a md, Decl.ax a md ∈ program.decls → ∃ a', Decl.ax a' md ∈ out.decls ∧
        (a' = a ∨ (a.e.hasBVar = false ∧ a'.e = FoldAxioms.foldAxiom
          (runCtx program F0).foldFactory (runCtx program F0).evalFuel a.e))) := by
  change (FoldAxioms.runFoldAxioms program).run s = _ at h
  simp only [FoldAxioms.runFoldAxioms, ExceptT.run_bind] at h
  rcases hF : (ExceptT.run (Simplify.programFactory program)) s with ⟨r, s1⟩
  simp only [bind, StateT.bind, hF] at h
  cases r with
  | error => cases h
  | ok F0 =>
    simp only [ExceptT.run, pure, ExceptT.pure] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    refine ⟨F0, _, rfl, fun q md hq => List.mem_map.mpr ⟨_, hq, rfl⟩, fun a' md ha' => ?_,
      fun a md ha => ?_⟩
    · obtain ⟨d, hd, heq⟩ := List.mem_map.mp ha'
      cases d with
      | ax a0 md0 =>
        simp only at heq
        split at heq
        · injection heq with h1 h2; subst h1 h2; exact ⟨a0, hd, .inl rfl⟩
        · rename_i hb; injection heq with h1 h2; subst h1 h2
          exact ⟨a0, hd, .inr ⟨by simpa using hb, rfl⟩⟩
      | _ => cases heq
    · by_cases hb : a.e.hasBVar = true
      · exact ⟨a, List.mem_map.mpr ⟨_, ha, by simp only [hb, ite_true]⟩, .inl rfl⟩
      · exact ⟨_, List.mem_map.mpr ⟨_, ha, by simp only [hb]; rfl⟩,
          .inr ⟨by simpa using hb, rfl⟩⟩


/-- Every axiom without bound variables evaluates to `true` in `σ`. -/
abbrev GroundAxiomsHold (Fs : Expression.Factory) (p : Program) (σ : SemanticStore Expression) :
    Prop :=
  ∀ a md, Decl.ax a md ∈ p.decls → a.e.hasBVar = false →
    Expression.eval Fs σ a.e = some (HasBool.ttVal Fs)

/-- Every axiom of `p` without bound variables has operators consistent with `F`. -/
abbrev GroundAxiomsOps (F : Lambda.Factory CoreLParams) (p : Program) : Prop :=
  ∀ a md, Decl.ax a md ∈ p.decls → a.e.hasBVar = false → Lambda.OpsConsistentR F a.e

/-- **Axiom folding is model-preserving.** Let a run of `foldAxiomsPhase` on `program` from
    the state `s` succeed with `out`. The run computes the factory `F0` of `program`, and
    every procedure of `program` is in `out`. Write `F` for the folding factory of
    `runCtx program F0`, and let the ground axioms of `program` have operators consistent
    with `F`. Then, for every runtime factory `Fs` for which folding with `F` is sound, in
    every well-formed store: each axiom of `out` comes from an axiom of `program` whose
    value it has, where that one has a value, and each axiom of `program` has a counterpart
    in `out` with its value, where it has one. Every model of `program` is one of `out`; the
    converse can fail (`fold_gives_value`). -/
theorem foldAxiomsPhase_modelPreserving {program out : Program}
    {s s' : Transform.CoreTransformState} {b : Bool}
    (h : (Core.foldAxiomsPhase.transform program).run s = (.ok (b, out), s')) :
    ∃ F0 s1, (Simplify.programFactory program).run s = (.ok F0, s1) ∧
      (∀ q md, Decl.proc q md ∈ program.decls → Decl.proc q md ∈ out.decls) ∧
      (GroundAxiomsOps (runCtx program F0).foldFactory program →
      ∀ {Fs : Expression.Factory},
      AxiomFoldSound (runCtx program F0).foldFactory Fs (runCtx program F0).evalFuel →
      ∀ {σ : SemanticStore Expression}, WellFormedStore σ Fs →
        (∀ a' md, Decl.ax a' md ∈ out.decls → ∃ a, Decl.ax a md ∈ program.decls ∧
          ∀ v, Expression.eval Fs σ a.e = some v → Expression.eval Fs σ a'.e = some v) ∧
        (∀ a md, Decl.ax a md ∈ program.decls → ∃ a', Decl.ax a' md ∈ out.decls ∧
          ∀ v, Expression.eval Fs σ a.e = some v → Expression.eval Fs σ a'.e = some v)) := by
  obtain ⟨F0, s1, hF, hp, hout, hin⟩ := foldAxiomsPhase_run h
  refine ⟨F0, s1, hF, hp, fun hops _ hfold _ hσ => ⟨fun a' md ha' => ?_, fun a md ha => ?_⟩⟩
  · obtain ⟨a, ha, hr⟩ := hout a' md ha'
    refine ⟨a, ha, fun v hv => ?_⟩
    rcases hr with heq | ⟨hb, he⟩
    · rw [heq]; exact hv
    · rw [he]; exact foldAxiom_eval hfold hσ (hops a md ha hb) hv
  · obtain ⟨a', ha', hr⟩ := hin a md ha
    refine ⟨a', ha', fun v hv => ?_⟩
    rcases hr with heq | ⟨hb, he⟩
    · rw [heq]; exact hv
    · rw [he]; exact foldAxiom_eval hfold hσ (hops a md ha hb) hv

/-- Folding keeps the ground axioms true: where the ground axioms of the input hold, and
    their operators are consistent with the folding factory, the ground axioms of the output
    hold. -/
theorem groundAxiomsHold_fold {program out : Program} {F : Lambda.Factory CoreLParams}
    {Fs : Expression.Factory} {fuel : Nat} (hfold : AxiomFoldSound F Fs fuel)
    {σ : SemanticStore Expression}
    (hσ : WellFormedStore σ Fs)
    (hout : ∀ a' md, Decl.ax a' md ∈ out.decls → ∃ a, Decl.ax a md ∈ program.decls ∧
        (a' = a ∨ (a.e.hasBVar = false ∧ a'.e = FoldAxioms.foldAxiom F fuel a.e)))
    (hops : GroundAxiomsOps F program) (hax : GroundAxiomsHold Fs program σ) :
    GroundAxiomsHold Fs out σ := by
  intro a' md ha' hb
  obtain ⟨a, ha, hr⟩ := hout a' md ha'
  rcases hr with heq | ⟨hb0, he⟩
  · subst heq; exact hax a' md ha hb
  · rw [he]; exact foldAxiom_eval hfold hσ (hops a md ha hb0) (hax a md ha hb0)

end -- public section

end FoldAxioms
end Core
