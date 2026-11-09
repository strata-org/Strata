/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.EqualitySimplification
public import Strata.Transform.FoldAxiomsCorrect
public import Strata.DL.Imperative.BigStep.GoalRewriteProps
public import Strata.DL.Imperative.BigStep.Adequacy
public import Strata.Languages.Core.InstWellFormedSemanticsEval
public import Strata.DL.Lambda.LExprDenoteEvalProps
public import Strata.DL.Lambda.Denote.Assumptions
import all Strata.Transform.EqualitySimplification
import all Strata.Transform.Simplify.Expr
import all Strata.DL.Imperative.Cmd
import all Strata.Languages.Core.PipelinePhase

/-! # Axiom folding and equality simplification keep failures

The phase's walk over a body (`stepStmts`) is a goal-rewriting pass
(`Imperative.BigStep.GoalRewrite.Pass`, `stepStmts_eq`): it rewrites only the goals of
`assert`s and `cover`s, under facts carried along the body. Give the facts their meaning:
`Facts.Holds Fs σ fs` says the store `σ` is well formed and every equation the facts
record (a variable's value, a definition, a closed term's value) evaluates to `true` in
`σ` under the factory `Fs`.

The walk is a sound pass (`pass_sound`) on the commands whose operators are consistent
with the folding factory `F` (`CmdOps`), once two expression-level steps are sound for `Fs`:
rewriting a goal keeps the value it has wherever the facts hold (`RewriteSound`), and the
facts `addAssumption` learns from an assumption that evaluates to `true` hold
(`AssumeSound`); `assumeFact` also marks contradictory facts, which only stops rewriting.
The facts the walk carries hold, and record values whose operators are consistent with `F`
(`FactsInv`). The rest is proved here: definitions record a true equation (the evaluator
is monotone and reads variables from the store), writes and the end of a block or `if` keep
the facts that do not mention what they write (`Facts.holds_forget`, `brunS_frame`), and the
axioms give facts that hold where the ground axioms evaluate to `true`. Consequently, under
the reference event semantics, a body without loops keeps its failures
(`FailuresKept`, `stepStmts_failsE`): each assertion or cover (a label and metadata) it
fails, its rewrite fails, and, where its goals have values (`GoalsDefined`), conversely.
So does each body
the phase rewrites, from the facts of the axioms declared before its procedure
(`rewriteBody`, `equalitySimplificationPhase_failsE`). The phase folds with the folding
factory and fuel of `FoldAxioms.runCtx program F0`, where `F0` is the factory the run
computes for the program; the theorems name it, so the soundness hypotheses are about a
factory the caller can identify.

`RewriteSound` reduces further, to the soundness of folding with `foldTerm` (`FoldSound`)
and of one substitution pass `substAux` with its definition cache (`SubstSound`): the
rounds, the stop at a Boolean literal and the fallback on a beta redex keep it
(`rewriteSound_of`).

The phase `foldAxiomsPhase`, which runs just before, folds each axiom without bound
variables with `Simplify.fold`. It keeps every procedure, and each folded axiom has the
value of the original, where that has one, wherever that fold is sound (`AxiomFoldSound`):
every model of its input is one of its output (`FoldAxioms.foldAxiomsPhase_modelPreserving`, in
`FoldAxiomsCorrect`). The two phases in order keep the failures of each body, from every
store that agrees, outside the procedure's parameters, with one where the input's ground
axioms evaluate to `true` (`foldAxioms_equalitySimplification_failsE`).

The folding and rewriting conditions keep values one way only: wherever an expression has a
value, its fold or rewrite has the same one. Folding can give a value to an expression that
has none (`FoldAxioms.fold_gives_value`: `1 + 2`, with `+` left without a type annotation,
has none, and folds to `3`), so a goal without a value can become a failing one. That is why
a failure of the output is one of the source only where the source's goals have values
(`GoalsDefined`).

Folding reads an operator by its name, while the denotation reads it at the type its
annotation gives, so the conditions also ask the operators of the expression to be annotated
at instances of their signatures in `F` (`Lambda.OpsConsistentR`): `Int.Add` annotated at
`int → int → bool` denotes a Boolean, and folds to an integer
(`FoldAxioms.fold_mistyped`). The theorems take that as a premise on the body's commands and
the ground axioms, which type checking supplies for the program's factory, whose signatures
`F` has.

`AxiomFoldSound`, `FoldSound`, `SubstSound` and `AssumeSound` are stated, not proved.
Expressions evaluate by their denotation under a model of the runtime factory `Fs`, which
obeys congruence, substitution and monotonicity laws, but the phase rewrites with the
fuel-based reducer `LExpr.eval`, the concrete evaluators of the folding factory `F`, and
the node rules of `foldTerm`. Proving `FoldSound` needs each of them to be sound for the
denotation: each step, evaluator and rule keeps the denotation under the model of `Fs`, and
keeps the term well typed, since an ill-typed term has no value. `SubstSound` and `AssumeSound`
rest on it too, as `substAux` and `addAssumption` fold the definitions they read through.

TODO: state the top-level result as `OverapproximatesTracesUptoWhen` (and its converse)
of `Strata/Transform/Specification.lean` over `EventLang.coreBlock`, with the event relation
`GoalRewrite.EvRel`, as `DeadDefElimCoreCorrect` does, so that it composes with the other
passes.

Key theorems: `stepStmts_eq`, `pass_sound`, `stepStmts_failsE`,
`equalitySimplificationPhase_failsE`, `rewriteSound_of`,
`foldAxioms_equalitySimplification_failsE`. -/

namespace Core
namespace EqualitySimplification

open Imperative Imperative.BigStep Imperative.BigStep.GoalRewrite

public section

/-- The phase's walk over a body, as a goal-rewriting pass (`GoalRewrite.Pass`). -/
@[expose] def pass (F : @Lambda.Factory CoreLParams) (fuel : Nat) : Pass Expression Facts where
  cmd fs c := stepCmd F fs fuel c
  forget fs ss := forgetWritten fs ss
  reset := {}

mutual

/-- `stepStmt` is the pass `pass` on a statement. -/
private theorem stepStmt_eq (F : @Lambda.Factory CoreLParams) (fuel : Nat) :
    ∀ (fs : Facts) (s : Statement), stepStmt F fs fuel s = (pass F fuel).stmt fs s
  | fs, .cmd (.cmd c) => by
    rw [stepStmt]; rfl
  | fs, .cmd (.call ..) => by
    rw [stepStmt]; rfl
  | fs, .block l ss md => by
    rw [stepStmt, stepStmts_eq F fuel fs ss]; rfl
  | fs, .ite c ts es md => by
    rw [stepStmt, stepStmts_eq F fuel fs ts, stepStmts_eq F fuel fs es]; rfl
  | fs, .loop g m invs body md => by
    rw [stepStmt, stepStmts_eq F fuel _ body]; rfl
  | fs, .exit .. => by
    rw [stepStmt]; rfl
  | fs, .typeDecl .. => by
    rw [stepStmt]; rfl

/-- `stepStmts` is the pass `pass` on a statement list. -/
theorem stepStmts_eq (F : @Lambda.Factory CoreLParams) (fuel : Nat) :
    ∀ (fs : Facts) (ss : Statements), stepStmts F fs fuel ss = (pass F fuel).stmts fs ss
  | fs, [] => by
    rw [stepStmts]; rfl
  | fs, s :: rest => by
    rw [stepStmts, stepStmt_eq F fuel fs s]
    rcases h : (pass F fuel).stmt fs s with ⟨s', fs'⟩
    simp only
    rw [stepStmts_eq F fuel fs' rest]
    simp only [Pass.stmts, h]

end


/-! ## What the facts mean -/

/-- The equation `lhs == rhs` evaluates to `true` in `σ`. -/
abbrev EqHolds (F : Expression.Factory) (σ : SemanticStore Expression)
    (lhs rhs : Expression.Expr) : Prop :=
  Expression.eval F σ (.eq () lhs rhs) = some (HasBool.ttVal F)

/-- **The facts hold in a store**: `σ` is well formed, and every equation the facts record
    (a variable's value, a definition, a closed term's value) evaluates to `true` in it. -/
@[expose] def Facts.Holds (F : Expression.Factory) (σ : SemanticStore Expression) (fs : Facts) :
    Prop :=
  WellFormedStore σ F ∧
  (∀ x v, fs.vars.get? x = some (some v) → ∀ ty, EqHolds F σ (.fvar () x ty) v) ∧
  (∀ x v, fs.defs.get? x = some v → ∀ ty, EqHolds F σ (.fvar () x ty) v) ∧
  (∀ h b, fs.terms.get? h = some b → ∀ t v, (t, some v) ∈ b → EqHolds F σ t v)

/-- An equation keeps holding in a store that agrees on its free variables. -/
private theorem eqHolds_congr {F : Expression.Factory}
    {σ σ' : SemanticStore Expression} (hσ : WellFormedStore σ F) (hσ' : WellFormedStore σ' F)
    {lhs rhs : Expression.Expr}
    (hag : ∀ x ∈ HasFvars.getFvars (P := Expression) lhs ++ HasFvars.getFvars (P := Expression) rhs,
      σ x = σ' x)
    (h : EqHolds F σ lhs rhs) : EqHolds F σ' lhs rhs := by
  unfold EqHolds at h ⊢
  rw [← coreEvaluator_WellFormedSemanticEvalExprCongr F _ σ σ' hσ hσ' hag]
  exact h

/-- Whether a list of names mentions none of `xs`. -/
private theorem not_mentions {xs ys : List CoreIdent}
    (h : (ys.any fun y => (Std.HashSet.ofList xs).contains y) = false) : ∀ y ∈ ys, y ∉ xs := by
  intro y hy hx
  have := List.any_eq_false.mp h y hy
  simp_all [Std.HashSet.contains_ofList]

/-- An entry `x ↦ v` that `forget xs` keeps holds in a store agreeing outside `xs`. -/
private theorem eqHolds_keep {F : Expression.Factory}
    {σ σ' : SemanticStore Expression} (hσ : WellFormedStore σ F) (hσ' : WellFormedStore σ' F)
    {xs : List CoreIdent} (hag : ∀ x, x ∉ xs → σ x = σ' x) {x : CoreIdent} {v : Expression.Expr}
    {ty : Option Lambda.LMonoTy}
    (hk : (!(Std.HashSet.ofList xs).contains x && !(Option.map (fun e =>
      (HasFvars.getFvars (P := Expression) e).any fun x => (Std.HashSet.ofList xs).contains x)
      (some v)).getD false) = true)
    (h : EqHolds F σ (.fvar () x ty) v) : EqHolds F σ' (.fvar () x ty) v := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', Option.map_some, Option.getD_some] at hk
  obtain ⟨hx, hm⟩ := hk
  refine eqHolds_congr hσ hσ' (fun y hy => hag y ?_) h
  simp only [List.mem_append] at hy
  rcases hy with hy | hy
  · simp only [HasFvars.getFvars, Lambda.LExpr.LExpr.getVars, List.mem_singleton] at hy
    subst hy
    simpa [Std.HashSet.contains_ofList] using hx
  · exact not_mentions hm y hy

/-- **Forgetting keeps the facts that hold.** If the facts hold in `σ`, those `forget xs`
    keeps hold in every well-formed store agreeing with `σ` outside `xs`. -/
private theorem Facts.holds_forget {F : Expression.Factory}
    {σ σ' : SemanticStore Expression} {fs : Facts} (h : fs.Holds F σ) (xs : List CoreIdent)
    (hσ' : WellFormedStore σ' F) (hag : ∀ x, x ∉ xs → σ x = σ' x) :
    (fs.forget xs).Holds F σ' := by
  obtain ⟨hσ, hv, hd, ht⟩ := h
  unfold Facts.forget
  split
  · rename_i hx
    have hxs : xs = [] := List.isEmpty_iff.mp hx
    subst hxs
    have hag' : ∀ x, σ x = σ' x := fun x => hag x (by simp)
    refine ⟨hσ', fun x v h ty => ?_, fun x v h ty => ?_, fun k b h t v hm => ?_⟩
    · exact eqHolds_congr hσ hσ' (fun y _ => hag' y) (hv x v h ty)
    · exact eqHolds_congr hσ hσ' (fun y _ => hag' y) (hd x v h ty)
    · exact eqHolds_congr hσ hσ' (fun y _ => hag' y) (ht k b h t v hm)
  · refine ⟨hσ', fun x v h ty => ?_, fun x v h ty => ?_, fun k b h t v hm => ?_⟩
    · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filter,
        Std.HashMap.getKey_eq, Option.pfilter_eq_some_iff] at h
      obtain ⟨ha, hk⟩ := h
      exact eqHolds_keep hσ hσ' hag hk (hv x v (by simpa using ha) ty)
    · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filter,
        Std.HashMap.getKey_eq, Option.pfilter_eq_some_iff] at h
      obtain ⟨ha, hk⟩ := h
      exact eqHolds_keep hσ hσ' hag hk (hd x v (by simpa using ha) ty)
    · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filterMap] at h
      obtain ⟨b0, hb0, hb⟩ := Option.pbind_eq_some_iff.mp h
      split at hb
      · cases hb
      cases hb
      obtain ⟨hm0, hk⟩ := List.mem_filter.mp hm
      simp only [Bool.and_eq_true, Bool.not_eq_true', Option.map_some, Option.getD_some] at hk
      refine eqHolds_congr hσ hσ' (fun y hy => hag y ?_)
        (ht k b0 (by simpa using hb0) t v hm0)
      rcases List.mem_append.mp hy with hy | hy
      · exact not_mentions hk.1 y hy
      · exact not_mentions hk.2 y hy

/-! ## Operators consistent with the folding factory

Folding reads an operator by its name, while the denotation reads it at the type its
annotation gives. An operator annotated at a type its signature does not have, such as
`Int.Add` at `int → int → bool`, denotes a value of that type, which folding replaces by a
value of another (`FoldAxioms.fold_mistyped`). So folding keeps values only on expressions
whose operators are annotated at instances of their signatures in the folding factory
(`Lambda.OpsConsistentR`), and the phase is sound on the commands whose expressions are. -/

/-- The command `c` reads expressions whose operators are consistent with `F`: the goal of
    an `assert` or `cover`, the condition of an `assume`, the value of a definition. The
    condition of an `assume` is moreover typed at `bool` by its own annotations, so the
    witness candidates it gives are typed (`AssumeSound`). Type checking is expected to supply
    both: it annotates each operator at an instance of its signature and each variable at its
    declared type (`typeCheck_bodyFvarsAnnotated` in the denotational-evaluation work). -/
@[expose] def CmdOps (F : Lambda.Factory CoreLParams) : Cmd Expression → Prop
  | .assert _ e _ | .cover _ e _ | .init _ _ (.det e) _ => Lambda.OpsConsistentR F e
  | .assume _ e _ => Lambda.OpsConsistentR F e ∧ Lambda.LExpr.HasTypeA [] e .bool
  | _ => True

/-- Every value the facts record has operators consistent with `F`, and every witness
    candidate they record for a function `f : ty → bool` has type `ty`. A candidate of another
    type can make the body of an existential over `ty` fold to `true` though no value of `ty`
    satisfies it: `∃ x : bool. ¬(x == true) ∧ ¬(x == false)` folds to `true` given the
    candidate `3`, since `3 == true` and `3 == false` fold to `false`. -/
@[expose] def Facts.Ops (F : Lambda.Factory CoreLParams) (fs : Facts) : Prop :=
  (∀ x v, fs.vars.get? x = some (some v) → Lambda.OpsConsistentR F v) ∧
  (∀ x v, fs.defs.get? x = some v → Lambda.OpsConsistentR F v) ∧
  (∀ h b, fs.terms.get? h = some b → ∀ t v, (t, some v) ∈ b → Lambda.OpsConsistentR F v) ∧
  (∀ f ty vs, fs.hints.get? (f, .arrow ty .bool) = some vs → ∀ v ∈ vs,
    Lambda.LExpr.HasTypeA [] v ty)

/-- The empty facts record nothing. -/
private theorem Facts.ops_empty (F : Lambda.Factory CoreLParams) : ({} : Facts).Ops F :=
  ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h, fun _ _ h => by simp at h,
    fun _ _ _ h => by simp at h⟩

/-- Forgetting keeps the facts' operators consistent: it only drops entries. -/
private theorem Facts.ops_forget {F : Lambda.Factory CoreLParams} {fs : Facts}
    (h : fs.Ops F) (xs : List CoreIdent) : (fs.forget xs).Ops F := by
  obtain ⟨hv, hd, ht, hh⟩ := h
  unfold Facts.forget
  split
  · exact ⟨hv, hd, ht, hh⟩
  · refine ⟨fun x v h => ?_, fun x v h => ?_, fun k b h t v hm => ?_, fun f ty vs h v hm => ?_⟩
    · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filter,
        Option.pfilter_eq_some_iff] at h
      exact hv x v (by simpa using h.1)
    · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filter,
        Option.pfilter_eq_some_iff] at h
      exact hd x v (by simpa using h.1)
    · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filterMap] at h
      obtain ⟨b0, hb0, hb⟩ := Option.pbind_eq_some_iff.mp h
      split at hb
      · cases hb
      cases hb
      exact ht k b0 (by simpa using hb0) t v (List.mem_filter.mp hm).1
    · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filterMap] at h
      obtain ⟨b0, hb0, hb⟩ := Option.pbind_eq_some_iff.mp h
      split at hb
      · cases hb
      cases hb
      exact hh f ty b0 (by simpa using hb0) v (List.mem_filter.mp hm).1


/-! ## What a statement writes -/

/-- The store an outcome ends with. -/
@[expose] def outStore : Outcome Expression → SemanticStore Expression
  | .normal σ | .exit _ σ => σ

/-- A store written at `x` with a value stays well formed. -/
private theorem wf_write {F : Expression.Factory} {σ σ' : SemanticStore Expression}
    {x : CoreIdent} {v : Expression.Val} (hσ : WellFormedStore σ F) (hv : HasVal.value F v)
    (hx : σ' x = some v) (hy : ∀ y, x ≠ y → σ' y = σ y) : WellFormedStore σ' F := by
  intro y w hw
  by_cases h : x = y
  · subst h; rw [hx] at hw; cases hw; exact hv
  · rw [hy y h] at hw; exact hσ y w hw

/-- A command keeps the store well formed and writes only the variables it defines or
    modifies. -/
private theorem cmd_frame {F : Expression.Factory} {σ σ' : SemanticStore Expression}
    {c : Cmd Expression} {evs : List (Event Expression)} (h : EvalCmdE Expression F σ c σ' evs)
    (hσ : WellFormedStore σ F) :
    WellFormedStore σ' F ∧ ∀ x, x ∉ Cmd.modifiedVars c ++ Cmd.definedVars c → σ' x = σ x := by
  cases h with
  | eval_init _ hi hty _ =>
    cases hi with
    | init _ hx hy =>
      refine ⟨wf_write hσ (LawfulHasVal.valueOfTy_isVal _ _ _ hty) hx hy, fun y hy' => ?_⟩
      exact hy y (fun h => hy' (by simp only [Cmd.modifiedVars, Cmd.definedVars, h, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false, or_true]))
  | eval_init_unconstrained hi hty _ =>
    cases hi with
    | init _ hx hy =>
      refine ⟨wf_write hσ (LawfulHasVal.valueOfTy_isVal _ _ _ hty) hx hy, fun y hy' => ?_⟩
      exact hy y (fun h => hy' (by simp only [Cmd.modifiedVars, Cmd.definedVars, h, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false, or_true]))
  | eval_set _ hu hty _ =>
    obtain ⟨_, _, _, _, hty⟩ := hty
    cases hu with
    | update _ hx hy =>
      refine ⟨wf_write hσ (LawfulHasVal.valueOfTy_isVal _ _ _ hty) hx hy, fun y hy' => ?_⟩
      exact hy y (fun h => hy' (by simp only [Cmd.modifiedVars, Cmd.definedVars, h, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false]))
  | eval_set_nondet hu hty _ =>
    obtain ⟨_, _, _, _, hty⟩ := hty
    cases hu with
    | update _ hx hy =>
      refine ⟨wf_write hσ (LawfulHasVal.valueOfTy_isVal _ _ _ hty) hx hy, fun y hy' => ?_⟩
      exact hy y (fun h => hy' (by simp only [Cmd.modifiedVars, Cmd.definedVars, h, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false]))
  | eval_assert | eval_assume | eval_cover => exact ⟨hσ, fun _ _ => rfl⟩

/-- Leaving a scope keeps a well-formed store well formed and, outside what the scope
    writes, the parent's values. -/
private theorem proj_frame {F : Expression.Factory} {σ σ' : SemanticStore Expression}
    {W : List CoreIdent} (hσ' : WellFormedStore σ' F) (hw : ∀ x, x ∉ W → σ' x = σ x) :
    WellFormedStore (projectStore σ σ') F ∧ ∀ x, x ∉ W → projectStore σ σ' x = σ x := by
  refine ⟨fun x v h => ?_, fun x hx => ?_⟩
  · unfold projectStore at h
    split at h
    · exact hσ' x v h
    · cases h
  · unfold projectStore
    split
    · exact hw x hx
    · rename_i h; simp only [Option.isSome_iff_ne_none, ne_eq, Decidable.not_not] at h
      exact h.symm

/-- The store an outcome leaves a scope with is its store projected on the parent's. -/
private theorem outStore_leave (σ : SemanticStore Expression) (o : Outcome Expression)
    (lb : Option String) :
    outStore (match lb with | none => o.proj σ | some l => o.block l σ) =
      projectStore σ (outStore o) := by
  cases lb with
  | none => cases o <;> rfl
  | some l =>
    cases o with
    | normal => rfl
    | exit l' _ => by_cases h : l' = l <;> simp [Outcome.block, h, outStore]

/-- Leaving a scope whose body writes within `W` writes within any `W'` containing `W`. -/
private theorem leave_frame {F : Expression.Factory} {σ : SemanticStore Expression}
    {o : Outcome Expression} {W W' : List CoreIdent} (lb : Option String)
    (h : WellFormedStore (outStore o) F ∧ ∀ x, x ∉ W → outStore o x = σ x)
    (hW : ∀ x, x ∈ W → x ∈ W') :
    WellFormedStore (outStore (match lb with | none => o.proj σ | some l => o.block l σ)) F ∧
      ∀ x, x ∉ W' → outStore (match lb with | none => o.proj σ | some l => o.block l σ) x =
        σ x := by
  rw [outStore_leave]
  exact proj_frame h.1 (fun x hx => h.2 x (fun hm => hx (hW x hm)))

mutual

/-- **A run writes only what the list defines or modifies**, and keeps the store well
    formed. -/
private theorem brun_frame {F : Expression.Factory} : ∀ {ss : Statements} {σ : SemanticStore Expression}
    {evs : List (Event Expression)} {o : Outcome Expression}, BRun F ss σ evs o →
    WellFormedStore σ F →
    WellFormedStore (outStore o) F ∧
      ∀ x, x ∉ Block.modifiedOrDefinedVars ss false → outStore o x = σ x
  | _, _, _, _, .nil, hσ => ⟨hσ, fun _ _ => rfl⟩
  | _, _, _, _, .cons_normal h1 h2, hσ => by
    obtain ⟨w1, f1⟩ := brunS_frame h1 hσ
    obtain ⟨w2, f2⟩ := brun_frame h2 w1
    refine ⟨w2, fun x hx => ?_⟩
    simp only [Block.modifiedOrDefinedVars, Block.modifiedVars, Block.definedVars,
      Stmt.modifiedOrDefinedVars, List.mem_append, not_or] at hx f1 f2
    rw [f2 x ⟨hx.1.2, hx.2.2⟩]
    exact f1 x ⟨hx.1.1, hx.2.1⟩
  | _, _, _, _, .cons_exit h1, hσ => by
    obtain ⟨w1, f1⟩ := brunS_frame h1 hσ
    refine ⟨w1, fun x hx => ?_⟩
    simp only [Block.modifiedOrDefinedVars, Block.modifiedVars, Block.definedVars,
      Stmt.modifiedOrDefinedVars, List.mem_append, not_or] at hx f1
    exact f1 x ⟨hx.1.1, hx.2.1⟩

/-- **A run writes only what the statement defines or modifies**, and keeps the store well
    formed. -/
private theorem brunS_frame {F : Expression.Factory} : ∀ {s : Statement} {σ : SemanticStore Expression}
    {evs : List (Event Expression)} {o : Outcome Expression}, BRunS F s σ evs o →
    WellFormedStore σ F →
    WellFormedStore (outStore o) F ∧
      ∀ x, x ∉ Stmt.modifiedOrDefinedVars s false → outStore o x = σ x
  | _, _, _, _, .cmd (c := .cmd _) h, hσ => by
    obtain ⟨w, f⟩ := cmd_frame h hσ
    refine ⟨w, fun x hx => f x ?_⟩
    simpa [Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.definedVars, HasVarsImp.modifiedVars,
      HasVarsImp.definedVars, CmdExt.modifiedVars, CmdExt.definedVars] using hx
  | _, _, _, _, .cmd (c := .call _ _ _) h, _ => h.elim
  | _, _, _, _, .ite_true _ h, hσ => by
    refine leave_frame none (brun_frame h hσ) (fun x hx => ?_)
    simp only [Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.definedVars,
      Block.modifiedOrDefinedVars, List.mem_append, Bool.false_eq_true, ite_false] at hx ⊢
    rcases hx with hx | hx <;> simp [hx]
  | _, _, _, _, .ite_false _ h, hσ => by
    refine leave_frame none (brun_frame h hσ) (fun x hx => ?_)
    simp only [Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.definedVars,
      Block.modifiedOrDefinedVars, List.mem_append, Bool.false_eq_true, ite_false] at hx ⊢
    rcases hx with hx | hx <;> simp [hx]
  | _, _, _, _, .ite_nondet_true h, hσ => by
    refine leave_frame none (brun_frame h hσ) (fun x hx => ?_)
    simp only [Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.definedVars,
      Block.modifiedOrDefinedVars, List.mem_append, Bool.false_eq_true, ite_false] at hx ⊢
    rcases hx with hx | hx <;> simp [hx]
  | _, _, _, _, .ite_nondet_false h, hσ => by
    refine leave_frame none (brun_frame h hσ) (fun x hx => ?_)
    simp only [Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.definedVars,
      Block.modifiedOrDefinedVars, List.mem_append, Bool.false_eq_true, ite_false] at hx ⊢
    rcases hx with hx | hx <;> simp [hx]
  | _, _, _, _, .block (l := l) h, hσ => by
    refine leave_frame (some l) (brun_frame h hσ) (fun x hx => ?_)
    simp only [Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.definedVars,
      Block.modifiedOrDefinedVars, List.mem_append, Bool.false_eq_true, ite_false] at hx ⊢
    rcases hx with hx | hx <;> simp [hx]
  | _, _, _, _, .exit, hσ => ⟨hσ, fun _ _ => rfl⟩
  | _, _, _, _, .typeDecl, hσ => ⟨hσ, fun _ _ => rfl⟩

end


/-! ## The phase's walk is sound -/

/-- **Goal rewriting is sound**: wherever the facts hold, for a goal whose operators, and
    whose facts' values, are consistent with the folding factory `F`, `rewriteGoal` keeps the
    value the goal has. This is the expression-level obligation the trace argument rests on
    (see the module documentation). It follows from `FoldSound` and `SubstSound`
    (`rewriteSound_of`). -/
@[expose] def RewriteSound (F : Lambda.Factory CoreLParams) (Fs : Expression.Factory)
    (fuel : Nat) : Prop :=
  ∀ fs σ e v, fs.Ops F → Lambda.OpsConsistentR F e → fs.Holds Fs σ →
    Expression.eval Fs σ e = some v → Expression.eval Fs σ (rewriteGoal F fs fuel e) = some v

/-- **Learning an assumption is sound**: from an assumption whose operators are consistent
    with `F` and that evaluates to `true`, `addAssumption` adds facts that hold where the
    facts before it hold, and whose values keep operators consistent with `F`. Among those, it
    claims that each witness candidate `v` recorded from `f(v)`, for `f : ty → bool`, has type
    `ty` (`Facts.Ops`), which the assumption being typed at `bool` by its own annotations
    gives. Without that premise it fails in the intended model: `Bool.Not(x) == true`, with `x`
    annotated `int` and bound to the Boolean `false`, evaluates to `true`, since evaluation
    reads a variable's sort from the store, and records the candidate `x`, which is not typed
    at `bool`.

    A static premise is enough because the two conclusions rest on different typings. That a
    candidate is typed is syntactic, and follows from `e` being typed by its own annotations,
    by inversion at the application that records it. That the facts hold is semantic, and
    follows from `e` evaluating to `true`, which types its store-annotated form. The two
    typings differ only at a variable whose sort in the store also types `e`, as in `x == x`,
    and then both conclusions still hold, one from each typing.

    TODO: prove it; no lemma about `addAssumption` exists yet. -/
@[expose] def AssumeSound (F : Lambda.Factory CoreLParams) (Fs : Expression.Factory) : Prop :=
  ∀ fs σ e, fs.Ops F → Lambda.OpsConsistentR F e → Lambda.LExpr.HasTypeA [] e .bool →
    fs.Holds Fs σ →
    Expression.eval Fs σ e = some (HasBool.ttVal Fs) →
    (addAssumption F fs defDepth e).Holds Fs σ ∧ (addAssumption F fs defDepth e).Ops F

/-- **Folding is sound**: on an expression whose operators, and whose facts' values, are
    consistent with the folding factory `F`, `foldTerm` (evaluation with `LExpr.eval` under
    the empty environment, then the node rules: the Boolean connectives, and an existential
    proved by a witness the facts suggest) keeps them consistent, and keeps the value the
    expression has under `Fs`, wherever the facts hold.

    It assumes two things. That folding keeps the operators consistent is the first conjunct,
    a syntactic fact. That it keeps values carries the link between the model of `Fs` and
    `F`: the model interprets each operator as `F`'s concrete evaluators compute it, at every
    instance of its signature (as `InterpConsistent` states), and interprets each operator a
    node rule decides as the rule decides it. The last part concerns operators with no
    concrete evaluator, which `InterpConsistent` does not constrain: `foldTerm` decides
    `str.in_re` on literals by regular-expression matching, so the model must interpret
    `regex` and `Str.InRegEx` that way. Core's standard interpretation (`factoryInterp`)
    does not, since it interprets `regex` as `Unit`: there `str.in_re("a", re.allchar)` and
    `str.in_re("a", re.none)` denote the same Boolean, while they fold to `true` and
    `false`.

    TODO: derive it from `eval_denote_sound`, which needs reduction from the empty environment
    to keep the free variables of `e` and their annotations, so that the store still defines
    and annotates the result alike (`Step.freeVars_subset`, `StepStar.getVars_nil`), closed
    function bodies (`Factory.Closed`), concrete evaluators that add no free variable
    (`Factory.EvalFreeVars`), the empty environment's well-formedness (`noValuesStepWF`), and
    the folding factory well formed and interpreted by the model of `Fs` as the program's
    factory is (`IsMapOf.factoryWF`, `IsMapOf.interpConsistent`). -/
@[expose] def FoldSound (F : Lambda.Factory CoreLParams) (Fs : Expression.Factory)
    (fuel : Nat) : Prop :=
  ∀ fs e, fs.Ops F → Lambda.OpsConsistentR F e →
    Lambda.OpsConsistentR F (foldTerm F fs fuel e) ∧
    ∀ σ v, fs.Holds Fs σ → Expression.eval Fs σ e = some v →
      Expression.eval Fs σ (foldTerm F fs fuel e) = some v

/-- Every definition the cache has read through to a replacement gives its variable's
    value. -/
@[expose] def CacheOk (Fs : Expression.Factory) (σ : SemanticStore Expression)
    (c : DefCache) : Prop :=
  ∀ x d v, c.get? (x, d) = some (some v) → ∀ ty, EqHolds Fs σ (.fvar () x ty) v

/-- Every replacement the cache records has operators consistent with `F`. -/
@[expose] def CacheOps (F : Lambda.Factory CoreLParams) (c : DefCache) : Prop :=
  ∀ x d v, c.get? (x, d) = some (some v) → Lambda.OpsConsistentR F v

/-- **One substitution pass is sound**: wherever the facts hold and the cache is right, on an
    expression whose operators, and whose facts' and cache's values, are consistent with
    `F`, `substAux` keeps the value the expression has, keeps the operators consistent, and
    leaves the cache right.

    TODO: prove it; no lemma about `substAux` exists yet, and it rests on `FoldSound` for
    the definitions it folds. -/
@[expose] def SubstSound (F : Lambda.Factory CoreLParams) (Fs : Expression.Factory)
    (fuel : Nat) : Prop :=
  ∀ fs σ e (c : DefCache), fs.Ops F → CacheOps F c → Lambda.OpsConsistentR F e →
    fs.Holds Fs σ → CacheOk Fs σ c →
    Lambda.OpsConsistentR F ((substAux F fs fuel defDepth e).run c).1.1 ∧
    CacheOps F ((substAux F fs fuel defDepth e).run c).2 ∧
    CacheOk Fs σ ((substAux F fs fuel defDepth e).run c).2 ∧
    ∀ v, Expression.eval Fs σ e = some v →
      Expression.eval Fs σ ((substAux F fs fuel defDepth e).run c).1.1 = some v

/-- The empty definition cache satisfies `CacheOk`: it records no replacement, so none can
    disagree with a variable's value. -/
private theorem cacheOk_empty {Fs : Expression.Factory} {σ : SemanticStore Expression} :
    CacheOk Fs σ {} := fun _ _ _ h => by simp at h

/-- The empty definition cache satisfies `CacheOps`: it records no replacement. -/
private theorem cacheOps_empty {F : Lambda.Factory CoreLParams} : CacheOps F {} :=
  fun _ _ _ h => by simp at h

/-- The rounds of `simplifyGoal` keep the value of the goal and leave the cache right. -/
private theorem simplifyGoal_sound {F : Lambda.Factory CoreLParams} {Fs : Expression.Factory}
    {fuel : Nat}
    (hfold : FoldSound F Fs fuel) (hsub : SubstSound F Fs fuel) {fs : Facts}
    {σ : SemanticStore Expression} (hops : fs.Ops F) (h : fs.Holds Fs σ) :
    ∀ (rounds : Nat) (goal : Expression.Expr) (c : DefCache) (v : Expression.Val),
      CacheOps F c → CacheOk Fs σ c → Lambda.OpsConsistentR F goal →
      Expression.eval Fs σ goal = some v →
      Expression.eval Fs σ ((simplifyGoal F fs fuel rounds goal).run c).1 = some v
  | 0, goal, c, _, _, _, _, hg => by
    simp only [simplifyGoal]
    exact hg
  | rounds + 1, goal, c, v, hco, hc, hgo, hg => by
    simp only [simplifyGoal, StateT.run_bind]
    obtain ⟨ho', hco', hc', hv⟩ := hsub fs σ goal c hops hco hgo h hc
    rcases hs : (substAux F fs fuel defDepth goal).run c with ⟨⟨g', ch, hh⟩, c'⟩
    rw [hs] at ho' hco' hc' hv
    simp only at ho' hco' hc' hv
    simp only [bind]
    obtain ⟨hfo, hfv⟩ := hfold fs g' hops ho'
    have hf : Expression.eval Fs σ (foldTerm F fs fuel g') = some v := hfv σ v h (hv v hg)
    split
    · exact hg
    · split
      · exact hf
      · exact simplifyGoal_sound hfold hsub hops h rounds _ c' v hco' hc' hfo hf

/-- **Goal rewriting is sound** given that folding and one substitution pass are: the
    rounds, the early stop at a Boolean literal and the fallback on a beta redex keep it. -/
theorem rewriteSound_of {F : Lambda.Factory CoreLParams} {Fs : Expression.Factory}
    {fuel : Nat}
    (hfold : FoldSound F Fs fuel) (hsub : SubstSound F Fs fuel) : RewriteSound F Fs fuel := by
  intro fs σ e v hops heo h he
  unfold rewriteGoal
  split
  · exact he
  · dsimp only
    obtain ⟨hfo, hfv⟩ := hfold fs e hops heo
    have hsg := simplifyGoal_sound hfold hsub hops h 4 _ {} v cacheOps_empty cacheOk_empty hfo
      (hfv σ v h he)
    split <;> split <;> first | exact hfv σ v h he | exact hsg | exact he

/-- After `forget [x]`, the facts record no definition of `x`. -/
private theorem forget_defs_self (fs : Facts) (x : CoreIdent) :
    (fs.forget [x]).defs[x]? = none := by
  simp [Facts.forget, Std.HashMap.getElem?_filter]

/-- A definition `x := e` run from `σ` to `σ'` makes the equation `x == e` hold in `σ'`. -/
private theorem eqHolds_init {Fs : Expression.Factory} {σ σ' : SemanticStore Expression}
    {x : CoreIdent} {e : Expression.Expr} {v : Expression.Val}
    (he : Expression.eval Fs σ e = some v)
    (hx0 : σ x = none) (hx : σ' x = some v) (hy : ∀ y, x ≠ y → σ' y = σ y)
    (hσ' : WellFormedStore σ' Fs) (ty : Option Lambda.LMonoTy) :
    EqHolds Fs σ' (.fvar () x ty) e := by
  have hext : ∀ y w, σ y = some w → σ' y = some w := by
    intro y w hw
    by_cases h : x = y
    · subst h; rw [hx0] at hw; cases hw
    · rw [hy y h]; exact hw
  have he' : Expression.eval Fs σ' e = some v := coreEvaluator_WellFormedSemanticEvalMono Fs e v σ σ' hext he
  have hfx : Expression.eval Fs σ' (.fvar () x ty) = some v := by
    rw [coreEvaluator_WellFormedSemanticEvalVar Fs _ x σ' hσ' rfl]; exact hx
  exact Lambda.LExpr.denoteEval_eq_true hfx he'

/-- The facts after a definition `x := e` hold after it. -/
private theorem holds_init {F : Lambda.Factory CoreLParams} {Fs : Expression.Factory}
    {fuel : Nat} {fs : Facts} {σ σ' : SemanticStore Expression} {x : CoreIdent} {ty : Expression.Ty}
    {e : Expression.Expr} {md : MetaData Expression} {evs : List (Event Expression)}
    (h : fs.Holds Fs σ) (hc : EvalCmdE Expression Fs σ (.init x ty (.det e) md) σ' evs) :
    ((pass F fuel).cmd fs (.init x ty (.det e) md)).2.Holds Fs σ' := by
  obtain ⟨hσ', hfr⟩ := cmd_frame hc h.1
  cases hc with
  | eval_init he hi _ _ =>
    match hi with
    | .init hx0 hx hy =>
      have hf := Facts.holds_forget h [x] hσ' (fun y hy' => (hfr y (by
        simpa [Cmd.modifiedVars, Cmd.definedVars] using hy')).symm)
      simp only [pass, stepCmd]
      split
      · exact hf
      · obtain ⟨_, hv, hd, ht⟩ := hf
        refine ⟨hσ', hv, fun y w hw ty' => ?_, ht⟩
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hw
        split at hw
        · rename_i hxy
          have hxy : x = y := by simpa using hxy
          subst hxy
          cases hw
          exact eqHolds_init he hx0 hx hy hσ' ty'
        · exact hd y w (by simpa [Std.HashMap.get?_eq_getElem?] using hw) ty'

/-- The facts after a definition `x := e` keep their values' operators consistent with `F`
    when `e`'s are. -/
private theorem ops_init {F : Lambda.Factory CoreLParams} {fuel : Nat} {fs : Facts}
    {x : CoreIdent} {ty : Expression.Ty} {e : Expression.Expr} {md : MetaData Expression}
    (h : fs.Ops F) (he : Lambda.OpsConsistentR F e) :
    ((pass F fuel).cmd fs (.init x ty (.det e) md)).2.Ops F := by
  have hf := Facts.ops_forget h [x]
  simp only [pass, stepCmd]
  split
  · exact hf
  · obtain ⟨hv, hd, ht, hh⟩ := hf
    refine ⟨hv, fun y w hw => ?_, ht, hh⟩
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hw
    split at hw
    · cases hw; exact he
    · exact hd y w (by simpa [Std.HashMap.get?_eq_getElem?] using hw)

/-- The facts the walk carries: they hold in the store, and their values have operators
    consistent with the folding factory `F`. -/
@[expose] def FactsInv (F : Lambda.Factory CoreLParams) (Fs : Expression.Factory)
    (fs : Facts) (σ : SemanticStore Expression) : Prop :=
  fs.Holds Fs σ ∧ fs.Ops F

/-- **The phase's walk is a sound goal-rewriting pass**, for the factory `Fs` the semantics
    evaluates with and the commands whose operators are consistent with the folding factory
    `F`, given that its two expression-level steps are sound for them. -/
theorem pass_sound {F : Lambda.Factory CoreLParams} {Fs : Expression.Factory} {fuel : Nat}
    (hrw : RewriteSound F Fs fuel) (has : AssumeSound F Fs) :
    Sound Fs (pass F fuel) (FactsInv F Fs) (CmdOps F) where
  cmd_rel fs c hok := by
    cases c with
    | assert l e md => exact .assert (fun σ h v he => hrw fs σ e v h.2 hok h.1 he)
    | cover l e md => exact .cover (fun σ h v he => hrw fs σ e v h.2 hok h.1 he)
    | init x ty e md =>
      cases e
      · simp only [pass, stepCmd]; split <;> exact .same
      · exact .same
    | set _ _ _ => exact .same
    | assume _ _ _ => exact .same
  cmd_post fs c σ σ' evs hok h hc hA := by
    have hc0 := hc
    have hσ := h.1.1
    obtain ⟨hσ', hfr⟩ := cmd_frame hc hσ
    cases hc with
    | eval_assert | eval_cover => exact h
    | eval_assume =>
      exact has fs σ _ h.2 hok.1 hok.2 h.1 (hA _ (List.mem_singleton_self _))
    | eval_init _ _ _ _ => exact ⟨holds_init h.1 hc0, ops_init h.2 hok⟩
    | eval_init_unconstrained =>
      exact ⟨Facts.holds_forget h.1 _ hσ' (fun y hy' => (hfr y (by
        simpa [Cmd.modifiedVars, Cmd.definedVars] using hy')).symm), Facts.ops_forget h.2 _⟩
    | eval_set | eval_set_nondet =>
      exact ⟨Facts.holds_forget h.1 _ hσ' (fun y hy' => (hfr y (by
        simpa [Cmd.modifiedVars, Cmd.definedVars] using hy')).symm), Facts.ops_forget h.2 _⟩
  forget_post fs s σ evs σ' h hr := by
    obtain ⟨hσ', hfr⟩ := brunS_frame hr h.1.1
    exact ⟨Facts.holds_forget h.1 _ hσ' (fun y hy' => (hfr y (by
      simpa [forgetWritten] using hy')).symm), Facts.ops_forget h.2 _⟩


/-! ## Failures are kept -/

variable {F : Lambda.Factory CoreLParams} {Fs : Expression.Factory} {fuel : Nat}

/-- **The walk keeps failures.** If the facts `fs` hold at `σ` with values whose operators
    are consistent with `F`, so are those of every command of `ss`, and `ss` fails `t` from `σ`
    under the factory `Fs`, the walk's output fails `t` from `σ`, with the rewritten
    condition. -/
private theorem stepStmts_fails (hrw : RewriteSound F Fs fuel)
    (has : AssumeSound F Fs) {fs : Facts} {σ : SemanticStore Expression}
    (hγ : FactsInv F Fs fs σ) {ss : Statements} (hok : CmdsOk (CmdOps F) ss)
    {t : AssertId Expression} {e : Expression.Expr}
    (h : Fails Fs ss σ t e) : ∃ e', Fails Fs (stepStmts F fs fuel ss).1 σ t e' := by
  rw [stepStmts_eq]
  exact Pass.fails_of_fails (pass_sound hrw has) hγ hok h

/-- **The walk adds no failures where the goals have values.** If the facts `fs` hold at
    `σ` with values whose operators are consistent with `F`, so are those of every command of
    `ss`, the goals of `ss` have values from `σ`, and the walk's output fails `t` from `σ`
    under the factory `Fs`, `ss` fails `t` from `σ`, with the original condition. -/
private theorem stepStmts_fails_out (hrw : RewriteSound F Fs fuel)
    (has : AssumeSound F Fs) {fs : Facts} {σ : SemanticStore Expression}
    (hγ : FactsInv F Fs fs σ) {ss : Statements} (hok : CmdsOk (CmdOps F) ss)
    (hdef : GoalsDefined Fs ss σ)
    {t : AssertId Expression} {e' : Expression.Expr}
    (h : Fails Fs (stepStmts F fs fuel ss).1 σ t e') : ∃ e, Fails Fs ss σ t e := by
  rw [stepStmts_eq] at h
  exact Pass.fails_of_fails_out (pass_sound hrw has) hγ hok hdef h

/-- **`ss'` keeps the failures of `ss` from `σ`** under the reference event semantics:
    each assertion or cover `t` (a label and metadata) that `ss` fails, `ss'` fails, and,
    where the goals of `ss` have values, each one `ss'` fails, `ss` fails. -/
@[expose] def FailuresKept (Fs : Expression.Factory) (ss ss' : Statements)
    (σ : SemanticStore Expression) : Prop :=
  ∀ t : AssertId Expression,
    ((∃ e, FailsE Fs ss σ t e) → ∃ e', FailsE Fs ss' σ t e') ∧
    (GoalsDefined Fs ss σ → (∃ e', FailsE Fs ss' σ t e') → ∃ e, FailsE Fs ss σ t e)

/-- **The walk keeps failures under the reference event semantics.** If the facts `fs` hold
    at `σ` with values whose operators are consistent with `F`, so are those of every command
    of `ss`, and `ss` has no loops, the walk's output keeps the failures of `ss` from `σ`. -/
theorem stepStmts_failsE
    (hWB : WellFormedSemanticEvalBool (P := Expression) Fs) (hrw : RewriteSound F Fs fuel)
    (has : AssumeSound F Fs) {fs : Facts} {σ : SemanticStore Expression}
    (hγ : FactsInv F Fs fs σ) {ss : Statements} (hok : CmdsOk (CmdOps F) ss)
    (hss : Block.noLoops ss = true) :
    FailuresKept Fs ss (stepStmts F fs fuel ss).1 σ := by
  have hss' : Block.noLoops (stepStmts F fs fuel ss).1 = true := by
    rw [stepStmts_eq]; exact (pass F fuel).stmts_noLoops ss fs hss
  refine fun t => ⟨fun ⟨e, h⟩ => ?_, fun hdef ⟨e', h⟩ => ?_⟩
  · obtain ⟨e', h'⟩ := stepStmts_fails hrw has hγ hok (failsE_fails_noLoops hss h)
    exact ⟨e', fails_failsE hWB h'⟩
  · obtain ⟨e, h'⟩ := stepStmts_fails_out hrw has hγ hok hdef (failsE_fails_noLoops hss' h)
    exact ⟨e, fails_failsE hWB h'⟩

/-- The facts an axiom adds: those of `assumeFact` for an axiom without bound variables,
    none for another declaration. -/
@[expose] def axStep (F : Lambda.Factory CoreLParams) (fuel : Nat) (fs : Facts) : Decl → Facts
  | .ax a _ => if a.e.hasBVar then fs else assumeFact F fs fuel a.e
  | _ => fs

/-- A declaration as the phase rewrites it under the facts `fs`. -/
@[expose] def declStep (F : Lambda.Factory CoreLParams) (fuel : Nat) (fs : Facts) : Decl → Decl
  | .proc proc md => .proc (rewriteProc F fs fuel proc) md
  | .lemma l md => .lemma { l with e := rewriteGoal F fs fuel l.e } md
  | d => d

/-- The declarations `ds` as the phase rewrites them, starting from the facts `fs`: each
    procedure under the facts of the axioms before it. -/
@[expose] def walkDecls (F : Lambda.Factory CoreLParams) (fuel : Nat) :
    Facts → List Decl → List Decl
  | _, [] => []
  | fs, d :: ds => declStep F fuel fs d :: walkDecls F fuel (axStep F fuel fs d) ds

/-- The facts the body of `q`, declared after the declarations `pre`, starts from: those of
    the axioms in `pre`, without those that mention one of its parameters. -/
@[expose] def procFacts (F : Lambda.Factory CoreLParams) (fuel : Nat) (pre : List Decl)
    (q : Procedure) :
    Facts :=
  (pre.foldl (axStep F fuel) {}).forget (q.header.inputs.keys ++ q.header.outputs.keys)

/-- A fold over the declarations whose step adds an axiom's facts to the first component and
    the rewritten declaration to the second is `walkDecls`, reversed onto the accumulator. -/
private theorem foldl_walk (F : Lambda.Factory CoreLParams) (fuel : Nat)
    (g : Facts × List Decl → Decl → Facts × List Decl)
    (hg : ∀ x d, g x d = (axStep F fuel x.1 d, declStep F fuel x.1 d :: x.2)) :
    ∀ (ds : List Decl) (fs : Facts) (acc : List Decl),
      ds.foldl g (fs, acc) = (ds.foldl (axStep F fuel) fs, (walkDecls F fuel fs ds).reverse ++ acc)
  | [], _, _ => rfl
  | d :: ds, fs, acc => by
    simp only [List.foldl_cons, walkDecls, List.reverse_cons, List.append_assoc,
      List.singleton_append, hg]
    exact foldl_walk F fuel g hg ds _ _

/-- `walkDecls` on a concatenation walks the second part from the facts of the first. -/
private theorem walkDecls_append (F : Lambda.Factory CoreLParams) (fuel : Nat) :
    ∀ (pre rest : List Decl) (fs : Facts),
      walkDecls F fuel fs (pre ++ rest) =
        walkDecls F fuel fs pre ++ walkDecls F fuel (pre.foldl (axStep F fuel) fs) rest
  | [], _, _ => rfl
  | d :: pre, rest, fs => by
    simp only [List.cons_append, walkDecls, List.foldl_cons]
    rw [walkDecls_append F fuel pre rest]

/-- The body `ss` of the procedure `q`, declared after the declarations `pre`, as the phase
    rewrites it with the folding factory and fuel of the context `C`, from the facts of the
    axioms in `pre`. -/
@[expose] def rewriteBody (C : Simplify.Ctx) (pre : List Decl) (q : Procedure)
    (ss : Statements) : Statements :=
  (stepStmts C.foldFactory (procFacts C.foldFactory C.evalFuel pre q) C.evalFuel ss).1

open Core.FoldAxioms in
/-- A run of the phase on `program` from the state `s` computes the factory `F0` of
    `program`, and rewrites each structured body with the context `runCtx program F0`, from
    the facts of the axioms declared before its procedure. -/
private theorem equalitySimplificationPhase_body {program out : Program}
    {s s' : Transform.CoreTransformState} {b : Bool}
    (h : (Core.equalitySimplificationPhase.transform program).run s = (.ok (b, out), s'))
    {q : Procedure} {md : Imperative.MetaData Expression} {ss : Statements}
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss) :
    ∃ F0 s1, (Simplify.programFactory program).run s = (.ok F0, s1) ∧
    ∃ pre, (∃ post, program.decls = pre ++ Decl.proc q md :: post) ∧
      Decl.proc { q with body := .structured (rewriteBody (runCtx program F0) pre q ss) } md ∈
        out.decls := by
  change (runEqualitySimplification program).run s = _ at h
  simp only [runEqualitySimplification, ExceptT.run_bind] at h
  rcases hF : (ExceptT.run (Simplify.programFactory program)) s with ⟨r, s1⟩
  simp only [bind, StateT.bind, hF] at h
  cases r with
  | error => cases h
  | ok F0 =>
    simp only [ExceptT.run, pure, ExceptT.pure] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    obtain ⟨pre, post, hd⟩ := List.append_of_mem hq
    refine ⟨F0, _, rfl, pre, ⟨post, hd⟩, ?_⟩
    rw [foldl_walk (runCtx program F0).foldFactory (runCtx program F0).evalFuel _
      (fun x d => by cases d <;> rfl), hd, walkDecls_append]
    simp only [List.append_nil, List.reverse_reverse, walkDecls, declStep, rewriteProc, hb,
      rewriteBody, List.mem_append, List.mem_cons]
    exact .inr (.inl rfl)

/-- Every axiom of `p` without bound variables is typed at `bool` by its own annotations. -/
abbrev GroundAxiomsTyped (p : Program) : Prop :=
  ∀ a md, Decl.ax a md ∈ p.decls → a.e.hasBVar = false → Lambda.LExpr.HasTypeA [] a.e .bool

/-- No facts hold in every well-formed store. -/
private theorem Facts.holds_empty {Fs : Expression.Factory} {σ : SemanticStore Expression}
    (hσ : WellFormedStore σ Fs) : ({} : Facts).Holds Fs σ :=
  ⟨hσ, fun _ _ h => by simp at h, fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩

/-- **The axioms' facts hold** in a store where every axiom of `ds` without quantifiers
    evaluates to `true`, and keep operators consistent with `F` when those axioms' are, given
    that learning an assumption is sound. -/
private theorem axStep_holds {F : Lambda.Factory CoreLParams} {Fs : Expression.Factory}
    {fuel : Nat} (has : AssumeSound F Fs)
    {σ : SemanticStore Expression} :
    ∀ (ds : List Decl) (fs : Facts), FactsInv F Fs fs σ →
      (∀ a md, Decl.ax a md ∈ ds → a.e.hasBVar = false →
        Lambda.OpsConsistentR F a.e ∧ Lambda.LExpr.HasTypeA [] a.e .bool) →
      (∀ a md, Decl.ax a md ∈ ds → a.e.hasBVar = false →
        Expression.eval Fs σ a.e = some (HasBool.ttVal Fs)) →
      FactsInv F Fs (ds.foldl (axStep F fuel) fs) σ
  | [], _, h, _, _ => h
  | d :: ds, fs, h, hops, hds => by
    simp only [List.foldl_cons]
    apply axStep_holds has ds _ _ (fun a md hm => hops a md (List.mem_cons_of_mem _ hm))
      (fun a md hm => hds a md (List.mem_cons_of_mem _ hm))
    cases d with
    | ax a md =>
      simp only [axStep]
      split
      · exact h
      · rename_i hb
        have hb' : a.e.hasBVar = false := by simpa using hb
        obtain ⟨ho, ht⟩ := hops a md (List.mem_cons_self ..) hb'
        exact has fs σ a.e h.2 ho ht h.1
          (hds a md (List.mem_cons_self ..) hb')
    | _ => exact h

open Core.FoldAxioms in
/-- **The equality simplification phase keeps failures, and adds none where the goals have
    values.** Let a run of `equalitySimplificationPhase` on `program` from the state `s`
    succeed with `out`, and let `q` be a procedure of `program`, declared after the
    declarations `pre`, with structured body `ss`. The run computes the factory `F0` of
    `program`, and `out` contains the procedure with body `rewriteBody (runCtx program F0) pre
    q ss`. Write `F` and `fuel` for the folding factory and fuel of `runCtx program F0`. If
    `ss` has no loops and the operators of its commands are consistent with `F`, then for
    every runtime factory `Fs` evaluating negations as Booleans, for which the phase's two
    expression-level steps are sound (`RewriteSound F Fs fuel`, `AssumeSound F Fs`), and
    every store `σ` where the starting facts `procFacts F fuel pre q` hold, with values whose
    operators are consistent with `F`, the output body keeps the failures of `ss` from `σ`
    (`FailuresKept`). The operator premise is expected from type checking, which annotates
    each operator at an instance of its signature in the program's factory
    (`Lambda.OpsConsistent`, then `Lambda.OpsConsistent_OpsConsistentR`), and from `F`
    keeping those signatures; no lemma derives either yet (follow-up work). -/
theorem equalitySimplificationPhase_failsE {program out : Program}
    {s s' : Transform.CoreTransformState} {b : Bool}
    (h : (Core.equalitySimplificationPhase.transform program).run s = (.ok (b, out), s'))
    {q : Procedure} {md : Imperative.MetaData Expression} {ss : Statements}
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss) :
    ∃ F0 s1, (Simplify.programFactory program).run s = (.ok F0, s1) ∧
    ∃ pre, (∃ post, program.decls = pre ++ Decl.proc q md :: post) ∧
      Decl.proc { q with body := .structured (rewriteBody (runCtx program F0) pre q ss) } md ∈
        out.decls ∧
      ∀ {Fs : Expression.Factory}, WellFormedSemanticEvalBool (P := Expression) Fs →
        RewriteSound (runCtx program F0).foldFactory Fs (runCtx program F0).evalFuel →
        AssumeSound (runCtx program F0).foldFactory Fs → Block.noLoops ss = true →
        CmdsOk (CmdOps (runCtx program F0).foldFactory) ss →
        ∀ {σ : SemanticStore Expression},
        FactsInv (runCtx program F0).foldFactory Fs
          (procFacts (runCtx program F0).foldFactory (runCtx program F0).evalFuel pre q) σ →
        FailuresKept Fs ss (rewriteBody (runCtx program F0) pre q ss) σ := by
  obtain ⟨F0, s1, hF, pre, hpre, hm⟩ := equalitySimplificationPhase_body h hq hb
  exact ⟨F0, s1, hF, pre, hpre, hm, fun hWB hrw has hss hok _ hγ =>
    stepStmts_failsE hWB hrw has hγ hok hss⟩

/-! ## Axiom folding, then equality simplification -/

open Core.FoldAxioms in
/-- **Axiom folding then equality simplification keeps failures, and adds none where
    the goals have values.** Let a run of `foldAxiomsPhase` on `program` from the state `s`
    succeed with `mid` and the state `s1`, and a run of `equalitySimplificationPhase` on
    `mid` from `s1` succeed with `out`. Let `q` be a procedure of `program` with structured
    body `ss`. The first run computes the factory `F₁` of `program`, the second the factory
    `F₂` of `mid`, and `out` contains `q` with body `rewriteBody (runCtx mid F₂) pre q ss`,
    for the declarations `pre` before `q` in `mid`. Let `ss` have no loops, the operators of
    its commands be consistent with the folding factory of `runCtx mid F₂`, and those of the
    ground axioms of `program` and of `mid` with the folding factories of `runCtx program F₁`
    and `runCtx mid F₂`, and the ground axioms of `mid` be typed at `bool`. Then for every
    runtime factory `Fs` evaluating negations as Booleans,
    for which the expression-level steps of the two phases are sound (`AxiomFoldSound` with
    `runCtx program F₁`, `RewriteSound` and `AssumeSound` with `runCtx mid F₂`), and every
    well-formed store `σ` that agrees, outside the parameters of `q`, with a well-formed store
    where the ground axioms of `program` evaluate to `true`, the output body keeps the
    failures of `ss` from `σ` (`FailuresKept`). The premises on `ss` and on the ground
    axioms of `program` are expected from type checking, as for
    `equalitySimplificationPhase_failsE`. Type checking never sees `mid`, so the premises on
    its ground axioms instead need axiom folding to keep operators consistent, with the
    folding factory of `mid` in place of that of `program`, and to keep the axioms typed at
    `bool`. `AxiomFoldSound` concludes neither, and no lemma derives them yet. -/
theorem foldAxioms_equalitySimplification_failsE {program mid out : Program}
    {s s1 s' : Transform.CoreTransformState} {b1 b : Bool}
    (h1 : (Core.foldAxiomsPhase.transform program).run s = (.ok (b1, mid), s1))
    (h2 : (Core.equalitySimplificationPhase.transform mid).run s1 = (.ok (b, out), s'))
    {q : Procedure} {md : Imperative.MetaData Expression} {ss : Statements}
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss) :
    ∃ F₁ s₁, (Simplify.programFactory program).run s = (.ok F₁, s₁) ∧
    ∃ F₂ s₂, (Simplify.programFactory mid).run s1 = (.ok F₂, s₂) ∧
    ∃ pre, (∃ post, mid.decls = pre ++ Decl.proc q md :: post) ∧
      Decl.proc { q with body := .structured (rewriteBody (runCtx mid F₂) pre q ss) } md ∈
        out.decls ∧
      ∀ {Fs : Expression.Factory}, WellFormedSemanticEvalBool (P := Expression) Fs →
        AxiomFoldSound (runCtx program F₁).foldFactory Fs (runCtx program F₁).evalFuel →
        RewriteSound (runCtx mid F₂).foldFactory Fs (runCtx mid F₂).evalFuel →
        AssumeSound (runCtx mid F₂).foldFactory Fs → Block.noLoops ss = true →
        CmdsOk (CmdOps (runCtx mid F₂).foldFactory) ss →
        GroundAxiomsOps (runCtx program F₁).foldFactory program →
        GroundAxiomsOps (runCtx mid F₂).foldFactory mid → GroundAxiomsTyped mid →
        ∀ {σ₀ σ : SemanticStore Expression}, WellFormedStore σ₀ Fs →
        GroundAxiomsHold Fs program σ₀ → WellFormedStore σ Fs →
        (∀ x, x ∉ q.header.inputs.keys ++ q.header.outputs.keys → σ₀ x = σ x) →
        FailuresKept Fs ss (rewriteBody (runCtx mid F₂) pre q ss) σ := by
  obtain ⟨F₁, s₁, hF₁, hp, hout, -⟩ := foldAxiomsPhase_run h1
  obtain ⟨F₂, s₂, hF₂, pre, ⟨post, hd⟩, hm, hiff⟩ :=
    equalitySimplificationPhase_failsE h2 (hp q md hq) hb
  refine ⟨F₁, s₁, hF₁, F₂, s₂, hF₂, pre, ⟨post, hd⟩, hm,
    fun hWB hfold hrw has hss hok hops₁ hops₂ hty _ _ hσ₀ hax hσ hag =>
      hiff hWB hrw has hss hok ?_⟩
  have hpre : ∀ a md', Decl.ax a md' ∈ pre → Decl.ax a md' ∈ mid.decls := fun a md' ha => by
    rw [hd]; exact List.mem_append_left _ ha
  obtain ⟨hh, ho⟩ := axStep_holds (fuel := (runCtx mid F₂).evalFuel) has pre _
    ⟨Facts.holds_empty hσ₀, Facts.ops_empty _⟩
    (fun a md' ha hb' => ⟨hops₂ a md' (hpre a md' ha) hb', hty a md' (hpre a md' ha) hb'⟩)
    (fun a md' ha hb' => groundAxiomsHold_fold hfold hσ₀ hout hops₁ hax a md' (hpre a md' ha) hb')
  exact ⟨Facts.holds_forget hh _ hσ hag, Facts.ops_forget ho _⟩

end -- public section

end EqualitySimplification
end Core
