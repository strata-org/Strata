/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.Languages.Core.EvaluatorResults
import Strata.DL.Imperative.PathConditionHolds
import Strata.DL.Imperative.EvalContextProps
import Strata.DL.Imperative.PathConditionsFoldProps
import all Strata.DL.Imperative.PathConditionsFold
import Strata.DL.Lambda.LExprDenoteEvalMeta
import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.LExpr
import Strata.Languages.Core.InstWellFormedSemanticsEval

/-!
# Proofs about `evaluatorResults`

The results the evaluator decides without a solver (`Strata.Languages.Core.EvaluatorResults`):
which obligations they are reported for, why they are sound, and that the discharge's
incremental trail gives the same results.

## Main results

- `Core.evaluatorResults_valid_sat` — when `evaluatorResults` reports a failure
- `Core.evaluatorResults_valid_sat_deductive` — the same, in `deductive` mode
- `Core.evaluatorResults_valid_sat_not_dead` — never on a known-dead path
- `Core.evaluatorResults_valid_unsat` — it reports a pass only for a goal that is literally `true`
  or, up to metadata, an assumption of its own path condition
- `Core.goal_eval_true_of_assumed`, `Core.evaluatorResults_valid_unsat_sound` — such a goal
  evaluates to `true` in every store where its path condition holds
- `Core.assumptionIndex_contains`, `Core.goalIsAssumed_iff`, `Core.goalIsRefuted_iff` — the
  assumption index holds exactly the path's metadata-erased assumptions and negated arguments
- `Core.evaluatorResults_sat_unsat` — it reports a satisfiability check unsatisfiable only for a
  goal that is literally `false`, a path with a literally `false` assumption, or a cover whose goal
  is, up to metadata, the negation of one of its path's assumptions or whose path assumes its
  negation
- `Core.evaluatorResults_sat_unsat_sound` — such a goal is not `true` in any store where its path
  condition holds
- `Core.evaluatorResultsTrail_eq` — on a trail satisfying its invariant, the discharge's evaluator
  results are `evaluatorResults`, and the advanced trail satisfies the invariant
-/

open Strata

/-! ## When the evaluator reports an assertion failing

`evaluatorResults` decides validity without a solver, reporting it `sat` with an empty
model, only when the goal is literally `false` and the path condition is known to be
satisfiable. The theorems below pin which path conditions those are, so a change to the
shape check cannot quietly widen when the evaluator reports a failure. -/

namespace Core

/-- The evaluator reports validity as `sat` only for a requested validity check of a goal
that is literally `false`, under a path condition that only declares or defines variables or
that the premise of `deductiveAssumingSatisfiablePaths` takes to be satisfiable. -/
theorem evaluatorResults_valid_sat {obligation : Imperative.ProofObligation Expression}
    {checkMode : VerificationMode} {satisfiabilityCheck validityCheck : Bool}
    {m : Imperative.SMT.Model Expression.Ident}
    (h : (evaluatorResults obligation checkMode satisfiabilityCheck validityCheck).2 =
      some (.sat m)) :
    validityCheck = true ∧ obligation.obligation.isFalse = true ∧
      (pathConditionShape obligation = .onlyDefinitions ∨
        usesSatisfiablePathsPremise obligation checkMode (pathConditionShape obligation)) := by
  grind [evaluatorResults, evaluatorResultsWith]

/-! ## The assumption index

`assumptionIndex` holds the metadata-erased assumptions of an obligation's path condition and the
arguments of those that are negations. Its two hash sets contain exactly those keys. -/

/-- Folding `AssumptionIndex.addEntry` over one path condition adds its assumptions to `pos`,
    and the arguments of its negated assumptions to `neg`. -/
private theorem foldl_addEntry (pc : List (Imperative.PathConditionEntry Expression)) :
    ∀ (idx : AssumptionIndex) (k : MetaFreeExpr),
      ((pc.foldl AssumptionIndex.addEntry idx).pos.contains k = true ↔
        idx.pos.contains k = true ∨
          ∃ label a, Imperative.PathConditionEntry.assumption label a ∈ pc ∧
            MetaFreeExpr.of a = k) ∧
      ((pc.foldl AssumptionIndex.addEntry idx).neg.contains k = true ↔
        idx.neg.contains k = true ∨
          ∃ label a, Imperative.PathConditionEntry.assumption label a ∈ pc ∧
            negArg? (MetaFreeExpr.of a).expr = some k.expr) := by
  induction pc with
  | nil => intro idx k; simp
  | cons e rest ih =>
    intro idx ⟨k⟩
    simp only [List.foldl_cons, ih, List.mem_cons]
    cases e with
    | assumption l a =>
      cases hn : negArg? (MetaFreeExpr.of a).expr <;>
        simp [AssumptionIndex.addEntry, AssumptionIndex.add, hn, or_and_right, exists_or,
          and_assoc, exists_and_left, exists_eq_left, or_assoc, or_left_comm]
    | _ => simp [AssumptionIndex.addEntry]

/-- The index of an obligation contains in `pos` exactly the metadata-erased assumptions of its
    path condition, and in `neg` exactly the arguments of its negated assumptions. -/
theorem assumptionIndex_contains (obligation : Imperative.ProofObligation Expression)
    (k : MetaFreeExpr) :
    ((assumptionIndex obligation).pos.contains k = true ↔
      ∃ pc ∈ obligation.assumptions, ∃ label a,
        Imperative.PathConditionEntry.assumption label a ∈ pc ∧ MetaFreeExpr.of a = k) ∧
    ((assumptionIndex obligation).neg.contains k = true ↔
      ∃ pc ∈ obligation.assumptions, ∃ label a,
        Imperative.PathConditionEntry.assumption label a ∈ pc ∧
          negArg? (MetaFreeExpr.of a).expr = some k.expr) := by
  unfold assumptionIndex
  suffices ∀ (pcs : Imperative.PathConditions Expression) (idx : AssumptionIndex),
      ((pcs.foldl (fun idx pc => pc.foldl AssumptionIndex.addEntry idx) idx).pos.contains k =
          true ↔ idx.pos.contains k = true ∨ ∃ pc ∈ pcs, ∃ label a,
            Imperative.PathConditionEntry.assumption label a ∈ pc ∧ MetaFreeExpr.of a = k) ∧
      ((pcs.foldl (fun idx pc => pc.foldl AssumptionIndex.addEntry idx) idx).neg.contains k =
          true ↔ idx.neg.contains k = true ∨ ∃ pc ∈ pcs, ∃ label a,
            Imperative.PathConditionEntry.assumption label a ∈ pc ∧
              negArg? (MetaFreeExpr.of a).expr = some k.expr) by
    simpa using this obligation.assumptions {}
  intro pcs
  induction pcs with
  | nil => intro idx; simp
  | cons pc rest ih =>
    intro idx
    simp only [List.foldl_cons, ih, foldl_addEntry]
    simp [or_and_right, exists_or, or_assoc]

/-- `goalIsAssumed` on the index of the obligation's own path condition holds exactly when the
    goal is, up to metadata, one of its assumptions. -/
theorem goalIsAssumed_iff (obligation : Imperative.ProofObligation Expression) :
    goalIsAssumed (assumptionIndex obligation) obligation = true ↔
      ∃ pc ∈ obligation.assumptions, ∃ label a,
        Imperative.PathConditionEntry.assumption label a ∈ pc ∧
          Lambda.LExpr.eqModuloMeta obligation.obligation a = true := by
  simp only [goalIsAssumed, (assumptionIndex_contains obligation _).1,
    Lambda.LExpr.eqModuloMeta_iff (T := CoreLParams), MetaFreeExpr.of, MetaFreeExpr.mk.injEq]
  grind

/-- `goalIsRefuted` on the index of the obligation's own path condition holds exactly when the
    goal is, up to metadata, the negation of one of its assumptions, or one of its assumptions is
    the negation of the goal. -/
theorem goalIsRefuted_iff (obligation : Imperative.ProofObligation Expression) :
    goalIsRefuted (assumptionIndex obligation) obligation = true ↔
      ∃ pc ∈ obligation.assumptions, ∃ label a,
        Imperative.PathConditionEntry.assumption label a ∈ pc ∧
          (isNegationOf a obligation.obligation = true ∨
            isNegationOf obligation.obligation a = true) := by
  have hc := assumptionIndex_contains obligation
  simp only [goalIsRefuted, Bool.or_eq_true]
  split
  · rename_i x hx
    rw [(hc _).2, (hc _).1]
    simp only [isNegationOf, decide_eq_true_eq, MetaFreeExpr.of, MetaFreeExpr.mk.injEq] at hx ⊢
    refine ⟨fun h => h.elim (fun ⟨pc, hpc, l, a, he, h⟩ => ⟨pc, hpc, l, a, he, .inl h⟩)
      fun ⟨pc, hpc, l, a, he, h⟩ => ⟨pc, hpc, l, a, he, .inr (h ▸ hx)⟩, ?_⟩
    exact fun ⟨pc, hpc, l, a, he, h⟩ => h.imp (fun h => ⟨pc, hpc, l, a, he, h⟩)
      fun h => ⟨pc, hpc, l, a, he, (Option.some.inj (hx.symm.trans h)).symm⟩
  · rename_i hx
    rw [(hc _).2]
    simp only [isNegationOf, decide_eq_true_eq, MetaFreeExpr.of] at hx ⊢
    simp [hx]

/-- The evaluator reports a validity check proved (`unsat`) only for a goal that is literally
`true` or that is, up to metadata, one of the assumptions of its own path condition, in every
check mode. So no mode's shortcut ever adds a pass. -/
theorem evaluatorResults_valid_unsat {obligation : Imperative.ProofObligation Expression}
    {checkMode : VerificationMode} {satisfiabilityCheck validityCheck : Bool}
    (h : (evaluatorResults obligation checkMode satisfiabilityCheck validityCheck).2 =
      some .unsat) :
    validityCheck = true ∧ (obligation.obligation.isTrue = true ∨
      ∃ pc ∈ obligation.assumptions, ∃ label a,
        Imperative.PathConditionEntry.assumption label a ∈ pc ∧
          Lambda.LExpr.eqModuloMeta obligation.obligation a = true) := by
  have hr : validityCheck = true ∧ (obligation.obligation.isTrue = true ∨
      goalIsAssumed (assumptionIndex obligation) obligation = true) := by
    grind [evaluatorResults, evaluatorResultsWith]
  exact ⟨hr.1, hr.2.imp_right (goalIsAssumed_iff obligation).1⟩

/-- The evaluator reports a satisfiability check unsatisfiable (`unsat`) only for a goal that is
literally `false`, a path condition with a literally `false` assumption, or a cover whose goal is,
up to metadata, the negation of one of its path's assumptions, or one of whose assumptions is the
negation of the goal. -/
theorem evaluatorResults_sat_unsat {obligation : Imperative.ProofObligation Expression}
    {checkMode : VerificationMode} {satisfiabilityCheck validityCheck : Bool}
    (h : (evaluatorResults obligation checkMode satisfiabilityCheck validityCheck).1 =
      some .unsat) :
    satisfiabilityCheck = true ∧ (obligation.obligation.isFalse = true ∨
      pathConditionShape obligation = .hasFalseAssumption ∨
      (obligation.property = .cover ∧ ∃ pc ∈ obligation.assumptions, ∃ label a,
        Imperative.PathConditionEntry.assumption label a ∈ pc ∧
          (isNegationOf a obligation.obligation = true ∨
            isNegationOf obligation.obligation a = true))) := by
  have hr : satisfiabilityCheck = true ∧ (obligation.obligation.isFalse = true ∨
      pathConditionShape obligation = .hasFalseAssumption ∨
      (obligation.property = .cover ∧
        goalIsRefuted (assumptionIndex obligation) obligation = true)) := by
    grind [evaluatorResults, evaluatorResultsWith]
  exact ⟨hr.1, hr.2.imp_right (Or.imp_right (And.imp_right (goalIsRefuted_iff obligation).1))⟩

/-- In `deductive` mode, the evaluator reports an assertion failing only when its path
condition only declares or defines variables. -/
theorem evaluatorResults_valid_sat_deductive {obligation : Imperative.ProofObligation Expression}
    {satisfiabilityCheck validityCheck : Bool} {m : Imperative.SMT.Model Expression.Ident}
    (h : (evaluatorResults obligation .deductive satisfiabilityCheck validityCheck).2 =
      some (.sat m)) :
    pathConditionShape obligation = .onlyDefinitions := by
  obtain ⟨-, -, h | h⟩ := evaluatorResults_valid_sat h
  · exact h
  · simp [usesSatisfiablePathsPremise] at h

/-- In any mode, the evaluator never reports an assertion failing on a path it knows is dead:
one with a literally `false` assumption. -/
theorem evaluatorResults_valid_sat_not_dead {obligation : Imperative.ProofObligation Expression}
    {checkMode : VerificationMode} {satisfiabilityCheck validityCheck : Bool}
    {m : Imperative.SMT.Model Expression.Ident}
    (h : (evaluatorResults obligation checkMode satisfiabilityCheck validityCheck).2 =
      some (.sat m)) :
    pathConditionShape obligation ≠ .hasFalseAssumption := by
  obtain ⟨-, -, h | h⟩ := evaluatorResults_valid_sat h
  · simp [h]
  · simp only [usesSatisfiablePathsPremise, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    exact h.2

/-! ## Why the evaluator's passes are sound

The predicate `Imperative.PathConditions.Holds` says what an obligation's path condition
asserts about a store. A goal the evaluator reports proved evaluates to `true` in every store
where its path condition holds. -/

/-- A goal that is, up to metadata, an assumption of its own path condition evaluates to `true`
in every store where that path condition holds. -/
theorem goal_eval_true_of_assumed {F : Expression.Factory}
    {σ : Imperative.SemanticStore Expression} {obligation : Imperative.ProofObligation Expression}
    (hpc : Imperative.PathConditions.Holds F σ obligation.assumptions)
    (h : ∃ pc ∈ obligation.assumptions, ∃ label a,
      Imperative.PathConditionEntry.assumption label a ∈ pc ∧
        Lambda.LExpr.eqModuloMeta obligation.obligation a = true) :
    Expression.eval F σ obligation.obligation = some (Imperative.HasBool.ttVal F) := by
  obtain ⟨pc, hpc', label, a, he, hm⟩ := h
  exact (Lambda.LExpr.denoteEval_eqModuloMeta (T := CoreLParams) hm).trans (hpc pc hpc' _ he)

/-- When the evaluator reports a validity check proved (`unsat`), the goal evaluates to `true`
in every store where the obligation's path condition holds. -/
theorem evaluatorResults_valid_unsat_sound {obligation : Imperative.ProofObligation Expression}
    {checkMode : VerificationMode} {satisfiabilityCheck validityCheck : Bool}
    {F : Expression.Factory} {σ : Imperative.SemanticStore Expression}
    (h : (evaluatorResults obligation checkMode satisfiabilityCheck validityCheck).2 =
      some .unsat)
    (hpc : Imperative.PathConditions.Holds F σ obligation.assumptions) :
    Expression.eval F σ obligation.obligation = some (Imperative.HasBool.ttVal F) := by
  refine (evaluatorResults_valid_unsat h).2.elim (fun ht => ?_) (goal_eval_true_of_assumed hpc)
  generalize obligation.obligation = g at ht ⊢
  unfold Lambda.LExpr.isTrue at ht
  split at ht <;> first | exact Lambda.LExpr.denoteEval_boolConst | cases ht

/-! ## Why the evaluator's unsatisfiable verdicts are sound

A goal the evaluator reports unsatisfiable does not evaluate to `true` in any store where its
path condition holds: a literally `false` goal or assumption evaluates to `false`, and the
negation of a value that holds is `false`. -/

section
open Imperative

/-- Inversion of `isNegationOf`: `p` is a negation `Bool.Not(x)` at `bool → bool` whose argument
    `x` is `q` up to metadata. -/
private theorem isNegationOf_inv {p q : Expression.Expr} (h : isNegationOf p q = true) :
    ∃ m m' o x, p = .app m (.op m' o (some (Lambda.LMonoTy.arrow .bool .bool))) x ∧
      o.name = "Bool.Not" ∧ x.eraseMetadata = q.eraseMetadata := by
  simp only [isNegationOf, decide_eq_true_eq] at h
  rcases p with _ | _ | _ | _ | _ | _ | ⟨m, _ | ⟨m', o, _ | ty⟩, x⟩
  all_goals simp only [Lambda.LExpr.eraseMetadata, Lambda.LExpr.replaceMetadata, negArg?,
    reduceCtorEq, Bool.and_eq_true, beq_iff_eq] at h
  split at h
  · obtain ⟨hn, rfl⟩ := ‹_ ∧ _›
    exact ⟨m, m', o, x, rfl, hn, Option.some.inj h⟩
  · cases h

/-- Expressions equal up to metadata have the same value. -/
private theorem eval_of_eraseMetadata_eq {F : Expression.Factory} {σ : SemanticStore Expression}
    {x q : Expression.Expr} (h : x.eraseMetadata = q.eraseMetadata) :
    Expression.eval F σ x = Expression.eval F σ q :=
  Lambda.LExpr.denoteEval_eqModuloMeta (T := CoreLParams)
    ((Lambda.LExpr.eqModuloMeta_iff (T := CoreLParams)).2 h)

/-- Under a factory that resolves `Bool.Not` to Core's built-in negation, `Bool.Not(x)` evaluates
    to `b` exactly when `x` evaluates to `!b`. -/
private theorem eval_not_true {F : Expression.Factory} {σ : SemanticStore Expression}
    (hF : F.factory["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func)
    {m m' : ExpressionMetadata} {o : Lambda.Identifier Unit} (ho : o.name = "Bool.Not")
    {x : Expression.Expr}
    {b : Bool} :
    Expression.eval F σ (.app m (.op m' o (some (Lambda.LMonoTy.arrow .bool .bool))) x) =
        some (Lambda.SemValue.ofBool F.model.tcInterp b) ↔
      Expression.eval F σ x = some (Lambda.SemValue.ofBool F.model.tcInterp (!b)) := by
  show Lambda.LExpr.denoteEval (T := CoreLParams) _ _ _ = _ ↔
    Lambda.LExpr.denoteEval (T := CoreLParams) _ _ _ = _
  rw [Lambda.LExpr.denoteEval_app_op_bool_iff (T := CoreLParams), ho]
  cases b <;> simp [boolNot_opInterp_of_lookup F.model hF]


/-- One step of `pathConditionShape`. -/
private def shapeStep : PathConditionShape → PathConditionEntry Expression → PathConditionShape :=
  fun shape entry => match shape, entry with
      | .hasFalseAssumption, _ => .hasFalseAssumption
      | _, .assumption _ e => if e.isFalse then .hasFalseAssumption else .other
      | _, .distinct .. => .other
      | shape, .varDecl .. => shape

/-- Folding `shapeStep` over entries ends at `hasFalseAssumption` only from that shape or past a
    literally `false` assumption. -/
private theorem shapeStep_fold (pc : List (PathConditionEntry Expression)) : ∀ s,
    pc.foldl shapeStep s = .hasFalseAssumption →
      s = .hasFalseAssumption ∨
        ∃ l e, PathConditionEntry.assumption l e ∈ pc ∧ e.isFalse = true := by
  induction pc with
  | nil => intro s h; exact .inl h
  | cons e es ih =>
    intro s h
    cases e <;> cases s <;> grind [shapeStep]

/-- A path condition of shape `hasFalseAssumption` has a literally `false` assumption. -/
private theorem exists_false_of_shape {obligation : ProofObligation Expression}
    (h : pathConditionShape obligation = .hasFalseAssumption) :
    ∃ pc ∈ obligation.assumptions, ∃ label e,
      PathConditionEntry.assumption label e ∈ pc ∧ e.isFalse = true := by
  suffices ∀ (pcs : PathConditions Expression) s, pcs.foldl (fun s pc => pc.foldl shapeStep s) s =
      .hasFalseAssumption → s = .hasFalseAssumption ∨ ∃ pc ∈ pcs, ∃ label e,
        PathConditionEntry.assumption label e ∈ pc ∧ e.isFalse = true by
    simpa using this obligation.assumptions .onlyDefinitions h
  intro pcs
  induction pcs with
  | nil => intro s h; exact .inl h
  | cons pc rest ih =>
    intro s h
    rcases ih _ h with h' | ⟨pc', hpc', l, e, he, hf⟩
    · exact (shapeStep_fold pc s h').imp_right fun ⟨l, e, he, hf⟩ => ⟨pc, .head _, l, e, he, hf⟩
    · exact .inr ⟨pc', .tail _ hpc', l, e, he, hf⟩

/-- A literally `false` Core expression evaluates to `false` in every store. -/
private theorem eval_of_isFalse {F : Expression.Factory} {σ : SemanticStore Expression}
    {e : Expression.Expr} (h : e.isFalse = true) :
    Expression.eval F σ e = some (HasBool.ffVal F) := by
  unfold Lambda.LExpr.isFalse at h
  split at h <;> first | exact Lambda.LExpr.denoteEval_boolConst | cases h

/-- When the evaluator reports a satisfiability check unsatisfiable (`unsat`), the goal does not
evaluate to `true` in any store where the obligation's path condition holds, under a factory
that resolves `Bool.Not` to Core's built-in negation. -/
theorem evaluatorResults_sat_unsat_sound {obligation : ProofObligation Expression}
    {checkMode : VerificationMode} {satisfiabilityCheck validityCheck : Bool}
    {F : Expression.Factory} {σ : SemanticStore Expression}
    (h : (evaluatorResults obligation checkMode satisfiabilityCheck validityCheck).1 =
      some .unsat)
    (hF : F.factory["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func)
    (hpc : PathConditions.Holds F σ obligation.assumptions) :
    Expression.eval F σ obligation.obligation ≠ some (HasBool.ttVal F) := by
  intro hg
  have htf : (HasBool.ttVal F : Expression.Val) ≠ HasBool.ffVal F := HasBool.ttVal_ne_ffVal F
  rcases (evaluatorResults_sat_unsat h).2 with hf | hs | ⟨-, pc, hpc', l, a, he, hn | hn⟩
  · exact htf (Option.some.inj (hg.symm.trans (eval_of_isFalse hf)))
  · obtain ⟨pc, hpc', l, e, he, hf⟩ := exists_false_of_shape hs
    exact htf (Option.some.inj ((hpc pc hpc' _ he).symm.trans (eval_of_isFalse hf)))
  · obtain ⟨m, m', o, x, rfl, ho, hx⟩ := isNegationOf_inv hn
    exact htf (Option.some.inj (hg.symm.trans
      ((eval_of_eraseMetadata_eq hx).symm.trans ((eval_not_true hF ho).1 (hpc pc hpc' _ he)))))
  · obtain ⟨m, m', o, x, hgoal, ho, hx⟩ := isNegationOf_inv hn
    exact htf (Option.some.inj ((hpc pc hpc' _ he).symm.trans
      ((eval_of_eraseMetadata_eq hx).symm.trans ((eval_not_true hF ho).1 (hgoal ▸ hg)))))

end

/-! ## The incremental assumption facts of the discharge

The discharge decides `evaluatorResults` from an `EvalTrail` advanced along the obligations
(`evaluatorResultsTrail`). On a trail whose counts are those of its entries (`EvalTrail.Inv`),
advancing to an obligation's entries, oldest first, keeps that invariant
(`PathConditions.UndoFold.advance_inv`) and gives exactly the results `evaluatorResults` gives
(`evaluatorResultsTrail_eq`), so the soundness theorems about `evaluatorResults` apply to the
results the discharge uses. -/

section Incremental
open Imperative

/-- The counts `c` are those of the entries `l`: for each key, the number of assumptions of `l`
    with that key (`pos`) and of negated assumptions of `l` with that argument (`neg`). -/
private def EvalCounts.Of (l : PathCondition Expression) (c : EvalCounts) : Prop :=
  ∀ k, c.pos.getD k 0 = l.countP (fun e => (entryKeys e).1 == some k) ∧
    c.neg.getD k 0 = l.countP (fun e => (entryKeys e).2 == some k)

/-- The counts of a trail are those of its entries. -/
private def EvalTrail.Inv (t : EvalTrail) : Prop :=
  EvalCounts.Of t.entries.toList t.current

/-- Counting a key once more. -/
private theorem bumpKey_getD (m : Std.HashMap MetaFreeExpr Nat) (o : Option MetaFreeExpr)
    (k : MetaFreeExpr) :
    (bumpKey m o).getD k 0 = m.getD k 0 + (if o == some k then 1 else 0) := by
  cases o with
  | none => simp [bumpKey]
  | some j => by_cases h : j = k <;> simp [bumpKey, Std.HashMap.getD_insert, h]

/-- Counting a key once less. -/
private theorem unbumpKey_getD (m : Std.HashMap MetaFreeExpr Nat) (o : Option MetaFreeExpr)
    (k : MetaFreeExpr) :
    (unbumpKey m o).getD k 0 = m.getD k 0 - (if o == some k then 1 else 0) := by
  cases o with
  | none => simp [unbumpKey]
  | some j => by_cases h : j = k <;> simp [unbumpKey, Std.HashMap.getD_insert, h]

/-- The count step keeps the counts those of the entries when an entry is appended. -/
private theorem evalCountsFold_step {l : PathCondition Expression} {c : EvalCounts}
    (h : EvalCounts.Of l c) (e : PathConditionEntry Expression) :
    EvalCounts.Of (l ++ [e]) (evalCountsFold.step c e) := fun k => by
  simp only [evalCountsFold, bumpKey_getD, (h k).1, (h k).2, List.countP_append,
    List.countP_singleton]
  constructor <;> (try split) <;> simp_all

/-- The count undo step keeps the counts those of the entries when the newest entry is
    dropped. -/
private theorem evalCountsFold_undo {l : PathCondition Expression} {c : EvalCounts}
    {e : PathConditionEntry Expression} (h : EvalCounts.Of (l ++ [e]) c) :
    EvalCounts.Of l (evalCountsFold.undo c e) := fun k => by
  simp only [evalCountsFold, unbumpKey_getD, (h k).1, (h k).2, List.countP_append,
    List.countP_singleton]
  constructor <;> (try split) <;> simp_all

/-- On a trail satisfying the invariant whose entries are `obligation`'s, oldest first, the
    goal facts are those of the obligation's own assumption index. -/
private theorem EvalTrail.goal_facts {t : EvalTrail} (ht : t.Inv)
    (obligation : ProofObligation Expression)
    (he : t.entries.toList = obligation.assumptions.reverse.flatten) :
    t.goalAssumed obligation = goalIsAssumed (assumptionIndex obligation) obligation ∧
      t.goalRefuted obligation = goalIsRefuted (assumptionIndex obligation) obligation := by
  have hc : ∀ k, (t.current.pos.getD k 0 != 0) = (assumptionIndex obligation).pos.contains k ∧
      (t.current.neg.getD k 0 != 0) = (assumptionIndex obligation).neg.contains k := by
    intro k
    obtain ⟨a1, a2⟩ := assumptionIndex_contains obligation k
    rw [(ht k).1, (ht k).2, he]
    refine ⟨Bool.eq_iff_iff.2 ?_, Bool.eq_iff_iff.2 ?_⟩ <;>
      simp only [a1, a2, bne_iff_ne, Nat.ne_zero_iff_zero_lt, List.countP_pos_iff,
        List.mem_flatten, List.mem_reverse, beq_iff_eq] <;> constructor
    · rintro ⟨e, ⟨pc, hpc, he⟩, hk⟩
      cases e <;> simp only [entryKeys, reduceCtorEq, Option.some.injEq] at hk
      exact ⟨pc, hpc, _, _, he, hk⟩
    · rintro ⟨pc, hpc, l, a, he, rfl⟩
      exact ⟨_, ⟨pc, hpc, he⟩, by simp [entryKeys]⟩
    · rintro ⟨e, ⟨pc, hpc, he⟩, hk⟩
      cases e <;> simp only [entryKeys, reduceCtorEq, Option.map_eq_some_iff] at hk
      obtain ⟨x, hx, rfl⟩ := hk
      exact ⟨pc, hpc, _, _, he, hx⟩
    · rintro ⟨pc, hpc, l, a, he, hn⟩
      exact ⟨_, ⟨pc, hpc, he⟩, by simp [entryKeys, hn]⟩
  refine ⟨(hc _).1, ?_⟩
  simp only [EvalTrail.goalRefuted, goalIsRefuted, (hc _).1, (hc _).2]

/-- The empty trail satisfies the invariant. -/
private theorem EvalTrail.empty_inv : EvalTrail.Inv (.init {}) := fun k => by
  simp [PathConditions.UndoFoldState.init]

/-- **The discharge's evaluator results are `evaluatorResults`.** On a trail whose counts are
    those of its entries, `evaluatorResultsTrail` gives the results `evaluatorResults` gives for
    `obligation`, and a trail whose counts are those of its entries again. -/
theorem evaluatorResultsTrail_eq {t : EvalTrail} (ht : t.Inv)
    (obligation : ProofObligation Expression) (checkMode : VerificationMode)
    (satisfiabilityCheck validityCheck : Bool) :
    (evaluatorResultsTrail t obligation checkMode satisfiabilityCheck validityCheck).1 =
        evaluatorResults obligation checkMode satisfiabilityCheck validityCheck ∧
      (evaluatorResultsTrail t obligation checkMode satisfiabilityCheck validityCheck).2.Inv := by
  obtain ⟨h1, h2⟩ := PathConditions.UndoFold.advance_inv evalCountsFold EvalCounts.Of
    (fun _ _ e h => evalCountsFold_step h e) (fun _ _ _ => evalCountsFold_undo) ht
    obligation.assumptions.reverse.flatten
  obtain ⟨g1, g2⟩ := EvalTrail.goal_facts h1 obligation h2
  exact ⟨by simp only [evaluatorResultsTrail, evaluatorResults, g1, g2], h1⟩

end Incremental

end Core
