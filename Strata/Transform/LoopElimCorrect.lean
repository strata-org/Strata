/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.LoopElimProps
public import Strata.DL.Imperative.BigStep.SemProps
public import Strata.DL.Imperative.Logic.TraceRelations
import Strata.DL.Imperative.Logic.TraceRelationsProps
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.Util.ListUtilsProps
import all Strata.Transform.LoopElim
import all Strata.DL.Imperative.Cmd

/-! # Loop elimination over-approximates (big-step)

A list `ss'` that is `ss` with its loops eliminated (`LoopElim.BlockRel ss ss'`, the output of
`Block.loopElim`) replays every run and every reach of `ss` from a value-valued store
(`WellFormedStore`, whose values have types by `LawfulHasVal.value_typed`), when `ss` is def-use
well formed there:

* a run of `ss` gives a run of `ss'` with the same outcome, whose trace is the source's with
  some events dropped (`Trace.MayDropEvents`) and operationally true assumptions inserted
  (`Trace.InsertsTrueAssumes`) — `run_sim`; when no loop iteration leaves its loop by an `exit`
  (`Block.loopExitsLocal`), for each event of the source run there is also such a run of `ss'`
  keeping that event, after events so related to those before it and before events so related
  to those after it — `run_sim_at`; so a run of `ss'` whose assertions are valid exists only if
  those of the source run are — `run_sim_valid`;
* a reach of `ss` gives a reach of `ss'` whose trace ends with the same event, after events so
  related to those before it in the source (`Trace.PreservesLastEvent`) — `reach_sim`.

The replay of a loop runs its passive encoding: the `if` enters its first branch exactly when
the loop runs an iteration; the first havoc block jumps from the loop's entry store to the
store at the start of one iteration of the source, the replayed body follows that iteration,
and the second havoc block jumps to the store the loop ends with.  For a reach, the replayed
iteration is the one the reach stops in.  For a run, it is the last one, which an `exit` out of
the loop forces; without such exits, `run_sim_at` replays instead the iteration the chosen event
is in, the second havoc block jumping from its end to the end of the loop.  The havocs
can choose those stores: an iteration changes only the loop-carried variables
(`Block.carriedVars`), since the variables the body defines are undefined at its start (def-use
well-formedness) and projected away at its end, and keeps each value typed alike
(`TypeAgree`).  The inserted assumptions of the guard and of its negation hold at those stores:
the source entered, and left, the loop there.

Key theorems: `LoopElim.run_sim`, `LoopElim.run_sim_at`, `LoopElim.run_sim_valid`,
`LoopElim.reach_sim`. -/

namespace Imperative
namespace LoopElim

open BigStep

public section

variable {P : PureExpr} [HasBool P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P]
  [LawfulHasVal P]

/-- How a trace of the encoding relates to a trace of the source: some source events dropped,
    then assumptions inserted that evaluate to `true` under an `allowed` factory. -/
private abbrev DropsInserts (allowed : P.Factory → Prop) : Trace P → Trace P → Prop :=
  RComp Trace.MayDropEvents (Trace.InsertsTrueAssumes allowed)

/-- The first branch of the passive encoding of a loop. -/
private abbrev thenB (n : String) (g : ExprOrNondet P) (M : List P.Ident)
    (body' : PStmts P) (md : MetaData P) : PStmts P :=
  .block s!"{Core.loopElimBlockPrefix}arbitrary_iter_facts_{n}"
    ([havocBlock n M md] ++ enterAssume n g md ++ body') {} ::
    ([havocBlock n M md] ++ exitAssume n g md)

omit [HasBool P] [HasFvar P] [HasFvars P] [HasOps P] [LawfulHasVal P] in
/-- The passive encoding of a loop is an `ite` on its guard whose first branch is `thenB` and
    whose second branch is empty. -/
private theorem loopPassive_eq (n : String) (g : ExprOrNondet P) (M : List P.Ident)
    (body' : PStmts P) (md : MetaData P) :
    Stmt.loopPassive n g M body' md = .ite g (thenB n g M body' md) [] {} :=
  rfl

omit [HasBool P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P] [LawfulHasVal P] in
/-- Projection depends only on the variables the parent store defines. -/
private theorem projectStore_congr_parent {σ₁ σ₂ σ : SemanticStore P}
    (h : ∀ x, (σ₁ x).isSome = (σ₂ x).isSome) : projectStore σ₁ σ = projectStore σ₂ σ :=
  funext fun x => by simp only [projectStore, h x]

omit [HasBool P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P] [LawfulHasVal P] in
/-- Projecting an outcome on a store defining every variable of its store leaves it. -/
private theorem Outcome.proj_of_dom {σp : SemanticStore P} {o : Outcome P}
    (h : ∀ x, (o.store x).isSome → (σp x).isSome) : o.proj σp = o := by
  cases o <;> simp only [Outcome.proj, Outcome.store] at h ⊢ <;>
    rw [projectStore_id fun x hx =>
      Option.isSome_iff_ne_none.1 (h x (Option.isSome_iff_ne_none.2 hx))]

/-- The label of the first block of the encoding starts with the reserved prefix. -/
private theorem arbitraryIterLabel_startsWith (n : String) :
    (s!"{Core.loopElimBlockPrefix}arbitrary_iter_facts_{n}").startsWith Core.loopElimPrefix =
      Bool.true := by
  rw [String.startsWith_string_iff]
  show _ <+: (Core.loopElimBlockPrefix ++ ("arbitrary_iter_facts_" ++ n)).toList
  simp only [String.toList_append]
  exact List.prefix_append_of_prefix (by decide)

variable {F : P.Factory} {allowed : P.Factory → Prop} {df : P.Ident → Bool}

/-! ## The commands of the encoding -/

omit [HasFvars P] [HasBoolOps P] [HasOps P] [LawfulHasVal P] in
/-- Havocking the variables `M` from `τ` can reach `σ` when `σ` changes only them, each to a
    value sharing a type with its value in `τ`. -/
private theorem havocs_run (hvar : WellFormedSemanticEvalVar (P := P) F) (md : MetaData P) :
    ∀ (M : List P.Ident) (τ σ : SemanticStore P),
    (∀ x ∈ M, ∃ p v ty, τ x = some p ∧ σ x = some v ∧ HasVal.valueOfTy F p ty ∧
      HasVal.valueOfTy F v ty) →
    (∀ x, x ∉ M → τ x = σ x) →
    BRun F (M.map fun n => Stmt.cmd (P := P) (HasHavoc.havoc (P := P) (CmdT := CmdExt P) n md))
      τ [] (.normal σ)
  | [], τ, σ, _, hfr => by
    have : τ = σ := funext fun x => hfr x (by simp)
    subst this
    exact .nil
  | x :: M, τ, σ, hM, hfr => by
    obtain ⟨p, v, ty, hp, hv, hpty, hvty⟩ := hM x (by simp)
    let τ' : SemanticStore P := fun y => if y = x then σ y else τ y
    have hup : UpdateState P τ x v τ' :=
      .update hp (by simp [τ', hv]) fun y hxy => by simp [τ', Ne.symm hxy]
    have hE : EvalE F τ (.cmd (.set x .nondet md)) τ' [] :=
      EvalCmdE.eval_set_nondet hup ⟨p, ty, hp, hpty, hvty⟩ hvar
    have hrest := havocs_run hvar md M τ' σ
      (fun y hy => by
        by_cases hyx : y = x
        · subst hyx; exact ⟨v, v, ty, by simp [τ', hv], hv, hvty, hvty⟩
        · obtain ⟨p', v', ty', hp', hv', h1, h2⟩ := hM y (by simp [hy])
          exact ⟨p', v', ty', by simp [τ', hyx, hp'], hv', h1, h2⟩)
      (fun y hy => by
        by_cases hyx : y = x
        · simp [τ', hyx]
        · simp only [τ', hyx, ite_false]; exact hfr y (by simp [hyx, hy]))
    exact BRun.cons_normal (evs1 := []) (evs2 := []) (.cmd hE) hrest

omit [HasFvars P] [HasBoolOps P] [HasOps P] [LawfulHasVal P] in
/-- The havoc block of a loop can jump from `τ` to `σ` under the premises of `havocs_run`. -/
private theorem havocBlock_run (hvar : WellFormedSemanticEvalVar (P := P) F) (n : String)
    (md : MetaData P) {M : List P.Ident} {τ σ : SemanticStore P}
    (hM : ∀ x ∈ M, ∃ p v ty, τ x = some p ∧ σ x = some v ∧ HasVal.valueOfTy F p ty ∧
      HasVal.valueOfTy F v ty)
    (hfr : ∀ x, x ∉ M → τ x = σ x) :
    BRunS F (havocBlock (C := CmdExt P) n M md) τ [] (.normal σ) := by
  have h := BRunS.block (l := s!"{Core.loopElimBlockPrefix}havoc_{n}") (md := {})
    (havocs_run hvar md M τ σ hM hfr)
  have hdom : ∀ x, σ x ≠ none → τ x ≠ none := fun x hx => by
    by_cases hxM : x ∈ M
    · obtain ⟨p, -, -, hp, -⟩ := hM x hxM; simp [hp]
    · rwa [hfr x hxM]
  simpa [Outcome.block, projectStore_id hdom, havocBlock, HasHavoc.havoc] using h

omit [HasFvars P] [HasBoolOps P] [HasOps P] [LawfulHasVal P] in
/-- The assumption of the guard runs, from a store where the guard admits entering, emitting
    only operationally true assumptions. -/
private theorem enter_run (hF : allowed F) (n : String) {g : ExprOrNondet P} (md : MetaData P)
    {σ : SemanticStore P} (hg : guardEnters F σ g) :
    ∃ evs, BRun F (enterAssume (C := CmdExt P) n g md) σ evs (.normal σ) ∧
      DropsInserts allowed [] evs := by
  cases g with
  | det g =>
    exact ⟨_, .cons_normal (.cmd (EvalCmdE.eval_assume)) .nil, [], .slnil, .assume hF hg .nil⟩
  | nondet => exact ⟨[], .nil, [], .slnil, .nil⟩

omit [HasFvars P] [HasOps P] [LawfulHasVal P] in
/-- The assumption of the negated guard runs, from a store where the guard admits stopping,
    emitting only operationally true assumptions. -/
private theorem exit_run (hbool : WellFormedSemanticEvalBool (P := P) F) (hF : allowed F)
    (n : String) {g : ExprOrNondet P} (md : MetaData P) {σ : SemanticStore P}
    (hg : guardExits F σ g) :
    ∃ evs, BRun F (exitAssume (C := CmdExt P) n g md) σ evs (.normal σ) ∧
      DropsInserts allowed [] evs := by
  cases g with
  | det g =>
    exact ⟨_, .cons_normal (.cmd (EvalCmdE.eval_assume)) .nil, [], .slnil,
      .assume hF ((hbool σ g).2.1 hg) .nil⟩
  | nondet => exact ⟨[], .nil, [], .slnil, .nil⟩

/-! ## Stores of the iterations

`Compat M σ₀ σ`: the store `σ` at the start of an iteration of a loop entered from `σ₀`
defines the same variables, agrees with `σ₀` outside the loop-carried variables `M`, holds
values typed alike and holds values. -/

/-- The store `σ` at the start of an iteration of a loop entered from `σ₀`. -/
private structure Compat (F : P.Factory) (M : List P.Ident) (σ₀ σ : SemanticStore P) :
    Prop where
  dom : ∀ x, (σ₀ x).isSome = (σ x).isSome
  frame : ∀ x, x ∉ M → σ x = σ₀ x
  agree : TypeAgree F σ₀ σ
  storeWF : WellFormedStore σ F

omit [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P] in
/-- A well-formed store is compatible with itself. -/
private theorem Compat.refl (M : List P.Ident) {σ : SemanticStore P} (h : WellFormedStore σ F) :
    Compat F M σ σ :=
  ⟨fun _ => rfl, fun _ _ => rfl, .refl h, h⟩

omit [HasBoolOps P] [LawfulHasVal P] in
/-- From the entry store `σ₀` of a loop, the havocs of its loop-carried variables can jump to
    the store `σ` of the start of an iteration. -/
private theorem Compat.havoc {body : PStmts P} {σ₀ σ : SemanticStore P}
    (hc : Compat F (Block.carriedVars body) σ₀ σ)
    (hdu : Block.defUseWellFormed (fun x => (σ₀ x).isSome) df body = true) :
    (∀ x ∈ Block.carriedVars body, ∃ p v ty, σ₀ x = some p ∧ σ x = some v ∧
      HasVal.valueOfTy F p ty ∧ HasVal.valueOfTy F v ty) ∧
    (∀ x, x ∉ Block.carriedVars body → σ₀ x = σ x) := by
  refine ⟨fun x hx => ?_, fun x hx => (hc.frame x hx).symm⟩
  have h0 := defined_of_mem_carriedVars hdu hx
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 h0
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 ((hc.dom x) ▸ h0)
  obtain ⟨ty, h1, h2⟩ := hc.agree x p v hp hv
  exact ⟨p, v, ty, hp, hv, h1, h2⟩

omit [HasBoolOps P] in
/-- At the store `σ` of the start of an iteration, the havocs of the loop-carried variables can
    stay at `σ`. -/
private theorem Compat.havoc_self {body : PStmts P} {σ₀ σ : SemanticStore P}
    (hc : Compat F (Block.carriedVars body) σ₀ σ)
    (hdu : Block.defUseWellFormed (fun x => (σ₀ x).isSome) df body = true) :
    ∀ x ∈ Block.carriedVars body, ∃ p v ty, σ x = some p ∧ σ x = some v ∧
      HasVal.valueOfTy F p ty ∧ HasVal.valueOfTy F v ty := by
  intro x hx
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 ((hc.dom x) ▸ defined_of_mem_carriedVars hdu hx)
  obtain ⟨ty, hty⟩ := LawfulHasVal.value_typed F v (hc.storeWF x v hv)
  exact ⟨v, v, ty, hv, hv, hty, hty⟩

omit [HasBoolOps P] in
/-- The store at the start of the next iteration (the end of an iteration projected on its
    start) is again the store of the start of an iteration. -/
private theorem Compat.step {body : PStmts P} {σ₀ σ σ1 : SemanticStore P}
    {evs : List (Event P)} (hc : Compat F (Block.carriedVars body) σ₀ σ)
    (hdu : Block.defUseWellFormed (fun x => (σ₀ x).isSome) df body = true)
    (h : BRun F body σ evs (.normal σ1)) :
    Compat F (Block.carriedVars body) σ₀ (projectStore σ σ1) := by
  have hdom := brun_dom h
  have hfr := brun_frame h
  have hT := brun_typed h hc.storeWF
  simp only [Outcome.store] at hdom hfr hT
  refine ⟨fun x => ?_, fun x hx => ?_, ?_, WellFormedStore.proj hT.1⟩
  · rw [hc.dom x]
    cases hs : (σ x).isSome
    · simp [projectStore, hs]
    · simp [projectStore, hs, hdom x hs]
  · cases hs : (σ x).isSome
    · have h0 : σ₀ x = none := by
        have := hc.dom x
        rw [hs] at this
        simpa using this
      simp [projectStore, hs, h0]
    · have hcv : x ∉ Block.modifiedVars body ∨ x ∈ Block.definedVars body false := by
        simp only [Block.carriedVars, List.mem_filter, decide_eq_true_eq, not_and] at hx
        by_cases hm : x ∈ Block.modifiedVars body
        · exact .inr (Classical.not_not.1 (hx hm))
        · exact .inl hm
      rcases hcv with hm | hd
      · simp only [projectStore, hs, ite_true]
        rw [hfr x hs hm, hc.frame x hx]
      · have := Block.not_defined_of_mem_definedVars hdu hd
        rw [hc.dom x, hs] at this
        cases this
  · exact hc.agree.trans hT.2.proj fun x hx => (hc.dom x) ▸ hx

/-! ## Replaying a loop -/

/-- The replay of a loop entered from `σ₀`, of which a run from the store `σ` of the start of
    an iteration emits `evs` and ends with `o`: either the loop stops at once (no event, at `σ`,
    where the guard admits stopping), or the guard admits entering at `σ` and the first branch
    of the encoding runs from `σ₀` to `o`, emitting a trace related to `evs` by `DropsInserts`,
    to a store defining only variables of `σ₀`. -/
private def LoopRunRes (F : P.Factory) (allowed : P.Factory → Prop) (n : String)
    (g : ExprOrNondet P) (body body' : PStmts P) (md : MetaData P) (σ₀ σ : SemanticStore P)
    (evs : List (Event P)) (o : Outcome P) : Prop :=
  (evs = [] ∧ o = .normal σ ∧ guardExits F σ g) ∨
  (guardEnters F σ g ∧ ∃ evs', BRun F (thenB n g (Block.carriedVars body) body' md) σ₀ evs' o ∧
    DropsInserts allowed evs evs' ∧ ∀ x, (o.store x).isSome → (σ₀ x).isSome)

/-- The replay of a loop entered from `σ₀`, of which a reach from the store `σ` of the start
    of an iteration emits `evs`: the guard admits entering at `σ` and the first branch of the
    encoding reaches from `σ₀`, emitting a trace ending with the same event
    (`Trace.PreservesLastEvent`). -/
private def LoopReachRes (F : P.Factory) (allowed : P.Factory → Prop) (n : String)
    (g : ExprOrNondet P) (body body' : PStmts P) (md : MetaData P) (σ₀ σ : SemanticStore P)
    (evs : List (Event P)) : Prop :=
  guardEnters F σ g ∧ ∃ evs', BReach F (thenB n g (Block.carriedVars body) body' md) σ₀ evs' ∧
    Trace.PreservesLastEvent (DropsInserts allowed) evs evs'

omit [HasBoolOps P] [LawfulHasVal P] in
/-- From the entry store `σ₀`, the start of the first branch of the encoding (the havoc block
    and the assumption of the guard) can reach the store `σ` of the start of an iteration
    entering the body, emitting only operationally true assumptions. -/
private theorem prelude_run (hvar : WellFormedSemanticEvalVar (P := P) F) (hF : allowed F)
    (n : String) {g : ExprOrNondet P} {body : PStmts P} (md : MetaData P)
    {σ₀ σ : SemanticStore P} (hc : Compat F (Block.carriedVars body) σ₀ σ)
    (hdu : Block.defUseWellFormed (fun x => (σ₀ x).isSome) df body = true)
    (hg : guardEnters F σ g) :
    ∃ ee, BRun F ([havocBlock n (Block.carriedVars body) md] ++ enterAssume n g md) σ₀ ee
      (.normal σ) ∧ DropsInserts allowed [] ee := by
  obtain ⟨ee, he, hae⟩ := enter_run (allowed := allowed) hF n md hg
  have hh := havocBlock_run hvar n md (hc.havoc hdu).1 (hc.havoc hdu).2
  exact ⟨[] ++ ee, .cons_normal hh he, by simpa using hae⟩

/-- **A run of a loop body, replayed in the encoding.**  If the loop entered from `σ₀` runs an
    iteration from `σ` (where the guard admits entering) ending normally, the body's output
    replays it, and the rest of the loop from the next iteration is replayed (`LoopRunRes`),
    then the loop from `σ` is replayed. -/
private theorem LoopRunRes.iter (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F) (hF : allowed F)
    {n : String} {g : ExprOrNondet P} {body body' : PStmts P} {md : MetaData P}
    {σ₀ σ σ1 : SemanticStore P} {evs1 evs1' evs2 : List (Event P)} {o : Outcome P}
    (hg : guardEnters F σ g) (hc : Compat F (Block.carriedVars body) σ₀ σ)
    (hdu : Block.defUseWellFormed (fun x => (σ₀ x).isSome) df body = true)
    (h1 : BRun F body σ evs1 (.normal σ1)) (h1' : BRun F body' σ evs1' (.normal σ1))
    (habs : DropsInserts allowed evs1 evs1')
    (hres : LoopRunRes F allowed n g body body' md σ₀ (projectStore σ σ1) evs2 o) :
    LoopRunRes F allowed n g body body' md σ₀ σ (evs1 ++ evs2) o := by
  rcases hres with ⟨rfl, rfl, hx⟩ | ⟨-, evs2', h2', habs2, hdom2⟩
  · refine .inr ⟨hg, ?_⟩
    have hc' := hc.step hdu h1
    obtain ⟨ee, hpre, hae⟩ := prelude_run (allowed := allowed) hvar hF n md hc hdu hg
    obtain ⟨ex, hex, hax⟩ := exit_run (allowed := allowed) hbool hF n md hx
    have harb := BRunS.block (l := s!"{Core.loopElimBlockPrefix}arbitrary_iter_facts_{n}")
      (md := {}) (brun_append hpre h1')
    have hσ : projectStore σ₀ σ1 = projectStore σ σ1 := projectStore_congr_parent hc.dom
    simp only [Outcome.block, hσ] at harb
    have hh := havocBlock_run hvar n md (hc'.havoc_self hdu) (fun _ _ => rfl)
    refine ⟨_, .cons_normal harb (.cons_normal hh hex), ?_, fun x hx => ?_⟩
    · simpa using Trace.mayDropEvents_insertsTrueAssumes_append hae
        (Trace.mayDropEvents_insertsTrueAssumes_append habs hax)
    · simp only [Outcome.store] at hx
      rwa [hc'.dom x]
  · exact .inr ⟨hg, evs2', h2', Trace.mayDropEvents_insertsTrueAssumes_drop_left evs1 habs2, hdom2⟩

omit [LawfulHasVal P] in
/-- **A breaking iteration, replayed in the encoding.**  If the loop entered from `σ₀` runs an
    iteration from `σ` (where the guard admits entering) that exits to a label other than the
    encoding's, and the body's output replays it, then the loop from `σ` is replayed. -/
private theorem LoopRunRes.break (hvar : WellFormedSemanticEvalVar (P := P) F) (hF : allowed F)
    {n : String} {g : ExprOrNondet P} {body body' : PStmts P} {md : MetaData P}
    {σ₀ σ σ1 : SemanticStore P} {evs evs' : List (Event P)} {l : String}
    (hg : guardEnters F σ g) (hc : Compat F (Block.carriedVars body) σ₀ σ)
    (hdu : Block.defUseWellFormed (fun x => (σ₀ x).isSome) df body = true)
    (hl : ∀ l ∈ Block.labels body, l.startsWith Core.loopElimPrefix = Bool.false)
    (h1 : BRun F body σ evs (.exit l σ1)) (h1' : BRun F body' σ evs' (.exit l σ1))
    (habs : DropsInserts allowed evs evs') :
    LoopRunRes F allowed n g body body' md σ₀ σ evs (.exit l (projectStore σ σ1)) := by
  refine .inr ⟨hg, ?_⟩
  obtain ⟨ee, hpre, hae⟩ := prelude_run (allowed := allowed) hvar hF n md hc hdu hg
  have harb := BRunS.block (l := s!"{Core.loopElimBlockPrefix}arbitrary_iter_facts_{n}")
    (md := {}) (brun_append hpre h1')
  have hlb : l ≠ s!"{Core.loopElimBlockPrefix}arbitrary_iter_facts_{n}" := by
    intro h
    have hfalse := hl l (brun_exit_label h1 l σ1 rfl)
    rw [h, arbitraryIterLabel_startsWith] at hfalse
    cases hfalse
  have hσ : projectStore σ₀ σ1 = projectStore σ σ1 := projectStore_congr_parent hc.dom
  simp only [Outcome.block, hlb, ite_false, hσ] at harb
  refine ⟨_, .cons_exit harb,
    by simpa using Trace.mayDropEvents_insertsTrueAssumes_append hae habs, fun x hx => ?_⟩
  simp only [Outcome.store, projectStore] at hx
  split at hx
  · rename_i h; rwa [hc.dom x]
  · cases hx

omit [HasOps P] [LawfulHasVal P] in
/-- A replay of the loop entered from its start store `σ` (`LoopRunRes` with `σ₀ = σ`) is a run
    of its encoding. -/
private theorem LoopRunRes.ite {n : String} {g : ExprOrNondet P} {body body' : PStmts P}
    {md : MetaData P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P}
    (h : LoopRunRes F allowed n g body body' md σ σ evs o) :
    ∃ evs', BRunS F (Stmt.loopPassive n g (Block.carriedVars body) body' md) σ evs' o ∧
      DropsInserts allowed evs evs' := by
  rw [loopPassive_eq]
  rcases h with ⟨rfl, rfl, hx⟩ | ⟨hg, evs', h', habs, hdom⟩
  · have hpr : (Outcome.normal σ).proj σ = .normal σ := by
      simp [Outcome.proj, projectStore_self]
    refine ⟨[], ?_, [], .slnil, .nil⟩
    cases g with
    | det g => exact hpr ▸ BRunS.ite_false hx .nil
    | nondet => exact hpr ▸ BRunS.ite_nondet_false .nil
  · refine ⟨evs', ?_, habs⟩
    rw [← Outcome.proj_of_dom hdom]
    cases g with
    | det g => exact BRunS.ite_true hg h'
    | nondet => exact BRunS.ite_nondet_true h'

omit [LawfulHasVal P] in
/-- **A reach of a loop body, replayed in the encoding.**  If the loop entered from `σ₀`
    reaches in an iteration from `σ` (where the guard admits entering), and the body's output
    replays that reach, then the loop from `σ` is replayed. -/
private theorem LoopReachRes.here (hvar : WellFormedSemanticEvalVar (P := P) F) (hF : allowed F)
    {n : String} {g : ExprOrNondet P} {body body' : PStmts P} {md : MetaData P}
    {σ₀ σ : SemanticStore P} {evs evs' : List (Event P)}
    (hg : guardEnters F σ g) (hc : Compat F (Block.carriedVars body) σ₀ σ)
    (hdu : Block.defUseWellFormed (fun x => (σ₀ x).isSome) df body = true)
    (h' : BReach F body' σ evs')
    (habs : Trace.PreservesLastEvent (DropsInserts allowed) evs evs') :
    LoopReachRes F allowed n g body body' md σ₀ σ evs := by
  obtain ⟨ee, hpre, hae⟩ := prelude_run (allowed := allowed) hvar hF n md hc hdu hg
  exact ⟨hg, _, .here (.block (breach_append_run hpre h')), by
    simpa using Trace.PreservesLastEvent.append_left
      Trace.mayDropEvents_insertsTrueAssumes_append hae habs (breach_ne_nil h')⟩

omit [HasOps P] [LawfulHasVal P] in
/-- A replay of the reach of a later iteration of the loop is a replay of the reach of the loop
    from an earlier iteration, dropping that iteration's events. -/
private theorem LoopReachRes.later {n : String} {g : ExprOrNondet P} {body body' : PStmts P}
    {md : MetaData P} {σ₀ σ σ' : SemanticStore P} {evs1 evs2 : List (Event P)}
    (hg : guardEnters F σ g) (hres : LoopReachRes F allowed n g body body' md σ₀ σ' evs2) :
    LoopReachRes F allowed n g body body' md σ₀ σ (evs1 ++ evs2) :=
  ⟨hg, hres.2.choose, hres.2.choose_spec.1, by
    simpa using Trace.PreservesLastEvent.append_left Trace.mayDropEvents_insertsTrueAssumes_append
      (Trace.mayDropEvents_insertsTrueAssumes_drop_left evs1
        (Trace.mayDropEvents_insertsTrueAssumes_refl []))
      hres.2.choose_spec.2 (breach_ne_nil hres.2.choose_spec.1)⟩

omit [HasOps P] [LawfulHasVal P] in
/-- A replay of the reach of the loop entered from its start store `σ` (`LoopReachRes` with
    `σ₀ = σ`) is a reach of its encoding. -/
private theorem LoopReachRes.ite {n : String} {g : ExprOrNondet P} {body body' : PStmts P}
    {md : MetaData P} {σ : SemanticStore P} {evs : List (Event P)}
    (h : LoopReachRes F allowed n g body body' md σ σ evs) :
    ∃ evs', BReachS F (Stmt.loopPassive n g (Block.carriedVars body) body' md) σ evs' ∧
      Trace.PreservesLastEvent (DropsInserts allowed) evs evs' := by
  rw [loopPassive_eq]
  obtain ⟨hg, evs', h', habs⟩ := h
  refine ⟨evs', ?_, habs⟩
  cases g with
  | det g => exact BReachS.ite_true hg h'
  | nondet => exact BReachS.ite_nondet_true h'

/-! ## The simulation -/

omit [HasBoolOps P] in
/-- A list def-use well formed from `σ` whose first statement ends normally at `σ1` leaves the
    rest def-use well formed from `σ1`. -/
private theorem defUse_rest {s : PStmt P} {rest : PStmts P} {σ σ1 : SemanticStore P}
    {evs : List (Event P)} (h : BRunS F s σ evs (.normal σ1))
    (hdu : Block.defUseWellFormed (fun x => (σ x).isSome) df (s :: rest) = true) :
    Stmt.defUseWellFormed (fun x => (σ x).isSome) df s = true ∧
      Block.defUseWellFormed (fun x => (σ1 x).isSome) df rest = true := by
  simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
  refine ⟨hdu.1, ?_⟩
  have : (fun x => (σ1 x).isSome) =
      (fun x => (σ x).isSome || decide (x ∈ Stmt.definedVars s true)) :=
    funext (brunS_normal_isSome h)
  rw [this]
  exact hdu.2

omit [HasBool P] [HasBoolOps P] [LawfulHasVal P] in
/-- Def-use well-formedness from stores defining the same variables. -/
private theorem defUse_congr {ss : PStmts P} {σ₀ σ : SemanticStore P}
    (hdom : ∀ x, (σ₀ x).isSome = (σ x).isSome)
    (hdu : Block.defUseWellFormed (fun x => (σ₀ x).isSome) df ss = true) :
    Block.defUseWellFormed (fun x => (σ x).isSome) df ss = true := by
  have : (fun x => (σ x).isSome) = (fun x => (σ₀ x).isSome) := funext fun x => (hdom x).symm
  rwa [this]

omit [HasBool P] [HasBoolOps P] [LawfulHasVal P] in
/-- The body of a def-use well-formed loop is def-use well formed. -/
private theorem defUse_loop_body {D : P.Ident → Bool} {g : ExprOrNondet P} {m : Option P.Expr}
    {inv : List (String × P.Expr)} {body : PStmts P} {md : MetaData P}
    (hdu : Stmt.defUseWellFormed D df (.loop g m inv body md) = true) :
    Block.defUseWellFormed D df body = true := by
  simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  exact hdu.2

/-! ## Replaying a loop without escaping exits

When no iteration of a loop leaves it by an `exit` (`Stmt.loopExitsLocal`), a run of the loop
ends normally, and the encoding may replay any of its iterations: the second havoc block jumps
from the end of the replayed iteration to the store the loop ends with.  So for every event of a
run, a run of the encoding keeps that event, after events related to those before it and before
events related to those after it by `DropsInserts`: the replay of the iteration the event is
in. -/

/-- A run with trace `evs` replays at each of its events: for every event `e` of `evs`, with
    `pre` before it and `post` after it, `run` holds of a trace having `e` after events related
    to `pre` and before events related to `post` by `DropsInserts`. -/
private def ReplaysAt (allowed : P.Factory → Prop) (run : List (Event P) → Prop)
    (evs : List (Event P)) : Prop :=
  ∀ pre e post, evs = pre ++ e :: post → ∃ pre' post', run (pre' ++ e :: post') ∧
    DropsInserts allowed pre pre' ∧ DropsInserts allowed post post'

omit [HasFvar P] [HasFvars P] [HasBoolOps P] [HasOps P] in
/-- The stores of the starts of iterations compose. -/
private theorem Compat.trans {M : List P.Ident} {σ₀ σ σ' : SemanticStore P}
    (h₁ : Compat F M σ₀ σ) (h₂ : Compat F M σ σ') : Compat F M σ₀ σ' :=
  ⟨fun x => (h₁.dom x).trans (h₂.dom x), fun x hx => (h₂.frame x hx).trans (h₁.frame x hx),
    h₁.agree.trans h₂.agree fun x hx => (h₁.dom x) ▸ hx, h₂.storeWF⟩

omit [HasBoolOps P] in
/-- A run of a loop whose body exits to no outer label ends normally, at a store of the start
    of an iteration where the guard admits stopping. -/
private theorem loopRun_normal : ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P}, BRunS F s σ evs o → ∀ {g : ExprOrNondet P} {m : Option P.Expr}
    {inv : List (String × P.Expr)} {body : PStmts P} {md : MetaData P},
    s = .loop g m inv body md → Block.exitsCoveredByBlocks [] body →
    Block.defUseWellFormed (fun x => (σ x).isSome) df body = true → WellFormedStore σ F →
    ∃ σn, o = .normal σn ∧ Compat F (Block.carriedVars body) σ σn ∧ guardExits F σn g
  | _, σ, _, _, .loop_exit hg, _, _, _, _, _, hs, _, _, hT => by
    obtain ⟨rfl, -, -, rfl, rfl⟩ := Stmt.loop.inj hs
    exact ⟨σ, rfl, .refl _ hT, hg⟩
  | _, σ, _, _, .loop_iter _ h1 h2, _, _, _, _, _, hs, hcov, hdu, hT => by
    obtain ⟨rfl, -, -, rfl, rfl⟩ := Stmt.loop.inj hs
    have hc1 := (Compat.refl _ hT).step hdu h1
    obtain ⟨σn, rfl, hc2, hx⟩ :=
      loopRun_normal h2 hs hcov (defUse_congr hc1.dom hdu) hc1.storeWF
    exact ⟨σn, rfl, hc1.trans hc2, hx⟩
  | _, _, _, _, .loop_break _ h1, _, _, _, _, _, hs, hcov, _, _ => by
    obtain ⟨rfl, -, -, rfl, rfl⟩ := Stmt.loop.inj hs
    exact absurd (brun_exit_covered h1 hcov _ _ rfl) (by simp)

/-- The replay of a loop entered from `σ₀`, without escaping exits, of which a run from the
    store `σ` of the start of an iteration emits the nonempty trace `evs` and ends with `o`: the
    guard admits entering at `σ`, `o` defines only variables of `σ₀`, and the first branch of the
    encoding runs from `σ₀` to `o` replaying each event of `evs` (`ReplaysAt`). -/
private def LoopRunResAt (F : P.Factory) (allowed : P.Factory → Prop) (n : String)
    (g : ExprOrNondet P) (body body' : PStmts P) (md : MetaData P) (σ₀ σ : SemanticStore P)
    (evs : List (Event P)) (o : Outcome P) : Prop :=
  evs ≠ [] → guardEnters F σ g ∧ (∀ x, (o.store x).isSome → (σ₀ x).isSome) ∧
    ReplaysAt allowed (fun t => BRun F (thenB n g (Block.carriedVars body) body' md) σ₀ t o) evs

/-- **An iteration of a loop without escaping exits, replayed in the encoding.**  If the loop
    entered from `σ₀` runs an iteration from `σ` (where the guard admits entering) ending
    normally, the body's output replays each of its events, and the rest of the loop from the
    next iteration is replayed (`LoopRunResAt`), then the loop from `σ` is replayed: an event of
    the rest by the replay of the rest, an event of this iteration by replaying this iteration
    and jumping to the end of the loop. -/
private theorem LoopRunResAt.iter (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F) (hF : allowed F)
    {n : String} {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body body' : PStmts P} {md : MetaData P}
    {σ₀ σ σ1 : SemanticStore P} {evs1 evs2 : List (Event P)} {o : Outcome P}
    (hg : guardEnters F σ g) (hc : Compat F (Block.carriedVars body) σ₀ σ)
    (hdu : Block.defUseWellFormed (fun x => (σ₀ x).isSome) df body = true)
    (hcov : Block.exitsCoveredByBlocks [] body)
    (h1 : BRun F body σ evs1 (.normal σ1))
    (hk1 : ReplaysAt allowed (fun t => BRun F body' σ t (.normal σ1)) evs1)
    (h2 : BRunS F (.loop g m inv body md) (projectStore σ σ1) evs2 o)
    (hres : LoopRunResAt F allowed n g body body' md σ₀ (projectStore σ σ1) evs2 o) :
    LoopRunResAt F allowed n g body body' md σ₀ σ (evs1 ++ evs2) o := by
  have hc' := hc.step hdu h1
  have hdu' := defUse_congr hc'.dom hdu
  obtain ⟨σn, rfl, hcn, hx⟩ := loopRun_normal h2 rfl hcov hdu' hc'.storeWF
  intro _
  refine ⟨hg, fun x hx' => ?_, fun pre e post h => ?_⟩
  · simp only [Outcome.store] at hx'
    rw [hc'.dom x, hcn.dom x]
    exact hx'
  · rcases List.append_eq_append_cons h with ⟨post₁, rfl, rfl⟩ | ⟨pre₂, rfl, rfl⟩
    · obtain ⟨pre', post₁', h1', hpre, hpost⟩ := hk1 pre e post₁ rfl
      obtain ⟨ee, hpr, hae⟩ := prelude_run (allowed := allowed) hvar hF n md hc hdu hg
      obtain ⟨ex, hex, hax⟩ := exit_run (allowed := allowed) hbool hF n md hx
      have harb := BRunS.block (l := s!"{Core.loopElimBlockPrefix}arbitrary_iter_facts_{n}")
        (md := {}) (brun_append hpr h1')
      have hσ : projectStore σ₀ σ1 = projectStore σ σ1 := projectStore_congr_parent hc.dom
      simp only [Outcome.block, hσ] at harb
      have hh := havocBlock_run hvar n md (hcn.havoc hdu').1 (hcn.havoc hdu').2
      have hrun := BRun.cons_normal harb (.cons_normal hh hex)
      have heq :
          (ee ++ pre') ++ e :: (post₁' ++ ex) = (ee ++ (pre' ++ e :: post₁')) ++ ([] ++ ex) := by
        simp
      refine ⟨ee ++ pre', post₁' ++ ex, heq ▸ hrun,
        by simpa using Trace.mayDropEvents_insertsTrueAssumes_append hae hpre, ?_⟩
      simpa using Trace.mayDropEvents_insertsTrueAssumes_append hpost
        (Trace.mayDropEvents_insertsTrueAssumes_drop_left evs2 hax)
    · obtain ⟨-, -, hrep⟩ := hres (by simp)
      obtain ⟨pre', post', h2', hpre, hpost⟩ := hrep pre₂ e post rfl
      exact ⟨pre', post', h2', Trace.mayDropEvents_insertsTrueAssumes_drop_left evs1 hpre, hpost⟩

omit [HasOps P] [LawfulHasVal P] in
/-- A replay of the loop entered from its start store `σ` (`LoopRunResAt` with `σ₀ = σ`) gives,
    for each event of the loop's run, a run of its encoding replaying it. -/
private theorem LoopRunResAt.ite {n : String} {g : ExprOrNondet P} {body body' : PStmts P}
    {md : MetaData P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P}
    (h : LoopRunResAt F allowed n g body body' md σ σ evs o) :
    ReplaysAt allowed
      (fun t => BRunS F (Stmt.loopPassive n g (Block.carriedVars body) body' md) σ t o) evs := by
  intro pre e post hpos
  obtain ⟨hg, hdom, hrep⟩ := h (by simp [hpos])
  obtain ⟨pre', post', h', hpre, hpost⟩ := hrep pre e post hpos
  refine ⟨pre', post', ?_, hpre, hpost⟩
  rw [loopPassive_eq, ← Outcome.proj_of_dom hdom]
  cases g with
  | det g => exact BRunS.ite_true hg h'
  | nondet => exact BRunS.ite_nondet_true h'

mutual
/-- **A run of a list, replayed by its output**, with the same outcome and a trace related to
    the source's by `DropsInserts`; when no loop iteration leaves its loop by an `exit`, also
    replaying each event of the source (`ReplaysAt`). -/
private theorem run_sim' (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F) (hF : allowed F) :
    ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    BRun F ss σ evs o → ∀ {ss' : PStmts P}, BlockRel ss ss' →
    Block.defUseWellFormed (fun x => (σ x).isSome) df ss = true → WellFormedStore σ F →
    (∃ evs', BRun F ss' σ evs' o ∧ DropsInserts allowed evs evs') ∧
      (Block.loopExitsLocal ss → ReplaysAt allowed (fun t => BRun F ss' σ t o) evs)
  | _, _, _, _, .nil, _, hr, _, _ => by
    cases hr
    exact ⟨⟨[], .nil, [], .slnil, .nil⟩, fun _ pre e post h => by simp at h⟩
  | _, _, _, _, .cons_normal h1 h2, _, hr, hdu, hT => by
    cases hr with
    | cons hs hr =>
      have hdu' := defUse_rest h1 hdu
      obtain ⟨⟨e1, h1', ha1⟩, hk1⟩ := runS_sim hvar hbool hF h1 hs hdu'.1 hT
      obtain ⟨⟨e2, h2', ha2⟩, hk2⟩ :=
        run_sim' hvar hbool hF h2 hr hdu'.2 (brunS_typed h1 hT).1
      refine ⟨⟨e1 ++ e2, .cons_normal h1' h2',
          Trace.mayDropEvents_insertsTrueAssumes_append ha1 ha2⟩,
        fun hl pre e post h => ?_⟩
      rcases List.append_eq_append_cons h with ⟨post₁, hpos, hpost⟩ | ⟨pre₂, hpre, hpos⟩
      · obtain ⟨pre', post', h1'', ha, hb⟩ := hk1 hl.1 pre e post₁ hpos
        have heq : pre' ++ e :: (post' ++ e2) = (pre' ++ e :: post') ++ e2 := by simp
        exact ⟨pre', post' ++ e2, heq ▸ .cons_normal h1'' h2', ha,
          hpost ▸ Trace.mayDropEvents_insertsTrueAssumes_append hb ha2⟩
      · obtain ⟨pre', post', h2'', ha, hb⟩ := hk2 hl.2 pre₂ e post hpos
        have heq : (e1 ++ pre') ++ e :: post' = e1 ++ (pre' ++ e :: post') := by simp
        exact ⟨e1 ++ pre', post', heq ▸ .cons_normal h1' h2'',
          hpre ▸ Trace.mayDropEvents_insertsTrueAssumes_append ha1 ha, hb⟩
  | _, _, _, _, .cons_exit h1, _, hr, hdu, hT => by
    cases hr with
    | cons hs hr =>
      simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
      obtain ⟨⟨e1, h1', ha1⟩, hk1⟩ := runS_sim hvar hbool hF h1 hs hdu.1 hT
      refine ⟨⟨e1, .cons_exit h1', ha1⟩, fun hl pre e post h => ?_⟩
      obtain ⟨pre', post', h1'', ha, hb⟩ := hk1 hl.1 pre e post h
      exact ⟨pre', post', .cons_exit h1'', ha, hb⟩

/-- **A run of a statement, replayed by its output**, as `run_sim'`. -/
private theorem runS_sim (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F) (hF : allowed F) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    BRunS F s σ evs o → ∀ {s' : PStmt P}, StmtRel s s' →
    Stmt.defUseWellFormed (fun x => (σ x).isSome) df s = true → WellFormedStore σ F →
    (∃ evs', BRunS F s' σ evs' o ∧ DropsInserts allowed evs evs') ∧
      (Stmt.loopExitsLocal s → ReplaysAt allowed (fun t => BRunS F s' σ t o) evs)
  | _, _, evs, _, .cmd h, _, hr, _, _ => by
    cases hr
    exact ⟨⟨evs, .cmd h, Trace.mayDropEvents_insertsTrueAssumes_refl evs⟩,
      fun _ pre e post hpos => ⟨pre, post, hpos ▸ .cmd h,
        Trace.mayDropEvents_insertsTrueAssumes_refl pre,
        Trace.mayDropEvents_insertsTrueAssumes_refl post⟩⟩
  | _, _, _, _, .ite_true hc h, _, hr, hdu, hT => by
    cases hr with
    | ite ht _ =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      obtain ⟨⟨e, h', ha⟩, hk⟩ := run_sim' hvar hbool hF h ht hdu.1.2 hT
      refine ⟨⟨e, .ite_true hc h', ha⟩, fun hl pre e0 post hpos => ?_⟩
      obtain ⟨pre', post', h'', hpre, hpost⟩ := hk hl.1 pre e0 post hpos
      exact ⟨pre', post', .ite_true hc h'', hpre, hpost⟩
  | _, _, _, _, .ite_false hc h, _, hr, hdu, hT => by
    cases hr with
    | ite _ he =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      obtain ⟨⟨e, h', ha⟩, hk⟩ := run_sim' hvar hbool hF h he hdu.2 hT
      refine ⟨⟨e, .ite_false hc h', ha⟩, fun hl pre e0 post hpos => ?_⟩
      obtain ⟨pre', post', h'', hpre, hpost⟩ := hk hl.2 pre e0 post hpos
      exact ⟨pre', post', .ite_false hc h'', hpre, hpost⟩
  | _, _, _, _, .ite_nondet_true h, _, hr, hdu, hT => by
    cases hr with
    | ite ht _ =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      obtain ⟨⟨e, h', ha⟩, hk⟩ := run_sim' hvar hbool hF h ht hdu.1.2 hT
      refine ⟨⟨e, .ite_nondet_true h', ha⟩, fun hl pre e0 post hpos => ?_⟩
      obtain ⟨pre', post', h'', hpre, hpost⟩ := hk hl.1 pre e0 post hpos
      exact ⟨pre', post', .ite_nondet_true h'', hpre, hpost⟩
  | _, _, _, _, .ite_nondet_false h, _, hr, hdu, hT => by
    cases hr with
    | ite _ he =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      obtain ⟨⟨e, h', ha⟩, hk⟩ := run_sim' hvar hbool hF h he hdu.2 hT
      refine ⟨⟨e, .ite_nondet_false h', ha⟩, fun hl pre e0 post hpos => ?_⟩
      obtain ⟨pre', post', h'', hpre, hpost⟩ := hk hl.2 pre e0 post hpos
      exact ⟨pre', post', .ite_nondet_false h'', hpre, hpost⟩
  | _, _, _, _, .block h, _, hr, hdu, hT => by
    cases hr with
    | block hb =>
      simp only [Stmt.defUseWellFormed] at hdu
      obtain ⟨⟨e, h', ha⟩, hk⟩ := run_sim' hvar hbool hF h hb hdu hT
      refine ⟨⟨e, .block h', ha⟩, fun hl pre e0 post hpos => ?_⟩
      obtain ⟨pre', post', h'', hpre, hpost⟩ := hk hl pre e0 post hpos
      exact ⟨pre', post', .block h'', hpre, hpost⟩
  | _, _, _, _, .exit, _, hr, _, _ => by
    cases hr
    exact ⟨⟨[], .exit, [], .slnil, .nil⟩, fun _ pre e post h => by simp at h⟩
  | _, _, _, _, .typeDecl, _, hr, _, _ => by
    cases hr
    exact ⟨⟨[], .typeDecl, [], .slnil, .nil⟩, fun _ pre e post h => by simp at h⟩
  | _, σ, _, _, .loop_exit hg, _, hr, _, _ => by
    obtain ⟨n, body', -, -, rfl⟩ := hr.loop_inv
    obtain ⟨e, h', ha⟩ := LoopRunRes.ite (allowed := allowed) (body' := body')
      (.inl ⟨rfl, rfl, hg⟩)
    exact ⟨⟨e, h', ha⟩, fun _ pre e post h => by simp at h⟩
  | _, σ, _, _, .loop_iter (g := g) (m := m) (inv := inv) (body := body) (md := md) hg h1 h2, _,
      hr, hdu, hT => by
    obtain ⟨n, body', hb, hl, rfl⟩ := hr.loop_inv
    have hdub := defUse_loop_body hdu
    obtain ⟨⟨_, h1', ha1⟩, hk1⟩ := run_sim' hvar hbool hF h1 hb hdub hT
    have hc := Compat.refl (Block.carriedVars body) hT
    have hres := loopRun_sim hvar hbool hF h2 rfl (n := n) hb hl σ (hc.step hdub h1) hdub
    obtain ⟨e, h', ha⟩ :=
      LoopRunRes.ite (LoopRunRes.iter hvar hbool hF hg hc hdub h1 h1' ha1 hres)
    refine ⟨⟨e, h', ha⟩, fun hloc => ?_⟩
    have hresA :=
      loopRun_simAt hvar hbool hF h2 rfl (n := n) hb hloc σ (hc.step hdub h1) hdub
    exact LoopRunResAt.ite
      (LoopRunResAt.iter hvar hbool hF hg hc hdub hloc.1 h1 (hk1 hloc.2) h2 hresA)
  | _, σ, _, _, .loop_break (body := body) hg h1, _, hr, hdu, hT => by
    obtain ⟨n, body', hb, hl, rfl⟩ := hr.loop_inv
    have hdub := defUse_loop_body hdu
    obtain ⟨⟨_, h1', ha1⟩, -⟩ := run_sim' hvar hbool hF h1 hb hdub hT
    obtain ⟨e, h', ha⟩ := LoopRunRes.ite
      (LoopRunRes.break hvar hF hg (Compat.refl (Block.carriedVars body) hT) hdub hl h1 h1' ha1)
    exact ⟨⟨e, h', ha⟩, fun hloc => absurd (brun_exit_covered h1 hloc.1 _ _ rfl) (by simp)⟩

/-- **A run of a loop from the start of an iteration, replayed in the encoding of the loop
    entered from `σ₀`.** -/
private theorem loopRun_sim (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F) (hF : allowed F) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    BRunS F s σ evs o → ∀ {g : ExprOrNondet P} {m : Option P.Expr}
    {inv : List (String × P.Expr)} {body : PStmts P} {md : MetaData P},
    s = .loop g m inv body md → ∀ {n : String} {body' : PStmts P}, BlockRel body body' →
    (∀ l ∈ Block.labels body, l.startsWith Core.loopElimPrefix = Bool.false) →
    ∀ σ₀, Compat F (Block.carriedVars body) σ₀ σ →
    Block.defUseWellFormed (fun x => (σ₀ x).isSome) df body = true →
    LoopRunRes F allowed n g body body' md σ₀ σ evs o
  | _, _, _, _, .loop_exit hg, _, _, _, _, _, hs, _, _, _, _, _, _, _ => by
    obtain ⟨rfl, -, -, rfl, rfl⟩ := Stmt.loop.inj hs
    exact .inl ⟨rfl, rfl, hg⟩
  | _, σ, _, _, .loop_iter hg h1 h2, _, _, _, _, _, hs, n, _, hb, hl, σ₀, hc, hdu => by
    obtain ⟨rfl, -, -, rfl, rfl⟩ := Stmt.loop.inj hs
    have hdub := defUse_congr hc.dom hdu
    obtain ⟨⟨_, h1', ha1⟩, -⟩ := run_sim' hvar hbool hF h1 hb hdub hc.storeWF
    have hres := loopRun_sim hvar hbool hF h2 hs (n := n) hb hl σ₀ (hc.step hdu h1) hdu
    exact LoopRunRes.iter hvar hbool hF hg hc hdu h1 h1' ha1 hres
  | _, σ, _, _, .loop_break hg h1, _, _, _, _, _, hs, _, _, hb, hl, σ₀, hc, hdu => by
    obtain ⟨rfl, -, -, rfl, rfl⟩ := Stmt.loop.inj hs
    obtain ⟨⟨_, h1', ha1⟩, -⟩ :=
      run_sim' hvar hbool hF h1 hb (defUse_congr hc.dom hdu) hc.storeWF
    exact LoopRunRes.break hvar hF hg hc hdu hl h1 h1' ha1

/-- **A run of a loop without escaping exits from the start of an iteration, replayed in the
    encoding of the loop entered from `σ₀` at each of its events.** -/
private theorem loopRun_simAt (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F) (hF : allowed F) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    BRunS F s σ evs o → ∀ {g : ExprOrNondet P} {m : Option P.Expr}
    {inv : List (String × P.Expr)} {body : PStmts P} {md : MetaData P},
    s = .loop g m inv body md → ∀ {n : String} {body' : PStmts P}, BlockRel body body' →
    Stmt.loopExitsLocal s → ∀ σ₀, Compat F (Block.carriedVars body) σ₀ σ →
    Block.defUseWellFormed (fun x => (σ₀ x).isSome) df body = true →
    LoopRunResAt F allowed n g body body' md σ₀ σ evs o
  | _, _, _, _, .loop_exit _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
    fun h => absurd rfl h
  | _, σ, _, _, .loop_iter hg h1 h2, _, _, _, _, _, hs, n, _, hb, hloc, σ₀, hc, hdu => by
    obtain ⟨rfl, -, -, rfl, rfl⟩ := Stmt.loop.inj hs
    have hdub := defUse_congr hc.dom hdu
    obtain ⟨-, hk1⟩ := run_sim' hvar hbool hF h1 hb hdub hc.storeWF
    have hres := loopRun_simAt hvar hbool hF h2 rfl (n := n) hb hloc σ₀ (hc.step hdu h1) hdu
    exact LoopRunResAt.iter hvar hbool hF hg hc hdu hloc.1 h1 (hk1 hloc.2) h2 hres
  | _, _, _, _, .loop_break _ h1, _, _, _, _, _, _, _, _, _, hloc, _, _, _ => by
    exact absurd (brun_exit_covered h1 hloc.1 _ _ rfl) (by simp)
end

mutual
/-- **A reach of a list, replayed by its output.** -/
private theorem reach_sim' (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F) (hF : allowed F) :
    ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)},
    BReach F ss σ evs → ∀ {ss' : PStmts P}, BlockRel ss ss' →
    Block.defUseWellFormed (fun x => (σ x).isSome) df ss = true → WellFormedStore σ F →
    ∃ evs', BReach F ss' σ evs' ∧ Trace.PreservesLastEvent (DropsInserts allowed) evs evs'
  | _, _, _, .here h, _, hr, hdu, hT => by
    cases hr with
    | cons hs _ =>
      simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
      obtain ⟨e, h', ha⟩ := reachS_sim hvar hbool hF h hs hdu.1 hT
      exact ⟨e, .here h', ha⟩
  | _, _, _, .later h1 h2, _, hr, hdu, hT => by
    cases hr with
    | cons hs hr =>
      have hdu' := defUse_rest h1 hdu
      obtain ⟨⟨e1, h1', ha1⟩, -⟩ := runS_sim hvar hbool hF h1 hs hdu'.1 hT
      obtain ⟨e2, h2', ha2⟩ := reach_sim' hvar hbool hF h2 hr hdu'.2 (brunS_typed h1 hT).1
      exact ⟨e1 ++ e2, .later h1' h2',
        Trace.PreservesLastEvent.append_left Trace.mayDropEvents_insertsTrueAssumes_append ha1 ha2
          (breach_ne_nil h2')⟩

/-- **A reach of a statement, replayed by its output.** -/
private theorem reachS_sim (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F) (hF : allowed F) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)},
    BReachS F s σ evs → ∀ {s' : PStmt P}, StmtRel s s' →
    Stmt.defUseWellFormed (fun x => (σ x).isSome) df s = true → WellFormedStore σ F →
    ∃ evs', BReachS F s' σ evs' ∧ Trace.PreservesLastEvent (DropsInserts allowed) evs evs'
  | _, _, evs, .cmd h hne, _, hr, _, _ => by
    cases hr
    obtain ⟨pre, e, he⟩ := (List.eq_nil_or_concat evs).resolve_left hne
    rw [List.concat_eq_append] at he
    subst he
    exact ⟨_, .cmd h hne, .inr ⟨pre, pre, e, rfl, rfl,
      Trace.mayDropEvents_insertsTrueAssumes_refl pre⟩⟩
  | _, _, _, .ite_true hc h, _, hr, hdu, hT => by
    cases hr with
    | ite ht _ =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      obtain ⟨e, h', ha⟩ := reach_sim' hvar hbool hF h ht hdu.1.2 hT
      exact ⟨e, .ite_true hc h', ha⟩
  | _, _, _, .ite_false hc h, _, hr, hdu, hT => by
    cases hr with
    | ite _ he =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      obtain ⟨e, h', ha⟩ := reach_sim' hvar hbool hF h he hdu.2 hT
      exact ⟨e, .ite_false hc h', ha⟩
  | _, _, _, .ite_nondet_true h, _, hr, hdu, hT => by
    cases hr with
    | ite ht _ =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      obtain ⟨e, h', ha⟩ := reach_sim' hvar hbool hF h ht hdu.1.2 hT
      exact ⟨e, .ite_nondet_true h', ha⟩
  | _, _, _, .ite_nondet_false h, _, hr, hdu, hT => by
    cases hr with
    | ite _ he =>
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      obtain ⟨e, h', ha⟩ := reach_sim' hvar hbool hF h he hdu.2 hT
      exact ⟨e, .ite_nondet_false h', ha⟩
  | _, _, _, .block h, _, hr, hdu, hT => by
    cases hr with
    | block hb =>
      simp only [Stmt.defUseWellFormed] at hdu
      obtain ⟨e, h', ha⟩ := reach_sim' hvar hbool hF h hb hdu hT
      exact ⟨e, .block h', ha⟩
  | _, σ, _, .loop_here hg h, _, hr, hdu, hT => by
    obtain ⟨n, body', hb, -, rfl⟩ := hr.loop_inv
    have hdub := defUse_loop_body hdu
    obtain ⟨e, h', ha⟩ := reach_sim' hvar hbool hF h hb hdub hT
    exact LoopReachRes.ite
      (LoopReachRes.here hvar hF hg (Compat.refl (Block.carriedVars (C := CmdExt P) _) hT) hdub
        h' ha)
  | _, σ, _, .loop_later (body := body) hg h1 h2, _, hr, hdu, hT => by
    obtain ⟨n, body', hb, hl, rfl⟩ := hr.loop_inv
    have hdub := defUse_loop_body hdu
    have hc := Compat.refl (Block.carriedVars body) hT
    exact LoopReachRes.ite (LoopReachRes.later hg
      (loopReach_sim hvar hbool hF h2 rfl hb hl σ (hc.step hdub h1) hdub))

/-- **A reach of a loop from the start of an iteration, replayed in the encoding of the loop
    entered from `σ₀`.** -/
private theorem loopReach_sim (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F) (hF : allowed F) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)},
    BReachS F s σ evs → ∀ {g : ExprOrNondet P} {m : Option P.Expr}
    {inv : List (String × P.Expr)} {body : PStmts P} {md : MetaData P},
    s = .loop g m inv body md → ∀ {n : String} {body' : PStmts P}, BlockRel body body' →
    (∀ l ∈ Block.labels body, l.startsWith Core.loopElimPrefix = Bool.false) →
    ∀ σ₀, Compat F (Block.carriedVars body) σ₀ σ →
    Block.defUseWellFormed (fun x => (σ₀ x).isSome) df body = true →
    LoopReachRes F allowed n g body body' md σ₀ σ evs
  | _, _, _, .loop_here hg h, _, _, _, _, _, hs, _, _, hb, _, σ₀, hc, hdu => by
    obtain ⟨rfl, -, -, rfl, rfl⟩ := Stmt.loop.inj hs
    obtain ⟨e, h', ha⟩ := reach_sim' hvar hbool hF h hb (defUse_congr hc.dom hdu) hc.storeWF
    exact LoopReachRes.here hvar hF hg hc hdu h' ha
  | _, _, _, .loop_later hg h1 h2, _, _, _, _, _, hs, _, _, hb, hl, σ₀, hc, hdu => by
    obtain ⟨rfl, -, -, rfl, rfl⟩ := Stmt.loop.inj hs
    exact LoopReachRes.later hg
      (loopReach_sim hvar hbool hF h2 hs hb hl σ₀ (hc.step hdu h1) hdu)
end

/-- **A run of a list, replayed by its output.**  If `ss'` is `ss` with its loops eliminated
    (`BlockRel`), `ss` is def-use well formed from `σ` and `σ` holds only values, every run
    of `ss` from `σ` has a run of `ss'` from `σ` with the same outcome whose trace is the
    source's with some events dropped (`Trace.MayDropEvents`) and assumptions inserted that
    evaluate to `true` under `F`, an `allowed` factory (`Trace.InsertsTrueAssumes`), for a
    factory whose evaluator reads variables from the store and respects negation. -/
theorem run_sim (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F) (hF : allowed F)
    {ss ss' : PStmts P} (hr : BlockRel ss ss') {σ : SemanticStore P}
    (hdu : Block.defUseWellFormed (fun x => (σ x).isSome) df ss = true) (hT : WellFormedStore σ F)
    {evs : List (Event P)} {o : Outcome P} (h : BRun F ss σ evs o) :
    ∃ evs', BRun F ss' σ evs' o ∧
      RComp Trace.MayDropEvents (Trace.InsertsTrueAssumes allowed) evs evs' :=
  (run_sim' hvar hbool hF h hr hdu hT).1

/-- **A run of a list without escaping exits, replayed by its output at any event.**  Under the
    premises of `run_sim`, if no loop iteration of `ss` leaves its loop by an `exit`
    (`Block.loopExitsLocal`), then for every run of `ss` from `σ` and every event `e` of its
    trace, with `pre` before it and `post` after it, a run of `ss'` from `σ` with the same
    outcome has `e` in its trace after events related to `pre` and before events related to
    `post` by dropping events and inserting true assumptions. -/
theorem run_sim_at (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F) (hF : allowed F)
    {ss ss' : PStmts P} (hr : BlockRel ss ss') (hloc : Block.loopExitsLocal ss)
    {σ : SemanticStore P}
    (hdu : Block.defUseWellFormed (fun x => (σ x).isSome) df ss = true) (hT : WellFormedStore σ F)
    {evs : List (Event P)} {o : Outcome P} (h : BRun F ss σ evs o)
    {pre : List (Event P)} {e : Event P} {post : List (Event P)} (hpos : evs = pre ++ e :: post) :
    ∃ pre' post', BRun F ss' σ (pre' ++ e :: post') o ∧
      RComp Trace.MayDropEvents (Trace.InsertsTrueAssumes allowed) pre pre' ∧
      RComp Trace.MayDropEvents (Trace.InsertsTrueAssumes allowed) post post' :=
  (run_sim' hvar hbool hF h hr hdu hT).2 hloc pre e post hpos

/-- **A run of a list without escaping exits, replayed by its output reflecting assertion
    validity.**  Under the premises of `run_sim_at`, for an interpretation `I` under which every
    condition that evaluates to `true` under an `allowed` factory holds, every run of `ss` from
    `σ` has a run of `ss'` from `σ` with the same outcome, its trace related to the source's as
    in `run_sim`, whose assertions are all valid under `I` only if those of the source are: when
    an assertion of the source fails, the run of `ss'` keeping it (`run_sim_at`) fails it too. -/
theorem run_sim_valid {I : ConditionInterp P} (htrue : I.TrueStutterHolds allowed)
    (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F) (hF : allowed F)
    {ss ss' : PStmts P} (hr : BlockRel ss ss') (hloc : Block.loopExitsLocal ss)
    {σ : SemanticStore P}
    (hdu : Block.defUseWellFormed (fun x => (σ x).isSome) df ss = true) (hT : WellFormedStore σ F)
    {evs : List (Event P)} {o : Outcome P} (h : BRun F ss σ evs o) :
    ∃ evs', BRun F ss' σ evs' o ∧
      RComp Trace.MayDropEvents (Trace.InsertsTrueAssumes allowed) evs evs' ∧
      (Trace.AssertionsValid P I evs' → Trace.AssertionsValid P I evs) := by
  by_cases hv : Trace.AssertionsValid P I evs
  · obtain ⟨evs', hb, ha⟩ := run_sim hvar hbool hF hr hdu hT h
    exact ⟨evs', hb, ha, fun _ => hv⟩
  · have hfail := hv
    rw [Trace.AssertionsValid_iff_occurrences] at hfail
    simp only [Classical.not_forall] at hfail
    obtain ⟨pre, c, post, hpos, w, hw, hc⟩ := hfail
    obtain ⟨pre', post', hb, hpre, hpost⟩ := run_sim_at hvar hbool hF hr hloc hdu hT h hpos
    refine ⟨_, hb, ?_, fun hv' => ?_⟩
    · subst hpos
      simpa using Trace.mayDropEvents_insertsTrueAssumes_append hpre
        (Trace.mayDropEvents_insertsTrueAssumes_append
          (Trace.mayDropEvents_insertsTrueAssumes_refl [.assert c]) hpost)
    · rw [Trace.AssertionsValid_iff_occurrences] at hv'
      exact absurd (hv' pre' c post' rfl w
        (Trace.mayDropEvents_insertsTrueAssumes_assumptionsHold htrue hpre hw)) hc

/-- **A reach of a list, replayed by its output.**  Under the premises of `run_sim`, every reach
    of `ss` from `σ` has a reach of `ss'` from `σ` whose trace ends with the same event, after
    events related to those before it in the source by dropping events and inserting true
    assumptions (`Trace.PreservesLastEvent`). -/
theorem reach_sim (hvar : WellFormedSemanticEvalVar (P := P) F)
    (hbool : WellFormedSemanticEvalBool (P := P) F) (hF : allowed F)
    {ss ss' : PStmts P} (hr : BlockRel ss ss') {σ : SemanticStore P}
    (hdu : Block.defUseWellFormed (fun x => (σ x).isSome) df ss = true) (hT : WellFormedStore σ F)
    {evs : List (Event P)} (h : BReach F ss σ evs) :
    ∃ evs', BReach F ss' σ evs' ∧
      Trace.PreservesLastEvent (RComp Trace.MayDropEvents (Trace.InsertsTrueAssumes allowed))
        evs evs' :=
  reach_sim' hvar hbool hF h hr hdu hT

end -- public section

end LoopElim
end Imperative
