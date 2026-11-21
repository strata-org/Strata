/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.CommonSubexprElimProps
public import Strata.DL.Imperative.BigStep.Adequacy
public import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.Denote.LExprDenoteProps
public import Strata.Languages.Core.ProgramFactProps
import all Strata.Transform.CommonSubexprElimProps
import all Strata.Transform.CommonSubexprElim
import all Strata.Languages.Core.Statement
import all Strata.DL.Imperative.Stmt
import all Strata.Languages.Core.PipelinePhase
import Strata.DL.Imperative.StmtSemanticsProps

/-! # Common subexpression elimination keeps failures

Under the reference event semantics, the output of `stmtRunCSESinglePass` fails where its
input fails, and only there, with conditions that unfold to the input's
(`stmtRunCSESinglePass_failures`, `CSEFailures`); so does each body the pipeline phase
rewrites (`commonSubexprElimPhase_failures`).

A body without `init`, `set` or loop never changes its store, so a run of the rewritten body
follows a run of the input step by step, from the store extended by the declarations
(`sim_list`, `fails_of_sim`). There a rewritten condition has the value of the original, by a
substitution law for evaluation (`LExpr.denoteEval_substFvarsBy_eval`, `eval_declStores`). The
declarations run when the input's typed subterms evaluate (`declRun_build`, `reach_inits`);
a reach of the output runs them first (`reach_inits_inv`).

TODO: state the top-level result as `OverapproximatesTracesUptoWhen` (and its converse)
of `Strata/Transform/Specification.lean` over `EventLang.coreBlock`, with an event relation
that relates assertion events whose conditions agree once the generated declarations are
inlined, as `DeadDefElimCoreCorrect` does, so that it composes with the other passes. -/

namespace Core.CSE

open Lambda Imperative Imperative.BigStep

/-! ## Statements with related expressions -/

/-- A statement mapped to a command is a command. -/
private theorem smap_cmd_inv {g : Expression.Expr → Expression.Expr} {t : Statement} {c : Command}
    (h : Statement.mapExprs g t = .cmd c) : ∃ c', t = .cmd c' ∧ Command.mapExpr g c' = c := by
  cases t with
  | cmd c' => exact ⟨c', rfl, by simpa [Statement.mapExprs, Stmt.mapExpr] using h⟩
  | ite cnd => cases cnd <;> simp [Statement.mapExprs, Stmt.mapExpr] at h
  | loop gd => cases gd <;> simp [Statement.mapExprs, Stmt.mapExpr] at h
  | _ => simp [Statement.mapExprs, Stmt.mapExpr] at h

/-- A command mapped to an assertion is an assertion. -/
private theorem cmap_assert_inv {g : Expression.Expr → Expression.Expr} {c : Command} {l : String}
    {x : Expression.Expr} {md : MetaData Expression}
    (h : Command.mapExpr g c = .cmd (.assert l x md)) :
    ∃ e, c = .cmd (.assert l e md) ∧ g e = x := by
  cases c with
  | cmd c =>
    cases c with
    | assert l' e md' =>
      simp only [Command.mapExpr, CmdExt.cmd.injEq, Cmd.assert.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨e, rfl, rfl⟩
    | init n ty e md' => cases e <;> simp [Command.mapExpr] at h
    | set n e md' => cases e <;> simp [Command.mapExpr] at h
    | _ => simp [Command.mapExpr] at h
  | call => simp [Command.mapExpr] at h

/-- A command mapped to an assumption is an assumption. -/
private theorem cmap_assume_inv {g : Expression.Expr → Expression.Expr} {c : Command} {l : String}
    {x : Expression.Expr} {md : MetaData Expression}
    (h : Command.mapExpr g c = .cmd (.assume l x md)) :
    ∃ e, c = .cmd (.assume l e md) ∧ g e = x := by
  cases c with
  | cmd c =>
    cases c with
    | assume l' e md' =>
      simp only [Command.mapExpr, CmdExt.cmd.injEq, Cmd.assume.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨e, rfl, rfl⟩
    | init n ty e md' => cases e <;> simp [Command.mapExpr] at h
    | set n e md' => cases e <;> simp [Command.mapExpr] at h
    | _ => simp [Command.mapExpr] at h
  | call => simp [Command.mapExpr] at h

/-- A command mapped to a cover is a cover. -/
private theorem cmap_cover_inv {g : Expression.Expr → Expression.Expr} {c : Command} {l : String}
    {x : Expression.Expr} {md : MetaData Expression}
    (h : Command.mapExpr g c = .cmd (.cover l x md)) :
    ∃ e, c = .cmd (.cover l e md) ∧ g e = x := by
  cases c with
  | cmd c =>
    cases c with
    | cover l' e md' =>
      simp only [Command.mapExpr, CmdExt.cmd.injEq, Cmd.cover.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨e, rfl, rfl⟩
    | init n ty e md' => cases e <;> simp [Command.mapExpr] at h
    | set n e md' => cases e <;> simp [Command.mapExpr] at h
    | _ => simp [Command.mapExpr] at h
  | call => simp [Command.mapExpr] at h

/-- A statement mapped to a deterministic `ite` is one. -/
private theorem smap_ite_inv {g : Expression.Expr → Expression.Expr} {t : Statement} {x : Expression.Expr}
    {A B : List Statement} {md : MetaData Expression}
    (h : Statement.mapExprs g t = .ite (.det x) A B md) :
    ∃ c tt et, t = .ite (.det c) tt et md ∧ g c = x ∧
      Statements.mapExprs g tt = A ∧ Statements.mapExprs g et = B := by
  cases t with
  | ite cnd tt et md' =>
    cases cnd with
    | det c =>
      simp only [Statement.mapExprs, Stmt.mapExpr, Stmt.ite.injEq, ExprOrNondet.det.injEq] at h
      obtain ⟨rfl, h1, h2, rfl⟩ := h
      exact ⟨c, tt, et, rfl, rfl, by rw [mapExprs_eq_block]; exact h1,
        by rw [mapExprs_eq_block]; exact h2⟩
    | nondet => simp [Statement.mapExprs, Stmt.mapExpr] at h
  | loop gd => cases gd <;> simp [Statement.mapExprs, Stmt.mapExpr] at h
  | _ => simp [Statement.mapExprs, Stmt.mapExpr] at h

/-- A statement mapped to a nondeterministic `ite` is one. -/
private theorem smap_ite_nondet_inv {g : Expression.Expr → Expression.Expr} {t : Statement}
    {A B : List Statement} {md : MetaData Expression}
    (h : Statement.mapExprs g t = .ite .nondet A B md) :
    ∃ tt et, t = .ite .nondet tt et md ∧
      Statements.mapExprs g tt = A ∧ Statements.mapExprs g et = B := by
  cases t with
  | ite cnd tt et md' =>
    cases cnd with
    | nondet =>
      simp only [Statement.mapExprs, Stmt.mapExpr, Stmt.ite.injEq, true_and] at h
      obtain ⟨h1, h2, rfl⟩ := h
      exact ⟨tt, et, rfl, by rw [mapExprs_eq_block]; exact h1, by rw [mapExprs_eq_block]; exact h2⟩
    | det c => simp [Statement.mapExprs, Stmt.mapExpr] at h
  | loop gd => cases gd <;> simp [Statement.mapExprs, Stmt.mapExpr] at h
  | _ => simp [Statement.mapExprs, Stmt.mapExpr] at h

/-- A statement mapped to a block is a block. -/
private theorem smap_block_inv {g : Expression.Expr → Expression.Expr} {t : Statement} {l : String}
    {A : List Statement} {md : MetaData Expression}
    (h : Statement.mapExprs g t = .block l A md) :
    ∃ tt, t = .block l tt md ∧ Statements.mapExprs g tt = A := by
  cases t with
  | block l' tt md' =>
    simp only [Statement.mapExprs, Stmt.mapExpr, Stmt.block.injEq] at h
    obtain ⟨rfl, h1, rfl⟩ := h
    exact ⟨tt, rfl, by rw [mapExprs_eq_block]; exact h1⟩
  | ite cnd => cases cnd <;> simp [Statement.mapExprs, Stmt.mapExpr] at h
  | loop gd => cases gd <;> simp [Statement.mapExprs, Stmt.mapExpr] at h
  | _ => simp [Statement.mapExprs, Stmt.mapExpr] at h

/-- A statement mapped to an `exit` is that `exit`. -/
private theorem smap_exit_inv {g : Expression.Expr → Expression.Expr} {t : Statement} {l : String}
    {md : MetaData Expression} (h : Statement.mapExprs g t = .exit l md) : t = .exit l md := by
  cases t with
  | exit l' md' => simpa [Statement.mapExprs, Stmt.mapExpr] using h
  | ite cnd => cases cnd <;> simp [Statement.mapExprs, Stmt.mapExpr] at h
  | loop gd => cases gd <;> simp [Statement.mapExprs, Stmt.mapExpr] at h
  | _ => simp [Statement.mapExprs, Stmt.mapExpr] at h

/-- A statement mapped to a type declaration is that declaration. -/
private theorem smap_typeDecl_inv {g : Expression.Expr → Expression.Expr} {t : Statement}
    {tc : TypeConstructor} {md : MetaData Expression}
    (h : Statement.mapExprs g t = .typeDecl tc md) : t = .typeDecl tc md := by
  cases t with
  | typeDecl tc' md' => simpa [Statement.mapExprs, Stmt.mapExpr] using h
  | ite cnd => cases cnd <;> simp [Statement.mapExprs, Stmt.mapExpr] at h
  | loop gd => cases gd <;> simp [Statement.mapExprs, Stmt.mapExpr] at h
  | _ => simp [Statement.mapExprs, Stmt.mapExpr] at h

/-- A statement that is not an `init`, a `set` or a loop. -/
private def Quiet (s : Statement) : Bool :=
  Statement.isNotInit s && Statement.isNotReassignment s && Stmt.isNotLoop s

section Sim
variable (F : Expression.Factory) (σa σb : SemanticStore Expression)
  (f g : Expression.Expr → Expression.Expr)

/-- Two events correspond: the same kind, label and metadata, the factory `F`, the stores
    `σa` and `σb`, and conditions with equal images under `f` and `g`. -/
private def EvC : Event Expression → Event Expression → Prop
  | .assert a, .assert b | .assume a, .assume b | .cover a, .cover b =>
    a.factory = F ∧ b.factory = F ∧ a.label = b.label ∧ a.metadata = b.metadata ∧ a.store = σa ∧
      b.store = σb ∧ f a.expr = g b.expr
  | _, _ => False

/-- Two outcomes correspond: both normal, or both an exit with the same label, at the stores
    `σa` and `σb`. -/
private def OutC (o o' : Outcome Expression) : Prop :=
  (o = .normal σa ∧ o' = .normal σb) ∨ ∃ l, o = .exit l σa ∧ o' = .exit l σb

/-- What a list keeps when run from `σa` against a related list run from `σb`. -/
private def SimL (ss tt : Statements) : Prop :=
  (∀ evs o, BRun F ss σa evs o → ∃ evs' o', BRun F tt σb evs' o' ∧
      List.Rel₂ (EvC F σa σb f g) evs evs' ∧ OutC σa σb o o') ∧
    (∀ evs, BReach F ss σa evs → ∃ evs', BReach F tt σb evs' ∧ List.Rel₂ (EvC F σa σb f g) evs evs')

/-- What a statement keeps when run from `σa` against a related statement run from `σb`. -/
private def SimS (s t : Statement) : Prop :=
  (∀ evs o, BRunS F s σa evs o → ∃ evs' o', BRunS F t σb evs' o' ∧
      List.Rel₂ (EvC F σa σb f g) evs evs' ∧ OutC σa σb o o') ∧
    (∀ evs, BReachS F s σa evs → ∃ evs', BReachS F t σb evs' ∧ List.Rel₂ (EvC F σa σb f g) evs evs')

/-- Corresponding traces appended correspond. -/
private theorem rel₂_append' {R : Event Expression → Event Expression → Prop} {a a' b b' : List (Event Expression)}
    (ha : List.Rel₂ R a a') (hb : List.Rel₂ R b b') : List.Rel₂ R (a ++ b) (a' ++ b') := by
  induction ha with
  | nil => exact hb
  | cons h _ ih => exact .cons h ih

/-- Leaving a scope keeps corresponding outcomes. -/
private theorem OutC.proj {o o' : Outcome Expression} (h : OutC σa σb o o') :
    OutC σa σb (o.proj σa) (o'.proj σb) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨l, rfl, rfl⟩
  · left; simp [Outcome.proj, projectStore_self]
  · right; exact ⟨l, by simp [Outcome.proj, projectStore_self]⟩

/-- Leaving a block keeps corresponding outcomes. -/
private theorem OutC.block {o o' : Outcome Expression} (l : String) (h : OutC σa σb o o') :
    OutC σa σb (o.block l σa) (o'.block l σb) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨l', rfl, rfl⟩
  · left; simp [Outcome.block, projectStore_self]
  · by_cases hl : l' = l
    · left; simp [Outcome.block, projectStore_self, hl]
    · right; exact ⟨l', by simp [Outcome.block, projectStore_self, hl]⟩

end Sim

section Sim2
variable {F : Expression.Factory} {σa σb : SemanticStore Expression}
  {f g : Expression.Expr → Expression.Expr}

/-- A command that is neither an `init` nor a `set`: an assertion, an assumption, a cover or
    a call. -/
private theorem cmd_cases {c : Command} (hq : Quiet (.cmd c) = true) :
    (∃ l e md, c = .cmd (.assert l e md)) ∨ (∃ l e md, c = .cmd (.assume l e md)) ∨
      (∃ l e md, c = .cmd (.cover l e md)) ∨ (∃ p ty a md, c = .call p ty a md) := by
  cases c with
  | cmd c =>
    cases c with
    | assert l e md => exact .inl ⟨l, e, md, rfl⟩
    | assume l e md => exact .inr (.inl ⟨l, e, md, rfl⟩)
    | cover l e md => exact .inr (.inr (.inl ⟨l, e, md, rfl⟩))
    | _ => simp [Quiet, Statement.isNotInit, Statement.isNotReassignment] at hq
  | call p ty a md => exact .inr (.inr (.inr ⟨p, ty, a, md, rfl⟩))

/-- **A command keeps its runs and reaches** against a related command. -/
private theorem sim_cmd (hc : ∀ a b, f a = g b → Expression.eval F σa a = Expression.eval F σb b)
    {c : Command} {t : Statement} (hq : Quiet (.cmd c) = true)
    (hm : Statement.mapExprs f (.cmd c) = Statement.mapExprs g t) : SimS F σa σb f g (.cmd c) t := by
  have key : ∀ evs σ', EvalE F σa c σ' evs → σ' = σa ∧ evs ≠ [] ∧ ∃ evs', BRunS F t σb evs' (.normal σb) ∧
      evs' ≠ [] ∧ (∃ c', t = .cmd c' ∧ EvalE F σb c' σb evs') ∧ List.Rel₂ (EvC F σa σb f g) evs evs' := by
    intro evs σ' he
    have hm' : Statement.mapExprs g t = .cmd (Command.mapExpr f c) := by
      rw [← hm]; simp only [Statement.mapExprs, Stmt.mapExpr]
    obtain ⟨c', rfl, hc'⟩ := smap_cmd_inv hm'
    rcases cmd_cases hq with ⟨l, e, md, rfl⟩ | ⟨l, e, md, rfl⟩ | ⟨l, e, md, rfl⟩ | ⟨p, ty, a, md, rfl⟩
    · obtain ⟨e', rfl, he'⟩ := cmap_assert_inv (l := l) (x := f e) (md := md)
        (hc'.trans (by simp only [Command.mapExpr]))
      cases he
      refine ⟨rfl, by simp, _, .cmd (c := .cmd (.assert l e' md)) .eval_assert, by simp, ⟨_, rfl, .eval_assert⟩,
        .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, he'.symm⟩ .nil⟩
    · obtain ⟨e', rfl, he'⟩ := cmap_assume_inv (l := l) (x := f e) (md := md)
        (hc'.trans (by simp only [Command.mapExpr]))
      cases he
      refine ⟨rfl, by simp, _, .cmd (c := .cmd (.assume l e' md)) .eval_assume, by simp, ⟨_, rfl, .eval_assume⟩,
        .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, he'.symm⟩ .nil⟩
    · obtain ⟨e', rfl, he'⟩ := cmap_cover_inv (l := l) (x := f e) (md := md)
        (hc'.trans (by simp only [Command.mapExpr]))
      cases he
      refine ⟨rfl, by simp, _, .cmd (c := .cmd (.cover l e' md)) .eval_cover, by simp, ⟨_, rfl, .eval_cover⟩,
        .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, he'.symm⟩ .nil⟩
    · exact absurd he (by simp [EvalE])
  refine ⟨fun evs o h => ?_, fun evs h => ?_⟩
  · cases h with
    | cmd he =>
      obtain ⟨rfl, -, evs', hr, -, -, hrel⟩ := key evs _ he
      exact ⟨evs', _, hr, hrel, .inl ⟨rfl, rfl⟩⟩
  · cases h with
    | cmd he hne =>
      obtain ⟨-, -, evs', -, hne', ⟨c', rfl, he'⟩, hrel⟩ := key evs _ he
      exact ⟨evs', .cmd he' hne', hrel⟩

end Sim2

section Sim3
variable {F : Expression.Factory} {σa σb : SemanticStore Expression}
  {f g : Expression.Expr → Expression.Expr}

/-- The mapped form of a deterministic `ite`. -/
private theorem smap_ite (f : Expression.Expr → Expression.Expr) (c : Expression.Expr) (tss ess : Statements)
    (md : MetaData Expression) :
    Statement.mapExprs f (.ite (.det c) tss ess md) =
      .ite (.det (f c)) (Statements.mapExprs f tss) (Statements.mapExprs f ess) md := by
  rw [mapExprs_eq_block, mapExprs_eq_block]; simp only [Statement.mapExprs, Stmt.mapExpr]

/-- The mapped form of a nondeterministic `ite`. -/
private theorem smap_ite_nondet (f : Expression.Expr → Expression.Expr) (tss ess : Statements)
    (md : MetaData Expression) :
    Statement.mapExprs f (.ite .nondet tss ess md) =
      .ite .nondet (Statements.mapExprs f tss) (Statements.mapExprs f ess) md := by
  rw [mapExprs_eq_block, mapExprs_eq_block]; simp only [Statement.mapExprs, Stmt.mapExpr]

/-- The mapped form of a block. -/
private theorem smap_block (f : Expression.Expr → Expression.Expr) (l : String) (ss : Statements)
    (md : MetaData Expression) :
    Statement.mapExprs f (.block l ss md) = .block l (Statements.mapExprs f ss) md := by
  rw [mapExprs_eq_block]; simp only [Statement.mapExprs, Stmt.mapExpr]

mutual
/-- **A list keeps its runs and reaches** against a related list, when it has no `init`, `set`
    or loop and related conditions evaluate alike in `σa` and `σb`. -/
private theorem sim_list (hc : ∀ a b, f a = g b → Expression.eval F σa a = Expression.eval F σb b) :
    ∀ (ss tt : Statements), Block.allSubstmts Quiet ss = true →
    Statements.mapExprs f ss = Statements.mapExprs g tt → SimL F σa σb f g ss tt
  | [], tt, _, hm => by
    have htt : tt = [] := by
      have : Statements.mapExprs g tt = [] := hm.symm
      simpa [Statements.mapExprs] using this
    subst htt
    refine ⟨fun evs o h => ?_, fun evs h => by cases h⟩
    cases h
    exact ⟨[], _, .nil, .nil, .inl ⟨rfl, rfl⟩⟩
  | s :: ss, tt, hq, hm => by
    simp only [Block.allSubstmts, Bool.and_eq_true] at hq
    obtain ⟨t, tt', rfl, hm1, hm2⟩ : ∃ t tt', tt = t :: tt' ∧
        Statement.mapExprs f s = Statement.mapExprs g t ∧
        Statements.mapExprs f ss = Statements.mapExprs g tt' := by
      cases tt with
      | nil => simp [Statements.mapExprs] at hm
      | cons t tt' =>
        simp only [Statements.mapExprs, List.map_cons, List.cons.injEq] at hm
        exact ⟨t, tt', rfl, hm.1, hm.2⟩
    have h1 := sim_one hc s t hq.1 hm1
    have h2 := sim_list hc ss tt' hq.2 hm2
    refine ⟨fun evs o h => ?_, fun evs h => ?_⟩
    · cases h with
      | cons_normal hs hr =>
        obtain ⟨e1, o1, hs', hrel1, ho1⟩ := h1.1 _ _ hs
        rcases ho1 with ⟨ho, rfl⟩ | ⟨l, ho, -⟩
        · cases ho
          obtain ⟨e2, o2, hr', hrel2, ho2⟩ := h2.1 _ _ hr
          exact ⟨_, _, .cons_normal hs' hr', rel₂_append' hrel1 hrel2, ho2⟩
        · cases ho
      | cons_exit hs =>
        obtain ⟨e1, o1, hs', hrel1, ho1⟩ := h1.1 _ _ hs
        rcases ho1 with ⟨ho, -⟩ | ⟨l, ho, rfl⟩
        · cases ho
        · cases ho
          exact ⟨_, _, .cons_exit hs', hrel1, .inr ⟨_, rfl, rfl⟩⟩
    · cases h with
      | here hs =>
        obtain ⟨e1, hs', hrel⟩ := h1.2 _ hs
        exact ⟨_, .here hs', hrel⟩
      | later hs hr =>
        obtain ⟨e1, o1, hs', hrel1, ho1⟩ := h1.1 _ _ hs
        rcases ho1 with ⟨ho, rfl⟩ | ⟨l, ho, -⟩
        · cases ho
          obtain ⟨e2, hr', hrel2⟩ := h2.2 _ hr
          exact ⟨_, .later hs' hr', rel₂_append' hrel1 hrel2⟩
        · cases ho

/-- **A statement keeps its runs and reaches** against a related statement, when it has no
    `init`, `set` or loop and related conditions evaluate alike in `σa` and `σb`. -/
private theorem sim_one (hc : ∀ a b, f a = g b → Expression.eval F σa a = Expression.eval F σb b) :
    ∀ (s t : Statement), Stmt.allSubstmts Quiet s = true →
    Statement.mapExprs f s = Statement.mapExprs g t → SimS F σa σb f g s t
  | .cmd c, t, hq, hm => by
    simp only [Stmt.allSubstmts, Bool.and_true] at hq
    exact sim_cmd hc hq hm
  | .ite (.det c) tss ess md, t, hq, hm => by
    simp only [Stmt.allSubstmts, Bool.and_eq_true] at hq
    rw [smap_ite] at hm
    obtain ⟨c', tts, ets, rfl, hgc, h1, h2⟩ := smap_ite_inv hm.symm
    have st := sim_list hc tss tts hq.2.1 h1.symm
    have se := sim_list hc ess ets hq.2.2 h2.symm
    have hcc : Expression.eval F σb c' = Expression.eval F σa c := (hc c c' hgc.symm).symm
    refine ⟨fun evs o h => ?_, fun evs h => ?_⟩
    · cases h with
      | ite_true hv hr =>
        obtain ⟨e1, o1, hr', hrel, ho⟩ := st.1 _ _ hr
        exact ⟨_, _, .ite_true (hcc.trans hv) hr', hrel, OutC.proj σa σb ho⟩
      | ite_false hv hr =>
        obtain ⟨e1, o1, hr', hrel, ho⟩ := se.1 _ _ hr
        exact ⟨_, _, .ite_false (hcc.trans hv) hr', hrel, OutC.proj σa σb ho⟩
    · cases h with
      | ite_true hv hr =>
        obtain ⟨e1, hr', hrel⟩ := st.2 _ hr
        exact ⟨_, .ite_true (hcc.trans hv) hr', hrel⟩
      | ite_false hv hr =>
        obtain ⟨e1, hr', hrel⟩ := se.2 _ hr
        exact ⟨_, .ite_false (hcc.trans hv) hr', hrel⟩
  | .ite .nondet tss ess md, t, hq, hm => by
    simp only [Stmt.allSubstmts, Bool.and_eq_true] at hq
    rw [smap_ite_nondet] at hm
    obtain ⟨tts, ets, rfl, h1, h2⟩ := smap_ite_nondet_inv hm.symm
    have st := sim_list hc tss tts hq.2.1 h1.symm
    have se := sim_list hc ess ets hq.2.2 h2.symm
    refine ⟨fun evs o h => ?_, fun evs h => ?_⟩
    · cases h with
      | ite_nondet_true hr =>
        obtain ⟨e1, o1, hr', hrel, ho⟩ := st.1 _ _ hr
        exact ⟨_, _, .ite_nondet_true hr', hrel, OutC.proj σa σb ho⟩
      | ite_nondet_false hr =>
        obtain ⟨e1, o1, hr', hrel, ho⟩ := se.1 _ _ hr
        exact ⟨_, _, .ite_nondet_false hr', hrel, OutC.proj σa σb ho⟩
    · cases h with
      | ite_nondet_true hr =>
        obtain ⟨e1, hr', hrel⟩ := st.2 _ hr
        exact ⟨_, .ite_nondet_true hr', hrel⟩
      | ite_nondet_false hr =>
        obtain ⟨e1, hr', hrel⟩ := se.2 _ hr
        exact ⟨_, .ite_nondet_false hr', hrel⟩
  | .block l ss md, t, hq, hm => by
    simp only [Stmt.allSubstmts, Bool.and_eq_true] at hq
    rw [smap_block] at hm
    obtain ⟨tt, rfl, h1⟩ := smap_block_inv hm.symm
    have sb := sim_list hc ss tt hq.2 h1.symm
    refine ⟨fun evs o h => ?_, fun evs h => ?_⟩
    · cases h with
      | block hr =>
        obtain ⟨e1, o1, hr', hrel, ho⟩ := sb.1 _ _ hr
        exact ⟨_, _, .block hr', hrel, OutC.block σa σb l ho⟩
    · cases h with
      | block hr =>
        obtain ⟨e1, hr', hrel⟩ := sb.2 _ hr
        exact ⟨_, .block hr', hrel⟩
  | .exit l md, t, _, hm => by
    have ht : t = .exit l md := smap_exit_inv (by rw [← hm]; simp [Statement.mapExprs, Stmt.mapExpr])
    subst ht
    refine ⟨fun evs o h => ?_, fun evs h => by cases h⟩
    cases h
    exact ⟨[], _, .exit, .nil, .inr ⟨l, rfl, rfl⟩⟩
  | .typeDecl tc md, t, _, hm => by
    have ht : t = .typeDecl tc md :=
      smap_typeDecl_inv (by rw [← hm]; simp [Statement.mapExprs, Stmt.mapExpr])
    subst ht
    refine ⟨fun evs o h => ?_, fun evs h => by cases h⟩
    cases h
    exact ⟨[], _, .typeDecl, .nil, .inl ⟨rfl, rfl⟩⟩
  | .loop .., _, hq, _ => by simp [Stmt.allSubstmts, Quiet, Stmt.isNotLoop] at hq
end

end Sim3

section Fails
variable {F : Expression.Factory} {σa σb : SemanticStore Expression}
  {f g : Expression.Expr → Expression.Expr}

/-- Corresponding traces split as an appended one does. -/
private theorem rel₂_append_single {R : Event Expression → Event Expression → Prop}
    {a : List (Event Expression)} {x : Event Expression} {c : List (Event Expression)}
    (h : List.Rel₂ R (a ++ [x]) c) : ∃ c' y, c = c' ++ [y] ∧ List.Rel₂ R a c' ∧ R x y := by
  induction a generalizing c with
  | nil =>
    cases h with
    | cons hx hr => cases hr; exact ⟨[], _, rfl, .nil, hx⟩
  | cons z a ih =>
    cases h with
    | cons hz hr =>
      obtain ⟨c', y, rfl, h1, h2⟩ := ih hr
      exact ⟨_ :: c', y, rfl, .cons hz h1, h2⟩

/-- An assumption of a corresponding trace corresponds to one of the trace. -/
private theorem rel₂_assume {evs evs' : List (Event Expression)}
    (h : List.Rel₂ (EvC F σa σb f g) evs evs') {b : EventArg Expression}
    (hb : Event.assume b ∈ evs') : ∃ a, Event.assume a ∈ evs ∧ EvC F σa σb f g (.assume a) (.assume b) := by
  induction h with
  | nil => simp at hb
  | @cons x y xs ys hxy _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · cases x with
      | assume a => exact ⟨a, by simp, hxy⟩
      | assert a => simp [EvC] at hxy
      | cover a => simp [EvC] at hxy
    · obtain ⟨a, ha, h⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

/-- **Failures carry over** between related lists without `init`, `set` or loops, when related
    conditions evaluate alike: a failure with the condition `e` becomes one with a condition
    `e'` such that `f e = g e'`. -/
private theorem fails_of_sim (hc : ∀ a b, f a = g b → Expression.eval F σa a = Expression.eval F σb b)
    {ss tt : Statements} (hq : Block.allSubstmts Quiet ss = true)
    (hm : Statements.mapExprs f ss = Statements.mapExprs g tt) {t : AssertId Expression}
    {e : Expression.Expr} (h : Fails F ss σa t e) : ∃ e', Fails F tt σb t e' ∧ f e = g e' := by
  obtain ⟨evs, ev, hr, has, hfa⟩ := h
  obtain ⟨evs'', hr', hrel⟩ := (sim_list hc ss tt hq hm).2 _ hr
  obtain ⟨evs', ev', rfl, hrel1, hrel2⟩ := rel₂_append_single hrel
  have has' : Trace.AssumptionsHold Expression evalInterp () evs' := by
    intro b hb
    obtain ⟨a, ha, hab⟩ := rel₂_assume hrel1 hb
    obtain ⟨hfa, hfb, -, -, hsa, hsb, hab⟩ := hab
    have hasa := has a ha
    change Expression.eval a.factory a.store a.expr = some (HasBool.ttVal a.factory) at hasa
    change Expression.eval b.factory b.store b.expr = some (HasBool.ttVal b.factory)
    rw [hfb, hsb, ← hc _ _ hab]
    rw [hfa, hsa] at hasa
    exact hasa
  cases ev with
  | assert a =>
    cases ev' with
    | assert b =>
      obtain ⟨hfa', hfb, hl, hmd, hsa, hsb, hab⟩ := hrel2
      obtain ⟨h1, h2, rfl, h4⟩ := hfa
      refine ⟨b.expr, ⟨evs', _, hr', has', ⟨hl ▸ h1, hmd ▸ h2, rfl, ?_⟩⟩, hab⟩
      rw [hfb, hsb, ← hc _ _ hab, ← hsa, ← hfa']; exact h4
    | _ => simp [EvC] at hrel2
  | cover a =>
    cases ev' with
    | cover b =>
      obtain ⟨hfa', hfb, hl, hmd, hsa, hsb, hab⟩ := hrel2
      obtain ⟨h1, h2, rfl, h4⟩ := hfa
      refine ⟨b.expr, ⟨evs', _, hr', has', ⟨hl ▸ h1, hmd ▸ h2, rfl, ?_⟩⟩, hab⟩
      rw [hfb, hsb, ← hc _ _ hab, ← hsa, ← hfa']; exact h4
    | _ => simp [EvC] at hrel2
  | assume a => exact absurd hfa (by simp [FailsAt])

end Fails

/-! ## Statements without writes -/

mutual
/-- A conjunction holds of every statement of a list when each conjunct does. -/
private theorem block_allSubstmts_and (p q : Statement → Bool) :
    ∀ ss : Statements, Block.allSubstmts p ss = true → Block.allSubstmts q ss = true →
      Block.allSubstmts (fun s => p s && q s) ss = true
  | [], _, _ => by simp [Block.allSubstmts]
  | s :: ss, hp, hq => by
    simp only [Block.allSubstmts, Bool.and_eq_true] at hp hq ⊢
    exact ⟨stmt_allSubstmts_and p q s hp.1 hq.1, block_allSubstmts_and p q ss hp.2 hq.2⟩

/-- A conjunction holds of every substatement when each conjunct does. -/
private theorem stmt_allSubstmts_and (p q : Statement → Bool) :
    ∀ s : Statement, Stmt.allSubstmts p s = true → Stmt.allSubstmts q s = true →
      Stmt.allSubstmts (fun s => p s && q s) s = true
  | .cmd c, hp, hq => by
    simp only [Stmt.allSubstmts, Bool.and_true] at hp hq ⊢; simp [hp, hq]
  | .exit l md, hp, hq => by
    simp only [Stmt.allSubstmts, Bool.and_true] at hp hq ⊢; simp [hp, hq]
  | .typeDecl tc md, hp, hq => by
    simp only [Stmt.allSubstmts, Bool.and_true] at hp hq ⊢; simp [hp, hq]
  | .block l ss md, hp, hq => by
    simp only [Stmt.allSubstmts, Bool.and_eq_true] at hp hq ⊢
    exact ⟨by simp [hp.1, hq.1], block_allSubstmts_and p q ss hp.2 hq.2⟩
  | .ite c tss ess md, hp, hq => by
    simp only [Stmt.allSubstmts, Bool.and_eq_true] at hp hq ⊢
    exact ⟨by simp [hp.1, hq.1], block_allSubstmts_and p q tss hp.2.1 hq.2.1,
      block_allSubstmts_and p q ess hp.2.2 hq.2.2⟩
  | .loop gd m inv body md, hp, hq => by
    simp only [Stmt.allSubstmts, Bool.and_eq_true] at hp hq ⊢
    exact ⟨by simp [hp.1, hq.1], block_allSubstmts_and p q body hp.2 hq.2⟩
end

/-- Mapping the expressions keeps what kind of statement each statement is. -/
private theorem quiet_mapExprs (f : Expression.Expr → Expression.Expr) (s : Statement) :
    Quiet (Statement.mapExprs f s) = Quiet s := by
  cases s with
  | cmd c =>
    cases c with
    | cmd c =>
      cases c with
      | init n ty e md => cases e <;> simp [Statement.mapExprs, Stmt.mapExpr, Command.mapExpr, Quiet, Statement.isNotInit,
        Statement.isNotReassignment, Stmt.isNotLoop]
      | set n e md => cases e <;> simp [Statement.mapExprs, Stmt.mapExpr, Command.mapExpr, Quiet, Statement.isNotInit,
        Statement.isNotReassignment, Stmt.isNotLoop]
      | _ => simp [Statement.mapExprs, Stmt.mapExpr, Command.mapExpr, Quiet, Statement.isNotInit,
        Statement.isNotReassignment, Stmt.isNotLoop]
    | call => simp [Statement.mapExprs, Stmt.mapExpr, Command.mapExpr, Quiet, Statement.isNotInit,
        Statement.isNotReassignment, Stmt.isNotLoop]
  | ite c => cases c <;> simp [Statement.mapExprs, Stmt.mapExpr, Quiet, Statement.isNotInit,
        Statement.isNotReassignment, Stmt.isNotLoop]
  | loop g => cases g <;> simp [Statement.mapExprs, Stmt.mapExpr, Quiet, Statement.isNotInit,
        Statement.isNotReassignment, Stmt.isNotLoop]
  | _ => simp [Statement.mapExprs, Stmt.mapExpr, Quiet, Statement.isNotInit,
        Statement.isNotReassignment, Stmt.isNotLoop]

mutual
/-- A list has no `init`, `set` or loop exactly when its mapped form has none. -/
private theorem block_quiet_mapExprs (f : Expression.Expr → Expression.Expr) :
    ∀ ss : Statements, Block.allSubstmts Quiet (Statements.mapExprs f ss) = Block.allSubstmts Quiet ss
  | [] => rfl
  | s :: ss => by
    show Block.allSubstmts Quiet (Statement.mapExprs f s :: Statements.mapExprs f ss) = _
    simp only [Block.allSubstmts]
    rw [stmt_quiet_mapExprs f s, block_quiet_mapExprs f ss]

/-- A statement has no `init`, `set` or loop exactly when its mapped form has none. -/
private theorem stmt_quiet_mapExprs (f : Expression.Expr → Expression.Expr) :
    ∀ s : Statement, Stmt.allSubstmts Quiet (Statement.mapExprs f s) = Stmt.allSubstmts Quiet s
  | .cmd c => by
    have hqc := quiet_mapExprs f (.cmd c)
    simp only [Statement.mapExprs, Stmt.mapExpr] at hqc ⊢
    simp only [Stmt.allSubstmts, hqc]
  | .exit l md => by simp only [Statement.mapExprs, Stmt.mapExpr]
  | .typeDecl tc md => by simp only [Statement.mapExprs, Stmt.mapExpr]
  | .block l ss md => by
    rw [smap_block]
    simp only [Stmt.allSubstmts]
    rw [block_quiet_mapExprs f ss]; rfl
  | .ite (.det c) tss ess md => by
    rw [smap_ite]
    simp only [Stmt.allSubstmts]
    rw [block_quiet_mapExprs f tss, block_quiet_mapExprs f ess]; rfl
  | .ite .nondet tss ess md => by
    rw [smap_ite_nondet]
    simp only [Stmt.allSubstmts]
    rw [block_quiet_mapExprs f tss, block_quiet_mapExprs f ess]; rfl
  | .loop gd m inv body md => by
    cases gd <;> simp [Statement.mapExprs, Stmt.mapExpr, Stmt.allSubstmts, Quiet, Stmt.isNotLoop]
end

/-! ## Running the declarations -/

/-- `σ` with `x` bound to `v`. -/
private def upd (σ : SemanticStore Expression) (x : Expression.Ident) (v : Expression.Val) :
    SemanticStore Expression :=
  fun y => if y = x then some v else σ y

/-- **Evaluating after a declaration** is evaluating the substitution of its right-hand side
    before it. -/
private theorem eval_upd (F : Expression.Factory) (σ : SemanticStore Expression) (x : Expression.Ident)
    (r : Expression.Expr) (v : Expression.Val) (hr : Expression.eval F σ r = some v)
    (e : Expression.Expr) :
    Expression.eval F (upd σ x v) e = Expression.eval F σ (LExpr.substFvar e x r) := by
  show LExpr.denoteEval F (upd σ x v) e = LExpr.denoteEval F σ (LExpr.substFvar e x r)
  rw [LExpr.substFvar_eq_substFvarsBy x r e]
  symm
  apply LExpr.denoteEval_substFvarsBy_eval
  · intro y ty r' _ hl
    by_cases h : y = x
    · subst h
      simp only [ite_true, Option.some.injEq] at hl
      subst hl
      exact ⟨v, by simp [upd], hr⟩
    · simp [h] at hl
  · intro y ty _ hl
    by_cases h : y = x
    · simp [h] at hl
    · simp [upd, h]

/-- The stores the declarations `ds` build from `σ` when each right-hand side evaluates. -/
private inductive DeclStores (F : Expression.Factory) : SemanticStore Expression → List Decl →
    SemanticStore Expression → Prop where
  | nil : DeclStores F σ [] σ
  | cons : Expression.eval F σ d.2.2 = some v → DeclStores F (upd σ (cseName d.1) v) ds σ' →
      DeclStores F σ (d :: ds) σ'

/-- **Evaluating after declarations** is evaluating their unfolding before them. -/
private theorem eval_declStores {F : Expression.Factory} {σ σ' : SemanticStore Expression}
    {ds : List Decl} (h : DeclStores F σ ds σ') (e : Expression.Expr) :
    Expression.eval F σ' e = Expression.eval F σ (unfold ds e) := by
  induction h generalizing e with
  | nil => rfl
  | @cons σ d v ds σ' hv _ ih =>
    rw [ih, eval_upd F σ _ _ v hv]
    rfl

/-- Declaration stores of an appended list. -/
private theorem DeclStores.append {F : Expression.Factory} {σ σ' : SemanticStore Expression}
    {ds : List Decl} (h : DeclStores F σ ds σ') {d : Decl} {v : Expression.Val}
    (hv : Expression.eval F σ' d.2.2 = some v) :
    DeclStores F σ (ds ++ [d]) (upd σ' (cseName d.1) v) := by
  induction h with
  | nil => exact .cons hv .nil
  | cons hv' _ ih => exact .cons hv' (ih hv)

/-- The stores the declarations `ds` build from `σ`, each right-hand side evaluating to a value
    of its type and each name unbound before its declaration. -/
private inductive DeclRun (F : Expression.Factory) : SemanticStore Expression → List Decl →
    SemanticStore Expression → Prop where
  | nil : DeclRun F σ [] σ
  | cons : Expression.eval F σ d.2.2 = some v → HasVal.valueOfTy F v (LTy.forAll [] d.2.1) →
      σ (cseName d.1) = none → DeclRun F (upd σ (cseName d.1) v) ds σ' → DeclRun F σ (d :: ds) σ'

/-- A run of the declarations builds their stores. -/
private theorem DeclRun.stores {F : Expression.Factory} {σ σ' : SemanticStore Expression} {ds : List Decl}
    (h : DeclRun F σ ds σ') : DeclStores F σ ds σ' := by
  induction h with
  | nil => exact .nil
  | cons hv _ _ _ ih => exact .cons hv ih

/-- Declaring a name binds it and nothing else. -/
private theorem initState_upd {σ σ' : SemanticStore Expression} {x : Expression.Ident} {v : Expression.Val}
    (h : InitState Expression σ x v σ') : σ' = upd σ x v := by
  cases h with
  | init h1 h2 h3 =>
    funext y
    by_cases hy : y = x
    · subst hy; simp [upd, h2]
    · simp [upd, hy, h3 y (Ne.symm hy)]

/-- **Reaching past the declarations.** A reach of declarations followed by `rest` runs the
    declarations, which emit nothing, and then reaches in `rest`. -/
private theorem reach_inits_inv {F : Expression.Factory} :
    ∀ (ds : List Decl) (rest : Statements) (σ : SemanticStore Expression) (evs : List (Event Expression)),
      BReach F (ds.map initOf ++ rest) σ evs → ∃ σ', DeclStores F σ ds σ' ∧ BReach F rest σ' evs := by
  intro ds
  induction ds with
  | nil => intro rest σ evs h; exact ⟨σ, .nil, h⟩
  | cons d ds ih =>
    intro rest σ evs h
    cases h with
    | here hs =>
      cases hs with
      | cmd he hne =>
        simp only [EvalE] at he
        cases he
        exact absurd rfl hne
    | later hs hr =>
      cases hs with
      | cmd he =>
        simp only [EvalE] at he
        cases he with
        | eval_init hv hinit _ _ =>
          rw [initState_upd hinit] at hr
          obtain ⟨σ', h1, h2⟩ := ih rest _ _ hr
          exact ⟨σ', .cons hv h1, by simpa using h2⟩

/-- **Running the declarations, then reaching.** -/
private theorem reach_inits {F : Expression.Factory} (hvar : WellFormedSemanticEvalVar (P := Expression) F)
    {σ σ' : SemanticStore Expression} {ds : List Decl} (h : DeclRun F σ ds σ') {rest : Statements}
    {evs : List (Event Expression)} (hr : BReach F rest σ' evs) :
    BReach F (ds.map initOf ++ rest) σ evs := by
  induction h with
  | nil => exact hr
  | @cons σ d v ds σ' hv hty hn _ ih =>
    have hreach := BReach.later (rest := ds.map initOf ++ rest)
      (BRunS.cmd (c := .cmd (.init (cseName d.1) (LTy.forAll [] d.2.1) (.det d.2.2) .empty))
        (σ' := upd σ (cseName d.1) v) (evs := [])
        (EvalCmdE.eval_init hv (.init hn (by simp [upd]) (fun y hy => by simp [upd, Ne.symm hy]))
          hty hvar)) (ih hr)
    simp only [List.nil_append] at hreach
    exact hreach

/-- The declarations change only the names they declare. -/
private theorem DeclStores.frame {F : Expression.Factory} {σ σ' : SemanticStore Expression}
    {ds : List Decl} (h : DeclStores F σ ds σ') (y : Expression.Ident)
    (hy : ∀ d ∈ ds, y ≠ cseName d.1) : σ' y = σ y := by
  induction h with
  | nil => rfl
  | @cons σ d v ds σ' _ _ ih =>
    rw [ih (fun d' hd' => hy d' (List.mem_cons_of_mem _ hd'))]
    simp [upd, hy d (by simp)]

/-- **The declarations run** from a store binding no generated name, when each one's
    unfolding evaluates to a value of its type. -/
private theorem declRun_build {F : Expression.Factory} {σ0 : SemanticStore Expression}
    (hσ0 : ∀ k, σ0 (cseName k) = none) :
    ∀ (ds pre : List Decl) (σi : SemanticStore Expression), DeclStores F σ0 pre σi →
      ((pre ++ ds).map (·.1)).Nodup →
      (∀ j (hj : j < ds.length), ∃ v, Expression.eval F σ0 (unfold (pre ++ ds.take j) ds[j].2.2) =
        some v ∧ HasVal.valueOfTy F v (LTy.forAll [] ds[j].2.1)) →
      ∃ σ', DeclRun F σi ds σ' := by
  intro ds
  induction ds with
  | nil => intro pre σi _ _ _; exact ⟨σi, .nil⟩
  | cons d ds ih =>
    intro pre σi hst hnd hev
    obtain ⟨v, hv, hty⟩ := hev 0 (by simp)
    simp only [List.take_zero, List.append_nil, List.getElem_cons_zero] at hv hty
    have hv' : Expression.eval F σi d.2.2 = some v := by rw [eval_declStores hst]; exact hv
    have hn : σi (cseName d.1) = none := by
      rw [hst.frame _ (fun d' hd' he => ?_)]
      · exact hσ0 _
      · have hname := cseName_inj he
        rw [List.map_append, List.nodup_append] at hnd
        exact hnd.2.2 d'.1 (List.mem_map.mpr ⟨d', hd', rfl⟩) d.1 (by simp) hname.symm
    obtain ⟨σ', hr⟩ := ih (pre ++ [d]) _ (hst.append hv') (by simpa using hnd) (fun j hj => by
      have := hev (j + 1) (by simp; omega)
      simpa using this)
    exact ⟨σ', .cons hv' hty hn hr⟩

/-! ## Failures of a well-formed output -/

/-- Unfolding a list splits at any point. -/
private theorem unfold_take_drop (j : Nat) (l : List Decl) (x : Expression.Expr) :
    unfold l x = unfold (l.take j) (unfold (l.drop j) x) := by
  conv => lhs; rw [← List.take_append_drop j l]
  rw [unfold, unfold, unfold, List.foldr_append]

public section

/-- Every subterm of `ss`'s expressions without bound variables that type checks at `ty`
    evaluates in `σ` to a value of type `ty`.

    TODO: derive this from a store that defines the body's variables at their annotated
    types, as evaluation is total on well-typed terms. The derivation needs the closed types
    to be ground; a body can type-check with a residual type variable (`function lm<a>() :
    Map int a;` used as `lm()[0]`), where this premise is false, although the SMT encoder
    rejects such a program. -/
def TypedSubtermsEvaluate (F : Expression.Factory) (σ : SemanticStore Expression)
    (ss : Statements) : Prop :=
  ∀ r ∈ Statements.collectExprs ss, ∀ c, IsSub c r → LExpr.hasBVar c = false →
    ∀ ty, LExpr.typeCheck [] c = some ty →
      ∃ v, Expression.eval F σ c = some v ∧ HasVal.valueOfTy F v (LTy.forAll [] ty)

/-- The failures of `ss` and `out` from `σ` correspond: `out` is declarations `ds` followed by
    a body, and, for every target, a failure of `ss` with the condition `e` is a failure of
    `out` with a condition `e'` that gives `e` back, up to locations, once the declarations are
    inlined (when the typed subterms of `ss` evaluate in `σ`), and conversely. -/
def CSEFailures (F : Expression.Factory) (ss out : Statements) (σ : SemanticStore Expression) :
    Prop :=
  ∃ (ds : List (Nat × LMonoTy × Expression.Expr)) (rest : Statements),
    out = ds.map (fun d => Statement.init ⟨s!"{cseVarPrefix}{d.1}", ()⟩ (LTy.forAll [] d.2.1)
      (.det d.2.2) .empty) ++ rest ∧
    ∀ t : AssertId Expression,
      (TypedSubtermsEvaluate F σ ss → ∀ e, FailsE F ss σ t e →
        ∃ e', FailsE F out σ t e' ∧ Core.eraseLocs (ds.foldr (fun d e =>
          LExpr.substFvar e ⟨s!"{cseVarPrefix}{d.1}", ()⟩ d.2.2) e') = Core.eraseLocs e) ∧
      (∀ e', FailsE F out σ t e' →
        ∃ e, FailsE F ss σ t e ∧ Core.eraseLocs (ds.foldr (fun d e =>
          LExpr.substFvar e ⟨s!"{cseVarPrefix}{d.1}", ()⟩ d.2.2) e') = Core.eraseLocs e)

end

/-- **A well-formed output keeps the failures**, when the input has no `init`, `set` or loop,
    the start store binds no generated name and the factory evaluates Boolean guards to
    Booleans and variables to their values. -/
private theorem failures_of_wf {ss out : Statements} {idx idx' : Nat} (hwf : CSEWellFormed ss idx out idx')
    (hfresh : FreshCSENames ss idx) (hq : Block.allSubstmts Quiet ss = true)
    {F : Expression.Factory} (hWB : WellFormedSemanticEvalBool (P := Expression) F)
    (hvar : WellFormedSemanticEvalVar (P := Expression) F) {σ : SemanticStore Expression}
    (hσ : ∀ k, σ (cseName k) = none) : CSEFailures F ss out σ := by
  obtain ⟨ds, rest, hout, -, hperm, -, hsub, hrhsv, -, hunf⟩ := hwf
  have hout' : out = ds.map initOf ++ rest := hout
  have hm : Statements.mapExprs (fun e => E (unfold ds e)) rest = Statements.mapExprs E ss := hunf
  have hqr : Block.allSubstmts Quiet rest = true := by
    rw [← block_quiet_mapExprs (fun e => E (unfold ds e)) rest, hm, block_quiet_mapExprs]; exact hq
  have hnd : (ds.map (·.1)).Nodup := hperm.nodup_iff.mpr List.nodup_range'
  have hidx : ∀ d ∈ ds, idx ≤ d.1 := fun d hd => by
    have := hperm.mem_iff.mp (List.mem_map.mpr ⟨d, hd, rfl⟩)
    rw [List.mem_range'_1] at this; exact this.1
  refine ⟨ds, rest, hout, fun t => ⟨fun hev e hfe => ?_, fun e' hfe => ?_⟩⟩
  · -- Forward: run the declarations, then follow the body.
    have hdecl : ∀ j (hj : j < ds.length), ∃ v, Expression.eval F σ
        (unfold ([] ++ ds.take j) ds[j].2.2) = some v ∧
        HasVal.valueOfTy F v (LTy.forAll [] ds[j].2.1) := by
      intro j hj
      obtain ⟨r, hr, c, hc, hty, hbv, hce⟩ := hsub ds[j] (List.getElem_mem hj)
      have hdrop : unfold (ds.drop j) ds[j].2.2 = ds[j].2.2 := by
        apply unfold_of_fresh
        intro d' hd' hv
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd'
        rw [List.getElem_drop] at hv
        rcases hrhsv j hj _ hv with ⟨k, hk, hke⟩ | hb
        · have hname := cseName_inj hke
          have hi' : i < ds.length - j := by simpa using hi
          have := hnd.eq_of_getElem_eq (i := k) (j := j + i) (by simp; omega) (by simp; omega)
            (by simp [hname])
          omega
        · exact hfresh _ (hidx _ (List.getElem_mem _)) hb
      obtain ⟨v, hv, hvt⟩ := hev r hr c hc hbv _ hty
      refine ⟨v, ?_, hvt⟩
      have : unfold ds ds[j].2.2 = unfold (ds.take j) ds[j].2.2 := by
        rw [unfold_take_drop j ds, hdrop]
      rw [List.nil_append, ← this, ← Expression.eval_eraseLocs, show Core.eraseLocs (unfold ds ds[j].2.2) = Core.eraseLocs c from hce, Expression.eval_eraseLocs]
      exact hv
    obtain ⟨σD, hrun⟩ := declRun_build hσ ds [] σ .nil (by simpa using hnd) hdecl
    have hc : ∀ a b, E a = (fun e => E (unfold ds e)) b →
        Expression.eval F σ a = Expression.eval F σD b := by
      intro a b hab
      rw [eval_declStores hrun.stores, ← Expression.eval_eraseLocs F σ (unfold ds b),
        show Core.eraseLocs (unfold ds b) = Core.eraseLocs a from hab.symm, Expression.eval_eraseLocs]
    obtain ⟨e', ⟨evs, ev, hr, has, hfa⟩, hee⟩ :=
      fails_of_sim hc hq hm.symm (failsE_fails hfe)
    refine ⟨e', fails_failsE hWB ⟨evs, ev, ?_, has, hfa⟩, hee.symm⟩
    rw [hout']
    exact reach_inits hvar hrun hr
  · -- Backward: the declarations ran; follow the body back.
    obtain ⟨evs, ev, hr, has, hfa⟩ := failsE_fails hfe
    rw [hout'] at hr
    obtain ⟨σD, hst, hr'⟩ := reach_inits_inv ds rest σ _ hr
    have hc : ∀ a b, (fun e => E (unfold ds e)) a = E b →
        Expression.eval F σD a = Expression.eval F σ b := by
      intro a b hab
      rw [eval_declStores hst, ← Expression.eval_eraseLocs F σ (unfold ds a), show Core.eraseLocs (unfold ds a) = Core.eraseLocs b from hab, Expression.eval_eraseLocs]
    obtain ⟨e, he, hee⟩ := fails_of_sim hc hqr hm ⟨evs, ev, hr', has, hfa⟩
    exact ⟨e, fails_failsE hWB he, hee⟩

/-- Unfolding no declarations changes nothing. -/
private theorem CSEFailures.refl (F : Expression.Factory) (ss : Statements) (σ : SemanticStore Expression) :
    CSEFailures F ss ss σ :=
  ⟨[], ss, rfl, fun _ => ⟨fun _ e h => ⟨e, h, rfl⟩, fun e h => ⟨e, h, rfl⟩⟩⟩

/-- No `init`, no `set` and no loop: the statements of `Quiet`. -/
private theorem quiet_of (ss : Statements) (hinits : Statements.noInits ss = true)
    (hssa : Statements.staticSingleAssignment ss = true) (hloops : Block.noLoops ss = true) :
    Block.allSubstmts Quiet ss = true :=
  block_allSubstmts_and _ _ ss (block_allSubstmts_and _ _ ss hinits hssa) hloops

public section

/-- **The single pass keeps the failures of a body** (see `CSEFailures`): a failure of `ss` is
    one of its output, with a condition that unfolds to the original up to locations, and
    conversely. The body mentions no generated name from `idx` on and has no hash collisions
    among its subterms, and has no `init`, `set` or loop; the factory evaluates Boolean guards to
    Booleans and variables to their values; the start store binds no generated name. The forward
    direction also needs the typed subterms of `ss` to evaluate in the start store, since the
    declarations are evaluated first.

    TODO: two premises are proof debt rather than conditions on programs. `NoHashCollisions`
    is needed only because the original pass's well-formedness proof uses it, and a hash
    collision can only drop candidates there. `TypedSubtermsEvaluate` should follow from
    typing (see its docstring). -/
theorem stmtRunCSESinglePass_failures (ss : Statements) (idx : Nat)
    (hfresh : FreshCSENames ss idx) (hnc : NoHashCollisions ss)
    (hinits : Statements.noInits ss = true) (hssa : Statements.staticSingleAssignment ss = true)
    (hloops : Block.noLoops ss = true)
    {F : Expression.Factory} (hWB : WellFormedSemanticEvalBool (P := Expression) F)
    (hvar : WellFormedSemanticEvalVar (P := Expression) F) {σ : SemanticStore Expression}
    (hσ : ∀ k : Nat, σ ⟨s!"{cseVarPrefix}{k}", ()⟩ = none) :
    CSEFailures F ss (stmtRunCSESinglePass ss idx).1 σ :=
  failures_of_wf (stmtRunCSESinglePass_wellFormed ss idx hfresh hnc) hfresh
    (quiet_of ss hinits hssa hloops) hWB hvar hσ

end

/-! ## The phase -/

/-- A fold over declarations whose step fails or prepends a declaration related to its input
    keeps what it prepended and relates every input declaration to one of the output. -/
private theorem foldlM_spec {α : Type} (step : List Core.Decl × α → Core.Decl → Transform.CoreTransformM (List Core.Decl × α))
    (R : Core.Decl → Core.Decl → Prop)
    (hstep : ∀ acc d s, (∃ e, ExceptT.run (step acc d) s = (.error e, s)) ∨
      ∃ d' a, ExceptT.run (step acc d) s = (.ok (d' :: acc.1, a), s) ∧ R d d') :
    ∀ (l : List Core.Decl) acc s r s', ExceptT.run (l.foldlM step acc) s = (.ok r, s') →
      (∀ d ∈ acc.1, d ∈ r.1) ∧ ∀ d ∈ l, ∃ d', R d d' ∧ d' ∈ r.1 := by
  intro l
  induction l with
  | nil =>
    intro acc s r s' h
    simp only [List.foldlM_nil, ExceptT.run_pure] at h
    cases h
    exact ⟨fun d hd => hd, fun d hd => by simp at hd⟩
  | cons d l ih =>
    intro acc s r s' h
    rw [List.foldlM_cons, ExceptT.run_bind] at h
    rcases hstep acc d s with ⟨e, he⟩ | ⟨d', a, he, hR⟩
    · simp only [bind, StateT.bind, he] at h
      cases h
    · simp only [bind, StateT.bind, he] at h
      obtain ⟨h1, h2⟩ := ih _ _ _ _ h
      refine ⟨fun x hx => h1 x (List.mem_cons_of_mem _ hx), fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨d', hR, h1 d' (by simp)⟩
      · exact h2 x hx

/-- The step of `runCSE` over the program's declarations. -/
private def cseStep : List Core.Decl × Nat × Bool → Core.Decl → Transform.CoreTransformM (List Core.Decl × Nat × Bool) :=
  fun (acc, idx, changed) decl =>
    match decl with
    | .proc proc md =>
      match proc.body with
      | .structured ss o =>
        let (body', idx') := stmtRunCSESinglePass ss idx
        pure (.proc { proc with body := .structured body' o } md :: acc, idx', changed || idx' > idx)
      | .cfg _ _ =>
        throw (Strata.Message.fromFormat
          f!"❌ CommonSubexprElim: procedure {proc.header.name.name} has a CFG body; \
             common subexpressions can only be eliminated from structured bodies.")
      | .abstract => pure (decl :: acc, idx, changed)
    | other => pure (other :: acc, idx, changed)

/-- `runCSE` through its step. -/
private theorem runCSE_eq (p : Program) : runCSE p = (do
    let (revDecls, _, changed) ← p.decls.foldlM cseStep ([], 0, false)
    return (changed, { decls := revDecls.reverse })) := rfl

/-- **`runCSE` rewrites each structured body** with the single pass, from some start index. -/
private theorem runCSE_mem {p out : Program} {s s' : Transform.CoreTransformState} {b : Bool}
    (h : (runCSE p).run s = (.ok (b, out), s')) {q : Procedure} {md : MetaData Expression}
    {ss : Statements} {opq : Bool} (hq : Decl.proc q md ∈ p.decls)
    (hb : q.body = .structured ss opq) :
    ∃ idx, Decl.proc { q with body := .structured (stmtRunCSESinglePass ss idx).1 opq } md ∈
      out.decls := by
  rw [runCSE_eq] at h
  simp only [ExceptT.run_bind] at h
  let R : Core.Decl → Core.Decl → Prop := fun d d' => ∀ q md ss o, d = Decl.proc q md →
    q.body = .structured ss o →
    ∃ idx, d' = Decl.proc { q with body := .structured (stmtRunCSESinglePass ss idx).1 o } md
  have hstep : ∀ acc d s, (∃ e, ExceptT.run (cseStep acc d) s = (.error e, s)) ∨
      ∃ d' a, ExceptT.run (cseStep acc d) s = (.ok (d' :: acc.1, a), s) ∧ R d d' := by
    intro acc d s
    obtain ⟨acc, idx, ch⟩ := acc
    cases d with
    | proc q' md' =>
      cases hb' : q'.body with
      | structured ss' o' =>
        right
        refine ⟨_, _, by simp [cseStep, hb']; rfl, fun q md ss o hd hbq => ?_⟩
        cases hd
        rw [hb'] at hbq
        cases hbq
        exact ⟨idx, rfl⟩
      | cfg c o' => left; exact ⟨_, by simp [cseStep, hb']; rfl⟩
      | abstract =>
        right
        refine ⟨_, _, by simp [cseStep, hb']; rfl, fun q md ss o hd hbq => ?_⟩
        cases hd
        rw [hb'] at hbq
        cases hbq
    | _ =>
      right
      exact ⟨_, _, by simp [cseStep]; rfl, fun q md ss o hd => by cases hd⟩
  cases hF : ExceptT.run (p.decls.foldlM cseStep ([], 0, false)) s with
  | mk res s1 =>
    simp only [bind, StateT.bind, hF] at h
    cases res with
    | error e => cases h
    | ok r =>
      obtain ⟨-, h2⟩ := foldlM_spec cseStep R hstep p.decls _ s r s1 hF
      obtain ⟨d', hR, hd'⟩ := h2 _ hq
      obtain ⟨idx, rfl⟩ := hR q md ss opq rfl hb
      have hout : out = { decls := r.1.reverse } := by
        simp only [ExceptT.pure, ExceptT.run, ExceptT.mk, pure, StateT.pure] at h
        cases h
        rfl
      subst hout
      exact ⟨idx, List.mem_reverse.mpr hd'⟩

/-- **The phase rewrites each structured body** with the single pass, or leaves the program
    unchanged. -/
private theorem commonSubexprElimPhase_mem {minTreeSize : Option Nat} {program out : Program}
    {s s' : Transform.CoreTransformState} {b : Bool}
    (h : ((Core.commonSubexprElimPhase minTreeSize).transform program).run s = (.ok (b, out), s'))
    {q : Procedure} {md : MetaData Expression} {ss : Statements}
    {opq : Bool} (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss opq) :
    ∃ ss', Decl.proc { q with body := .structured ss' opq } md ∈ out.decls ∧
      (ss' = ss ∨ ∃ idx, ss' = (stmtRunCSESinglePass ss idx).1) := by
  cases minTreeSize with
  | none =>
    obtain ⟨idx, hm⟩ := runCSE_mem (p := program) h hq hb
    exact ⟨_, hm, .inr ⟨idx, rfl⟩⟩
  | some n =>
    change (runCSEAbove n program).run s = (.ok (b, out), s') at h
    unfold runCSEAbove at h
    split at h
    · simp only [pure] at h
      cases h
      refine ⟨ss, ?_, .inl rfl⟩
      have : ({ q with body := .structured ss opq } : Procedure) = q := by
        cases q; simp only at hb; rw [hb]
      rw [this]; exact hq
    · obtain ⟨idx, hm⟩ := runCSE_mem (p := program) h hq hb
      exact ⟨_, hm, .inr ⟨idx, rfl⟩⟩

public section

/-- **The common-subexpression-elimination phase keeps failures.** Let a run of the phase on
    `program` succeed with `out`, with `program` satisfying the phase's facts `noInits`,
    `staticSingleAssignment` and `noLoops`, and let `q` be a procedure of `program` with
    structured body `ss` that mentions no generated name and has no hash collisions among its
    subterms. Then `out` contains `q` with some body `ss'`, and the failures of `ss` and `ss'`
    correspond (`CSEFailures`) from every store binding no generated name, for every factory
    evaluating Boolean guards to Booleans and variables to their values. -/
theorem commonSubexprElimPhase_failures {minTreeSize : Option Nat} {program out : Program}
    {s s' : Transform.CoreTransformState} {b : Bool}
    (h : ((Core.commonSubexprElimPhase minTreeSize).transform program).run s = (.ok (b, out), s'))
    (hinits : ProgramFact.noInits.holds program)
    (hssa : ProgramFact.staticSingleAssignment.holds program)
    (hloops : ProgramFact.noLoops.holds program)
    {q : Procedure} {md : MetaData Expression} {ss : Statements}
    {opq : Bool} (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss opq)
    (hfresh : FreshCSENames ss 0) (hnc : NoHashCollisions ss) :
    ∃ ss', Decl.proc { q with body := .structured ss' opq } md ∈ out.decls ∧
      ∀ {F : Expression.Factory}, WellFormedSemanticEvalBool (P := Expression) F →
        WellFormedSemanticEvalVar (P := Expression) F →
        ∀ {σ : SemanticStore Expression}, (∀ k : Nat, σ ⟨s!"{cseVarPrefix}{k}", ()⟩ = none) →
          CSEFailures F ss ss' σ := by
  obtain ⟨ss', hm, hss'⟩ := commonSubexprElimPhase_mem h hq hb
  refine ⟨ss', hm, fun hWB hvar σ hσ => ?_⟩
  rcases hss' with rfl | ⟨idx, rfl⟩
  · exact CSEFailures.refl _ _ _
  · exact stmtRunCSESinglePass_failures ss idx (fun k _ => hfresh k (Nat.zero_le k)) hnc
      (Program.allStatements_of_proc hinits hq hb) (Program.allStatements_of_proc hssa hq hb)
      (Program.allStatements_of_proc hloops hq hb) hWB hvar hσ

end

end Core.CSE
