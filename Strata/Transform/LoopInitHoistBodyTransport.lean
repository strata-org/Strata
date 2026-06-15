/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CmdSemantics
public import Strata.Transform.LoopInitHoist
public import Strata.Transform.LoopInitHoistContains
public import Strata.Transform.LoopInitHoistFreshness
public import Strata.Transform.LoopInitHoistRewrite
public import Strata.Transform.LoopInitHoistInfra
public import Strata.Transform.LoopInitHoistLoopDriver
public import Strata.Transform.LoopInitHoistOptEStepBProviderSpike
public import Strata.Transform.LoopInitHoistOptEKeystoneScratch

import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.Cmd
import all Strata.Transform.LoopInitHoist
import all Strata.Transform.LoopInitHoistContains
import all Strata.Transform.LoopInitHoistFreshness
import all Strata.Transform.LoopInitHoistRewrite
import all Strata.Transform.LoopInitHoistInfra

public section

namespace Imperative
namespace LoopInitHoistBodyTransport

/-!
# Body transport for the loop-init hoist pass (Option E).

This module provides the general per-iteration *body transport* the loop-init
hoist correctness proof consumes for a renamed-and-lifted loop body.

When the pass processes a `.loop`, it (post-order) first hoist-processes the body
to `body₁`, then `Block.liftInitsInLoopBodyM body₁` harvests the prefix inits into
prelude havocs, rewrites each lifted `init y ty rhs md` to `set y rhs md` in
`body₂`, and records a rename `(y, y')`.  Finally `body₃ = Block.applyRenames
renames body₂` renames every recorded source name `y` to its fresh hoist target
`y'`.  The per-iteration *body simulation* needed by the loop driver relates the
source body `body₁` to the renamed-lifted body `body₃`.

The correspondence between `body₁` and `body₃` is captured by the inductive
relation `BodyTransport A B subst body_src body_h`: a per-statement rewrite where
* a lifted `init` becomes a renamed `set` (`set_both_in_subst` transport),
* an `assert`/`assume`/`cover` predicate is renamed by `substFvarMany`,
* a `.block` is rewritten recursively and re-projected on exit,
* a `.ite` keeps its guard (it reads no renamed name) and rewrites both branches,
* a nested `.loop` keeps measure/invariants empty and has its guard renamed to
  `substFvarMany g subst` and its body rewritten recursively.

`Block.bodyTransport` then turns a `BodyTransport` derivation into the
eval-carrying body simulation `BodySimE A B subst body_src body_h` (the loop
driver's `body_sim` slot, after forgetting the eval conjunct).  The proof is by
induction on the `BodyTransport` derivation; the nested-loop arm feeds the
inductive hypothesis on the inner body into the renamed-guard loop driver.
-/

open StructuredToUnstructuredCorrect (extendStoreOne extendStoreOne_self extendStoreOne_other)
open OptEStepBProvider (BodySim BodySimE StmtSimE bodySimE_cons bodySimE_nil
  bodySimE_to_bodySim nestedLoop_stmtSimE)

variable {P : PureExpr}
  [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
  [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr]
  [DecidableEq P.Ident]

/-! ## Local inversion / forward helpers.

The general inversion/forward step lemmas live `private` in the infra modules; we
re-derive the few we need against `EvalCmd` so they are usable in this module. -/

/-- Invert `.stmt (.cmd c) ρ ⟶* .terminal ρ'` into the `EvalCmd` evidence. -/
private theorem stmt_cmd_terminal_inv'
    {extendEval : ExtendEval P}
    {c : Cmd P} {ρ ρ' : Env P}
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmt (.cmd c) ρ) (.terminal ρ')) :
    ∃ σ' hf, EvalCmd P ρ.eval ρ.store c σ' hf ∧
      ρ' = { ρ with store := σ', hasFailure := ρ.hasFailure || hf } := by
  cases h with
  | step _ _ _ h1 hr1 =>
    cases h1 with
    | step_cmd h_eval =>
      cases hr1 with
      | refl => exact ⟨_, _, h_eval, rfl⟩
      | step _ _ _ hd _ => exact nomatch hd

/-- Forward: a single command whose `EvalCmd` holds steps to `.terminal`. -/
private theorem stmt_cmd_step_forward'
    {extendEval : ExtendEval P}
    {c : Cmd P} {ρ : Env P} {σ' : SemanticStore P} {hf : Bool}
    (h : EvalCmd P ρ.eval ρ.store c σ' hf) :
    StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.cmd c) ρ)
      (.terminal { ρ with store := σ', hasFailure := ρ.hasFailure || hf }) :=
  .step _ _ _ (.step_cmd h) (.refl _)

/-- Forward: enter a labeled block, run its inner body to terminal, exit
projecting through the parent store. -/
private theorem block_step_forward'
    {extendEval : ExtendEval P}
    {lbl : String} {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {ρ ρ_inner : Env P}
    (h_inner : StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ) (.terminal ρ_inner)) :
    StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.block lbl body md) ρ)
      (.terminal { ρ_inner with store := projectStore ρ.store ρ_inner.store }) := by
  refine .step _ _ _ .step_block ?_
  have h_lift := block_inner_star P (EvalCmd P) extendEval _ _ (.some lbl) ρ.store h_inner
  refine ReflTrans_Transitive _ _ _ _ h_lift ?_
  exact .step _ _ _ .step_block_done (.refl _)

/-- Invert a det-`.ite` run to terminal: the guard selects a branch, which then
runs to terminal in the same store frame. -/
private theorem ite_terminal_inv'
    {extendEval : ExtendEval P}
    {g : P.Expr} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} {ρ ρ' : Env P}
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmt (.ite (.det g) tss ess md) ρ) (.terminal ρ')) :
    (ρ.eval ρ.store g = .some HasBool.tt ∧ WellFormedSemanticEvalBool ρ.eval ∧
       StepStmtStar P (EvalCmd P) extendEval (.stmts tss ρ) (.terminal ρ')) ∨
    (ρ.eval ρ.store g = .some HasBool.ff ∧ WellFormedSemanticEvalBool ρ.eval ∧
       StepStmtStar P (EvalCmd P) extendEval (.stmts ess ρ) (.terminal ρ')) := by
  cases h with
  | step _ _ _ h1 hr1 =>
    cases h1 with
    | step_ite_true h_g h_wfb => exact .inl ⟨h_g, h_wfb, hr1⟩
    | step_ite_false h_g h_wfb => exact .inr ⟨h_g, h_wfb, hr1⟩

/-- Forward: a det-`.ite` whose guard is tt steps to its then-branch run. -/
private theorem ite_step_then_forward'
    {extendEval : ExtendEval P}
    {g : P.Expr} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} {ρ ρ' : Env P}
    (h_g : ρ.eval ρ.store g = .some HasBool.tt)
    (h_wfb : WellFormedSemanticEvalBool ρ.eval)
    (h_branch : StepStmtStar P (EvalCmd P) extendEval (.stmts tss ρ) (.terminal ρ')) :
    StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.ite (.det g) tss ess md) ρ) (.terminal ρ') :=
  .step _ _ _ (.step_ite_true h_g h_wfb) h_branch

/-- Forward: a det-`.ite` whose guard is ff steps to its else-branch run. -/
private theorem ite_step_else_forward'
    {extendEval : ExtendEval P}
    {g : P.Expr} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} {ρ ρ' : Env P}
    (h_g : ρ.eval ρ.store g = .some HasBool.ff)
    (h_wfb : WellFormedSemanticEvalBool ρ.eval)
    (h_branch : StepStmtStar P (EvalCmd P) extendEval (.stmts ess ρ) (.terminal ρ')) :
    StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.ite (.det g) tss ess md) ρ) (.terminal ρ') :=
  .step _ _ _ (.step_ite_false h_g h_wfb) h_branch

/-- Invert a nondet-`.ite` run to terminal: the run selected the then- or else-
branch (no guard evaluation), which then runs to terminal in the same frame. -/
private theorem ite_nondet_terminal_inv'
    {extendEval : ExtendEval P}
    {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} {ρ ρ' : Env P}
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmt (.ite .nondet tss ess md) ρ) (.terminal ρ')) :
    StepStmtStar P (EvalCmd P) extendEval (.stmts tss ρ) (.terminal ρ') ∨
    StepStmtStar P (EvalCmd P) extendEval (.stmts ess ρ) (.terminal ρ') := by
  cases h with
  | step _ _ _ h1 hr1 =>
    cases h1 with
    | step_ite_nondet_true => exact .inl hr1
    | step_ite_nondet_false => exact .inr hr1

/-- Forward: a nondet-`.ite` steps to its then-branch run. -/
private theorem ite_nondet_step_then_forward'
    {extendEval : ExtendEval P}
    {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} {ρ ρ' : Env P}
    (h_branch : StepStmtStar P (EvalCmd P) extendEval (.stmts tss ρ) (.terminal ρ')) :
    StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.ite .nondet tss ess md) ρ) (.terminal ρ') :=
  .step _ _ _ .step_ite_nondet_true h_branch

/-- Forward: a nondet-`.ite` steps to its else-branch run. -/
private theorem ite_nondet_step_else_forward'
    {extendEval : ExtendEval P}
    {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} {ρ ρ' : Env P}
    (h_branch : StepStmtStar P (EvalCmd P) extendEval (.stmts ess ρ) (.terminal ρ')) :
    StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.ite .nondet tss ess md) ρ) (.terminal ρ') :=
  .step _ _ _ .step_ite_nondet_false h_branch

/-- Invert a `.typeDecl` run to terminal: it is a runtime no-op (env unchanged). -/
private theorem typeDecl_terminal_inv'
    {extendEval : ExtendEval P}
    {tc : TypeConstructor} {md : MetaData P} {ρ ρ' : Env P}
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmt (.typeDecl tc md) ρ) (.terminal ρ')) :
    ρ' = ρ := by
  cases h with
  | step _ _ _ h1 hr1 =>
    cases h1
    cases hr1 with
    | refl => rfl
    | step _ _ _ hd _ => exact nomatch hd

/-- Forward: a `.typeDecl` steps to `.terminal` with the env unchanged. -/
private theorem typeDecl_step_forward'
    {extendEval : ExtendEval P}
    {tc : TypeConstructor} {md : MetaData P} {ρ : Env P} :
    StepStmtStar P (EvalCmd P) extendEval (.stmt (.typeDecl tc md) ρ) (.terminal ρ) :=
  .step _ _ _ .step_typeDecl (.refl _)

/-- Split a source block run into its inner terminal run (given no exit). -/
private theorem block_terminal_inv'
    {extendEval : ExtendEval P}
    {lbl : String} {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {ρ ρ' : Env P}
    (h_no_exit : ∀ (l : String) (ρe : Env P),
      ¬ StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ) (.exiting l ρe))
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmt (.block lbl body md) ρ) (.terminal ρ')) :
    ∃ ρ_inner : Env P,
      StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ) (.terminal ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore ρ.store ρ_inner.store } := by
  cases h with
  | step _ _ _ hs hr =>
    cases hs
    rcases block_reaches_terminal P (EvalCmd P) extendEval hr with
      ⟨ρ_inner, hterm, heq⟩ | ⟨l, ρ_inner, hexit, heq⟩
    · exact ⟨ρ_inner, hterm, heq⟩
    · exact absurd hexit (h_no_exit l ρ_inner)

/-- Condition transport across the multi-pair `HoistInv`, re-derived from the
public `substFvarMany_eval_tweak`. -/
private theorem cond_transport'
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {δ : SemanticEval P} {e : P.Expr} {σ_s σ_h : SemanticStore P}
    (h_A_subst_fst : ∀ a ∈ A, a ∈ subst.map Prod.fst)
    (h_src_nodup : (subst.map Prod.fst).Nodup)
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd)
    (h_tgt_nodup : (subst.map Prod.snd).Nodup)
    (h_B_fresh : ∀ x ∈ B, x ∉ HasVarsPure.getVars e)
    (h_hinv : HoistInv (P := P) A B subst σ_s σ_h)
    (h_read_def : ∀ x ∈ HasVarsPure.getVars e, σ_s x ≠ none)
    (h_wfcongr : WellFormedSemanticEvalExprCongr δ)
    (h_wfsubst : WellFormedSemanticEvalSubstFvar δ) :
    δ σ_s e = δ σ_h (substFvarMany e subst) := by
  classical
  have h_congr : δ σ_s e = δ (fun x => σ_h (renameLookup subst x)) e := by
    apply h_wfcongr e σ_s (fun x => σ_h (renameLookup subst x))
    intro x hx
    -- A read var `x` is either a rename SOURCE (in `subst.fst`) — handled by the
    -- guarded pairing (read ⇒ defined ⇒ the pairing antecedent holds) — or it is
    -- outside the rename and `A`/`B`-frame, handled by the guarded frame.
    by_cases hx_src : x ∈ subst.map Prod.fst
    · obtain ⟨⟨a, b⟩, hb_pair, hxa⟩ := List.mem_map.mp hx_src
      simp only at hxa
      subst a
      rw [renameLookup_mem subst h_src_nodup hb_pair]
      exact (h_hinv.2 x b hb_pair (h_read_def x hx)).2
    · have hx_notin_A : x ∉ A := fun hA => hx_src (h_A_subst_fst x hA)
      have hx_notin_B : x ∉ B := fun hB => h_B_fresh x hB hx
      rw [renameLookup_notin subst x hx_src]
      -- Guarded frame: read var `x` is defined in `σ_s` by `h_read_def`.
      exact h_hinv.1 x hx_notin_A hx_notin_B (h_read_def x hx)
  rw [h_congr]
  exact substFvarMany_eval_tweak δ subst h_src_nodup h_disjoint h_tgt_nodup h_wfsubst

/-! ## The body-transport correspondence relation.

`BodyTransport A B subst body_src body_h` relates a source body (post Step A) to
its renamed-lifted image, per statement.  This is the exact correspondence that
`Block.applyRenames (substOf' entries) (Block.liftInitsInLoopBodyM body_src).2.2`
produces: lifted inits become renamed sets, expressions are `substFvarMany`-renamed,
nested loops have their guard renamed and body recursively transported. -/
inductive BodyTransport
    (A B : List P.Ident) (subst : List (P.Ident × P.Ident)) :
    List (Stmt P (Cmd P)) → List (Stmt P (Cmd P)) → Prop where
  | nil : BodyTransport A B subst [] []
  | init_set {a b : P.Ident} {τ : P.Ty} {rhs : P.Expr} {md : MetaData P}
      {body_src body_h : List (Stmt P (Cmd P))}
      (h_pair : (a, b) ∈ subst) (h_a_in_A : a ∈ A) (h_b_in_B : b ∈ B)
      (h_unique_a : ∀ a' b', (a', b') ∈ subst → a' = a → b' = b)
      (h_unique_b : ∀ a' b', (a', b') ∈ subst → b' = b → a' = a)
      (h_B_fresh_rhs : ∀ x ∈ B, x ∉ HasVarsPure.getVars rhs)
      (h_rest : BodyTransport A B subst body_src body_h) :
      BodyTransport A B subst
        (.cmd (.init a τ (.det rhs) md) :: body_src)
        (.cmd (.set b (.det (substFvarMany rhs subst)) md) :: body_h)
  -- A nondet-rhs `init` is lifted exactly like a det one: the lift harvests a
  -- fresh-name havoc + rename `(a, b)` and rewrites the source statement to a
  -- `set a .nondet`, which `applyRenames` renames to `set b .nondet`.  The source
  -- nondet-init `InitState`s `a` (undef → arbitrary `v`); the hoist nondet-set
  -- `UpdateState`s `b` (def → the SAME `v`) — `set_both_in_subst` transport.
  | init_nondet {a b : P.Ident} {τ : P.Ty} {md : MetaData P}
      {body_src body_h : List (Stmt P (Cmd P))}
      (h_pair : (a, b) ∈ subst) (h_a_in_A : a ∈ A) (h_b_in_B : b ∈ B)
      (h_unique_a : ∀ a' b', (a', b') ∈ subst → a' = a → b' = b)
      (h_unique_b : ∀ a' b', (a', b') ∈ subst → b' = b → a' = a)
      (h_rest : BodyTransport A B subst body_src body_h) :
      BodyTransport A B subst
        (.cmd (.init a τ .nondet md) :: body_src)
        (.cmd (.set b .nondet md) :: body_h)
  -- A `.set` whose LHS `a` is a rename SOURCE (`a ∈ A`, `(a, b) ∈ subst`).  When a
  -- loop body BOTH declares (`init a`) AND later sets (`set a`) the same var, the
  -- lift hoists the declaration and renames the source `a → b` consistently in BOTH
  -- the lifted-init and the later `.set` (`applyRenames` renames `.set a → .set b`,
  -- identical to the `.init` site).  So the later `.set a` becomes `.set b` on the
  -- hoist side, with its `.det` rhs `substFvarMany`-renamed.  The source `UpdateState`s
  -- `a` (def → `v`); the hoist `UpdateState`s `b` (def → the SAME `v`) —
  -- `set_both_in_subst` transport (the SAME transport `init_set` uses for its set side).
  | set_renamed {a b : P.Ident} {rhs : P.Expr} {md : MetaData P}
      {body_src body_h : List (Stmt P (Cmd P))}
      (h_pair : (a, b) ∈ subst) (h_a_in_A : a ∈ A) (h_b_in_B : b ∈ B)
      (h_unique_a : ∀ a' b', (a', b') ∈ subst → a' = a → b' = b)
      (h_unique_b : ∀ a' b', (a', b') ∈ subst → b' = b → a' = a)
      (h_B_fresh_rhs : ∀ x ∈ B, x ∉ HasVarsPure.getVars rhs)
      (h_rest : BodyTransport A B subst body_src body_h) :
      BodyTransport A B subst
        (.cmd (.set a (.det rhs) md) :: body_src)
        (.cmd (.set b (.det (substFvarMany rhs subst)) md) :: body_h)
  -- A nondet-rhs `.set` whose LHS `a` is a rename source, renamed `a → b` exactly
  -- like the det case (`applyRenames` renames `.set a .nondet → .set b .nondet`).  The
  -- source `InitState`-free nondet set chooses `v`; the hoist nondet-set replays the
  -- SAME `v` into `b` — `set_both_in_subst` transport.
  | set_renamed_nondet {a b : P.Ident} {md : MetaData P}
      {body_src body_h : List (Stmt P (Cmd P))}
      (h_pair : (a, b) ∈ subst) (h_a_in_A : a ∈ A) (h_b_in_B : b ∈ B)
      (h_unique_a : ∀ a' b', (a', b') ∈ subst → a' = a → b' = b)
      (h_unique_b : ∀ a' b', (a', b') ∈ subst → b' = b → a' = a)
      (h_rest : BodyTransport A B subst body_src body_h) :
      BodyTransport A B subst
        (.cmd (.set a .nondet md) :: body_src)
        (.cmd (.set b .nondet md) :: body_h)
  -- A genuine `.set` (NOT from init lifting, NOT a rename source) is passed through by
  -- the lift (no entry, no rename of its name because its name `∈ modifiedVars` hence
  -- `∉ A` and the subst sources lie in `A`).  Its `.det` rhs is `substFvarMany`-renamed.
  -- The source `UpdateState`s `name` (def → `v`); the hoist `UpdateState`s the SAME
  -- `name` (def → `v`) — `extend_both_outside_subst` transport (`name ∉ A ∪ B`).
  | set {name : P.Ident} {rhs : P.Expr} {md : MetaData P}
      {body_src body_h : List (Stmt P (Cmd P))}
      (h_name_notin_A : name ∉ A) (h_name_notin_B : name ∉ B)
      (h_B_fresh_rhs : ∀ x ∈ B, x ∉ HasVarsPure.getVars rhs)
      (h_rest : BodyTransport A B subst body_src body_h) :
      BodyTransport A B subst
        (.cmd (.set name (.det rhs) md) :: body_src)
        (.cmd (.set name (.det (substFvarMany rhs subst)) md) :: body_h)
  -- A genuine nondet-rhs `.set` is passed through identically (name unchanged,
  -- `.nondet` rhs fixed by `substFvarMany`).  `extend_both_outside_subst` transport.
  | set_nondet {name : P.Ident} {md : MetaData P}
      {body_src body_h : List (Stmt P (Cmd P))}
      (h_name_notin_A : name ∉ A) (h_name_notin_B : name ∉ B)
      (h_rest : BodyTransport A B subst body_src body_h) :
      BodyTransport A B subst
        (.cmd (.set name .nondet md) :: body_src)
        (.cmd (.set name .nondet md) :: body_h)
  | assert {lbl : String} {e : P.Expr} {md : MetaData P}
      {body_src body_h : List (Stmt P (Cmd P))}
      (h_B_fresh_e : ∀ x ∈ B, x ∉ HasVarsPure.getVars e)
      (h_rest : BodyTransport A B subst body_src body_h) :
      BodyTransport A B subst
        (.cmd (.assert lbl e md) :: body_src)
        (.cmd (.assert lbl (substFvarMany e subst) md) :: body_h)
  | assume {lbl : String} {e : P.Expr} {md : MetaData P}
      {body_src body_h : List (Stmt P (Cmd P))}
      (h_B_fresh_e : ∀ x ∈ B, x ∉ HasVarsPure.getVars e)
      (h_rest : BodyTransport A B subst body_src body_h) :
      BodyTransport A B subst
        (.cmd (.assume lbl e md) :: body_src)
        (.cmd (.assume lbl (substFvarMany e subst) md) :: body_h)
  | cover {lbl : String} {e : P.Expr} {md : MetaData P}
      {body_src body_h : List (Stmt P (Cmd P))}
      (h_rest : BodyTransport A B subst body_src body_h) :
      BodyTransport A B subst
        (.cmd (.cover lbl e md) :: body_src)
        (.cmd (.cover lbl (substFvarMany e subst) md) :: body_h)
  -- A `.typeDecl` is a runtime no-op, left unchanged by the rename (`substIdent`
  -- fixes it); the source and hoist both step to terminal with the same env.
  | typeDecl {tc : TypeConstructor} {md : MetaData P}
      {body_src body_h : List (Stmt P (Cmd P))}
      (h_rest : BodyTransport A B subst body_src body_h) :
      BodyTransport A B subst
        (.typeDecl tc md :: body_src)
        (.typeDecl tc md :: body_h)
  | block {lbl : String} {md : MetaData P}
      {inner_src inner_h body_src body_h : List (Stmt P (Cmd P))}
      (h_inner : BodyTransport A B subst inner_src inner_h)
      (h_rest : BodyTransport A B subst body_src body_h) :
      BodyTransport A B subst
        (.block lbl inner_src md :: body_src)
        (.block lbl inner_h md :: body_h)
  -- `.ite`: guard RENAMED to `substFvarMany g subst` (the pass `applyRenames`-
  -- substitutes it).  The renamed guard reads no renamed name (every var of `g`
  -- is `A`/`B`-fresh), so it evaluates as the original `g` under `HoistInv`.
  | ite {g : P.Expr} {md : MetaData P}
      {tss_src tss_h ess_src ess_h body_src body_h : List (Stmt P (Cmd P))}
      (h_B_fresh_g : ∀ x ∈ B, x ∉ HasVarsPure.getVars g)
      (h_then : BodyTransport A B subst tss_src tss_h)
      (h_else : BodyTransport A B subst ess_src ess_h)
      (h_rest : BodyTransport A B subst body_src body_h) :
      BodyTransport A B subst
        (.ite (.det g) tss_src ess_src md :: body_src)
        (.ite (.det (substFvarMany g subst)) tss_h ess_h md :: body_h)
  -- A nondet-guard `.ite` is passed through (guard `.nondet` fixed by the rename);
  -- the source's nondet branch selection is replayed verbatim by the hoist.
  | ite_nondet {md : MetaData P}
      {tss_src tss_h ess_src ess_h body_src body_h : List (Stmt P (Cmd P))}
      (h_then : BodyTransport A B subst tss_src tss_h)
      (h_else : BodyTransport A B subst ess_src ess_h)
      (h_rest : BodyTransport A B subst body_src body_h) :
      BodyTransport A B subst
        (.ite .nondet tss_src ess_src md :: body_src)
        (.ite .nondet tss_h ess_h md :: body_h)
  -- Nested loop: measure/invariants empty (the pass requires it); guard RENAMED to
  -- `substFvarMany g subst`; body recursively transported.
  | loop {g : P.Expr} {md : MetaData P}
      {lbody_src lbody_h body_src body_h : List (Stmt P (Cmd P))}
      (h_B_fresh_g : ∀ x ∈ B, x ∉ HasVarsPure.getVars g)
      (h_lbody : BodyTransport A B subst lbody_src lbody_h)
      (h_rest : BodyTransport A B subst body_src body_h) :
      BodyTransport A B subst
        (.loop (.det g) none [] lbody_src md :: body_src)
        (.loop (.det (substFvarMany g subst)) none [] lbody_h md :: body_h)

/-! ## Structural facts about `BodyTransport` source/hoist bodies.

`BodyTransport`-related bodies are `noFuncDecl` (no `.funcDecl` constructor) and
never reach a labeled `.exiting` (no top-level `.exit` constructor). -/

/-- A `BodyTransport` source body contains no `.funcDecl`. -/
theorem BodyTransport.noFuncDecl_src
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {body_src body_h : List (Stmt P (Cmd P))}
    (hrw : BodyTransport (P := P) A B subst body_src body_h) :
    Block.noFuncDecl body_src = true := by
  induction hrw with
  | nil => simp [Block.noFuncDecl]
  | init_set _ _ _ _ _ _ _ ih | assert _ _ ih | assume _ _ ih | cover _ ih
  | init_nondet _ _ _ _ _ _ ih | set _ _ _ _ ih | set_nondet _ _ _ ih | typeDecl _ ih
  | set_renamed _ _ _ _ _ _ _ ih | set_renamed_nondet _ _ _ _ _ _ ih =>
    simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.true_and]; exact ih
  | block _ _ ih_inner ih_rest =>
    simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true]
    exact ⟨by simpa [Block.noFuncDecl] using ih_inner, ih_rest⟩
  | ite _ _ _ _ ih_then ih_else ih_rest =>
    simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true]
    exact ⟨⟨by simpa [Block.noFuncDecl] using ih_then,
            by simpa [Block.noFuncDecl] using ih_else⟩, ih_rest⟩
  | ite_nondet _ _ _ ih_then ih_else ih_rest =>
    simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true]
    exact ⟨⟨by simpa [Block.noFuncDecl] using ih_then,
            by simpa [Block.noFuncDecl] using ih_else⟩, ih_rest⟩
  | loop _ _ _ ih_lbody ih_rest =>
    simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true]
    exact ⟨by simpa [Block.noFuncDecl] using ih_lbody, ih_rest⟩

/-- A `BodyTransport` hoist body contains no `.funcDecl`. -/
theorem BodyTransport.noFuncDecl_h
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {body_src body_h : List (Stmt P (Cmd P))}
    (hrw : BodyTransport (P := P) A B subst body_src body_h) :
    Block.noFuncDecl body_h = true := by
  induction hrw with
  | nil => simp [Block.noFuncDecl]
  | init_set _ _ _ _ _ _ _ ih | assert _ _ ih | assume _ _ ih | cover _ ih
  | init_nondet _ _ _ _ _ _ ih | set _ _ _ _ ih | set_nondet _ _ _ ih | typeDecl _ ih
  | set_renamed _ _ _ _ _ _ _ ih | set_renamed_nondet _ _ _ _ _ _ ih =>
    simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.true_and]; exact ih
  | block _ _ ih_inner ih_rest =>
    simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true]
    exact ⟨by simpa [Block.noFuncDecl] using ih_inner, ih_rest⟩
  | ite _ _ _ _ ih_then ih_else ih_rest =>
    simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true]
    exact ⟨⟨by simpa [Block.noFuncDecl] using ih_then,
            by simpa [Block.noFuncDecl] using ih_else⟩, ih_rest⟩
  | ite_nondet _ _ _ ih_then ih_else ih_rest =>
    simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true]
    exact ⟨⟨by simpa [Block.noFuncDecl] using ih_then,
            by simpa [Block.noFuncDecl] using ih_else⟩, ih_rest⟩
  | loop _ _ _ ih_lbody ih_rest =>
    simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true]
    exact ⟨by simpa [Block.noFuncDecl] using ih_lbody, ih_rest⟩

/-- A `BodyTransport` source body never reaches a labeled `.exiting`. -/
theorem BodyTransport.src_no_exit
    {extendEval : ExtendEval P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {body_src body_h : List (Stmt P (Cmd P))}
    (hrw : BodyTransport (P := P) A B subst body_src body_h) :
    ∀ (ρ : Env P) (lbl : String) (ρe : Env P),
      ¬ StepStmtStar P (EvalCmd P) extendEval (.stmts body_src ρ) (.exiting lbl ρe) := by
  induction hrw with
  | nil =>
    intro ρ lbl ρe h
    cases h with
    | step _ _ _ h1 hr1 =>
      cases h1
      cases hr1 with
      | step _ _ _ hd _ => exact nomatch hd
  | init_set _ _ _ _ _ _ _ ih | assert _ _ ih | assume _ _ ih | cover _ ih
  | init_nondet _ _ _ _ _ _ ih | set _ _ _ _ ih | set_nondet _ _ _ ih
  | set_renamed _ _ _ _ _ _ _ ih | set_renamed_nondet _ _ _ _ _ _ ih =>
    intro ρ lbl ρe h
    cases h with
    | step _ _ _ h1 hr1 =>
      cases h1
      rcases seq_reaches_exiting _ _ _ hr1 with h_inner | ⟨ρ_m, _h_term, h_tail⟩
      · cases h_inner with
        | step _ _ _ h2 hr2 =>
          cases h2 with
          | step_cmd _ =>
            cases hr2 with
            | step _ _ _ hd _ => exact nomatch hd
      · exact ih ρ_m lbl ρe h_tail
  | typeDecl _ ih =>
    intro ρ lbl ρe h
    cases h with
    | step _ _ _ h1 hr1 =>
      cases h1
      rcases seq_reaches_exiting _ _ _ hr1 with h_inner | ⟨ρ_m, _h_term, h_tail⟩
      · cases h_inner with
        | step _ _ _ h2 hr2 =>
          cases h2 with
          | step_typeDecl =>
            cases hr2 with
            | step _ _ _ hd _ => exact nomatch hd
      · exact ih ρ_m lbl ρe h_tail
  | @block lbl md inner_src inner_h body_src body_h h_inner h_rest ih_inner ih_rest =>
    intro ρ lbl' ρe h
    cases h with
    | step _ _ _ h1 hr1 =>
      cases h1
      rcases seq_reaches_exiting _ _ _ hr1 with h_blk | ⟨ρ_m, _h_term, h_tail⟩
      · cases h_blk with
        | step _ _ _ h2 hr2 =>
          cases h2
          obtain ⟨lbl_i, ρ_i, hexit, _⟩ := block_reaches_exiting P (EvalCmd P) extendEval hr2
          exact ih_inner ρ lbl_i ρ_i hexit
      · exact ih_rest ρ_m lbl' ρe h_tail
  | @ite g md tss_src tss_h ess_src ess_h body_src body_h
      _ h_then h_else h_rest ih_then ih_else ih_rest =>
    intro ρ lbl' ρe h
    cases h with
    | step _ _ _ h1 hr1 =>
      cases h1 with
      | step_stmts_cons =>
        rcases seq_reaches_exiting _ _ _ hr1 with h_ite | ⟨ρ_m, _h_term, h_tail⟩
        · cases h_ite with
          | step _ _ _ hi hri =>
            cases hi with
            | step_ite_true _ _ => exact ih_then ρ lbl' ρe hri
            | step_ite_false _ _ => exact ih_else ρ lbl' ρe hri
        · exact ih_rest ρ_m lbl' ρe h_tail
  | @ite_nondet md tss_src tss_h ess_src ess_h body_src body_h
      h_then h_else h_rest ih_then ih_else ih_rest =>
    intro ρ lbl' ρe h
    cases h with
    | step _ _ _ h1 hr1 =>
      cases h1 with
      | step_stmts_cons =>
        rcases seq_reaches_exiting _ _ _ hr1 with h_ite | ⟨ρ_m, _h_term, h_tail⟩
        · cases h_ite with
          | step _ _ _ hi hri =>
            cases hi with
            | step_ite_nondet_true => exact ih_then ρ lbl' ρe hri
            | step_ite_nondet_false => exact ih_else ρ lbl' ρe hri
        · exact ih_rest ρ_m lbl' ρe h_tail
  | @loop g md lbody_src lbody_h body_src body_h _ h_lbody h_rest ih_lbody ih_rest =>
    intro ρ lbl' ρe h
    cases h with
    | step _ _ _ h1 hr1 =>
      cases h1 with
      | step_stmts_cons =>
        rcases seq_reaches_exiting _ _ _ hr1 with h_loop | ⟨ρ_m, _h_term, h_tail⟩
        · exact LoopInitHoistLoopDriver.loopDet_no_exit
            (fun ρ0 hif lbl0 ρe0 => ih_lbody { ρ0 with hasFailure := ρ0.hasFailure || hif } lbl0 ρe0)
            h_loop
        · exact ih_rest ρ_m lbl' ρe h_tail

/-! ## The body transport: `BodyTransport` derivation → `BodySimE`.

By induction on the `BodyTransport` derivation.  Each arm fires the per-statement
hoist replay (renamed set/predicate, recursive block/ite, renamed nested loop) and
sequences via the cons-shaped tail IH.  The nested-loop arm feeds the inner-body
IH into the renamed-guard loop driver (via `nestedLoop_stmtSimE`). -/
theorem Block.bodyTransport
    {extendEval : ExtendEval P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {body_src body_h : List (Stmt P (Cmd P))}
    (hrw : BodyTransport (P := P) A B subst body_src body_h)
    (h_subst_fst_A : ∀ a ∈ subst.map Prod.fst, a ∈ A)
    (h_A_subst_fst : ∀ a ∈ A, a ∈ subst.map Prod.fst)
    (h_subst_snd_B : ∀ b ∈ subst.map Prod.snd, b ∈ B)
    (h_src_nodup : (subst.map Prod.fst).Nodup)
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd)
    (h_tgt_nodup : (subst.map Prod.snd).Nodup)
    (h_wfvar   : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval)
    (h_wfcongr : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval)
    (h_wfsubst : ∀ ρ : Env P, WellFormedSemanticEvalSubstFvar ρ.eval)
    (h_wfdef   : ∀ ρ : Env P, WellFormedSemanticEvalDef ρ.eval) :
    BodySimE (extendEval := extendEval) A B subst body_src body_h := by
  classical
  induction hrw with
  | nil => exact bodySimE_nil A B subst
  | @init_set a b τ rhs md body_src body_h h_pair h_a_in_A h_b_in_B
      h_unique_a h_unique_b h_B_fresh_rhs _ ih =>
    refine bodySimE_cons ?_ ih
    -- head StmtSimE: init a → set b.
    unfold OptEStepBProvider.StmtSimE
    intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
    obtain ⟨σ_a, hf_a, h_init_eval, h_ρ_a_eq⟩ := stmt_cmd_terminal_inv' h_run
    obtain ⟨v, h_rhs_src, h_initstate, _wfv, _wfc⟩ :
        ∃ v, ρ_s.eval ρ_s.store rhs = .some v ∧
              InitState P ρ_s.store a v σ_a ∧
              WellFormedSemanticEvalVar ρ_s.eval ∧
              WellFormedSemanticEvalExprCongr ρ_s.eval := by
      cases h_init_eval with
      | eval_init h_eval h_is h_wfv h_wfc => exact ⟨_, h_eval, h_is, h_wfv, h_wfc⟩
    obtain ⟨h_is_a_none, h_is_a_some, h_is_other⟩ := h_initstate
    have h_hf_a : hf_a = false := by cases h_init_eval with | eval_init _ _ _ _ => rfl
    subst h_hf_a
    subst h_ρ_a_eq
    have h_rhs_hoist :
        ρ_h.eval ρ_h.store (substFvarMany rhs subst) = .some v := by
      have h := cond_transport' (δ := ρ_s.eval) (e := rhs)
        (σ_s := ρ_s.store) (σ_h := ρ_h.store)
        h_A_subst_fst h_src_nodup h_disjoint h_tgt_nodup
        h_B_fresh_rhs h_hinv
        (read_vars_def_of_eval (h_wfdef ρ_s) h_rhs_src)
        (h_wfcongr ρ_s) (h_wfsubst ρ_s)
      rw [← h_eval, ← h]; exact h_rhs_src
    obtain ⟨v_old, h_b_old⟩ := Option.ne_none_iff_exists'.mp (h_bnd b h_b_in_B)
    have h_update : UpdateState P ρ_h.store b v (extendStoreOne ρ_h.store b v) :=
      .update h_b_old (extendStoreOne_self ρ_h.store b v)
        (fun z hz => extendStoreOne_other ρ_h.store b v z (fun h => hz h.symm))
    have h_set_eval : EvalCmd P ρ_h.eval ρ_h.store
        (.set b (.det (substFvarMany rhs subst)) md)
        (extendStoreOne ρ_h.store b v) false :=
      .eval_set h_rhs_hoist h_update (h_wfvar ρ_h) (h_wfcongr ρ_h)
    have h_σa_ext : σ_a = extendStoreOne ρ_s.store a v := by
      funext z
      by_cases hza : z = a
      · subst z
        have e1 : σ_a a = some v := h_is_a_some
        have e2 : extendStoreOne ρ_s.store a v a = some v := extendStoreOne_self ρ_s.store a v
        rw [e1, e2]
      · have e1 : σ_a z = ρ_s.store z := h_is_other z (fun h => hza h.symm)
        have e2 : extendStoreOne ρ_s.store a v z = ρ_s.store z :=
          extendStoreOne_other ρ_s.store a v z hza
        rw [e1, e2]
    have h_hinv_mid : HoistInv (P := P) A B subst
        σ_a (extendStoreOne ρ_h.store b v) := by
      rw [h_σa_ext]
      exact HoistInv.set_both_in_subst (a := a) (b := b) (v := v)
        h_pair h_a_in_A h_b_in_B h_unique_a h_unique_b h_hinv
    obtain ⟨ρ_h', h_ρ_h'⟩ : ∃ em : Env P,
        em = { ρ_h with store := extendStoreOne ρ_h.store b v, hasFailure := ρ_h.hasFailure || false } := ⟨_, rfl⟩
    have h_store' : ρ_h'.store = extendStoreOne ρ_h.store b v := congrArg (·.store) h_ρ_h'
    have h_eval' : ρ_h'.eval = ρ_h.eval := congrArg (·.eval) h_ρ_h'
    have h_hf' : ρ_h'.hasFailure = (ρ_h.hasFailure || false) := congrArg (·.hasFailure) h_ρ_h'
    refine ⟨ρ_h', ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ρ_h']; exact stmt_cmd_step_forward' h_set_eval
    · rw [h_store']; exact h_hinv_mid
    · rw [h_hf']; simp only [Bool.or_false]; exact h_hf
    · intro b' hb'
      rw [h_store']
      by_cases hb'b : b' = b
      · subst hb'b
        have e : extendStoreOne ρ_h.store b' v b' = some v := extendStoreOne_self ρ_h.store b' v
        rw [e]; exact Option.some_ne_none v
      · have e : extendStoreOne ρ_h.store b v b' = ρ_h.store b' :=
          extendStoreOne_other ρ_h.store b v b' hb'b
        rw [e]; exact h_bnd b' hb'
    · rw [h_eval']; exact h_eval
  | @init_nondet a b τ md body_src body_h h_pair h_a_in_A h_b_in_B
      h_unique_a h_unique_b _ ih =>
    refine bodySimE_cons ?_ ih
    -- head StmtSimE: nondet init a → nondet set b (replays the SAME chosen value).
    unfold OptEStepBProvider.StmtSimE
    intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
    obtain ⟨σ_a, hf_a, h_init_eval, h_ρ_a_eq⟩ := stmt_cmd_terminal_inv' h_run
    obtain ⟨v, h_initstate, _wfv⟩ :
        ∃ v, InitState P ρ_s.store a v σ_a ∧ WellFormedSemanticEvalVar ρ_s.eval := by
      cases h_init_eval with
      | eval_init_unconstrained h_is h_wfv => exact ⟨_, h_is, h_wfv⟩
    obtain ⟨h_is_a_none, h_is_a_some, h_is_other⟩ := h_initstate
    have h_hf_a : hf_a = false := by cases h_init_eval with | eval_init_unconstrained _ _ => rfl
    subst h_hf_a
    subst h_ρ_a_eq
    obtain ⟨v_old, h_b_old⟩ := Option.ne_none_iff_exists'.mp (h_bnd b h_b_in_B)
    have h_update : UpdateState P ρ_h.store b v (extendStoreOne ρ_h.store b v) :=
      .update h_b_old (extendStoreOne_self ρ_h.store b v)
        (fun z hz => extendStoreOne_other ρ_h.store b v z (fun h => hz h.symm))
    have h_set_eval : EvalCmd P ρ_h.eval ρ_h.store
        (.set b .nondet md) (extendStoreOne ρ_h.store b v) false :=
      .eval_set_nondet h_update (h_wfvar ρ_h)
    have h_σa_ext : σ_a = extendStoreOne ρ_s.store a v := by
      funext z
      by_cases hza : z = a
      · subst z
        have e1 : σ_a a = some v := h_is_a_some
        have e2 : extendStoreOne ρ_s.store a v a = some v := extendStoreOne_self ρ_s.store a v
        rw [e1, e2]
      · have e1 : σ_a z = ρ_s.store z := h_is_other z (fun h => hza h.symm)
        have e2 : extendStoreOne ρ_s.store a v z = ρ_s.store z :=
          extendStoreOne_other ρ_s.store a v z hza
        rw [e1, e2]
    have h_hinv_mid : HoistInv (P := P) A B subst
        σ_a (extendStoreOne ρ_h.store b v) := by
      rw [h_σa_ext]
      exact HoistInv.set_both_in_subst (a := a) (b := b) (v := v)
        h_pair h_a_in_A h_b_in_B h_unique_a h_unique_b h_hinv
    obtain ⟨ρ_h', h_ρ_h'⟩ : ∃ em : Env P,
        em = { ρ_h with store := extendStoreOne ρ_h.store b v, hasFailure := ρ_h.hasFailure || false } := ⟨_, rfl⟩
    have h_store' : ρ_h'.store = extendStoreOne ρ_h.store b v := congrArg (·.store) h_ρ_h'
    have h_eval' : ρ_h'.eval = ρ_h.eval := congrArg (·.eval) h_ρ_h'
    have h_hf' : ρ_h'.hasFailure = (ρ_h.hasFailure || false) := congrArg (·.hasFailure) h_ρ_h'
    refine ⟨ρ_h', ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ρ_h']; exact stmt_cmd_step_forward' h_set_eval
    · rw [h_store']; exact h_hinv_mid
    · rw [h_hf']; simp only [Bool.or_false]; exact h_hf
    · intro b' hb'
      rw [h_store']
      by_cases hb'b : b' = b
      · subst hb'b
        have e : extendStoreOne ρ_h.store b' v b' = some v := extendStoreOne_self ρ_h.store b' v
        rw [e]; exact Option.some_ne_none v
      · have e : extendStoreOne ρ_h.store b v b' = ρ_h.store b' :=
          extendStoreOne_other ρ_h.store b v b' hb'b
        rw [e]; exact h_bnd b' hb'
    · rw [h_eval']; exact h_eval
  | @set_renamed a b rhs md body_src body_h h_pair h_a_in_A h_b_in_B
      h_unique_a h_unique_b h_B_fresh_rhs _ ih =>
    refine bodySimE_cons ?_ ih
    -- head StmtSimE: set a (.det rhs) → set b (.det (substFvarMany rhs subst)).
    -- The LHS `a` is a rename SOURCE, renamed to its target `b`.  The source updates
    -- slot `a` (def → `v`); the hoist updates slot `b` (def → the SAME `v`) — exactly
    -- the `set_both_in_subst` transport that `init_set` uses for its hoist set side.
    unfold OptEStepBProvider.StmtSimE
    intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
    obtain ⟨σ_a, hf_a, h_set_eval_src, h_ρ_a_eq⟩ := stmt_cmd_terminal_inv' h_run
    obtain ⟨v, v_old, h_rhs_src, h_us_a_some_old, h_us_a_some, h_us_other⟩ :
        ∃ v v_old, ρ_s.eval ρ_s.store rhs = .some v ∧
              ρ_s.store a = .some v_old ∧ σ_a a = .some v ∧
              (∀ y, a ≠ y → σ_a y = ρ_s.store y) := by
      cases h_set_eval_src with
      | eval_set h_eval h_us h_wfv h_wfc =>
        cases h_us with
        | update h1 h2 h3 => exact ⟨_, _, h_eval, h1, h2, h3⟩
    have h_hf_a : hf_a = false := by cases h_set_eval_src with | eval_set _ _ _ _ => rfl
    subst h_hf_a
    subst h_ρ_a_eq
    have h_rhs_hoist :
        ρ_h.eval ρ_h.store (substFvarMany rhs subst) = .some v := by
      have h := cond_transport' (δ := ρ_s.eval) (e := rhs)
        (σ_s := ρ_s.store) (σ_h := ρ_h.store)
        h_A_subst_fst h_src_nodup h_disjoint h_tgt_nodup
        h_B_fresh_rhs h_hinv
        (read_vars_def_of_eval (h_wfdef ρ_s) h_rhs_src)
        (h_wfcongr ρ_s) (h_wfsubst ρ_s)
      rw [← h_eval, ← h]; exact h_rhs_src
    obtain ⟨v_old_b, h_b_old⟩ := Option.ne_none_iff_exists'.mp (h_bnd b h_b_in_B)
    have h_update : UpdateState P ρ_h.store b v (extendStoreOne ρ_h.store b v) :=
      .update h_b_old (extendStoreOne_self ρ_h.store b v)
        (fun z hz => extendStoreOne_other ρ_h.store b v z (fun h => hz h.symm))
    have h_set_eval : EvalCmd P ρ_h.eval ρ_h.store
        (.set b (.det (substFvarMany rhs subst)) md)
        (extendStoreOne ρ_h.store b v) false :=
      .eval_set h_rhs_hoist h_update (h_wfvar ρ_h) (h_wfcongr ρ_h)
    have h_σa_ext : σ_a = extendStoreOne ρ_s.store a v := by
      funext z
      by_cases hza : z = a
      · subst z
        have e1 : σ_a a = some v := h_us_a_some
        have e2 : extendStoreOne ρ_s.store a v a = some v := extendStoreOne_self ρ_s.store a v
        rw [e1, e2]
      · have e1 : σ_a z = ρ_s.store z := h_us_other z (fun h => hza h.symm)
        have e2 : extendStoreOne ρ_s.store a v z = ρ_s.store z :=
          extendStoreOne_other ρ_s.store a v z hza
        rw [e1, e2]
    have h_hinv_mid : HoistInv (P := P) A B subst
        σ_a (extendStoreOne ρ_h.store b v) := by
      rw [h_σa_ext]
      exact HoistInv.set_both_in_subst (a := a) (b := b) (v := v)
        h_pair h_a_in_A h_b_in_B h_unique_a h_unique_b h_hinv
    obtain ⟨ρ_h', h_ρ_h'⟩ : ∃ em : Env P,
        em = { ρ_h with store := extendStoreOne ρ_h.store b v, hasFailure := ρ_h.hasFailure || false } := ⟨_, rfl⟩
    have h_store' : ρ_h'.store = extendStoreOne ρ_h.store b v := congrArg (·.store) h_ρ_h'
    have h_eval' : ρ_h'.eval = ρ_h.eval := congrArg (·.eval) h_ρ_h'
    have h_hf' : ρ_h'.hasFailure = (ρ_h.hasFailure || false) := congrArg (·.hasFailure) h_ρ_h'
    refine ⟨ρ_h', ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ρ_h']; exact stmt_cmd_step_forward' h_set_eval
    · rw [h_store']; exact h_hinv_mid
    · rw [h_hf']; simp only [Bool.or_false]; exact h_hf
    · intro b' hb'
      rw [h_store']
      by_cases hb'b : b' = b
      · subst hb'b
        have e : extendStoreOne ρ_h.store b' v b' = some v := extendStoreOne_self ρ_h.store b' v
        rw [e]; exact Option.some_ne_none v
      · have e : extendStoreOne ρ_h.store b v b' = ρ_h.store b' :=
          extendStoreOne_other ρ_h.store b v b' hb'b
        rw [e]; exact h_bnd b' hb'
    · rw [h_eval']; exact h_eval
  | @set_renamed_nondet a b md body_src body_h h_pair h_a_in_A h_b_in_B
      h_unique_a h_unique_b _ ih =>
    refine bodySimE_cons ?_ ih
    -- head StmtSimE: nondet set a → nondet set b (replays the SAME chosen value).
    -- The LHS `a` is a rename source, renamed to `b`; `set_both_in_subst` transport.
    unfold OptEStepBProvider.StmtSimE
    intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
    obtain ⟨σ_a, hf_a, h_set_eval_src, h_ρ_a_eq⟩ := stmt_cmd_terminal_inv' h_run
    obtain ⟨v, v_old, h_us_a_some_old, h_us_a_some, h_us_other⟩ :
        ∃ v v_old, ρ_s.store a = .some v_old ∧ σ_a a = .some v ∧
              (∀ y, a ≠ y → σ_a y = ρ_s.store y) := by
      cases h_set_eval_src with
      | eval_set_nondet h_us h_wfv =>
        cases h_us with
        | update h1 h2 h3 => exact ⟨_, _, h1, h2, h3⟩
    have h_hf_a : hf_a = false := by cases h_set_eval_src with | eval_set_nondet _ _ => rfl
    subst h_hf_a
    subst h_ρ_a_eq
    obtain ⟨v_old_b, h_b_old⟩ := Option.ne_none_iff_exists'.mp (h_bnd b h_b_in_B)
    have h_update : UpdateState P ρ_h.store b v (extendStoreOne ρ_h.store b v) :=
      .update h_b_old (extendStoreOne_self ρ_h.store b v)
        (fun z hz => extendStoreOne_other ρ_h.store b v z (fun h => hz h.symm))
    have h_set_eval : EvalCmd P ρ_h.eval ρ_h.store
        (.set b .nondet md) (extendStoreOne ρ_h.store b v) false :=
      .eval_set_nondet h_update (h_wfvar ρ_h)
    have h_σa_ext : σ_a = extendStoreOne ρ_s.store a v := by
      funext z
      by_cases hza : z = a
      · subst z
        have e1 : σ_a a = some v := h_us_a_some
        have e2 : extendStoreOne ρ_s.store a v a = some v := extendStoreOne_self ρ_s.store a v
        rw [e1, e2]
      · have e1 : σ_a z = ρ_s.store z := h_us_other z (fun h => hza h.symm)
        have e2 : extendStoreOne ρ_s.store a v z = ρ_s.store z :=
          extendStoreOne_other ρ_s.store a v z hza
        rw [e1, e2]
    have h_hinv_mid : HoistInv (P := P) A B subst
        σ_a (extendStoreOne ρ_h.store b v) := by
      rw [h_σa_ext]
      exact HoistInv.set_both_in_subst (a := a) (b := b) (v := v)
        h_pair h_a_in_A h_b_in_B h_unique_a h_unique_b h_hinv
    obtain ⟨ρ_h', h_ρ_h'⟩ : ∃ em : Env P,
        em = { ρ_h with store := extendStoreOne ρ_h.store b v, hasFailure := ρ_h.hasFailure || false } := ⟨_, rfl⟩
    have h_store' : ρ_h'.store = extendStoreOne ρ_h.store b v := congrArg (·.store) h_ρ_h'
    have h_eval' : ρ_h'.eval = ρ_h.eval := congrArg (·.eval) h_ρ_h'
    have h_hf' : ρ_h'.hasFailure = (ρ_h.hasFailure || false) := congrArg (·.hasFailure) h_ρ_h'
    refine ⟨ρ_h', ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ρ_h']; exact stmt_cmd_step_forward' h_set_eval
    · rw [h_store']; exact h_hinv_mid
    · rw [h_hf']; simp only [Bool.or_false]; exact h_hf
    · intro b' hb'
      rw [h_store']
      by_cases hb'b : b' = b
      · subst hb'b
        have e : extendStoreOne ρ_h.store b' v b' = some v := extendStoreOne_self ρ_h.store b' v
        rw [e]; exact Option.some_ne_none v
      · have e : extendStoreOne ρ_h.store b v b' = ρ_h.store b' :=
          extendStoreOne_other ρ_h.store b v b' hb'b
        rw [e]; exact h_bnd b' hb'
    · rw [h_eval']; exact h_eval
  | @set name rhs md body_src body_h h_name_notin_A h_name_notin_B
      h_B_fresh_rhs _ ih =>
    refine bodySimE_cons ?_ ih
    -- head StmtSimE: set name (.det rhs) → set name (.det (substFvarMany rhs subst)).
    -- The name is UNCHANGED (it is `∉ A`, and the subst sources lie in `A`), so both
    -- sides update the SAME slot, off the subst frame — `extend_both_outside_subst`.
    unfold OptEStepBProvider.StmtSimE
    intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
    obtain ⟨σ_a, hf_a, h_set_eval_src, h_ρ_a_eq⟩ := stmt_cmd_terminal_inv' h_run
    obtain ⟨v, v_old, h_rhs_src, h_us_name_some_old, h_us_name_some, h_us_other⟩ :
        ∃ v v_old, ρ_s.eval ρ_s.store rhs = .some v ∧
              ρ_s.store name = .some v_old ∧ σ_a name = .some v ∧
              (∀ y, name ≠ y → σ_a y = ρ_s.store y) := by
      cases h_set_eval_src with
      | eval_set h_eval h_us h_wfv h_wfc =>
        cases h_us with
        | update h1 h2 h3 => exact ⟨_, _, h_eval, h1, h2, h3⟩
    have h_hf_a : hf_a = false := by cases h_set_eval_src with | eval_set _ _ _ _ => rfl
    subst h_hf_a
    subst h_ρ_a_eq
    have h_rhs_hoist :
        ρ_h.eval ρ_h.store (substFvarMany rhs subst) = .some v := by
      have h := cond_transport' (δ := ρ_s.eval) (e := rhs)
        (σ_s := ρ_s.store) (σ_h := ρ_h.store)
        h_A_subst_fst h_src_nodup h_disjoint h_tgt_nodup
        h_B_fresh_rhs h_hinv
        (read_vars_def_of_eval (h_wfdef ρ_s) h_rhs_src)
        (h_wfcongr ρ_s) (h_wfsubst ρ_s)
      rw [← h_eval, ← h]; exact h_rhs_src
    -- name is bound on the hoist side (it equals the source slot, which is `some`).
    -- The frame read needs `name` defined in the source: it IS (`set` updates a
    -- previously-bound slot, so `ρ_s.store name = some v_old`).
    have h_name_src_ne : ρ_s.store name ≠ none := by rw [h_us_name_some_old]; exact Option.some_ne_none v_old
    have h_name_src_eq_hoist : ρ_s.store name = ρ_h.store name :=
      h_hinv.1 name h_name_notin_A h_name_notin_B h_name_src_ne
    have h_name_hoist_some : ρ_h.store name = some v_old := by
      rw [← h_name_src_eq_hoist]; exact h_us_name_some_old
    have h_update : UpdateState P ρ_h.store name v (extendStoreOne ρ_h.store name v) :=
      .update h_name_hoist_some (extendStoreOne_self ρ_h.store name v)
        (fun z hz => extendStoreOne_other ρ_h.store name v z (fun h => hz h.symm))
    have h_set_eval : EvalCmd P ρ_h.eval ρ_h.store
        (.set name (.det (substFvarMany rhs subst)) md)
        (extendStoreOne ρ_h.store name v) false :=
      .eval_set h_rhs_hoist h_update (h_wfvar ρ_h) (h_wfcongr ρ_h)
    have h_σa_ext : σ_a = extendStoreOne ρ_s.store name v := by
      funext z
      by_cases hzn : z = name
      · subst z
        have e1 : σ_a name = some v := h_us_name_some
        have e2 : extendStoreOne ρ_s.store name v name = some v := extendStoreOne_self ρ_s.store name v
        rw [e1, e2]
      · have e1 : σ_a z = ρ_s.store z := h_us_other z (fun h => hzn h.symm)
        have e2 : extendStoreOne ρ_s.store name v z = ρ_s.store z :=
          extendStoreOne_other ρ_s.store name v z hzn
        rw [e1, e2]
    have h_hinv_mid : HoistInv (P := P) A B subst
        σ_a (extendStoreOne ρ_h.store name v) := by
      rw [h_σa_ext]
      exact HoistInv.extend_both_outside_subst (x := name) (v := v)
        h_name_notin_A h_name_notin_B
        (fun a' b' hp => ⟨h_subst_fst_A a' (List.mem_map.mpr ⟨(a', b'), hp, rfl⟩),
          h_subst_snd_B b' (List.mem_map.mpr ⟨(a', b'), hp, rfl⟩)⟩)
        h_hinv
    obtain ⟨ρ_h', h_ρ_h'⟩ : ∃ em : Env P,
        em = { ρ_h with store := extendStoreOne ρ_h.store name v, hasFailure := ρ_h.hasFailure || false } := ⟨_, rfl⟩
    have h_store' : ρ_h'.store = extendStoreOne ρ_h.store name v := congrArg (·.store) h_ρ_h'
    have h_eval' : ρ_h'.eval = ρ_h.eval := congrArg (·.eval) h_ρ_h'
    have h_hf' : ρ_h'.hasFailure = (ρ_h.hasFailure || false) := congrArg (·.hasFailure) h_ρ_h'
    refine ⟨ρ_h', ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ρ_h']; exact stmt_cmd_step_forward' h_set_eval
    · rw [h_store']; exact h_hinv_mid
    · rw [h_hf']; simp only [Bool.or_false]; exact h_hf
    · intro b' hb'
      rw [h_store']
      by_cases hb'n : b' = name
      · subst hb'n
        have e : extendStoreOne ρ_h.store b' v b' = some v := extendStoreOne_self ρ_h.store b' v
        rw [e]; exact Option.some_ne_none v
      · have e : extendStoreOne ρ_h.store name v b' = ρ_h.store b' :=
          extendStoreOne_other ρ_h.store name v b' hb'n
        rw [e]; exact h_bnd b' hb'
    · rw [h_eval']; exact h_eval
  | @set_nondet name md body_src body_h h_name_notin_A h_name_notin_B _ ih =>
    refine bodySimE_cons ?_ ih
    -- head StmtSimE: nondet set name → nondet set name (same slot, off the frame).
    unfold OptEStepBProvider.StmtSimE
    intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
    obtain ⟨σ_a, hf_a, h_set_eval_src, h_ρ_a_eq⟩ := stmt_cmd_terminal_inv' h_run
    obtain ⟨v, v_old, h_us_name_some_old, h_us_name_some, h_us_other⟩ :
        ∃ v v_old, ρ_s.store name = .some v_old ∧ σ_a name = .some v ∧
              (∀ y, name ≠ y → σ_a y = ρ_s.store y) := by
      cases h_set_eval_src with
      | eval_set_nondet h_us h_wfv =>
        cases h_us with
        | update h1 h2 h3 => exact ⟨_, _, h1, h2, h3⟩
    have h_hf_a : hf_a = false := by cases h_set_eval_src with | eval_set_nondet _ _ => rfl
    subst h_hf_a
    subst h_ρ_a_eq
    have h_name_src_ne : ρ_s.store name ≠ none := by rw [h_us_name_some_old]; exact Option.some_ne_none v_old
    have h_name_src_eq_hoist : ρ_s.store name = ρ_h.store name :=
      h_hinv.1 name h_name_notin_A h_name_notin_B h_name_src_ne
    have h_name_hoist_some : ρ_h.store name = some v_old := by
      rw [← h_name_src_eq_hoist]; exact h_us_name_some_old
    have h_update : UpdateState P ρ_h.store name v (extendStoreOne ρ_h.store name v) :=
      .update h_name_hoist_some (extendStoreOne_self ρ_h.store name v)
        (fun z hz => extendStoreOne_other ρ_h.store name v z (fun h => hz h.symm))
    have h_set_eval : EvalCmd P ρ_h.eval ρ_h.store
        (.set name .nondet md) (extendStoreOne ρ_h.store name v) false :=
      .eval_set_nondet h_update (h_wfvar ρ_h)
    have h_σa_ext : σ_a = extendStoreOne ρ_s.store name v := by
      funext z
      by_cases hzn : z = name
      · subst z
        have e1 : σ_a name = some v := h_us_name_some
        have e2 : extendStoreOne ρ_s.store name v name = some v := extendStoreOne_self ρ_s.store name v
        rw [e1, e2]
      · have e1 : σ_a z = ρ_s.store z := h_us_other z (fun h => hzn h.symm)
        have e2 : extendStoreOne ρ_s.store name v z = ρ_s.store z :=
          extendStoreOne_other ρ_s.store name v z hzn
        rw [e1, e2]
    have h_hinv_mid : HoistInv (P := P) A B subst
        σ_a (extendStoreOne ρ_h.store name v) := by
      rw [h_σa_ext]
      exact HoistInv.extend_both_outside_subst (x := name) (v := v)
        h_name_notin_A h_name_notin_B
        (fun a' b' hp => ⟨h_subst_fst_A a' (List.mem_map.mpr ⟨(a', b'), hp, rfl⟩),
          h_subst_snd_B b' (List.mem_map.mpr ⟨(a', b'), hp, rfl⟩)⟩)
        h_hinv
    obtain ⟨ρ_h', h_ρ_h'⟩ : ∃ em : Env P,
        em = { ρ_h with store := extendStoreOne ρ_h.store name v, hasFailure := ρ_h.hasFailure || false } := ⟨_, rfl⟩
    have h_store' : ρ_h'.store = extendStoreOne ρ_h.store name v := congrArg (·.store) h_ρ_h'
    have h_eval' : ρ_h'.eval = ρ_h.eval := congrArg (·.eval) h_ρ_h'
    have h_hf' : ρ_h'.hasFailure = (ρ_h.hasFailure || false) := congrArg (·.hasFailure) h_ρ_h'
    refine ⟨ρ_h', ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ρ_h']; exact stmt_cmd_step_forward' h_set_eval
    · rw [h_store']; exact h_hinv_mid
    · rw [h_hf']; simp only [Bool.or_false]; exact h_hf
    · intro b' hb'
      rw [h_store']
      by_cases hb'n : b' = name
      · subst hb'n
        have e : extendStoreOne ρ_h.store b' v b' = some v := extendStoreOne_self ρ_h.store b' v
        rw [e]; exact Option.some_ne_none v
      · have e : extendStoreOne ρ_h.store name v b' = ρ_h.store b' :=
          extendStoreOne_other ρ_h.store name v b' hb'n
        rw [e]; exact h_bnd b' hb'
    · rw [h_eval']; exact h_eval
  | @assert lbl e md body_src body_h h_B_fresh_e _ ih =>
    refine bodySimE_cons ?_ ih
    unfold OptEStepBProvider.StmtSimE
    intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
    obtain ⟨σ_a, hf_a, h_head_eval, h_ρ_a_eq⟩ := stmt_cmd_terminal_inv' h_run
    have h_store_eq : σ_a = ρ_s.store := by
      cases h_head_eval with
      | eval_assert_pass _ _ _ => rfl
      | eval_assert_fail _ _ _ => rfl
    have h_e_some : ∃ w, ρ_s.eval ρ_s.store e = some w := by
      cases h_head_eval with
      | eval_assert_pass h_tt _ _ => exact ⟨_, h_tt⟩
      | eval_assert_fail h_ff _ _ => exact ⟨_, h_ff⟩
    have h_cond : ρ_s.eval ρ_s.store e =
        ρ_h.eval ρ_h.store (substFvarMany e subst) := by
      rw [← h_eval]
      obtain ⟨w, h_e_w⟩ := h_e_some
      exact cond_transport' (δ := ρ_s.eval) (e := e) (σ_s := ρ_s.store) (σ_h := ρ_h.store)
        h_A_subst_fst h_src_nodup h_disjoint h_tgt_nodup
        h_B_fresh_e h_hinv
        (read_vars_def_of_eval (h_wfdef ρ_s) h_e_w)
        (h_wfcongr ρ_s) (h_wfsubst ρ_s)
    have h_assert_hoist : EvalCmd P ρ_h.eval ρ_h.store
        (.assert lbl (substFvarMany e subst) md) ρ_h.store hf_a := by
      cases h_head_eval with
      | eval_assert_pass h_tt h_wfb _ =>
        exact .eval_assert_pass (by rw [← h_cond]; exact h_tt) (h_eval ▸ h_wfb) (h_wfcongr ρ_h)
      | eval_assert_fail h_ff h_wfb _ =>
        exact .eval_assert_fail (by rw [← h_cond]; exact h_ff) (h_eval ▸ h_wfb) (h_wfcongr ρ_h)
    subst h_ρ_a_eq
    obtain ⟨ρ_h', h_ρ_h'⟩ : ∃ em : Env P,
        em = { ρ_h with store := ρ_h.store, hasFailure := ρ_h.hasFailure || hf_a } := ⟨_, rfl⟩
    have h_store' : ρ_h'.store = ρ_h.store := congrArg (·.store) h_ρ_h'
    have h_eval' : ρ_h'.eval = ρ_h.eval := congrArg (·.eval) h_ρ_h'
    have h_hf' : ρ_h'.hasFailure = (ρ_h.hasFailure || hf_a) := congrArg (·.hasFailure) h_ρ_h'
    refine ⟨ρ_h', ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ρ_h']; exact stmt_cmd_step_forward' h_assert_hoist
    · rw [h_store', h_store_eq]; exact h_hinv
    · rw [h_hf']; rw [h_hf]
    · intro b' hb'; rw [h_store']; exact h_bnd b' hb'
    · rw [h_eval']; exact h_eval
  | @assume lbl e md body_src body_h h_B_fresh_e _ ih =>
    refine bodySimE_cons ?_ ih
    unfold OptEStepBProvider.StmtSimE
    intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
    obtain ⟨σ_a, hf_a, h_head_eval, h_ρ_a_eq⟩ := stmt_cmd_terminal_inv' h_run
    have h_store_eq : σ_a = ρ_s.store := by cases h_head_eval with | eval_assume _ _ _ => rfl
    have h_hf_a : hf_a = false := by cases h_head_eval with | eval_assume _ _ _ => rfl
    have h_e_some : ∃ w, ρ_s.eval ρ_s.store e = some w := by
      cases h_head_eval with | eval_assume h_tt _ _ => exact ⟨_, h_tt⟩
    have h_cond : ρ_s.eval ρ_s.store e =
        ρ_h.eval ρ_h.store (substFvarMany e subst) := by
      rw [← h_eval]
      obtain ⟨w, h_e_w⟩ := h_e_some
      exact cond_transport' (δ := ρ_s.eval) (e := e) (σ_s := ρ_s.store) (σ_h := ρ_h.store)
        h_A_subst_fst h_src_nodup h_disjoint h_tgt_nodup
        h_B_fresh_e h_hinv
        (read_vars_def_of_eval (h_wfdef ρ_s) h_e_w)
        (h_wfcongr ρ_s) (h_wfsubst ρ_s)
    have h_assume_hoist : EvalCmd P ρ_h.eval ρ_h.store
        (.assume lbl (substFvarMany e subst) md) ρ_h.store false := by
      cases h_head_eval with
      | eval_assume h_tt h_wfb _ =>
        exact .eval_assume (by rw [← h_cond]; exact h_tt) (h_eval ▸ h_wfb) (h_wfcongr ρ_h)
    subst h_hf_a
    subst h_ρ_a_eq
    obtain ⟨ρ_h', h_ρ_h'⟩ : ∃ em : Env P,
        em = { ρ_h with store := ρ_h.store, hasFailure := ρ_h.hasFailure || false } := ⟨_, rfl⟩
    have h_store' : ρ_h'.store = ρ_h.store := congrArg (·.store) h_ρ_h'
    have h_eval' : ρ_h'.eval = ρ_h.eval := congrArg (·.eval) h_ρ_h'
    have h_hf' : ρ_h'.hasFailure = (ρ_h.hasFailure || false) := congrArg (·.hasFailure) h_ρ_h'
    refine ⟨ρ_h', ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ρ_h']; exact stmt_cmd_step_forward' h_assume_hoist
    · rw [h_store', h_store_eq]; exact h_hinv
    · rw [h_hf']; simp only [Bool.or_false]; exact h_hf
    · intro b' hb'; rw [h_store']; exact h_bnd b' hb'
    · rw [h_eval']; exact h_eval
  | @cover lbl e md body_src body_h _ ih =>
    refine bodySimE_cons ?_ ih
    unfold OptEStepBProvider.StmtSimE
    intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
    obtain ⟨σ_a, hf_a, h_head_eval, h_ρ_a_eq⟩ := stmt_cmd_terminal_inv' h_run
    have h_store_eq : σ_a = ρ_s.store := by cases h_head_eval with | eval_cover _ => rfl
    have h_hf_a : hf_a = false := by cases h_head_eval with | eval_cover _ => rfl
    have h_cover_hoist : EvalCmd P ρ_h.eval ρ_h.store
        (.cover lbl (substFvarMany e subst) md) ρ_h.store false := by
      cases h_head_eval with
      | eval_cover h_wfb => exact .eval_cover (h_eval ▸ h_wfb)
    subst h_hf_a
    subst h_ρ_a_eq
    obtain ⟨ρ_h', h_ρ_h'⟩ : ∃ em : Env P,
        em = { ρ_h with store := ρ_h.store, hasFailure := ρ_h.hasFailure || false } := ⟨_, rfl⟩
    have h_store' : ρ_h'.store = ρ_h.store := congrArg (·.store) h_ρ_h'
    have h_eval' : ρ_h'.eval = ρ_h.eval := congrArg (·.eval) h_ρ_h'
    have h_hf' : ρ_h'.hasFailure = (ρ_h.hasFailure || false) := congrArg (·.hasFailure) h_ρ_h'
    refine ⟨ρ_h', ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ρ_h']; exact stmt_cmd_step_forward' h_cover_hoist
    · rw [h_store', h_store_eq]; exact h_hinv
    · rw [h_hf']; simp only [Bool.or_false]; exact h_hf
    · intro b' hb'; rw [h_store']; exact h_bnd b' hb'
    · rw [h_eval']; exact h_eval
  | @typeDecl tc md body_src body_h _ ih =>
    refine bodySimE_cons ?_ ih
    -- head StmtSimE: a `.typeDecl` is a no-op on both sides (env unchanged).
    unfold OptEStepBProvider.StmtSimE
    intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
    have h_ρ_s'_eq : ρ_s' = ρ_s := typeDecl_terminal_inv' h_run
    subst h_ρ_s'_eq
    exact ⟨ρ_h, typeDecl_step_forward', h_hinv, h_hf, h_bnd, h_eval⟩
  | @block lbl md inner_src inner_h body_src body_h h_inner h_rest ih_inner ih_rest =>
    refine bodySimE_cons ?_ ih_rest
    unfold OptEStepBProvider.StmtSimE
    intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
    obtain ⟨ρ_inner, h_inner_run, h_ρ_a_eq⟩ :=
      block_terminal_inv' (h_inner.src_no_exit ρ_s) h_run
    obtain ⟨ρ_h_inner, h_inner_h_run, h_hinv_inner, h_hf_inner, h_bnd_inner, h_eval_inner⟩ :=
      ih_inner ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_inner h_inner_run
    have h_hinv_blk : HoistInv (P := P) A B subst
        (projectStore ρ_s.store ρ_inner.store)
        (projectStore ρ_h.store ρ_h_inner.store) :=
      HoistInv.project_both h_hinv h_hinv_inner
    obtain ⟨ρ_h', h_ρ_h'⟩ : ∃ em : Env P,
        em = { ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store } := ⟨_, rfl⟩
    have h_store' : ρ_h'.store = projectStore ρ_h.store ρ_h_inner.store := congrArg (·.store) h_ρ_h'
    have h_eval' : ρ_h'.eval = ρ_h_inner.eval := congrArg (·.eval) h_ρ_h'
    have h_hf' : ρ_h'.hasFailure = ρ_h_inner.hasFailure := congrArg (·.hasFailure) h_ρ_h'
    refine ⟨ρ_h', ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ρ_h']; exact block_step_forward' h_inner_h_run
    · rw [h_ρ_a_eq, h_store']; exact h_hinv_blk
    · rw [h_ρ_a_eq, h_hf']; exact h_hf_inner
    · intro b' hb'
      rw [h_store']
      show projectStore ρ_h.store ρ_h_inner.store b' ≠ none
      unfold projectStore
      have h_parent_some : (ρ_h.store b').isSome = true := by
        cases h : ρ_h.store b' with
        | none => exact absurd h (h_bnd b' hb')
        | some _ => rfl
      rw [h_parent_some]; simp; exact h_bnd_inner b' hb'
    · rw [h_ρ_a_eq, h_eval']; exact h_eval_inner
  | @ite g md tss_src tss_h ess_src ess_h body_src body_h
      h_B_fresh_g h_then h_else h_rest ih_then ih_else ih_rest =>
    refine bodySimE_cons ?_ ih_rest
    unfold OptEStepBProvider.StmtSimE
    intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
    -- Invert the source `.ite` run first to expose the (successful) guard
    -- evaluation, which discharges the guarded-frame read-var definedness.
    have h_g_some : ∃ w, ρ_s.eval ρ_s.store g = some w := by
      rcases ite_terminal_inv' h_run with
        ⟨h_g_tt, _, _⟩ | ⟨h_g_ff, _, _⟩
      · exact ⟨_, h_g_tt⟩
      · exact ⟨_, h_g_ff⟩
    -- The renamed guard `substFvarMany g subst` evaluates on `ρ_h` exactly as the
    -- source guard `g` on `ρ_s` (it reads no renamed name).
    have h_guard_eq : ρ_s.eval ρ_s.store g
        = ρ_h.eval ρ_h.store (substFvarMany g subst) := by
      obtain ⟨w, h_g_w⟩ := h_g_some
      have h := cond_transport' (δ := ρ_s.eval) (e := g) (σ_s := ρ_s.store) (σ_h := ρ_h.store)
        h_A_subst_fst h_src_nodup h_disjoint h_tgt_nodup
        h_B_fresh_g h_hinv
        (read_vars_def_of_eval (h_wfdef ρ_s) h_g_w)
        (h_wfcongr ρ_s) (h_wfsubst ρ_s)
      rw [h, h_eval]
    rcases ite_terminal_inv' h_run with
      ⟨h_g_tt, h_wfb, h_branch_run⟩ | ⟨h_g_ff, h_wfb, h_branch_run⟩
    · obtain ⟨ρ_h_a, h_branch_h, h_hinv_a, h_hf_a, h_bnd_a, h_eval_a⟩ :=
        ih_then ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_branch_run
      have h_g_tt_h : ρ_h.eval ρ_h.store (substFvarMany g subst) = .some HasBool.tt := by
        rw [← h_guard_eq]; exact h_g_tt
      have h_wfb_hoist : WellFormedSemanticEvalBool ρ_h.eval := h_eval ▸ h_wfb
      exact ⟨ρ_h_a, ite_step_then_forward' h_g_tt_h h_wfb_hoist h_branch_h,
        h_hinv_a, h_hf_a, h_bnd_a, h_eval_a⟩
    · obtain ⟨ρ_h_a, h_branch_h, h_hinv_a, h_hf_a, h_bnd_a, h_eval_a⟩ :=
        ih_else ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_branch_run
      have h_g_ff_h : ρ_h.eval ρ_h.store (substFvarMany g subst) = .some HasBool.ff := by
        rw [← h_guard_eq]; exact h_g_ff
      have h_wfb_hoist : WellFormedSemanticEvalBool ρ_h.eval := h_eval ▸ h_wfb
      exact ⟨ρ_h_a, ite_step_else_forward' h_g_ff_h h_wfb_hoist h_branch_h,
        h_hinv_a, h_hf_a, h_bnd_a, h_eval_a⟩
  | @ite_nondet md tss_src tss_h ess_src ess_h body_src body_h
      h_then h_else h_rest ih_then ih_else ih_rest =>
    refine bodySimE_cons ?_ ih_rest
    -- A nondet `.ite` makes no guard test; the hoist replays the SAME branch choice.
    unfold OptEStepBProvider.StmtSimE
    intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
    rcases ite_nondet_terminal_inv' h_run with h_branch_run | h_branch_run
    · obtain ⟨ρ_h_a, h_branch_h, h_hinv_a, h_hf_a, h_bnd_a, h_eval_a⟩ :=
        ih_then ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_branch_run
      exact ⟨ρ_h_a, ite_nondet_step_then_forward' h_branch_h,
        h_hinv_a, h_hf_a, h_bnd_a, h_eval_a⟩
    · obtain ⟨ρ_h_a, h_branch_h, h_hinv_a, h_hf_a, h_bnd_a, h_eval_a⟩ :=
        ih_else ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_branch_run
      exact ⟨ρ_h_a, ite_nondet_step_else_forward' h_branch_h,
        h_hinv_a, h_hf_a, h_bnd_a, h_eval_a⟩
  | @loop g md lbody_src lbody_h body_src body_h
      h_B_fresh_g h_lbody h_rest ih_lbody ih_rest =>
    refine bodySimE_cons ?_ ih_rest
    -- head StmtSimE for the renamed nested loop, via nestedLoop_stmtSimE.
    have inner_sim : BodySim (extendEval := extendEval) A B subst lbody_src lbody_h :=
      bodySimE_to_bodySim ih_lbody
    exact nestedLoop_stmtSimE (A := A) (B := B) (subst := subst)
      h_A_subst_fst h_src_nodup h_disjoint h_tgt_nodup h_B_fresh_g
      h_wfvar h_wfcongr h_wfsubst h_wfdef inner_sim
      (h_lbody.src_no_exit) h_lbody.noFuncDecl_src h_lbody.noFuncDecl_h

end LoopInitHoistBodyTransport
end Imperative

end -- public section
