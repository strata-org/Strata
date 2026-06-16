/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.LoopInitHoistLoopDriver
public import Strata.Transform.LoopInitHoistStepCProducer
public import Strata.Transform.LoopInitHoistContains

import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.Cmd
import all Strata.Transform.LoopInitHoist
import all Strata.Transform.LoopInitHoistContains
import all Strata.Transform.LoopInitHoistLoopDriver
import all Strata.Transform.LoopInitHoistStepCProducer
import all Strata.Transform.LoopInitHoistFreshness

public section

namespace Imperative
namespace LoopInitHoistLoopArmWF

open LoopInitHoistLoopDriver (Entry havocStmts' substOf' targetsOf' sourcesOf'
  Stmt.entriesOf Block.entriesOf
  Stmt.entriesOf_block Stmt.entriesOf_ite Block.entriesOf_cons
  Block.sourcesOf_entriesOf_subset)
open LoopInitHoistStepCProducer (Block.transportShape Block.transportShape_of_arm_preconds)
open _root_.StringGenState (GenStep)

variable {P : PureExpr}

/-- `targetsOf'` distributes over list append (companion to the `substOf'`/
`sourcesOf'`/`havocStmts'` append lemmas). -/
theorem targetsOf'_append (xs ys : List (Entry P)) :
    targetsOf' (xs ++ ys) = targetsOf' xs ++ targetsOf' ys := by
  simp [targetsOf', List.map_append]

/-! ## `namesFreshInExprs` is preserved by a single `substIdent` rename.

`Block.substIdent y y'` renames every free occurrence of `y` to `y'` in the
value positions (rhs / guards / invariants / measure) and rewrites the binding
positions. The freshness check `namesFreshInExprs` only inspects the value
positions, so by the `LawfulHasSubstFvar.substFvar_getVars_subset` law (a
renamed expression's read-set is the original's plus possibly `y'`) every
`names`-element that was fresh in the original stays fresh after the rename,
PROVIDED the new name `y'` is not itself in `names` (otherwise the rename could
introduce `y'` where `y` appeared). -/

/-- `freshFromIdents z vars = true` iff `z ∉ vars`. -/
private theorem freshFromIdents_eq_true_iff [DecidableEq P.Ident]
    {z : P.Ident} {vars : List P.Ident} :
    freshFromIdents z vars = true ↔ z ∉ vars := by
  constructor
  · intro h hmem
    unfold freshFromIdents at h
    rw [List.all_eq_true] at h
    have h_z := h z hmem
    have h_eq : (P.EqIdent z z).decide = true := by simp
    rw [h_eq] at h_z
    exact absurd h_z (by decide)
  · intro h
    unfold freshFromIdents
    rw [List.all_eq_true]
    intro v hmem
    simp only [decide_eq_true_eq]
    intro h_eq; subst h_eq; exact h hmem

/-- The read-set transfer law as a `freshFromIdents` fact: if `z ≠ y'` is fresh
in `e`'s read-set, it stays fresh after substituting `y → y'`. -/
private theorem freshFromIdents_substFvar [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P]
    {z y y' : P.Ident} (e : P.Expr)
    (h_ne : z ≠ y')
    (h : freshFromIdents z (HasVarsPure.getVars e) = true) :
    freshFromIdents z
      (HasVarsPure.getVars (HasSubstFvar.substFvar e y (HasFvar.mkFvar y'))) = true := by
  rw [freshFromIdents_eq_true_iff] at h ⊢
  intro hmem
  rcases LawfulHasSubstFvar.substFvar_getVars_subset e y y' z hmem with h_orig | h_y'
  · exact h h_orig
  · exact h_ne h_y'

/-- Same transfer law over `ExprOrNondet` (the `.nondet` case has empty
read-set, trivially preserved). -/
private theorem freshFromIdents_exprOrNondet_substIdent [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P]
    {z y y' : P.Ident} (e : ExprOrNondet P)
    (h_ne : z ≠ y')
    (h : freshFromIdents z (ExprOrNondet.getVars e) = true) :
    freshFromIdents z (ExprOrNondet.getVars (e.substIdent y y')) = true := by
  cases e with
  | det e => exact freshFromIdents_substFvar e h_ne h
  | nondet => simp only [ExprOrNondet.substIdent_nondet]; exact h

mutual
/-- `Stmt.substIdent y y'` preserves `Stmt.namesFreshInExprs names` whenever
`y' ∉ names`. -/
theorem Stmt.namesFreshInExprs_substIdent [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P]
    (names : List P.Ident) (y y' : P.Ident) (s : Stmt P (Cmd P))
    (h_y'_not : y' ∉ names)
    (h : Stmt.namesFreshInExprs names s = true) :
    Stmt.namesFreshInExprs names (Stmt.substIdent y y' s) = true := by
  cases s with
  | cmd c =>
    cases c with
    | init x ty rhs md =>
      simp only [Stmt.substIdent_cmd, Cmd.substIdent_init, Stmt.namesFreshInExprs,
                 List.all_eq_true] at h ⊢
      intro z hz
      exact freshFromIdents_exprOrNondet_substIdent rhs (fun he => h_y'_not (he ▸ hz)) (h z hz)
    | set x rhs md =>
      simp only [Stmt.substIdent_cmd, Cmd.substIdent_set, Stmt.namesFreshInExprs,
                 List.all_eq_true] at h ⊢
      intro z hz
      exact freshFromIdents_exprOrNondet_substIdent rhs (fun he => h_y'_not (he ▸ hz)) (h z hz)
    | assert l e md =>
      simp only [Stmt.substIdent_cmd, Cmd.substIdent_assert, Stmt.namesFreshInExprs,
                 List.all_eq_true] at h ⊢
      intro z hz
      exact freshFromIdents_substFvar e (fun he => h_y'_not (he ▸ hz)) (h z hz)
    | assume l e md =>
      simp only [Stmt.substIdent_cmd, Cmd.substIdent_assume, Stmt.namesFreshInExprs,
                 List.all_eq_true] at h ⊢
      intro z hz
      exact freshFromIdents_substFvar e (fun he => h_y'_not (he ▸ hz)) (h z hz)
    | cover l e md =>
      simp only [Stmt.substIdent_cmd, Cmd.substIdent_cover, Stmt.namesFreshInExprs,
                 List.all_eq_true] at h ⊢
      intro z hz
      exact freshFromIdents_substFvar e (fun he => h_y'_not (he ▸ hz)) (h z hz)
  | block lbl bss md =>
    simp only [Stmt.substIdent_block, Stmt.namesFreshInExprs] at h ⊢
    exact Block.namesFreshInExprs_substIdent names y y' bss h_y'_not h
  | ite g tss ess md =>
    simp only [Stmt.substIdent_ite, Stmt.namesFreshInExprs, Bool.and_eq_true,
               List.all_eq_true] at h ⊢
    obtain ⟨⟨h_g, h_t⟩, h_e⟩ := h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro z hz
      exact freshFromIdents_exprOrNondet_substIdent g (fun he => h_y'_not (he ▸ hz)) (h_g z hz)
    · exact Block.namesFreshInExprs_substIdent names y y' tss h_y'_not h_t
    · exact Block.namesFreshInExprs_substIdent names y y' ess h_y'_not h_e
  | loop g m inv body md =>
    rw [Stmt.substIdent_loop]
    unfold Stmt.namesFreshInExprs at h ⊢
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨⟨h_g, h_m⟩, h_inv⟩, h_body⟩ := h
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [List.all_eq_true] at h_g ⊢
      intro z hz
      exact freshFromIdents_exprOrNondet_substIdent g (fun he => h_y'_not (he ▸ hz)) (h_g z hz)
    · cases m with
      | none => simp only [Option.map_none]
      | some me =>
        simp only [Option.map_some] at h_m ⊢
        rw [List.all_eq_true] at h_m ⊢
        intro z hz
        exact freshFromIdents_substFvar me (fun he => h_y'_not (he ▸ hz)) (h_m z hz)
    · rw [List.all_eq_true] at h_inv ⊢
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨p0, hp0_mem, hp0_eq⟩ := hp
      subst hp0_eq
      have h_p := h_inv p0 hp0_mem
      rw [List.all_eq_true] at h_p ⊢
      intro z hz
      exact freshFromIdents_substFvar p0.2 (fun he => h_y'_not (he ▸ hz)) (h_p z hz)
    · exact Block.namesFreshInExprs_substIdent names y y' body h_y'_not h_body
  | exit lbl md =>
    simp only [Stmt.substIdent_exit, Stmt.namesFreshInExprs]
  | funcDecl d md =>
    simp only [Stmt.substIdent_funcDecl, Stmt.namesFreshInExprs]
  | typeDecl t md =>
    simp only [Stmt.substIdent_typeDecl, Stmt.namesFreshInExprs]
  termination_by sizeOf s

/-- `Block.substIdent y y'` preserves `Block.namesFreshInExprs names` whenever
`y' ∉ names`. -/
theorem Block.namesFreshInExprs_substIdent [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P]
    (names : List P.Ident) (y y' : P.Ident) (ss : List (Stmt P (Cmd P)))
    (h_y'_not : y' ∉ names)
    (h : Block.namesFreshInExprs names ss = true) :
    Block.namesFreshInExprs names (Block.substIdent y y' ss) = true := by
  match ss with
  | [] => simp only [Block.substIdent_nil, Block.namesFreshInExprs]
  | s :: rest =>
    simp only [Block.substIdent_cons, Block.namesFreshInExprs, Bool.and_eq_true] at h ⊢
    exact ⟨Stmt.namesFreshInExprs_substIdent names y y' s h_y'_not h.1,
           Block.namesFreshInExprs_substIdent names y y' rest h_y'_not h.2⟩
  termination_by sizeOf ss
end

/-- `Block.applyRenames` preserves `Block.namesFreshInExprs names` whenever
every rename TARGET (`renames.map Prod.snd`) is disjoint from `names`. The
sources may be in `names`; only the targets matter, because substitution can
only INTRODUCE the target (`y'`) into the value positions. -/
theorem Block.namesFreshInExprs_applyRenames [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P]
    (names : List P.Ident) (renames : List (P.Ident × P.Ident))
    (ss : List (Stmt P (Cmd P)))
    (h_tgt_not : ∀ p ∈ renames, p.2 ∉ names)
    (h : Block.namesFreshInExprs names ss = true) :
    Block.namesFreshInExprs names (Block.applyRenames renames ss) = true := by
  induction renames generalizing ss with
  | nil => simpa only [Block.applyRenames] using h
  | cons p rest ih =>
    rw [Block.applyRenames]
    simp only [List.foldl_cons]
    have h_step : Block.namesFreshInExprs names (Block.substIdent p.1 p.2 ss) = true :=
      Block.namesFreshInExprs_substIdent names p.1 p.2 ss
        (h_tgt_not p (List.mem_cons_self ..)) h
    have := ih (Block.substIdent p.1 p.2 ss)
      (fun q hq => h_tgt_not q (List.mem_cons_of_mem _ hq)) h_step
    rw [Block.applyRenames] at this
    exact this

/-- The MONADIC lift residual preserves `Block.namesFreshInExprs names` (no
name-list change).  The residual only ever rewrites `init`→`set` (rhs
unchanged) and recurses structurally; freshness transfers verbatim.  Bridged
from the pure-wrapper preservation via the state-independence of the residual
(`Block.liftInitsInLoopBody_snd_eq`). -/
theorem Block.liftInitsInLoopBodyM_snd_namesFreshInExprs [HasIdent P] [HasVarsPure P P.Expr]
    (names : List P.Ident) (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h : Block.namesFreshInExprs names ss = true) :
    Block.namesFreshInExprs names (Block.liftInitsInLoopBodyM ss σ).1.2.2 = true := by
  rw [← Block.liftInitsInLoopBody_snd_eq ss σ]
  exact Block.liftInitsInLoopBody_snd_namesFreshInExprs names ss h

/-! ## The harvest targets are generator-shaped (`_<digit>` suffix).

Every entry harvested by `Stmt/Block.entriesOf` has a target ident
`e.2.1 = HasIdent.ident s` for a generator string `s` (it is the `.1` of a
`StringGenState.gen` call), so `s` always has the `_<digit>` suffix shape.  This
lets us conclude that any name whose underlying string lacks that suffix is
disjoint from every rename TARGET the pass introduces — the precise condition
that `namesFreshInExprs_applyRenames` consumes. -/

mutual
/-- Every entry target harvested from a statement is a `Q`-kind ident, given the
mint witness `hQmint` that hoist's freshly minted names satisfy `Q`.
Instantiating `Q := String.HasUnderscoreDigitSuffix` with the `gen`-suffix
witness recovers the blanket "generator-suffixed" statement. -/
theorem Stmt.entriesOf_target_suffix [HasIdent P] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    ∀ e ∈ Stmt.entriesOf s σ,
      ∃ str : String, e.2.1 = HasIdent.ident str ∧ Q str := by
  match s with
  | .cmd c =>
      cases c with
      | init y ty rhs md =>
          intro e he
          rw [Stmt.entriesOf] at he
          simp only [List.mem_singleton] at he
          subst he
          exact ⟨(StringGenState.gen hoistFreshPrefix σ).1, rfl, hQmint σ⟩
      | set x rhs md => intro e he; simp only [Stmt.entriesOf, List.not_mem_nil] at he
      | assert l ex md => intro e he; simp only [Stmt.entriesOf, List.not_mem_nil] at he
      | assume l ex md => intro e he; simp only [Stmt.entriesOf, List.not_mem_nil] at he
      | cover l ex md => intro e he; simp only [Stmt.entriesOf, List.not_mem_nil] at he
  | .block lbl bss md =>
      rw [Stmt.entriesOf]; exact Block.entriesOf_target_suffix hQmint bss σ
  | .ite g tss ess md =>
      rw [Stmt.entriesOf, List.forall_mem_append]
      exact ⟨Block.entriesOf_target_suffix hQmint tss σ,
             Block.entriesOf_target_suffix hQmint ess (Block.liftInitsInLoopBodyM tss σ).2⟩
  | .loop g m inv body md => intro e he; simp only [Stmt.entriesOf, List.not_mem_nil] at he
  | .exit lbl md => intro e he; simp only [Stmt.entriesOf, List.not_mem_nil] at he
  | .funcDecl d md => intro e he; simp only [Stmt.entriesOf, List.not_mem_nil] at he
  | .typeDecl t md => intro e he; simp only [Stmt.entriesOf, List.not_mem_nil] at he
  termination_by sizeOf s

/-- Every entry target harvested from a block is a `Q`-kind ident. -/
theorem Block.entriesOf_target_suffix [HasIdent P] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∀ e ∈ Block.entriesOf ss σ,
      ∃ str : String, e.2.1 = HasIdent.ident str ∧ Q str := by
  match ss with
  | [] => intro e he; simp only [Block.entriesOf, List.not_mem_nil] at he
  | s :: rest =>
      rw [Block.entriesOf, List.forall_mem_append]
      exact ⟨Stmt.entriesOf_target_suffix hQmint s σ,
             Block.entriesOf_target_suffix hQmint rest (Stmt.liftInitsInLoopBodyM s σ).2⟩
  termination_by sizeOf ss
end

/-- Every rename pair produced by the monadic lift has a generator-suffixed
target.  (The renames are `substOf' (entriesOf …)`; their `.2` projection is the
entries' target idents.) -/
theorem Block.liftInitsInLoopBodyM_renames_target_suffix [HasIdent P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∀ p ∈ (Block.liftInitsInLoopBodyM ss σ).1.2.1,
      ∃ str : String, p.2 = HasIdent.ident str ∧ String.HasUnderscoreDigitSuffix str := by
  rw [(LoopInitHoistLoopDriver.Block.lift_harvest_subst ss σ).2]
  intro p hp
  -- `substOf' entries = entries.map (fun e => (e.1, e.2.1))`, so `p.2 = e.2.1`.
  simp only [LoopInitHoistLoopDriver.substOf', List.mem_map] at hp
  obtain ⟨e, he_mem, he_eq⟩ := hp
  subst he_eq
  exact Block.entriesOf_target_suffix
    (fun sg => StringGenState.gen_hasUnderscoreDigitSuffix hoistFreshPrefix sg) ss σ e he_mem

/-- The havoc prelude `havocStmts' E` is always fresh in any `names`: every
havoc cmd is `init target ty .nondet md` whose rhs has empty read-set. -/
theorem namesFreshInExprs_havocStmts' [HasVarsPure P P.Expr]
    (names : List P.Ident) (entries : List (Entry P)) :
    Block.namesFreshInExprs names (havocStmts' entries) = true := by
  induction entries with
  | nil => rw [LoopInitHoistLoopDriver.havocStmts'_nil, Block.namesFreshInExprs]
  | cons e rest ih =>
    rw [LoopInitHoistLoopDriver.havocStmts'_cons, Block.namesFreshInExprs, Bool.and_eq_true]
    refine ⟨?_, ih⟩
    simp only [Stmt.namesFreshInExprs, ExprOrNondet.getVars, freshFromIdents,
               List.all_nil, List.all_eq_true, implies_true]

/-! ## Generic preservation: the hoist pass preserves `namesFreshInExprs` for
names that avoid the generator's `_<digit>` naming scheme.

The pass renames each loop body's prefix inits to fresh generator names and
emits the matching havoc prelude OUTSIDE the loop.  Generator names always carry
the `_<digit>` suffix, so any `names`-list whose elements are *not* of that shape
is disjoint from every rename target.  Under that disjointness:

* `.cmd` is identity (residual `[.cmd c]`);
* `.block`/`.ite` recurse structurally (state-threaded);
* `.loop` emits `havocs.map .cmd` (all `.nondet` rhs, trivially fresh) plus the
  renamed loop `[.loop g m inv body₃ md]`, where `body₃ = applyRenames renames
  body₂`; `body₂` is the lift residual of the post-order body `body₁`, and
  `body₁` is fresh by the IH, so `body₂` is fresh (lift residual preservation)
  and `body₃` is fresh (rename targets ∉ names by `..._renames_target_suffix`).

This handles the SOURCES carrier (`sourcesOf' E`), whose elements lie in
`initVars body₁` and hence — by the `h_src_shapefree` invariant — never carry
the generator suffix. -/

mutual
/-- `Stmt.hoistLoopPrefixInitsM` preserves `Block.namesFreshInExprs names` for
names that avoid the generator's `_<digit>` naming scheme. -/
theorem Stmt.hoistLoopPrefixInitsM_namesFreshInExprs [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P]
    (names : List P.Ident) (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h_no_gen : ∀ str : String, String.HasUnderscoreDigitSuffix str →
        HasIdent.ident (P := P) str ∉ names)
    (h : Stmt.namesFreshInExprs names s = true) :
    Block.namesFreshInExprs names (Stmt.hoistLoopPrefixInitsM s σ).1 = true := by
  match s with
  | .cmd c =>
      simp only [Stmt.hoistLoopPrefixInitsM, Block.namesFreshInExprs, Bool.and_true]
      exact h
  | .block lbl bss md =>
      rw [Stmt.hoistLoopPrefixInitsM_block_out]
      simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true]
      have h_bss : Block.namesFreshInExprs names bss = true := by
        simp only [Stmt.namesFreshInExprs] at h; exact h
      exact Block.hoistLoopPrefixInitsM_namesFreshInExprs names bss σ h_no_gen h_bss
  | .ite g tss ess md =>
      rw [Stmt.hoistLoopPrefixInitsM_ite_out]
      have h_parts :
          names.all (fun z => freshFromIdents z (ExprOrNondet.getVars g)) = true ∧
          Block.namesFreshInExprs names tss = true ∧
          Block.namesFreshInExprs names ess = true := by
        simp only [Stmt.namesFreshInExprs, Bool.and_eq_true] at h
        exact ⟨h.1.1, h.1.2, h.2⟩
      have ih_t := Block.hoistLoopPrefixInitsM_namesFreshInExprs names tss σ h_no_gen h_parts.2.1
      have ih_e := Block.hoistLoopPrefixInitsM_namesFreshInExprs names ess
        (Block.hoistLoopPrefixInitsM tss σ).2 h_no_gen h_parts.2.2
      simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true]
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨h_parts.1, ih_t⟩, ih_e⟩
  | .loop g m inv body md =>
      rw [Stmt.hoistLoopPrefixInitsM_loop_out]
      -- decompose `namesFreshInExprs names [.loop g m inv body md]`.
      have h_loop : Stmt.namesFreshInExprs names (.loop g m inv body md) = true := h
      unfold Stmt.namesFreshInExprs at h_loop
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h_loop
      obtain ⟨⟨⟨h_g, h_m⟩, h_inv⟩, h_body⟩ := h_loop
      -- the post-order body is fresh by the IH.
      have ih_body : Block.namesFreshInExprs names (Block.hoistLoopPrefixInitsM body σ).1 = true :=
        Block.hoistLoopPrefixInitsM_namesFreshInExprs names body σ h_no_gen h_body
      -- the lift residual of body₁ is fresh.
      have h_body₂ :
          Block.namesFreshInExprs names
            (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1.2.2 = true :=
        Block.liftInitsInLoopBodyM_snd_namesFreshInExprs names _ _ ih_body
      -- the renamed body `body₃` is fresh: rename targets are suffixed, so ∉ names.
      have h_body₃ :
          Block.namesFreshInExprs names
            (Block.applyRenames
              (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
                (Block.hoistLoopPrefixInitsM body σ).2).1.2.1
              (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
                (Block.hoistLoopPrefixInitsM body σ).2).1.2.2) = true := by
        refine Block.namesFreshInExprs_applyRenames names _ _ ?_ h_body₂
        intro p hp
        obtain ⟨str, hstr_eq, hstr_suffix⟩ :=
          Block.liftInitsInLoopBodyM_renames_target_suffix
            (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2 p hp
        rw [hstr_eq]
        exact h_no_gen str hstr_suffix
      -- assemble: havocs (all `.nondet` rhs) ++ [.loop g m inv body₃ md].
      refine Block.namesFreshInExprs_append names _ _ ?_ ?_
      · -- havoc prelude: `havocs.map .cmd = havocStmts' E`, all `.nondet` rhs.
        rw [(LoopInitHoistLoopDriver.Block.lift_harvest_subst
              (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1]
        exact namesFreshInExprs_havocStmts' names _
      · -- the renamed loop: singleton block, decompose the loop's freshness.
        rw [Block.namesFreshInExprs]
        simp only [Block.namesFreshInExprs, Bool.and_true]
        unfold Stmt.namesFreshInExprs
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨⟨⟨h_g, h_m⟩, h_inv⟩, h_body₃⟩
  | .exit lbl md =>
      simp only [Stmt.hoistLoopPrefixInitsM, Block.namesFreshInExprs, Stmt.namesFreshInExprs,
                 Bool.and_true]
  | .funcDecl d md =>
      simp only [Stmt.hoistLoopPrefixInitsM, Block.namesFreshInExprs, Stmt.namesFreshInExprs,
                 Bool.and_true]
  | .typeDecl t md =>
      simp only [Stmt.hoistLoopPrefixInitsM, Block.namesFreshInExprs, Stmt.namesFreshInExprs,
                 Bool.and_true]
  termination_by sizeOf s

/-- `Block.hoistLoopPrefixInitsM` preserves `Block.namesFreshInExprs names` for
names that avoid the generator's `_<digit>` naming scheme. -/
theorem Block.hoistLoopPrefixInitsM_namesFreshInExprs [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P]
    (names : List P.Ident) (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h_no_gen : ∀ str : String, String.HasUnderscoreDigitSuffix str →
        HasIdent.ident (P := P) str ∉ names)
    (h : Block.namesFreshInExprs names ss = true) :
    Block.namesFreshInExprs names (Block.hoistLoopPrefixInitsM ss σ).1 = true := by
  match ss with
  | [] =>
      simp only [Block.hoistLoopPrefixInitsM, Block.namesFreshInExprs]
  | s :: rest =>
      rw [Block.hoistLoopPrefixInitsM_cons_out]
      have h_s : Stmt.namesFreshInExprs names s = true := by
        simp only [Block.namesFreshInExprs, Bool.and_eq_true] at h; exact h.1
      have h_rest : Block.namesFreshInExprs names rest = true := by
        simp only [Block.namesFreshInExprs, Bool.and_eq_true] at h; exact h.2
      have ih_s := Stmt.hoistLoopPrefixInitsM_namesFreshInExprs names s σ h_no_gen h_s
      have ih_rest := Block.hoistLoopPrefixInitsM_namesFreshInExprs names rest
        (Stmt.hoistLoopPrefixInitsM s σ).2 h_no_gen h_rest
      exact Block.namesFreshInExprs_append names _ _ ih_s ih_rest
  termination_by sizeOf ss
end

/-! ## Specialization for the producer's `h_B_fresh` precondition.

`Block.bodyTransport_of_lift` is fed at `B := targetsOf' E`,
`body₁ := (Block.hoistLoopPrefixInitsM body σ).1`, with
`E := Block.entriesOf body₁ σ₁`.  Its only remaining freshness precondition is
the TARGET-side `namesFreshInExprs B body₁`: the producer needs no SOURCE-side
freshness (a rename source that is also read is closed by the guarded pairing in
`cond_transport'` / `renamed_guard_eval_same_delta`).  The targets-side
precondition reduces, via the generic
`Block.hoistLoopPrefixInitsM_namesFreshInExprs` preservation, to the carrier
being fresh in the source body's exprs; it is supplied by the producer wiring
(see `Block.hoistLoopPrefixInitsM_namesFreshInExprs_targets`). -/

/-!
# Producer-precondition WF sub-lemmas for the §E `.loop` arm.

The §E `.loop` arm feeds `Block.bodyTransport_of_lift` on the post-order body
`body₁ = (Block.hoistLoopPrefixInitsM body σ).1` with carriers
`A := sourcesOf' E`, `B := targetsOf' E`, `subst := substOf' E`, where
`E := Block.entriesOf body₁ σ₁` is the harvest of `body₁`'s prefix inits.

This file proves the structural WF facts that producer needs as preconditions,
phrased over `E`.  The hardest is `targetsOf' E` Nodup: the targets are the
fresh idents the generator produced along the harvest, and they are globally
distinct because each is generated at a distinct generator state and the
generator never repeats a label (`StringGenState` monotonicity + well-formed
uniqueness).
-/

/-! ## State-threading helpers for the lift.

The harvest `Block.entriesOf` threads its generator state in lockstep with the
lift `Block.liftInitsInLoopBodyM`; these equalities expose the lift's final
state under `.block`/`.ite`/cons so the `entriesOf_targetGen` recursion can name
the intermediate states. -/

theorem Stmt.liftInitsInLoopBodyM_block_residual_state [HasIdent P]
    (lbl : String) (bss : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ : StringGenState) :
    (Stmt.liftInitsInLoopBodyM (.block lbl bss md) σ).2
      = (Block.liftInitsInLoopBodyM bss σ).2 := by
  rw [Stmt.liftInitsInLoopBodyM]
  rcases h : Block.liftInitsInLoopBodyM bss σ with ⟨⟨hs, rn, bss'⟩, σ'⟩
  simp only [h]

theorem Stmt.liftInitsInLoopBodyM_ite_residual_state [HasIdent P]
    (g : ExprOrNondet P) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ : StringGenState) :
    (Stmt.liftInitsInLoopBodyM (.ite g tss ess md) σ).2
      = (Block.liftInitsInLoopBodyM ess (Block.liftInitsInLoopBodyM tss σ).2).2 := by
  rw [Stmt.liftInitsInLoopBodyM]
  rcases h₁ : Block.liftInitsInLoopBodyM tss σ with ⟨⟨ths, trn, tss'⟩, σ₁⟩
  rcases h₂ : Block.liftInitsInLoopBodyM ess σ₁ with ⟨⟨ehs, ern, ess'⟩, σ₂⟩
  simp only [h₁, h₂]

theorem Block.liftInitsInLoopBodyM_cons_residual_state [HasIdent P]
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) (σ : StringGenState) :
    (Block.liftInitsInLoopBodyM (s :: rest) σ).2
      = (Block.liftInitsInLoopBodyM rest (Stmt.liftInitsInLoopBodyM s σ).2).2 := by
  rw [Block.liftInitsInLoopBodyM]
  rcases h₁ : Stmt.liftInitsInLoopBodyM s σ with ⟨⟨hs_s, rn_s, ss_s⟩, σ₁⟩
  rcases h₂ : Block.liftInitsInLoopBodyM rest σ₁ with ⟨⟨hs_r, rn_r, ss_r⟩, σ₂⟩
  simp only [h₁, h₂]

/-! ## The harvest targets are fresh generated names: distinct and captured.

The master invariant: under `WF σ`, every entry harvested from `body` at `σ`
has a target ident `e.2.1 = HasIdent.ident s` for a generator STRING `s` that is
(a) NOT yet present in `σ`'s produced labels, and (b) ALREADY present in the
final state's labels of the lift.  Together with monotonicity this yields
pairwise distinctness of the harvest's target strings, hence `Nodup`. -/

/-- Per-entry target fact: the target is `HasIdent.ident s` for a generator
string `s` fresh from the input state and captured in the lift's final state. -/
def TargetGen [HasIdent P] (σ σ' : StringGenState) (e : Entry P) : Prop :=
  ∃ s : String, e.2.1 = HasIdent.ident s
    ∧ s ∈ StringGenState.stringGens σ'
    ∧ s ∉ StringGenState.stringGens σ

mutual
/-- Every entry harvested from a single statement carries a `TargetGen` fact
between the input state and the lift's final state; and the targets are
`Nodup`. -/
theorem Stmt.entriesOf_targetGen [HasIdent P] [LawfulHasIdent P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) (h_wf : StringGenState.WF σ) :
    (∀ e ∈ Stmt.entriesOf s σ, TargetGen σ (Stmt.liftInitsInLoopBodyM s σ).2 e)
      ∧ (targetsOf' (Stmt.entriesOf s σ)).Nodup := by
  match s with
  | .cmd c =>
      cases c with
      | init y ty rhs md =>
          refine ⟨?_, ?_⟩
          · intro e he
            rw [Stmt.entriesOf] at he
            simp only [List.mem_singleton] at he
            subst he
            rw [Stmt.liftInitsInLoopBodyM]
            refine ⟨(StringGenState.gen hoistFreshPrefix σ).1, rfl, ?_, ?_⟩
            · rw [StringGenState.stringGens_gen]; exact List.mem_cons_self ..
            · exact StringGenState.stringGens_gen_not_in hoistFreshPrefix σ h_wf
          · rw [Stmt.entriesOf]
            simp [targetsOf']
      | set x rhs md => refine ⟨?_, ?_⟩ <;> simp [Stmt.entriesOf, targetsOf']
      | assert l e md => refine ⟨?_, ?_⟩ <;> simp [Stmt.entriesOf, targetsOf']
      | assume l e md => refine ⟨?_, ?_⟩ <;> simp [Stmt.entriesOf, targetsOf']
      | cover l e md => refine ⟨?_, ?_⟩ <;> simp [Stmt.entriesOf, targetsOf']
  | .block lbl bss md =>
      rw [Stmt.entriesOf, Stmt.liftInitsInLoopBodyM_block_residual_state]
      exact Block.entriesOf_targetGen bss σ h_wf
  | .ite g tss ess md =>
      rw [Stmt.entriesOf, Stmt.liftInitsInLoopBodyM_ite_residual_state]
      have ih_t := Block.entriesOf_targetGen tss σ h_wf
      have h_wf_σ₁ : StringGenState.WF (Block.liftInitsInLoopBodyM tss σ).2 :=
        (Block.liftInitsInLoopBodyM_genStep tss σ).wf_mono h_wf
      have ih_e := Block.entriesOf_targetGen ess (Block.liftInitsInLoopBodyM tss σ).2 h_wf_σ₁
      have h_step_t : GenStep σ (Block.liftInitsInLoopBodyM tss σ).2 :=
        Block.liftInitsInLoopBodyM_genStep tss σ
      have h_step_e : GenStep (Block.liftInitsInLoopBodyM tss σ).2
          (Block.liftInitsInLoopBodyM ess (Block.liftInitsInLoopBodyM tss σ).2).2 :=
        Block.liftInitsInLoopBodyM_genStep ess _
      refine ⟨?_, ?_⟩
      · intro e he
        rw [List.mem_append] at he
        rcases he with h | h
        · obtain ⟨t, ht_eq, ht_in, ht_not⟩ := ih_t.1 e h
          exact ⟨t, ht_eq, h_step_e.subset ht_in, ht_not⟩
        · obtain ⟨t, ht_eq, ht_in, ht_not⟩ := ih_e.1 e h
          refine ⟨t, ht_eq, ht_in, ?_⟩
          intro h_in_σ; exact ht_not (h_step_t.subset h_in_σ)
      · rw [targetsOf'_append, List.nodup_append]
        refine ⟨ih_t.2, ih_e.2, ?_⟩
        intro x hx_t y hx_e h_eq
        -- x is a then-target string captured in σ₁; y is an else-target fresh from σ₁.
        obtain ⟨et, het_mem, het_eq⟩ := List.mem_map.mp hx_t
        obtain ⟨ee, hee_mem, hee_eq⟩ := List.mem_map.mp hx_e
        obtain ⟨st, hst_eq, hst_in, _⟩ := ih_t.1 et het_mem
        obtain ⟨se, hse_eq, _, hse_not⟩ := ih_e.1 ee hee_mem
        -- x = et.2.1 = ident st (captured in σ₁) and y = ee.2.1 = ident se (fresh from σ₁)
        apply hse_not
        have h_id : (HasIdent.ident st : P.Ident) = HasIdent.ident se := by
          rw [← hst_eq, ← hse_eq, het_eq, hee_eq, h_eq]
        have : st = se := LawfulHasIdent.ident_inj h_id
        rw [← this]; exact hst_in
  | .loop g m inv body md =>
      rw [Stmt.entriesOf]; refine ⟨by simp, by simp [targetsOf']⟩
  | .exit lbl md => rw [Stmt.entriesOf]; refine ⟨by simp, by simp [targetsOf']⟩
  | .funcDecl d md => rw [Stmt.entriesOf]; refine ⟨by simp, by simp [targetsOf']⟩
  | .typeDecl t md => rw [Stmt.entriesOf]; refine ⟨by simp, by simp [targetsOf']⟩
  termination_by sizeOf s

theorem Block.entriesOf_targetGen [HasIdent P] [LawfulHasIdent P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) (h_wf : StringGenState.WF σ) :
    (∀ e ∈ Block.entriesOf ss σ, TargetGen σ (Block.liftInitsInLoopBodyM ss σ).2 e)
      ∧ (targetsOf' (Block.entriesOf ss σ)).Nodup := by
  match ss with
  | [] =>
      rw [Block.entriesOf]; refine ⟨by simp, by simp [targetsOf']⟩
  | s :: rest =>
      rw [Block.entriesOf, Block.liftInitsInLoopBodyM_cons_residual_state]
      have ih_s := Stmt.entriesOf_targetGen s σ h_wf
      have h_wf_σ₁ : StringGenState.WF (Stmt.liftInitsInLoopBodyM s σ).2 :=
        (Stmt.liftInitsInLoopBodyM_genStep s σ).wf_mono h_wf
      have ih_r := Block.entriesOf_targetGen rest (Stmt.liftInitsInLoopBodyM s σ).2 h_wf_σ₁
      have h_step_s : GenStep σ (Stmt.liftInitsInLoopBodyM s σ).2 :=
        Stmt.liftInitsInLoopBodyM_genStep s σ
      have h_step_r : GenStep (Stmt.liftInitsInLoopBodyM s σ).2
          (Block.liftInitsInLoopBodyM rest (Stmt.liftInitsInLoopBodyM s σ).2).2 :=
        Block.liftInitsInLoopBodyM_genStep rest _
      refine ⟨?_, ?_⟩
      · intro e he
        rw [List.mem_append] at he
        rcases he with h | h
        · obtain ⟨t, ht_eq, ht_in, ht_not⟩ := ih_s.1 e h
          exact ⟨t, ht_eq, h_step_r.subset ht_in, ht_not⟩
        · obtain ⟨t, ht_eq, ht_in, ht_not⟩ := ih_r.1 e h
          refine ⟨t, ht_eq, ht_in, ?_⟩
          intro h_in_σ; exact ht_not (h_step_s.subset h_in_σ)
      · rw [targetsOf'_append, List.nodup_append]
        refine ⟨ih_s.2, ih_r.2, ?_⟩
        intro x hx_s y hx_r h_eq
        obtain ⟨es, hes_mem, hes_eq⟩ := List.mem_map.mp hx_s
        obtain ⟨er, her_mem, her_eq⟩ := List.mem_map.mp hx_r
        obtain ⟨ss', hss_eq, hss_in, _⟩ := ih_s.1 es hes_mem
        obtain ⟨sr, hsr_eq, _, hsr_not⟩ := ih_r.1 er her_mem
        apply hsr_not
        have h_id : (HasIdent.ident ss' : P.Ident) = HasIdent.ident sr := by
          rw [← hss_eq, ← hsr_eq, hes_eq, her_eq, h_eq]
        have : ss' = sr := LawfulHasIdent.ident_inj h_id
        rw [← this]; exact hss_in
  termination_by sizeOf ss
end

/-! ## The lift rename targets are captured in the lift's output state.

A WF-free companion to `entriesOf_targetGen`: every rename TARGET the monadic
lift produces is `HasIdent.ident s` for a generator string `s` that lies in the
lift's *output* `stringGens`.  (No freshness/Nodup needed — just that each fresh
name is captured.)  This is the half consumed by the gen-state freshness route
for the TARGETS carrier. -/

/-- The renames component of `Stmt.liftInitsInLoopBodyM (.block ..) σ` equals the
sub-block's renames. -/
private theorem Stmt.liftInitsInLoopBodyM_block_renames [HasIdent P]
    (lbl : String) (bss : List (Stmt P (Cmd P))) (md : MetaData P) (σ : StringGenState) :
    (Stmt.liftInitsInLoopBodyM (.block lbl bss md) σ).1.2.1
      = (Block.liftInitsInLoopBodyM bss σ).1.2.1 := by
  rw [Stmt.liftInitsInLoopBodyM]
  rcases h : Block.liftInitsInLoopBodyM bss σ with ⟨⟨hs, rn, bss'⟩, σ'⟩
  simp only [h]

/-- The renames component of `Stmt.liftInitsInLoopBodyM (.ite ..) σ` is the
concatenation of the two branches' renames. -/
private theorem Stmt.liftInitsInLoopBodyM_ite_renames [HasIdent P]
    (g : ExprOrNondet P) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ : StringGenState) :
    (Stmt.liftInitsInLoopBodyM (.ite g tss ess md) σ).1.2.1
      = (Block.liftInitsInLoopBodyM tss σ).1.2.1 ++
        (Block.liftInitsInLoopBodyM ess (Block.liftInitsInLoopBodyM tss σ).2).1.2.1 := by
  rw [Stmt.liftInitsInLoopBodyM]
  rcases h₁ : Block.liftInitsInLoopBodyM tss σ with ⟨⟨ths, trn, tss'⟩, σ₁⟩
  rcases h₂ : Block.liftInitsInLoopBodyM ess σ₁ with ⟨⟨ehs, ern, ess'⟩, σ₂⟩
  simp only [h₁, h₂]

/-- The renames component of `Block.liftInitsInLoopBodyM (s :: rest) σ` is the
head's renames concatenated with the tail's. -/
private theorem Block.liftInitsInLoopBodyM_cons_renames [HasIdent P]
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) (σ : StringGenState) :
    (Block.liftInitsInLoopBodyM (s :: rest) σ).1.2.1
      = (Stmt.liftInitsInLoopBodyM s σ).1.2.1 ++
        (Block.liftInitsInLoopBodyM rest (Stmt.liftInitsInLoopBodyM s σ).2).1.2.1 := by
  rw [Block.liftInitsInLoopBodyM]
  rcases h₁ : Stmt.liftInitsInLoopBodyM s σ with ⟨⟨hs_s, rn_s, ss_s⟩, σ₁⟩
  rcases h₂ : Block.liftInitsInLoopBodyM rest σ₁ with ⟨⟨hs_r, rn_r, ss_r⟩, σ₂⟩
  simp only [h₁, h₂]

mutual
/-- Every rename target produced by `Stmt.liftInitsInLoopBodyM s σ` is captured
in the lift's output state's `stringGens`. -/
theorem Stmt.liftInitsInLoopBodyM_renames_captured [HasIdent P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    ∀ p ∈ (Stmt.liftInitsInLoopBodyM s σ).1.2.1,
      ∃ str : String, p.2 = HasIdent.ident str ∧
        str ∈ StringGenState.stringGens (Stmt.liftInitsInLoopBodyM s σ).2 := by
  match s with
  | .cmd c =>
      cases c with
      | init y ty rhs md =>
          intro p hp
          rw [Stmt.liftInitsInLoopBodyM] at hp ⊢
          simp only [List.mem_singleton] at hp
          subst hp
          refine ⟨(StringGenState.gen hoistFreshPrefix σ).1, rfl, ?_⟩
          rw [StringGenState.stringGens_gen]; exact List.mem_cons_self ..
      | set x rhs md => intro p hp; simp only [Stmt.liftInitsInLoopBodyM, List.not_mem_nil] at hp
      | assert l ex md => intro p hp; simp only [Stmt.liftInitsInLoopBodyM, List.not_mem_nil] at hp
      | assume l ex md => intro p hp; simp only [Stmt.liftInitsInLoopBodyM, List.not_mem_nil] at hp
      | cover l ex md => intro p hp; simp only [Stmt.liftInitsInLoopBodyM, List.not_mem_nil] at hp
  | .block lbl bss md =>
      rw [Stmt.liftInitsInLoopBodyM_block_renames, Stmt.liftInitsInLoopBodyM_block_residual_state]
      exact Block.liftInitsInLoopBodyM_renames_captured bss σ
  | .ite g tss ess md =>
      have h_step_e : GenStep (Block.liftInitsInLoopBodyM tss σ).2
          (Block.liftInitsInLoopBodyM ess (Block.liftInitsInLoopBodyM tss σ).2).2 :=
        Block.liftInitsInLoopBodyM_genStep ess _
      rw [Stmt.liftInitsInLoopBodyM_ite_renames, Stmt.liftInitsInLoopBodyM_ite_residual_state,
          List.forall_mem_append]
      refine ⟨fun p h => ?_, Block.liftInitsInLoopBodyM_renames_captured ess _⟩
      obtain ⟨str, hstr_eq, hstr_in⟩ := Block.liftInitsInLoopBodyM_renames_captured tss σ p h
      exact ⟨str, hstr_eq, h_step_e.subset hstr_in⟩
  | .loop g m inv body md => intro p hp; simp only [Stmt.liftInitsInLoopBodyM, List.not_mem_nil] at hp
  | .exit lbl md => intro p hp; simp only [Stmt.liftInitsInLoopBodyM, List.not_mem_nil] at hp
  | .funcDecl d md => intro p hp; simp only [Stmt.liftInitsInLoopBodyM, List.not_mem_nil] at hp
  | .typeDecl t md => intro p hp; simp only [Stmt.liftInitsInLoopBodyM, List.not_mem_nil] at hp
  termination_by sizeOf s

/-- Every rename target produced by `Block.liftInitsInLoopBodyM ss σ` is captured
in the lift's output state's `stringGens`. -/
theorem Block.liftInitsInLoopBodyM_renames_captured [HasIdent P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∀ p ∈ (Block.liftInitsInLoopBodyM ss σ).1.2.1,
      ∃ str : String, p.2 = HasIdent.ident str ∧
        str ∈ StringGenState.stringGens (Block.liftInitsInLoopBodyM ss σ).2 := by
  match ss with
  | [] => intro p hp; simp only [Block.liftInitsInLoopBodyM, List.not_mem_nil] at hp
  | s :: rest =>
      have h_step_r : GenStep (Stmt.liftInitsInLoopBodyM s σ).2
          (Block.liftInitsInLoopBodyM rest (Stmt.liftInitsInLoopBodyM s σ).2).2 :=
        Block.liftInitsInLoopBodyM_genStep rest _
      rw [Block.liftInitsInLoopBodyM_cons_renames, Block.liftInitsInLoopBodyM_cons_residual_state,
          List.forall_mem_append]
      refine ⟨fun p h => ?_, Block.liftInitsInLoopBodyM_renames_captured rest _⟩
      obtain ⟨str, hstr_eq, hstr_in⟩ := Stmt.liftInitsInLoopBodyM_renames_captured s σ p h
      exact ⟨str, hstr_eq, h_step_r.subset hstr_in⟩
  termination_by sizeOf ss
end

/-! ## Output-state peels for the hoist pass.

These expose `(Block/Stmt.hoistLoopPrefixInitsM _ σ).2` in terms of the
sub-structure's output states, the analogue of the `_out` list peels.  They let
the gen-state freshness route name the per-subtree output `stringGens`. -/

theorem Stmt.hoistLoopPrefixInitsM_block_state [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (lbl : String) (bss : List (Stmt P (Cmd P))) (md : MetaData P) (σ : StringGenState) :
    (Stmt.hoistLoopPrefixInitsM (.block lbl bss md) σ).2
      = (Block.hoistLoopPrefixInitsM bss σ).2 := by
  rw [Stmt.hoistLoopPrefixInitsM]
  rcases h : Block.hoistLoopPrefixInitsM bss σ with ⟨bss', σ'⟩
  simp only [h]

theorem Stmt.hoistLoopPrefixInitsM_ite_state [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (g : ExprOrNondet P) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ : StringGenState) :
    (Stmt.hoistLoopPrefixInitsM (.ite g tss ess md) σ).2
      = (Block.hoistLoopPrefixInitsM ess (Block.hoistLoopPrefixInitsM tss σ).2).2 := by
  rw [Stmt.hoistLoopPrefixInitsM]
  rcases h₁ : Block.hoistLoopPrefixInitsM tss σ with ⟨tss', σ₁⟩
  rcases h₂ : Block.hoistLoopPrefixInitsM ess σ₁ with ⟨ess', σ₂⟩
  simp only [h₁, h₂]

theorem Stmt.hoistLoopPrefixInitsM_loop_state [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (g : ExprOrNondet P) (m : Option P.Expr) (inv : List (String × P.Expr))
    (body : List (Stmt P (Cmd P))) (md : MetaData P) (σ : StringGenState) :
    (Stmt.hoistLoopPrefixInitsM (.loop g m inv body md) σ).2
      = (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
          (Block.hoistLoopPrefixInitsM body σ).2).2 := by
  rw [Stmt.hoistLoopPrefixInitsM]
  rcases h₁ : Block.hoistLoopPrefixInitsM body σ with ⟨body₁, σ₁⟩
  rcases h₂ : Block.liftInitsInLoopBodyM body₁ σ₁ with ⟨⟨havocs, renames, body₂⟩, σ₂⟩
  simp only [h₁, h₂]

theorem Block.hoistLoopPrefixInitsM_cons_state [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) (σ : StringGenState) :
    (Block.hoistLoopPrefixInitsM (s :: rest) σ).2
      = (Block.hoistLoopPrefixInitsM rest (Stmt.hoistLoopPrefixInitsM s σ).2).2 := by
  rw [Block.hoistLoopPrefixInitsM]
  rcases h₁ : Stmt.hoistLoopPrefixInitsM s σ with ⟨ss_s, σ₁⟩
  rcases h₂ : Block.hoistLoopPrefixInitsM rest σ₁ with ⟨ss_r, σ₂⟩
  simp only [h₁, h₂]

/-! ## Gen-state freshness route to the TARGETS carrier.

A second generic preservation, dual to the suffix route: names that are fresh
from the pass's OUTPUT state's `stringGens` stay fresh through the pass (given
they were fresh in the source body's exprs).  Every rename target the pass
introduces is captured in that output state (`..._renames_captured`), so the
`.loop` arm's `applyRenames` cannot reintroduce a name.  This is the half that
the TARGETS carrier (`targetsOf' E`, fresh from the pass output by `TargetGen`)
satisfies. -/

mutual
/-- `Stmt.hoistLoopPrefixInitsM` preserves `Block.namesFreshInExprs names` for
names that are fresh from the pass output state's `stringGens` (and fresh in the
source statement's exprs). -/
theorem Stmt.hoistLoopPrefixInitsM_namesFreshInExprs_genfresh [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P]
    (names : List P.Ident) (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h_genfresh : ∀ str : String,
        HasIdent.ident (P := P) str ∈ names →
        str ∉ StringGenState.stringGens (Stmt.hoistLoopPrefixInitsM s σ).2)
    (h : Stmt.namesFreshInExprs names s = true) :
    Block.namesFreshInExprs names (Stmt.hoistLoopPrefixInitsM s σ).1 = true := by
  match s with
  | .cmd c =>
      simp only [Stmt.hoistLoopPrefixInitsM, Block.namesFreshInExprs, Bool.and_true]
      exact h
  | .block lbl bss md =>
      rw [Stmt.hoistLoopPrefixInitsM_block_out]
      simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true]
      have h_bss : Block.namesFreshInExprs names bss = true := by
        simp only [Stmt.namesFreshInExprs] at h; exact h
      refine Block.hoistLoopPrefixInitsM_namesFreshInExprs_genfresh names bss σ ?_ h_bss
      intro str hstr
      rw [← Stmt.hoistLoopPrefixInitsM_block_state lbl bss md σ]
      exact h_genfresh str hstr
  | .ite g tss ess md =>
      rw [Stmt.hoistLoopPrefixInitsM_ite_out]
      have h_parts :
          names.all (fun z => freshFromIdents z (ExprOrNondet.getVars g)) = true ∧
          Block.namesFreshInExprs names tss = true ∧
          Block.namesFreshInExprs names ess = true := by
        simp only [Stmt.namesFreshInExprs, Bool.and_eq_true] at h
        exact ⟨h.1.1, h.1.2, h.2⟩
      have h_step_e : GenStep (Block.hoistLoopPrefixInitsM tss σ).2
          (Block.hoistLoopPrefixInitsM ess (Block.hoistLoopPrefixInitsM tss σ).2).2 :=
        Block.hoistLoopPrefixInitsM_genStep ess _
      have ih_t := Block.hoistLoopPrefixInitsM_namesFreshInExprs_genfresh names tss σ
        (fun str hstr => by
          intro hin
          exact h_genfresh str hstr (by
            rw [Stmt.hoistLoopPrefixInitsM_ite_state]
            exact h_step_e.subset hin)) h_parts.2.1
      have ih_e := Block.hoistLoopPrefixInitsM_namesFreshInExprs_genfresh names ess
        (Block.hoistLoopPrefixInitsM tss σ).2
        (fun str hstr => by
          intro hin
          exact h_genfresh str hstr (by
            rw [Stmt.hoistLoopPrefixInitsM_ite_state]; exact hin)) h_parts.2.2
      simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_true]
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨h_parts.1, ih_t⟩, ih_e⟩
  | .loop g m inv body md =>
      rw [Stmt.hoistLoopPrefixInitsM_loop_out]
      have h_loop : Stmt.namesFreshInExprs names (.loop g m inv body md) = true := h
      unfold Stmt.namesFreshInExprs at h_loop
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h_loop
      obtain ⟨⟨⟨h_g, h_m⟩, h_inv⟩, h_body⟩ := h_loop
      -- the inner-loop renames are captured in this loop's output state σ₂.
      have h_step_lift : GenStep (Block.hoistLoopPrefixInitsM body σ).2
          (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
            (Block.hoistLoopPrefixInitsM body σ).2).2 :=
        Block.liftInitsInLoopBodyM_genStep _ _
      -- the post-order body is fresh by the IH (its output state ⊆ σ₂).
      have ih_body : Block.namesFreshInExprs names (Block.hoistLoopPrefixInitsM body σ).1 = true := by
        refine Block.hoistLoopPrefixInitsM_namesFreshInExprs_genfresh names body σ ?_ h_body
        intro str hstr hin
        exact h_genfresh str hstr (by
          rw [Stmt.hoistLoopPrefixInitsM_loop_state]
          exact h_step_lift.subset hin)
      have h_body₂ :
          Block.namesFreshInExprs names
            (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1.2.2 = true :=
        Block.liftInitsInLoopBodyM_snd_namesFreshInExprs names _ _ ih_body
      have h_body₃ :
          Block.namesFreshInExprs names
            (Block.applyRenames
              (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
                (Block.hoistLoopPrefixInitsM body σ).2).1.2.1
              (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
                (Block.hoistLoopPrefixInitsM body σ).2).1.2.2) = true := by
        refine Block.namesFreshInExprs_applyRenames names _ _ ?_ h_body₂
        intro p hp
        obtain ⟨str, hstr_eq, hstr_in⟩ :=
          Block.liftInitsInLoopBodyM_renames_captured
            (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2 p hp
        rw [hstr_eq]
        intro hmem
        exact h_genfresh str hmem (by rw [Stmt.hoistLoopPrefixInitsM_loop_state]; exact hstr_in)
      refine Block.namesFreshInExprs_append names _ _ ?_ ?_
      · rw [(LoopInitHoistLoopDriver.Block.lift_harvest_subst
              (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1]
        exact namesFreshInExprs_havocStmts' names _
      · rw [Block.namesFreshInExprs]
        simp only [Block.namesFreshInExprs, Bool.and_true]
        unfold Stmt.namesFreshInExprs
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨⟨⟨h_g, h_m⟩, h_inv⟩, h_body₃⟩
  | .exit lbl md =>
      simp only [Stmt.hoistLoopPrefixInitsM, Block.namesFreshInExprs, Stmt.namesFreshInExprs,
                 Bool.and_true]
  | .funcDecl d md =>
      simp only [Stmt.hoistLoopPrefixInitsM, Block.namesFreshInExprs, Stmt.namesFreshInExprs,
                 Bool.and_true]
  | .typeDecl t md =>
      simp only [Stmt.hoistLoopPrefixInitsM, Block.namesFreshInExprs, Stmt.namesFreshInExprs,
                 Bool.and_true]
  termination_by sizeOf s

/-- `Block.hoistLoopPrefixInitsM` preserves `Block.namesFreshInExprs names` for
names that are fresh from the pass output state's `stringGens`. -/
theorem Block.hoistLoopPrefixInitsM_namesFreshInExprs_genfresh [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P]
    (names : List P.Ident) (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h_genfresh : ∀ str : String,
        HasIdent.ident (P := P) str ∈ names →
        str ∉ StringGenState.stringGens (Block.hoistLoopPrefixInitsM ss σ).2)
    (h : Block.namesFreshInExprs names ss = true) :
    Block.namesFreshInExprs names (Block.hoistLoopPrefixInitsM ss σ).1 = true := by
  match ss with
  | [] =>
      simp only [Block.hoistLoopPrefixInitsM, Block.namesFreshInExprs]
  | s :: rest =>
      rw [Block.hoistLoopPrefixInitsM_cons_out]
      have h_s : Stmt.namesFreshInExprs names s = true := by
        simp only [Block.namesFreshInExprs, Bool.and_eq_true] at h; exact h.1
      have h_rest : Block.namesFreshInExprs names rest = true := by
        simp only [Block.namesFreshInExprs, Bool.and_eq_true] at h; exact h.2
      have h_step_rest : GenStep (Stmt.hoistLoopPrefixInitsM s σ).2
          (Block.hoistLoopPrefixInitsM rest (Stmt.hoistLoopPrefixInitsM s σ).2).2 :=
        Block.hoistLoopPrefixInitsM_genStep rest _
      have ih_s := Stmt.hoistLoopPrefixInitsM_namesFreshInExprs_genfresh names s σ
        (fun str hstr hin => h_genfresh str hstr (by
          rw [Block.hoistLoopPrefixInitsM_cons_state]
          exact h_step_rest.subset hin)) h_s
      have ih_rest := Block.hoistLoopPrefixInitsM_namesFreshInExprs_genfresh names rest
        (Stmt.hoistLoopPrefixInitsM s σ).2
        (fun str hstr hin => h_genfresh str hstr (by
          rw [Block.hoistLoopPrefixInitsM_cons_state]; exact hin)) h_rest
      exact Block.namesFreshInExprs_append names _ _ ih_s ih_rest
  termination_by sizeOf ss
end

/-! ## The TARGETS carrier is fresh from the harvest's input state.

`targetsOf' (Block.entriesOf body₁ σ₁)` are the freshly generated names harvested
from `body₁` at `σ₁`.  By `Block.entriesOf_targetGen` (under `WF σ₁`), every such
target is `HasIdent.ident s` with `s ∉ stringGens σ₁`.  Hence the targets satisfy
the `genfresh` premise at `σ₁`. -/

/-- Every `targetsOf'`-element of `Block.entriesOf body₁ σ₁` is `HasIdent.ident
str` for a `str ∉ stringGens σ₁` (given `WF σ₁`).  This is exactly the `genfresh`
premise of `..._namesFreshInExprs_genfresh` at the harvest input state. -/
theorem Block.targetsOf'_entriesOf_genfresh [HasIdent P] [LawfulHasIdent P]
    (body₁ : List (Stmt P (Cmd P))) (σ₁ : StringGenState) (h_wf : StringGenState.WF σ₁) :
    ∀ str : String,
      HasIdent.ident (P := P) str ∈ targetsOf' (Block.entriesOf body₁ σ₁) →
      str ∉ StringGenState.stringGens σ₁ := by
  intro str hstr hin
  -- `targetsOf' E = E.map (·.2.1)`, so the membership comes from an entry.
  simp only [LoopInitHoistLoopDriver.targetsOf', List.mem_map] at hstr
  obtain ⟨e, he_mem, he_eq⟩ := hstr
  obtain ⟨s, hs_eq, hs_in, hs_not⟩ := (Block.entriesOf_targetGen body₁ σ₁ h_wf).1 e he_mem
  -- `ident str = e.2.1 = ident s`, so `str = s` by injectivity, and `s ∉ stringGens σ₁`.
  have h_id : (HasIdent.ident str : P.Ident) = HasIdent.ident s := he_eq.symm.trans hs_eq
  have : str = s := LawfulHasIdent.ident_inj h_id
  exact hs_not (this ▸ hin)

/-- Producer `h_B_fresh` for the TARGETS carrier: the harvest targets
`targetsOf' (Block.entriesOf body₁ σ₁)` (with `body₁ = (hoistLoopPrefixInitsM
body σ).1`, `σ₁ = (hoistLoopPrefixInitsM body σ).2`) are fresh in `body₁` PROVIDED
they are fresh in the SOURCE body's exprs.  The gen-state freshness premise is
discharged internally from `WF σ₁` via `targetsOf'_entriesOf_genfresh`.

`h_tgt_body_fresh` (targets fresh in `body`'s exprs) is supplied by the producer
wiring: the targets are generator-suffixed names minted strictly after `σ`, so
they are fresh in the original (pre-pass) source body, which only mentions
program names. -/
theorem Block.hoistLoopPrefixInitsM_namesFreshInExprs_targets [HasIdent P] [LawfulHasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P]
    (body : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h_wf₁ : StringGenState.WF (Block.hoistLoopPrefixInitsM body σ).2)
    (h_tgt_body_fresh :
      Block.namesFreshInExprs
        (targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1
          (Block.hoistLoopPrefixInitsM body σ).2)) body = true) :
    Block.namesFreshInExprs
      (targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1
        (Block.hoistLoopPrefixInitsM body σ).2))
      (Block.hoistLoopPrefixInitsM body σ).1 = true := by
  refine Block.hoistLoopPrefixInitsM_namesFreshInExprs_genfresh _ body σ ?_ h_tgt_body_fresh
  exact Block.targetsOf'_entriesOf_genfresh (Block.hoistLoopPrefixInitsM body σ).1
    (Block.hoistLoopPrefixInitsM body σ).2 h_wf₁

/-! ## The harvest targets carry hoist's mint kind `Q`.

Routing the harvest through `entriesOf_target_suffix` (which exposes that every
harvested `.init` target is literally a `gen hoistFreshPrefix _` output) with the
mint witness `hQmint` exposes that every member of `targetsOf' (Block.entriesOf
ss σ)` is `HasIdent.ident str` for a `Q`-kind `str` — the structural fact that
separates the harvest targets from program names (which never carry hoist's
mint kind).  Instantiating `Q := String.HasUnderscoreDigitSuffix` recovers the
blanket generator-suffix statement. -/

/-- Every entry harvested from a block has a target ident that is
`HasIdent.ident str` for a `Q`-kind generator string `str` (given the mint
witness `hQmint`). -/
theorem Block.entriesOf_target_hasUnderscoreDigitSuffix [HasIdent P] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    {e : Entry P} (he : e ∈ Block.entriesOf ss σ) :
    ∃ str : String, e.2.1 = HasIdent.ident str ∧ Q str :=
  Block.entriesOf_target_suffix hQmint ss σ e he

/-- Every member of `targetsOf' (Block.entriesOf ss σ)` is `HasIdent.ident str`
for a `Q`-kind generator string `str`. -/
theorem Block.mem_targetsOf'_entriesOf_hasUnderscoreDigitSuffix [HasIdent P] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    {x : P.Ident} (hx : x ∈ targetsOf' (Block.entriesOf ss σ)) :
    ∃ str : String, x = HasIdent.ident str ∧ Q str := by
  obtain ⟨e, he_mem, he_eq⟩ := List.mem_map.mp hx
  obtain ⟨str, h_eq, h_suf⟩ :=
    Block.entriesOf_target_hasUnderscoreDigitSuffix hQmint ss σ he_mem
  exact ⟨str, by rw [← he_eq, h_eq], h_suf⟩

/-! ## The `exprsShapeFree` ⇒ `h_B_fresh` bridge.

`Block.bodyTransport_of_lift` is fed at `B := targetsOf' E` with
`E := Block.entriesOf body₁ σ₁`, `body₁ = (hoistLoopPrefixInitsM body σ).1`,
`σ₁ = (hoistLoopPrefixInitsM body σ).2`.  Its `h_B_fresh` reads
`namesFreshInExprs (targetsOf' E) body₁ = true`.  The reducer
`hoistLoopPrefixInitsM_namesFreshInExprs_targets` reduces that to freshness in
the SOURCE body `body`.  Source-body freshness in turn follows from the
front-end well-formedness assumption `Block.exprsShapeFree body`: every target
is a `_<digits>`-suffixed ident (`mem_targetsOf'_entriesOf_hasUnderscoreDigitSuffix`)
and a shape-free body never reads such a name, so the targets are fresh in
`body`'s exprs. -/

/-- The harvest targets are fresh in the SOURCE body's exprs, given the
body is `exprsShapeFree Q`.  This is exactly the `h_tgt_body_fresh` premise of
`hoistLoopPrefixInitsM_namesFreshInExprs_targets`. -/
theorem Block.targetsOf'_entriesOf_namesFreshInExprs_of_exprsShapeFree [HasIdent P] [HasVarsPure P P.Expr] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (body body₁ : List (Stmt P (Cmd P))) (σ₁ : StringGenState)
    (_h_wf₁ : StringGenState.WF σ₁)
    (h_sf : Block.exprsShapeFree (P := P) Q body) :
    Block.namesFreshInExprs (targetsOf' (Block.entriesOf body₁ σ₁)) body = true :=
  Block.namesFreshInExprs_of_exprsShapeFree'
    (fun _z hz => Block.mem_targetsOf'_entriesOf_hasUnderscoreDigitSuffix hQmint body₁ σ₁ hz)
    body h_sf

/-- The full producer-side `h_B_fresh` for the `.loop` arm: from
`Block.exprsShapeFree Q body`, the harvest targets `targetsOf' (entriesOf body₁
σ₁)` (`body₁`/`σ₁` the post-order body / its gen state) are fresh in `body₁`'s
exprs.  The targets carry hoist's mint kind; the source body is shape-free,
so they are fresh in `body`; the reducer lifts that to `body₁`. -/
theorem Block.hoistLoopPrefixInitsM_namesFreshInExprs_targets_of_exprsShapeFree [HasIdent P] [LawfulHasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (body : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h_wf₁ : StringGenState.WF (Block.hoistLoopPrefixInitsM body σ).2)
    (h_sf : Block.exprsShapeFree (P := P) Q body) :
    Block.namesFreshInExprs
      (targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1
        (Block.hoistLoopPrefixInitsM body σ).2))
      (Block.hoistLoopPrefixInitsM body σ).1 = true :=
  Block.hoistLoopPrefixInitsM_namesFreshInExprs_targets body σ h_wf₁
    (Block.targetsOf'_entriesOf_namesFreshInExprs_of_exprsShapeFree hQmint body
      (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2 h_wf₁ h_sf)

/-! ## Disjointness producer-preconditions at the entries carriers.

`Block.bodyTransport_of_lift` is fed at `A := sourcesOf' E`, `B := targetsOf' E`,
`subst := substOf' E` with `E := Block.entriesOf body₁ σ`.  Its disjointness
side-conditions then read:

* `h_mod_disjoint_A : ∀ x ∈ Block.modifiedVars body₁, x ∉ sourcesOf' E`,
* `h_mod_disjoint_B : ∀ x ∈ Block.modifiedVars body₁, x ∉ targetsOf' E`,

and the §E `.loop` arm separately needs the targets and sources of `E` to be
disjoint from the *ambient* outer carriers `A`/`B` and from `Block.initVars [s]`.

The targets are generator idents with the `_<digit>` suffix
(`mem_targetsOf'_entriesOf_hasUnderscoreDigitSuffix`), so every disjointness of
the form "targets ∩ V = ∅" reduces to "no member of `V` is the ident of a
suffix-shaped string".  For the ambient `A`/`B` and `Block.initVars [s]` that is
exactly the contrapositive of the arm's `h_src_shapefree`.  For
`Block.modifiedVars body₁` the same shape-freedom holds because `modifiedVars`
collects only `.set` targets — program names that never carry the generator
suffix — supplied as a hypothesis by the caller.

The sources `sourcesOf' E ⊆ Block.initVars body₁` (`Block.sourcesOf_entriesOf_subset`),
so source-disjointness reduces to a disjointness hypothesis on `Block.initVars body₁`. -/

/-- A target carrier is disjoint from any `vars` whose every member is *not* the
ident of a `Q`-kind string.  This is the generic engine behind every
"targets ∩ V = ∅" side-condition. -/
theorem targetsOf'_entriesOf_disjoint_of_shapefree [HasIdent P] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (vars : List P.Ident)
    (h_shapefree : ∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉ vars) :
    ∀ x ∈ vars, x ∉ targetsOf' (Block.entriesOf ss σ) := by
  intro x hx_vars hx_tgt
  obtain ⟨str, h_eq, h_suf⟩ :=
    Block.mem_targetsOf'_entriesOf_hasUnderscoreDigitSuffix hQmint ss σ hx_tgt
  exact h_shapefree str h_suf (h_eq ▸ hx_vars)

/-- `h_mod_disjoint_B` at `B := targetsOf' E`: the post-order body's
`modifiedVars` are disjoint from the harvest targets.  `modifiedVars` collect
only `.set` targets — program names without hoist's mint kind — so the
shape-free hypothesis on `Block.modifiedVars body₁` discharges it. -/
theorem modifiedVars_disjoint_targetsOf'_entriesOf [HasIdent P] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (body₁ : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h_mod_shapefree : ∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉ Block.modifiedVars body₁) :
    ∀ x ∈ Block.modifiedVars body₁, x ∉ targetsOf' (Block.entriesOf body₁ σ) :=
  targetsOf'_entriesOf_disjoint_of_shapefree hQmint body₁ σ
    (Block.modifiedVars body₁) h_mod_shapefree

/-- `h_mod_disjoint_A` at `A := sourcesOf' E`: the post-order body's
`modifiedVars` are disjoint from the harvest sources.  Sources are body inits
(`Block.sourcesOf_entriesOf_subset`), so the caller's disjointness of
`modifiedVars body₁` from `initVars body₁` discharges it. -/
theorem modifiedVars_disjoint_sourcesOf'_entriesOf [HasIdent P]
    [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIntOrder P] [HasVarsPure P P.Expr]
    (body₁ : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h_mod_init_disjoint : ∀ x ∈ Block.modifiedVars body₁, x ∉ Block.initVars body₁) :
    ∀ x ∈ Block.modifiedVars body₁, x ∉ sourcesOf' (Block.entriesOf body₁ σ) := by
  intro x hx_mod hx_src
  exact h_mod_init_disjoint x hx_mod (Block.sourcesOf_entriesOf_subset body₁ σ x hx_src)

/-! ## Compose-union side-conditions: harvest carriers vs the ambient `A`/`B`.

The §E `.loop` arm's `compose_union` step needs the harvest's targets and
sources to stay disjoint from the *outer* substitution carriers `A`/`B` (and the
loop statement's own inits).  Each fact below is a direct instance of the
generic shape-free engine (for targets) or of the source ⊆ init subset (for
sources). -/

/-- Harvest targets are disjoint from the ambient outer carrier `A`, via the
arm's `h_src_shapefree` (whose `A`-component says no suffix-shaped ident is in
`A`). -/
theorem targetsOf'_entriesOf_disjoint_ambient_A [HasIdent P] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (A B : List P.Ident) (s : Stmt P (Cmd P))
    (h_src_shapefree : ∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉ A ∧
      HasIdent.ident (P := P) str ∉ B ∧
      HasIdent.ident (P := P) str ∉ Block.initVars [s]) :
    ∀ x ∈ A, x ∉ targetsOf' (Block.entriesOf ss σ) :=
  targetsOf'_entriesOf_disjoint_of_shapefree hQmint ss σ A
    (fun str h_suf => (h_src_shapefree str h_suf).1)

/-- Harvest targets are disjoint from the ambient outer carrier `B`. -/
theorem targetsOf'_entriesOf_disjoint_ambient_B [HasIdent P] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (A B : List P.Ident) (s : Stmt P (Cmd P))
    (h_src_shapefree : ∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉ A ∧
      HasIdent.ident (P := P) str ∉ B ∧
      HasIdent.ident (P := P) str ∉ Block.initVars [s]) :
    ∀ x ∈ B, x ∉ targetsOf' (Block.entriesOf ss σ) :=
  targetsOf'_entriesOf_disjoint_of_shapefree hQmint ss σ B
    (fun str h_suf => (h_src_shapefree str h_suf).2.1)

/-- Harvest targets are disjoint from the loop statement's own inits. -/
theorem targetsOf'_entriesOf_disjoint_initVars_stmt [HasIdent P] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (A B : List P.Ident) (s : Stmt P (Cmd P))
    (h_src_shapefree : ∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉ A ∧
      HasIdent.ident (P := P) str ∉ B ∧
      HasIdent.ident (P := P) str ∉ Block.initVars [s]) :
    ∀ x ∈ Block.initVars [s], x ∉ targetsOf' (Block.entriesOf ss σ) :=
  targetsOf'_entriesOf_disjoint_of_shapefree hQmint ss σ (Block.initVars [s])
    (fun str h_suf => (h_src_shapefree str h_suf).2.2)

/-- Harvest sources are disjoint from the ambient outer carrier `A`, via
`Block.sourcesOf_entriesOf_subset` (sources ⊆ body inits) and a disjointness
hypothesis on the body inits (the §E arm supplies `h_lhs_disjoint` for
`Block.initVars [s]`; the caller threads the initVars relationship
`Block.initVars body₁ ⊆ Block.initVars [s]`). -/
theorem sourcesOf'_entriesOf_disjoint_ambient [HasIdent P]
    [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIntOrder P] [HasVarsPure P P.Expr]
    (body₁ : List (Stmt P (Cmd P))) (σ : StringGenState)
    (V : List P.Ident)
    (h_init_disjoint : ∀ y ∈ Block.initVars body₁, y ∉ V) :
    ∀ x ∈ V, x ∉ sourcesOf' (Block.entriesOf body₁ σ) := by
  intro x hx_V hx_src
  exact h_init_disjoint x (Block.sourcesOf_entriesOf_subset body₁ σ x hx_src) hx_V

/-! ## The harvest sources are a `Sublist` of the body's inits.

`Block.sourcesOf_entriesOf_subset` (in `LoopInitHoistLoopDriver`) records the
membership form `sourcesOf' (entriesOf ss σ) ⊆ Block.initVars ss`.  For the
producer-precondition `(sourcesOf' (entriesOf ss σ)).Nodup` we need the stronger
`List.Sublist` form, so `Nodup` transfers via `List.Sublist.nodup`.

The harvest `entriesOf` and `initVars` walk the SAME `.block`/`.ite`/cons shape
and harvest the SAME `.cmd (.init y _ _ _)` heads (`[y]` each); they diverge only
at `.loop`, where `entriesOf` harvests `[]` (loops are passed through, their
inits hoisted separately) while `initVars` descends into the loop body.  Hence
the harvest sources are a SUBLIST (`[] <+ Block.initVars body` at the `.loop`
arm; refl/append elsewhere), not necessarily equal. -/

mutual
/-- `sourcesOf' (Stmt.entriesOf s σ)` is a `List.Sublist` of `Stmt.initVars s`. -/
theorem Stmt.sourcesOf_entriesOf_sublist [HasIdent P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    (sourcesOf' (Stmt.entriesOf s σ)).Sublist (Stmt.initVars s) := by
  match s with
  | .cmd c =>
      cases c <;>
        simp only [Stmt.entriesOf, Stmt.initVars, sourcesOf', List.map_cons,
          List.map_nil] <;>
        exact (List.Sublist.refl _)
  | .block lbl bss md =>
      rw [Stmt.entriesOf, Stmt.initVars]
      exact Block.sourcesOf_entriesOf_sublist bss σ
  | .ite g tss ess md =>
      rw [Stmt.entriesOf, Stmt.initVars]
      simp only [sourcesOf', List.map_append]
      exact (Block.sourcesOf_entriesOf_sublist tss σ).append
        (Block.sourcesOf_entriesOf_sublist ess _)
  | .loop g m inv body md =>
      rw [Stmt.entriesOf, Stmt.initVars]
      simp only [sourcesOf', List.map_nil]
      exact List.nil_sublist _
  | .exit lbl md =>
      rw [Stmt.entriesOf, Stmt.initVars]
      simp only [sourcesOf', List.map_nil]; exact List.nil_sublist _
  | .funcDecl d md =>
      rw [Stmt.entriesOf, Stmt.initVars]
      simp only [sourcesOf', List.map_nil]; exact List.nil_sublist _
  | .typeDecl t md =>
      rw [Stmt.entriesOf, Stmt.initVars]
      simp only [sourcesOf', List.map_nil]; exact List.nil_sublist _
  termination_by sizeOf s

/-- `sourcesOf' (Block.entriesOf ss σ)` is a `List.Sublist` of `Block.initVars ss`. -/
theorem Block.sourcesOf_entriesOf_sublist [HasIdent P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    (sourcesOf' (Block.entriesOf ss σ)).Sublist (Block.initVars ss) := by
  match ss with
  | [] =>
      rw [Block.entriesOf, Block.initVars]
      simp only [sourcesOf', List.map_nil]; exact List.nil_sublist _
  | s :: rest =>
      rw [Block.entriesOf, Block.initVars]
      simp only [sourcesOf', List.map_append]
      exact (Stmt.sourcesOf_entriesOf_sublist s σ).append
        (Block.sourcesOf_entriesOf_sublist rest _)
  termination_by sizeOf ss
end

/-- **Producer precondition (GAP 1).** From `(Block.initVars body₁).Nodup`, the
harvest sources `sourcesOf' (Block.entriesOf body₁ σ)` are `Nodup`.  This is the
shape `Block.bodyTransport_of_lift` consumes as `h_src_nodup` (recall
`(substOf' E).map Prod.fst = sourcesOf' E`).  `Nodup` transfers along the sublist
of the previous lemma. -/
theorem Block.entriesOf_sourcesOf_nodup_of_initVars [HasIdent P]
    (body₁ : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h_nd : (Block.initVars body₁).Nodup) :
    (sourcesOf' (Block.entriesOf body₁ σ)).Nodup :=
  (Block.sourcesOf_entriesOf_sublist body₁ σ).nodup h_nd

/-- The producer's `h_src_nodup` reads `(subst.map Prod.fst).Nodup` over
`subst := substOf' E`; this records the projection identity
`(substOf' E).map Prod.fst = sourcesOf' E` so the previous lemma lands directly
on the producer's shape. -/
theorem substOf'_map_fst (entries : List (Entry P)) :
    (substOf' entries).map Prod.fst = sourcesOf' entries := by
  simp only [substOf', sourcesOf', List.map_map, Function.comp_def]

/-- **Producer precondition, in the producer's own `h_src_nodup` shape.** From
`(Block.initVars body₁).Nodup`, the substitution `substOf' (Block.entriesOf body₁ σ)`
has `Nodup` sources — exactly the `h_src_nodup` argument of
`Block.bodyTransport_of_lift` at `subst := substOf' (Block.entriesOf body₁ σ)`. -/
theorem Block.entriesOf_substOf_src_nodup_of_initVars [HasIdent P]
    (body₁ : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h_nd : (Block.initVars body₁).Nodup) :
    ((substOf' (Block.entriesOf body₁ σ)).map Prod.fst).Nodup := by
  rw [substOf'_map_fst]
  exact Block.entriesOf_sourcesOf_nodup_of_initVars body₁ σ h_nd

/-! ## Producer shape precondition on the post-order body.

`Block.bodyTransport_of_lift` needs `Block.transportShape body₁ = true` for
`body₁ = (Block.hoistLoopPrefixInitsM body σ).1`.  The post-order pass preserves
each of the structural Bool walkers (`containsNondetLoop`, `containsFuncDecl`,
`loopHasNoInvariants`, `loopMeasureNone`, `noExit`) in value, so the body's §E
arm preconditions transport to `body₁`, and `transportShape_of_arm_preconds`
assembles them. -/
theorem Block.transportShape_hoistLoopPrefixInitsM [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIntOrder P] [HasVarsPure P P.Expr]
    (body : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h_nd : Block.containsNondetLoop body = false)
    (h_fd : Block.containsFuncDecl body = false)
    (h_inv : Block.loopHasNoInvariants body = true)
    (h_measure : Block.loopMeasureNone body = true)
    (h_noexit : Block.noExit body = true) :
    Block.transportShape (Block.hoistLoopPrefixInitsM body σ).1 = true := by
  apply Block.transportShape_of_arm_preconds
  · rw [Block.hoistLoopPrefixInitsM_containsNondetLoop]; exact h_nd
  · rw [Block.hoistLoopPrefixInitsM_containsFuncDecl]; exact h_fd
  · rw [Block.hoistLoopPrefixInitsM_loopHasNoInvariants]; exact h_inv
  · rw [Block.hoistLoopPrefixInitsM_loopMeasureNone]; exact h_measure
  · rw [Block.hoistLoopPrefixInitsM_noExit]; exact h_noexit

/-! ## The post-order body's `initVars` is `Nodup` (GAP 1 part (b)).

The §E `.loop` arm needs `(Block.initVars body₁).Nodup` for
`body₁ = (Block.hoistLoopPrefixInitsM body σ).1` — the producer-precondition GAP
1 part (b) that part (a) (`entriesOf_sourcesOf_nodup_of_initVars`) reduces to.
It does NOT follow from `uniqueInits body` alone: the pass lifts nested-loop
prefix inits to NET-NEW fresh `_hoist<digits>` names at `body₁`'s top level, so
`initVars body₁` is `{body's non-nested-loop inits} ∪ {fresh _hoist names}`.

The proof mirrors `entriesOf_targetGen`: a mutual induction over the pass that
both proves `Nodup` and classifies every member of `initVars (pass output)` as
either an ORIGINAL (a member of the source `initVars`, hence suffix-free by
`h_src_shapefree`) or a FRESH generator name (suffix-shaped, captured in the
pass output state's `stringGens` but absent from the input state's).  The two
classes are disjoint by shape; same-class collisions are ruled out by
`uniqueInits` (originals) and `StringGenState` monotonicity (fresh).

The `.loop` arm is where the fresh names appear: its output is
`havocs.map .cmd ++ [.loop g m inv body₃ md]`.  Crucially the rewritten body
`body₃` is init-free — the post-order body is `allLoopBodiesInitFree`, so the
lift residual `body₂` has no inits (`liftInitsInLoopBodyM_snd_noInitsAnywhere`)
and `applyRenames` preserves init-emptiness — so the loop arm's `initVars` is
exactly the havoc targets `targetsOf' (entriesOf body₁' σ₁')`, which are
generator names, `Nodup` by `entriesOf_targetGen`. -/

/-- `Block.applyRenames` preserves whether `Block.initVars` is empty: each
`substIdent` rename maps one init binder to one new binder, never adding or
removing init binders, so emptiness is invariant under the whole fold. -/
theorem Block.applyRenames_initVars_isEmpty [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (renames : List (P.Ident × P.Ident)) (ss : List (Stmt P (Cmd P))) :
    (Block.initVars (Block.applyRenames renames ss)).isEmpty
      = (Block.initVars ss).isEmpty := by
  induction renames generalizing ss with
  | nil => simp only [Block.applyRenames, List.foldl_nil]
  | cons p rest ih =>
    have hstep : Block.applyRenames (p :: rest) ss
        = Block.applyRenames rest (Block.substIdent p.1 p.2 ss) := by
      simp only [Block.applyRenames, List.foldl_cons]
    rw [hstep, ih (Block.substIdent p.1 p.2 ss),
        Block.substIdent_initVars_isEmpty p.1 p.2 ss]

/-- The rewritten loop body `body₃ = applyRenames renames body₂` produced by the
`.loop` arm is init-free.  `body₁ = (hoistLoopPrefixInitsM body σ).1` is
`allLoopBodiesInitFree`, so the lift residual `body₂` has no inits anywhere, and
`applyRenames` preserves init-emptiness. -/
theorem Block.applyRenames_liftResidual_initVars_nil [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (body : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.initVars
      (Block.applyRenames
        (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
          (Block.hoistLoopPrefixInitsM body σ).2).1.2.1
        (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
          (Block.hoistLoopPrefixInitsM body σ).2).1.2.2) = [] := by
  -- `body₂` is `noInitsAnywhere`, so its `initVars` is empty; `applyRenames`
  -- preserves emptiness.
  have h_albif : Block.allLoopBodiesInitFree (Block.hoistLoopPrefixInitsM body σ).1 = true :=
    Block.hoistLoopPrefixInitsM_allLoopBodiesInitFree body σ
  have h_nia :
      Block.noInitsAnywhere
        (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
          (Block.hoistLoopPrefixInitsM body σ).2).1.2.2 = true :=
    Block.liftInitsInLoopBodyM_snd_noInitsAnywhere _ _ h_albif
  have h_body₂_nil :
      Block.initVars
        (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
          (Block.hoistLoopPrefixInitsM body σ).2).1.2.2 = [] :=
    Block.initVars_eq_nil_of_noInitsAnywhere _ h_nia
  have h_isEmpty := Block.applyRenames_initVars_isEmpty
    (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
      (Block.hoistLoopPrefixInitsM body σ).2).1.2.1
    (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
      (Block.hoistLoopPrefixInitsM body σ).2).1.2.2
  rw [h_body₂_nil] at h_isEmpty
  simp only [List.isEmpty_nil] at h_isEmpty
  exact List.isEmpty_iff.mp h_isEmpty

/-- `Block.initVars` distributes over `++`. -/
theorem Block.initVars_append'
    (xs ys : List (Stmt P (Cmd P))) :
    Block.initVars (xs ++ ys) = Block.initVars xs ++ Block.initVars ys := by
  induction xs with
  | nil => simp [Block.initVars]
  | cons x rest ih =>
    simp only [List.cons_append, Block.initVars_cons, ih, List.append_assoc]

/-- The havoc prelude's `initVars` are exactly the harvest targets: every havoc
is `init e.2.1 ty .nondet md`, contributing its target ident `e.2.1`. -/
theorem Block.initVars_havocStmts' (entries : List (Entry P)) :
    Block.initVars (havocStmts' entries) = targetsOf' entries := by
  induction entries with
  | nil =>
      simp only [LoopInitHoistLoopDriver.havocStmts'_nil, Block.initVars,
                 LoopInitHoistLoopDriver.targetsOf'_nil]
  | cons e rest ih =>
      rw [LoopInitHoistLoopDriver.havocStmts'_cons, Block.initVars_cons,
          LoopInitHoistLoopDriver.targetsOf'_cons, ih]
      simp only [Stmt.initVars, List.singleton_append]

/-- Classification of an `initVars` element of the post-order pass output:
either an ORIGINAL source init (a member of the source `initVars` carrier
`src`), or a FRESH generator name (`HasIdent.ident str` for a string `str`
captured in the output state `σ'` but absent from the input state `σ`).  The
fresh disjunct additionally records that `str` carries the hoist pass's mint
kind `Q` (`Q str`), which the freshly minted carrier names satisfy by the mint
witness `hQmint`.  Instantiating `Q := String.HasUnderscoreDigitSuffix` recovers
the blanket generator-suffix statement. -/
def HoistInitClass [HasIdent P] (Q : String → Prop) (src : List P.Ident) (σ σ' : StringGenState) (x : P.Ident) : Prop :=
  (x ∈ src) ∨
  (∃ str : String, x = HasIdent.ident str
    ∧ str ∈ StringGenState.stringGens σ'
    ∧ str ∉ StringGenState.stringGens σ
    ∧ Q str)

/-- Two classified `initVars` carriers from consecutive sub-passes are disjoint:
originals are disjoint by `uniqueInits` and suffix-free by `h_src_shapefree`;
fresh names are suffix-shaped and captured in disjoint state windows.  All four
cross-class collisions are impossible. -/
theorem hoistInitClass_disjoint [HasIdent P] [LawfulHasIdent P] {Q : String → Prop}
    (src₁ src₂ : List P.Ident) (σ σmid σ' : StringGenState)
    (_h_wf : StringGenState.WF σ)
    (_h_step₁ : GenStep σ σmid) (_h_step₂ : GenStep σmid σ')
    (h_src_disjoint : ∀ a ∈ src₁, ∀ b ∈ src₂, a ≠ b)
    (h_sf₁ : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ src₁)
    (h_sf₂ : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ src₂)
    (L₁ L₂ : List P.Ident)
    (hc₁ : ∀ x ∈ L₁, HoistInitClass Q src₁ σ σmid x)
    (hc₂ : ∀ x ∈ L₂, HoistInitClass Q src₂ σmid σ' x) :
    ∀ a ∈ L₁, ∀ b ∈ L₂, a ≠ b := by
  intro a ha b hb hab
  subst hab
  rcases hc₁ a ha with h_o₁ | ⟨str₁, hstr₁_eq, hstr₁_in, hstr₁_not, hstr₁_Q⟩
  · rcases hc₂ a hb with h_o₂ | ⟨str₂, hstr₂_eq, hstr₂_in, _, hstr₂_Q⟩
    · exact h_src_disjoint a h_o₁ a h_o₂ rfl
    · -- a ∈ src₁ (kind-free) but a = ident str₂ with `Q str₂`.
      exact h_sf₁ str₂ hstr₂_Q (hstr₂_eq ▸ h_o₁)
  · -- a = ident str₁ with str₁ ∈ σmid \ σ and `Q str₁`.
    rcases hc₂ a hb with h_o₂ | ⟨str₂, hstr₂_eq, hstr₂_in, hstr₂_not, _⟩
    · exact h_sf₂ str₁ hstr₁_Q (hstr₁_eq ▸ h_o₂)
    · -- ident str₁ = ident str₂ ⇒ str₁ = str₂; but str₁ ∈ σmid, str₂ ∉ σmid.
      have h_id : (HasIdent.ident str₁ : P.Ident) = HasIdent.ident str₂ :=
        hstr₁_eq.symm.trans hstr₂_eq
      have : str₁ = str₂ := LawfulHasIdent.ident_inj h_id
      exact hstr₂_not (this ▸ hstr₁_in)

mutual
/-- Mutual `Stmt` step: the post-order pass output's `initVars` is `Nodup`, and
each member is `HoistInitClass`-classified between the input and output states. -/
theorem Stmt.hoistLoopPrefixInitsM_initVars_classified [HasIdent P] [LawfulHasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (s : Stmt P (Cmd P)) (σ : StringGenState) (h_wf : StringGenState.WF σ)
    (h_unique : (Stmt.initVars s).Nodup)
    (h_shapefree : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ Stmt.initVars s) :
    (∀ x ∈ Block.initVars (Stmt.hoistLoopPrefixInitsM s σ).1,
        HoistInitClass Q (Stmt.initVars s) σ (Stmt.hoistLoopPrefixInitsM s σ).2 x)
      ∧ (Block.initVars (Stmt.hoistLoopPrefixInitsM s σ).1).Nodup := by
  match s with
  | .cmd c =>
      -- residual `[.cmd c]`; initVars unchanged; every member is an original.
      cases c with
      | init y ty rhs md =>
          refine ⟨?_, ?_⟩
          · intro x hx
            simp only [Stmt.hoistLoopPrefixInitsM, Block.initVars_cons, Stmt.initVars,
                       Block.initVars, List.append_nil] at hx ⊢
            exact Or.inl hx
          · simp only [Stmt.hoistLoopPrefixInitsM, Block.initVars_cons, Stmt.initVars,
                       Block.initVars, List.append_nil]
            simp [List.nodup_cons]
      | set x rhs md =>
          refine ⟨fun x hx => ?_, ?_⟩ <;>
            simp_all [Stmt.hoistLoopPrefixInitsM, Block.initVars, Stmt.initVars]
      | assert l e md =>
          refine ⟨fun x hx => ?_, ?_⟩ <;>
            simp_all [Stmt.hoistLoopPrefixInitsM, Block.initVars, Stmt.initVars]
      | assume l e md =>
          refine ⟨fun x hx => ?_, ?_⟩ <;>
            simp_all [Stmt.hoistLoopPrefixInitsM, Block.initVars, Stmt.initVars]
      | cover l e md =>
          refine ⟨fun x hx => ?_, ?_⟩ <;>
            simp_all [Stmt.hoistLoopPrefixInitsM, Block.initVars, Stmt.initVars]
  | .block lbl bss md =>
      rw [Stmt.hoistLoopPrefixInitsM_block_out, Stmt.hoistLoopPrefixInitsM_block_state]
      have h_unique' : (Block.initVars bss).Nodup := by
        simpa only [Stmt.initVars_block] using h_unique
      have h_shapefree' : ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ Block.initVars bss := by
        intro str hsuf; simpa only [Stmt.initVars_block] using h_shapefree str hsuf
      have ih := Block.hoistLoopPrefixInitsM_initVars_classified hQmint bss σ h_wf h_unique' h_shapefree'
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_block, Block.initVars,
                   List.append_nil] at hx
        have := ih.1 x hx
        simpa only [Stmt.initVars_block] using this
      · simp only [Block.initVars_cons, Stmt.initVars_block, Block.initVars, List.append_nil]
        exact ih.2
  | .ite g tss ess md =>
      rw [Stmt.hoistLoopPrefixInitsM_ite_out, Stmt.hoistLoopPrefixInitsM_ite_state]
      -- split uniqueInits/shapefree across the two branches.
      have h_uni : (Block.initVars tss ++ Block.initVars ess).Nodup := by
        simpa only [Stmt.initVars_ite] using h_unique
      have h_uni_t : (Block.initVars tss).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_e : (Block.initVars ess).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_disj_te : ∀ a ∈ Block.initVars tss, ∀ b ∈ Block.initVars ess, a ≠ b :=
        (List.nodup_append.mp h_uni).2.2
      have h_sf_t : ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ Block.initVars tss := by
        intro str hsuf hmem
        exact h_shapefree str hsuf (by
          rw [Stmt.initVars_ite, List.mem_append]; exact Or.inl hmem)
      have h_sf_e : ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ Block.initVars ess := by
        intro str hsuf hmem
        exact h_shapefree str hsuf (by
          rw [Stmt.initVars_ite, List.mem_append]; exact Or.inr hmem)
      have ih_t := Block.hoistLoopPrefixInitsM_initVars_classified hQmint tss σ h_wf h_uni_t h_sf_t
      have h_wf_t : StringGenState.WF (Block.hoistLoopPrefixInitsM tss σ).2 :=
        (Block.hoistLoopPrefixInitsM_genStep tss σ).wf_mono h_wf
      have ih_e := Block.hoistLoopPrefixInitsM_initVars_classified hQmint ess
        (Block.hoistLoopPrefixInitsM tss σ).2 h_wf_t h_uni_e h_sf_e
      have h_step_t : GenStep σ (Block.hoistLoopPrefixInitsM tss σ).2 :=
        Block.hoistLoopPrefixInitsM_genStep tss σ
      have h_step_e : GenStep (Block.hoistLoopPrefixInitsM tss σ).2
          (Block.hoistLoopPrefixInitsM ess (Block.hoistLoopPrefixInitsM tss σ).2).2 :=
        Block.hoistLoopPrefixInitsM_genStep ess _
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_ite, Block.initVars,
                   List.append_nil] at hx ⊢
        rw [List.mem_append] at hx
        rcases hx with h | h
        · rcases ih_t.1 x h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [List.mem_append]; exact Or.inl h_o)
          · exact Or.inr ⟨str, he, h_step_e.subset hin, hnot, hQ⟩
        · rcases ih_e.1 x h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [List.mem_append]; exact Or.inr h_o)
          · refine Or.inr ⟨str, he, hin, ?_, hQ⟩
            intro h_in_σ; exact hnot (h_step_t.subset h_in_σ)
      · simp only [Block.initVars_cons, Stmt.initVars_ite, Block.initVars, List.append_nil]
        rw [List.nodup_append]
        refine ⟨ih_t.2, ih_e.2, ?_⟩
        exact hoistInitClass_disjoint (Block.initVars tss) (Block.initVars ess)
          σ (Block.hoistLoopPrefixInitsM tss σ).2 _ h_wf h_step_t h_step_e
          h_disj_te h_sf_t h_sf_e _ _ ih_t.1 ih_e.1
  | .loop g m inv body md =>
      rw [Stmt.hoistLoopPrefixInitsM_loop_out, Stmt.hoistLoopPrefixInitsM_loop_state]
      -- output initVars = targetsOf'(entriesOf body₁ σ₁) ++ initVars body₃ = targets ++ [].
      have h_wf₁ : StringGenState.WF (Block.hoistLoopPrefixInitsM body σ).2 :=
        (Block.hoistLoopPrefixInitsM_genStep body σ).wf_mono h_wf
      have h_body₃_nil :
          Block.initVars
            (Block.applyRenames
              (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
                (Block.hoistLoopPrefixInitsM body σ).2).1.2.1
              (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
                (Block.hoistLoopPrefixInitsM body σ).2).1.2.2) = [] :=
        Block.applyRenames_liftResidual_initVars_nil body σ
      -- the havoc prelude's initVars are the harvest targets.
      have h_havoc_init :
          Block.initVars
            ((Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1.1.map Stmt.cmd)
            = targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1
                (Block.hoistLoopPrefixInitsM body σ).2) := by
        rw [(LoopInitHoistLoopDriver.Block.lift_harvest_subst
              (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1]
        exact Block.initVars_havocStmts' _
      -- GenStep window: σ ⊆ σ₁, so a target fresh from σ₁ is fresh from σ.
      have h_step_body : GenStep σ (Block.hoistLoopPrefixInitsM body σ).2 :=
        Block.hoistLoopPrefixInitsM_genStep body σ
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Block.initVars_append', h_havoc_init] at hx
        simp only [Block.initVars_cons, Stmt.initVars_loop, Block.initVars,
                   List.append_nil] at hx
        rw [h_body₃_nil, List.append_nil] at hx
        -- x is a harvest target: fresh between σ₁ and σ₂; classify as fresh from σ.
        obtain ⟨e, he_mem, he_eq⟩ := List.mem_map.mp hx
        obtain ⟨t, ht_eq, ht_in, ht_not⟩ :=
          (Block.entriesOf_targetGen (Block.hoistLoopPrefixInitsM body σ).1
            (Block.hoistLoopPrefixInitsM body σ).2 h_wf₁).1 e he_mem
        obtain ⟨t', ht'_eq, ht'_Q⟩ :=
          Block.entriesOf_target_suffix hQmint (Block.hoistLoopPrefixInitsM body σ).1
            (Block.hoistLoopPrefixInitsM body σ).2 e he_mem
        have h_t_eq : t = t' :=
          LawfulHasIdent.ident_inj (ht_eq.symm.trans ht'_eq)
        refine Or.inr ⟨t, ?_, ht_in, ?_, h_t_eq ▸ ht'_Q⟩
        · rw [← he_eq, ht_eq]
        · intro h_in_σ; exact ht_not (h_step_body.subset h_in_σ)
      · rw [Block.initVars_append', h_havoc_init]
        simp only [Block.initVars_cons, Stmt.initVars_loop, Block.initVars, List.append_nil]
        rw [h_body₃_nil, List.append_nil]
        exact (Block.entriesOf_targetGen (Block.hoistLoopPrefixInitsM body σ).1
          (Block.hoistLoopPrefixInitsM body σ).2 h_wf₁).2
  | .exit lbl md =>
      refine ⟨fun x hx => ?_, ?_⟩ <;>
        simp_all [Stmt.hoistLoopPrefixInitsM, Block.initVars, Stmt.initVars]
  | .funcDecl d md =>
      refine ⟨fun x hx => ?_, ?_⟩ <;>
        simp_all [Stmt.hoistLoopPrefixInitsM, Block.initVars, Stmt.initVars]
  | .typeDecl t md =>
      refine ⟨fun x hx => ?_, ?_⟩ <;>
        simp_all [Stmt.hoistLoopPrefixInitsM, Block.initVars, Stmt.initVars]
  termination_by sizeOf s

/-- Mutual `Block` step. -/
theorem Block.hoistLoopPrefixInitsM_initVars_classified [HasIdent P] [LawfulHasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) (h_wf : StringGenState.WF σ)
    (h_unique : (Block.initVars ss).Nodup)
    (h_shapefree : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ Block.initVars ss) :
    (∀ x ∈ Block.initVars (Block.hoistLoopPrefixInitsM ss σ).1,
        HoistInitClass Q (Block.initVars ss) σ (Block.hoistLoopPrefixInitsM ss σ).2 x)
      ∧ (Block.initVars (Block.hoistLoopPrefixInitsM ss σ).1).Nodup := by
  match ss with
  | [] =>
      refine ⟨fun x hx => ?_, ?_⟩ <;>
        simp_all [Block.hoistLoopPrefixInitsM, Block.initVars]
  | s :: rest =>
      rw [Block.hoistLoopPrefixInitsM_cons_out, Block.hoistLoopPrefixInitsM_cons_state]
      have h_uni : (Stmt.initVars s ++ Block.initVars rest).Nodup := by
        simpa only [Block.initVars_cons] using h_unique
      have h_uni_s : (Stmt.initVars s).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_r : (Block.initVars rest).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_disj_sr : ∀ a ∈ Stmt.initVars s, ∀ b ∈ Block.initVars rest, a ≠ b :=
        (List.nodup_append.mp h_uni).2.2
      have h_sf_s : ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ Stmt.initVars s := by
        intro str hsuf hmem
        exact h_shapefree str hsuf (by
          rw [Block.initVars_cons, List.mem_append]; exact Or.inl hmem)
      have h_sf_r : ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ Block.initVars rest := by
        intro str hsuf hmem
        exact h_shapefree str hsuf (by
          rw [Block.initVars_cons, List.mem_append]; exact Or.inr hmem)
      have ih_s := Stmt.hoistLoopPrefixInitsM_initVars_classified hQmint s σ h_wf h_uni_s h_sf_s
      have h_wf_s : StringGenState.WF (Stmt.hoistLoopPrefixInitsM s σ).2 :=
        (Stmt.hoistLoopPrefixInitsM_genStep s σ).wf_mono h_wf
      have ih_r := Block.hoistLoopPrefixInitsM_initVars_classified hQmint rest
        (Stmt.hoistLoopPrefixInitsM s σ).2 h_wf_s h_uni_r h_sf_r
      have h_step_s : GenStep σ (Stmt.hoistLoopPrefixInitsM s σ).2 :=
        Stmt.hoistLoopPrefixInitsM_genStep s σ
      have h_step_r : GenStep (Stmt.hoistLoopPrefixInitsM s σ).2
          (Block.hoistLoopPrefixInitsM rest (Stmt.hoistLoopPrefixInitsM s σ).2).2 :=
        Block.hoistLoopPrefixInitsM_genStep rest _
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Block.initVars_append'] at hx
        rw [Block.initVars_cons]
        rw [List.mem_append] at hx
        rcases hx with h | h
        · rcases ih_s.1 x h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [List.mem_append]; exact Or.inl h_o)
          · exact Or.inr ⟨str, he, h_step_r.subset hin, hnot, hQ⟩
        · rcases ih_r.1 x h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [List.mem_append]; exact Or.inr h_o)
          · refine Or.inr ⟨str, he, hin, ?_, hQ⟩
            intro h_in_σ; exact hnot (h_step_s.subset h_in_σ)
      · rw [Block.initVars_append', List.nodup_append]
        refine ⟨ih_s.2, ih_r.2, ?_⟩
        exact hoistInitClass_disjoint (Stmt.initVars s) (Block.initVars rest)
          σ (Stmt.hoistLoopPrefixInitsM s σ).2 _ h_wf h_step_s h_step_r
          h_disj_sr h_sf_s h_sf_r _ _ ih_s.1 ih_r.1
  termination_by sizeOf ss
end

/-- **GAP 1 part (b).** The post-order body `body₁ = (hoistLoopPrefixInitsM body
σ).1` has `Nodup` `initVars`, given `WF σ`, the source body's `uniqueInits`, and
the arm's `h_src_shapefree` (originals avoid the generator `_<digit>` suffix).
Combined with part (a) (`entriesOf_sourcesOf_nodup_of_initVars`) this discharges
the producer's `h_src_nodup` for the §E `.loop` arm. -/
theorem Block.hoistLoopPrefixInitsM_initVars_nodup [HasIdent P] [LawfulHasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (body : List (Stmt P (Cmd P))) (σ : StringGenState) (h_wf : StringGenState.WF σ)
    (h_unique : (Block.initVars body).Nodup)
    (h_shapefree : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ Block.initVars body) :
    (Block.initVars (Block.hoistLoopPrefixInitsM body σ).1).Nodup :=
  (Block.hoistLoopPrefixInitsM_initVars_classified hQmint body σ h_wf h_unique h_shapefree).2

/-! ## `modifiedVars` classification of the post-order pass output.

The `.loop` arm's final disjointness obligation is `modifiedVars body₁ ∩
targetsOf' E = ∅` for `body₁ = (hoistLoopPrefixInitsM body σ).1` and `E =
entriesOf body₁ σ₁`.  Mirroring `Block.sourcesOf'_disjoint_targetsOf'_self`, this
follows from classifying each `x ∈ modifiedVars body₁` as either an ORIGINAL
source modified-or-init var (suffix-free for a well-formed source) or a FRESH
generator name captured by `σ₁`; both are disjoint from the suffix-shaped
targets `∉ σ₁`.  The lemmas below build that classification bottom-up from the
structural action of `substIdent`/`applyRenames`/`liftInitsInLoopBodyM` on
`modifiedVars`. -/

/-- `Block.modifiedVars` cons split. -/
private theorem Block.modVars_cons (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) :
    Block.modifiedVars (s :: rest) = Stmt.modifiedVars s ++ Block.modifiedVars rest := by
  simp only [Block.modifiedVars]

/-- `Block.modifiedVars` distributes over `++`. -/
private theorem Block.modVars_append (xs ys : List (Stmt P (Cmd P))) :
    Block.modifiedVars (xs ++ ys) = Block.modifiedVars xs ++ Block.modifiedVars ys := by
  induction xs with
  | nil => simp [Block.modifiedVars]
  | cons x rest ih => simp only [List.cons_append, Block.modVars_cons, ih, List.append_assoc]

mutual
/-- A `substIdent y y'` rename sends each modified var of a statement either to
an unchanged original (`≠ y`) or to the new name `y'`. -/
theorem Stmt.substIdent_modVars_mem [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] (y y' : P.Ident) (s : Stmt P (Cmd P))
    (x : P.Ident) (hx : x ∈ Stmt.modifiedVars (Stmt.substIdent y y' s)) :
    (x ∈ Stmt.modifiedVars s ∧ x ≠ y) ∨ x = y' := by
  match s with
  | .cmd c =>
      cases c with
      | init name ty rhs md =>
          simp only [Stmt.substIdent_cmd, Cmd.substIdent_init, Stmt.modifiedVars,
            HasVarsImp.modifiedVars, Cmd.modifiedVars] at hx
          exact absurd hx List.not_mem_nil
      | set name rhs md =>
          simp only [Stmt.substIdent_cmd, Cmd.substIdent_set, Stmt.modifiedVars,
            HasVarsImp.modifiedVars, Cmd.modifiedVars, List.mem_singleton] at hx
          by_cases h : name = y
          · subst h; simp only [] at hx; exact Or.inr hx
          · simp only [if_neg h] at hx
            subst hx
            refine Or.inl ⟨?_, h⟩
            simp only [Stmt.modifiedVars, HasVarsImp.modifiedVars, Cmd.modifiedVars,
              List.mem_singleton]
      | assert l e md =>
          simp only [Stmt.substIdent_cmd, Cmd.substIdent_assert, Stmt.modifiedVars,
            HasVarsImp.modifiedVars, Cmd.modifiedVars] at hx
          exact absurd hx List.not_mem_nil
      | assume l e md =>
          simp only [Stmt.substIdent_cmd, Cmd.substIdent_assume, Stmt.modifiedVars,
            HasVarsImp.modifiedVars, Cmd.modifiedVars] at hx
          exact absurd hx List.not_mem_nil
      | cover l e md =>
          simp only [Stmt.substIdent_cmd, Cmd.substIdent_cover, Stmt.modifiedVars,
            HasVarsImp.modifiedVars, Cmd.modifiedVars] at hx
          exact absurd hx List.not_mem_nil
  | .block lbl bss md =>
      simp only [Stmt.substIdent_block, Stmt.modifiedVars] at hx ⊢
      exact Block.substIdent_modVars_mem y y' bss x hx
  | .ite g tss ess md =>
      simp only [Stmt.substIdent_ite, Stmt.modifiedVars, List.mem_append] at hx ⊢
      rcases hx with h | h
      · rcases Block.substIdent_modVars_mem y y' tss x h with ⟨hm, hne⟩ | he
        · exact Or.inl ⟨Or.inl hm, hne⟩
        · exact Or.inr he
      · rcases Block.substIdent_modVars_mem y y' ess x h with ⟨hm, hne⟩ | he
        · exact Or.inl ⟨Or.inr hm, hne⟩
        · exact Or.inr he
  | .loop g m inv body md =>
      simp only [Stmt.substIdent_loop, Stmt.modifiedVars] at hx ⊢
      exact Block.substIdent_modVars_mem y y' body x hx
  | .exit lbl md =>
      simp only [Stmt.substIdent_exit, Stmt.modifiedVars] at hx
      exact absurd hx List.not_mem_nil
  | .funcDecl d md =>
      simp only [Stmt.substIdent_funcDecl, Stmt.modifiedVars] at hx
      exact absurd hx List.not_mem_nil
  | .typeDecl t md =>
      simp only [Stmt.substIdent_typeDecl, Stmt.modifiedVars] at hx
      exact absurd hx List.not_mem_nil
  termination_by sizeOf s

/-- Block-level `substIdent` modified-var classification. -/
theorem Block.substIdent_modVars_mem [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] (y y' : P.Ident) (ss : List (Stmt P (Cmd P)))
    (x : P.Ident) (hx : x ∈ Block.modifiedVars (Block.substIdent y y' ss)) :
    (x ∈ Block.modifiedVars ss ∧ x ≠ y) ∨ x = y' := by
  match ss with
  | [] =>
      simp only [Block.substIdent_nil, Block.modifiedVars] at hx
      exact absurd hx List.not_mem_nil
  | s :: rest =>
      simp only [Block.substIdent_cons, Block.modVars_cons, List.mem_append] at hx ⊢
      rcases hx with h | h
      · rcases Stmt.substIdent_modVars_mem y y' s x h with ⟨hm, hne⟩ | he
        · exact Or.inl ⟨Or.inl hm, hne⟩
        · exact Or.inr he
      · rcases Block.substIdent_modVars_mem y y' rest x h with ⟨hm, hne⟩ | he
        · exact Or.inl ⟨Or.inr hm, hne⟩
        · exact Or.inr he
  termination_by sizeOf ss
end

/-- `applyRenames` modified-var classification: each modified var of the renamed
block is either an original modified var or one of the rename TARGETS. -/
theorem Block.applyRenames_modVars_mem [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] (renames : List (P.Ident × P.Ident))
    (ss : List (Stmt P (Cmd P))) (x : P.Ident)
    (hx : x ∈ Block.modifiedVars (Block.applyRenames renames ss)) :
    x ∈ Block.modifiedVars ss ∨ x ∈ renames.map Prod.snd := by
  induction renames generalizing ss with
  | nil =>
      simp only [Block.applyRenames, List.foldl_nil] at hx
      exact Or.inl hx
  | cons p rest ih =>
      have hstep : Block.applyRenames (p :: rest) ss
          = Block.applyRenames rest (Block.substIdent p.1 p.2 ss) := by
        simp only [Block.applyRenames, List.foldl_cons]
      rw [hstep] at hx
      rcases ih (Block.substIdent p.1 p.2 ss) hx with h | h
      · rcases Block.substIdent_modVars_mem p.1 p.2 ss x h with ⟨hm, _⟩ | he
        · exact Or.inl hm
        · refine Or.inr ?_; simp only [List.map_cons, List.mem_cons]; exact Or.inl he
      · refine Or.inr ?_; simp only [List.map_cons, List.mem_cons]; exact Or.inr h

mutual
/-- The lift residual's `modifiedVars` are contained in the input block's
`modifiedVars` plus the rename SOURCES (each lifted `.init y` adds a `.set y`
residual whose target `y` is the rename source). -/
theorem Stmt.liftResidual_modVars_mem [HasIdent P] (s : Stmt P (Cmd P)) (σ : StringGenState)
    (x : P.Ident) (hx : x ∈ Block.modifiedVars (Stmt.liftInitsInLoopBodyM s σ).1.2.2) :
    x ∈ Stmt.modifiedVars s ∨ x ∈ (Stmt.liftInitsInLoopBodyM s σ).1.2.1.map Prod.fst := by
  match s with
  | .cmd c =>
      cases c with
      | init name ty rhs md =>
          simp only [Stmt.liftInitsInLoopBodyM, Block.modifiedVars, Stmt.modifiedVars,
            HasVarsImp.modifiedVars, Cmd.modifiedVars, List.append_nil, List.mem_singleton,
            List.map_cons, List.map_nil] at hx ⊢
          exact Or.inr hx
      | set name rhs md =>
          simp only [Stmt.liftInitsInLoopBodyM, Block.modifiedVars, Stmt.modifiedVars,
            List.append_nil] at hx ⊢
          exact Or.inl hx
      | assert l e md =>
          simp only [Stmt.liftInitsInLoopBodyM, Block.modifiedVars, Stmt.modifiedVars,
            HasVarsImp.modifiedVars, Cmd.modifiedVars, List.append_nil] at hx
          exact absurd hx List.not_mem_nil
      | assume l e md =>
          simp only [Stmt.liftInitsInLoopBodyM, Block.modifiedVars, Stmt.modifiedVars,
            HasVarsImp.modifiedVars, Cmd.modifiedVars, List.append_nil] at hx
          exact absurd hx List.not_mem_nil
      | cover l e md =>
          simp only [Stmt.liftInitsInLoopBodyM, Block.modifiedVars, Stmt.modifiedVars,
            HasVarsImp.modifiedVars, Cmd.modifiedVars, List.append_nil] at hx
          exact absurd hx List.not_mem_nil
  | .block lbl bss md =>
      have hx' : x ∈ Block.modifiedVars (Block.liftInitsInLoopBodyM bss σ).1.2.2 := by
        rw [Stmt.liftInitsInLoopBodyM_block_residual] at hx
        simpa only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil] using hx
      have hfst : (Stmt.liftInitsInLoopBodyM (.block lbl bss md) σ).1.2.1
          = (Block.liftInitsInLoopBodyM bss σ).1.2.1 := by
        rw [Stmt.liftInitsInLoopBodyM]
        rcases hb : Block.liftInitsInLoopBodyM bss σ with ⟨⟨hs, rn, bss'⟩, σ'⟩
        simp only [hb]
      simp only [Stmt.modifiedVars, hfst]
      exact Block.liftResidual_modVars_mem bss σ x hx'
  | .ite g tss ess md =>
      have hx' : x ∈ Block.modifiedVars (Block.liftInitsInLoopBodyM tss σ).1.2.2 ∨
          x ∈ Block.modifiedVars
            (Block.liftInitsInLoopBodyM ess (Block.liftInitsInLoopBodyM tss σ).2).1.2.2 := by
        rw [Stmt.liftInitsInLoopBodyM_ite_residual] at hx
        simpa only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil, List.mem_append] using hx
      have hfst : (Stmt.liftInitsInLoopBodyM (.ite g tss ess md) σ).1.2.1
          = (Block.liftInitsInLoopBodyM tss σ).1.2.1 ++
            (Block.liftInitsInLoopBodyM ess (Block.liftInitsInLoopBodyM tss σ).2).1.2.1 := by
        rw [Stmt.liftInitsInLoopBodyM]
        rcases ht : Block.liftInitsInLoopBodyM tss σ with ⟨⟨ths, trn, tss'⟩, σ₁⟩
        rcases he : Block.liftInitsInLoopBodyM ess σ₁ with ⟨⟨ehs, ern, ess'⟩, σ₂⟩
        simp only [ht, he]
      simp only [Stmt.modifiedVars, hfst, List.map_append, List.mem_append]
      rcases hx' with h | h
      · rcases Block.liftResidual_modVars_mem tss σ x h with h2 | h2
        · exact Or.inl (Or.inl h2)
        · exact Or.inr (Or.inl h2)
      · rcases Block.liftResidual_modVars_mem ess (Block.liftInitsInLoopBodyM tss σ).2 x h with h2 | h2
        · exact Or.inl (Or.inr h2)
        · exact Or.inr (Or.inr h2)
  | .loop g m inv body md =>
      simp only [Stmt.liftInitsInLoopBodyM, Block.modifiedVars, Stmt.modifiedVars,
        List.append_nil] at hx ⊢
      exact Or.inl hx
  | .exit lbl md =>
      simp only [Stmt.liftInitsInLoopBodyM, Block.modifiedVars, Stmt.modifiedVars,
        List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  | .funcDecl d md =>
      simp only [Stmt.liftInitsInLoopBodyM, Block.modifiedVars, Stmt.modifiedVars,
        List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  | .typeDecl t md =>
      simp only [Stmt.liftInitsInLoopBodyM, Block.modifiedVars, Stmt.modifiedVars,
        List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  termination_by sizeOf s

/-- Block-level lift residual modified-var containment. -/
theorem Block.liftResidual_modVars_mem [HasIdent P] (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (x : P.Ident) (hx : x ∈ Block.modifiedVars (Block.liftInitsInLoopBodyM ss σ).1.2.2) :
    x ∈ Block.modifiedVars ss ∨ x ∈ (Block.liftInitsInLoopBodyM ss σ).1.2.1.map Prod.fst := by
  match ss with
  | [] =>
      simp only [Block.liftInitsInLoopBodyM, Block.modifiedVars] at hx
      exact absurd hx List.not_mem_nil
  | s :: rest =>
      have hx' : x ∈ Block.modifiedVars (Stmt.liftInitsInLoopBodyM s σ).1.2.2 ∨
          x ∈ Block.modifiedVars
            (Block.liftInitsInLoopBodyM rest (Stmt.liftInitsInLoopBodyM s σ).2).1.2.2 := by
        rw [Block.liftInitsInLoopBodyM_cons_residual] at hx
        simpa only [Block.modVars_append, List.mem_append] using hx
      have hfst : (Block.liftInitsInLoopBodyM (s :: rest) σ).1.2.1
          = (Stmt.liftInitsInLoopBodyM s σ).1.2.1 ++
            (Block.liftInitsInLoopBodyM rest (Stmt.liftInitsInLoopBodyM s σ).2).1.2.1 := by
        rw [Block.liftInitsInLoopBodyM]
        rcases hs : Stmt.liftInitsInLoopBodyM s σ with ⟨⟨hs_s, rn_s, ss_s⟩, σ₁⟩
        rcases hr : Block.liftInitsInLoopBodyM rest σ₁ with ⟨⟨hs_r, rn_r, ss_r⟩, σ₂⟩
        simp only [hs, hr]
      simp only [Block.modVars_cons, hfst, List.map_append, List.mem_append]
      rcases hx' with h | h
      · rcases Stmt.liftResidual_modVars_mem s σ x h with h2 | h2
        · exact Or.inl (Or.inl h2)
        · exact Or.inr (Or.inl h2)
      · rcases Block.liftResidual_modVars_mem rest (Stmt.liftInitsInLoopBodyM s σ).2 x h with h2 | h2
        · exact Or.inl (Or.inr h2)
        · exact Or.inr (Or.inr h2)
  termination_by sizeOf ss
end

/-- The havoc prelude `havocStmts' entries` (all `.init`) modifies nothing. -/
private theorem Block.modifiedVars_havocStmts' (entries : List (Entry P)) :
    Block.modifiedVars (havocStmts' entries) = [] := by
  induction entries with
  | nil =>
      simp only [LoopInitHoistLoopDriver.havocStmts'_nil, Block.modifiedVars]
  | cons e rest ih =>
      rw [LoopInitHoistLoopDriver.havocStmts'_cons, Block.modVars_cons, ih]
      simp only [Stmt.modifiedVars, HasVarsImp.modifiedVars, Cmd.modifiedVars, List.append_nil]

mutual
/-- Mutual `Stmt` step of the `modifiedVars` classification: every modified var
of the post-order pass output is either an ORIGINAL source modified-or-init var,
or a FRESH generator name captured between the input and output states.  (The
source carrier is `modifiedVars ++ initVars`: a lifted nested-loop init turns a
`.init y` into a `.set y` residual whose name `y` may survive un-renamed, so the
ORIGINAL branch must admit source inits as well as source set-targets.) -/
theorem Stmt.hoistLoopPrefixInitsM_modVars_classified [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] [LawfulHasIdent P] [HasVarsPure P P.Expr] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIntOrder P] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (s : Stmt P (Cmd P)) (σ : StringGenState) (h_wf : StringGenState.WF σ)
    (h_unique : (Stmt.initVars s).Nodup)
    (h_shapefree : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ Stmt.initVars s) :
    ∀ x ∈ Block.modifiedVars (Stmt.hoistLoopPrefixInitsM s σ).1,
        HoistInitClass Q (Stmt.modifiedVars s ++ Stmt.initVars s) σ
          (Stmt.hoistLoopPrefixInitsM s σ).2 x := by
  match s with
  | .cmd c =>
      intro x hx
      cases c with
      | init y ty rhs md =>
          simp only [Stmt.hoistLoopPrefixInitsM, Block.modifiedVars, Stmt.modifiedVars,
            HasVarsImp.modifiedVars, Cmd.modifiedVars, List.append_nil] at hx
          exact absurd hx List.not_mem_nil
      | set y rhs md =>
          simp only [Stmt.hoistLoopPrefixInitsM, Block.modifiedVars, Stmt.modifiedVars,
            HasVarsImp.modifiedVars, Cmd.modifiedVars, List.append_nil] at hx
          refine Or.inl ?_
          simp only [Stmt.modifiedVars, HasVarsImp.modifiedVars, Cmd.modifiedVars,
            Stmt.initVars, List.mem_append]
          exact Or.inl hx
      | assert l e md =>
          simp only [Stmt.hoistLoopPrefixInitsM, Block.modifiedVars, Stmt.modifiedVars,
            HasVarsImp.modifiedVars, Cmd.modifiedVars, List.append_nil] at hx
          exact absurd hx List.not_mem_nil
      | assume l e md =>
          simp only [Stmt.hoistLoopPrefixInitsM, Block.modifiedVars, Stmt.modifiedVars,
            HasVarsImp.modifiedVars, Cmd.modifiedVars, List.append_nil] at hx
          exact absurd hx List.not_mem_nil
      | cover l e md =>
          simp only [Stmt.hoistLoopPrefixInitsM, Block.modifiedVars, Stmt.modifiedVars,
            HasVarsImp.modifiedVars, Cmd.modifiedVars, List.append_nil] at hx
          exact absurd hx List.not_mem_nil
  | .block lbl bss md =>
      intro x hx
      rw [Stmt.hoistLoopPrefixInitsM_block_out, Stmt.hoistLoopPrefixInitsM_block_state] at *
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx
      have h_unique' : (Block.initVars bss).Nodup := by simpa only [Stmt.initVars_block] using h_unique
      have h_shapefree' : ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ Block.initVars bss := by
        intro str hsuf; simpa only [Stmt.initVars_block] using h_shapefree str hsuf
      have ih := Block.hoistLoopPrefixInitsM_modVars_classified hQmint bss σ h_wf h_unique' h_shapefree' x hx
      rcases ih with h_o | h_f
      · refine Or.inl ?_
        simp only [Stmt.modifiedVars, Stmt.initVars_block, List.mem_append] at h_o ⊢
        exact h_o
      · exact Or.inr h_f
  | .ite g tss ess md =>
      intro x hx
      rw [Stmt.hoistLoopPrefixInitsM_ite_out, Stmt.hoistLoopPrefixInitsM_ite_state] at *
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil, List.mem_append] at hx
      have h_uni : (Block.initVars tss ++ Block.initVars ess).Nodup := by
        simpa only [Stmt.initVars_ite] using h_unique
      have h_uni_t : (Block.initVars tss).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_e : (Block.initVars ess).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_sf_t : ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ Block.initVars tss := by
        intro str hsuf hmem
        exact h_shapefree str hsuf (by rw [Stmt.initVars_ite, List.mem_append]; exact Or.inl hmem)
      have h_sf_e : ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ Block.initVars ess := by
        intro str hsuf hmem
        exact h_shapefree str hsuf (by rw [Stmt.initVars_ite, List.mem_append]; exact Or.inr hmem)
      have h_wf_t : StringGenState.WF (Block.hoistLoopPrefixInitsM tss σ).2 :=
        (Block.hoistLoopPrefixInitsM_genStep tss σ).wf_mono h_wf
      have h_step_t : GenStep σ (Block.hoistLoopPrefixInitsM tss σ).2 :=
        Block.hoistLoopPrefixInitsM_genStep tss σ
      have h_step_e : GenStep (Block.hoistLoopPrefixInitsM tss σ).2
          (Block.hoistLoopPrefixInitsM ess (Block.hoistLoopPrefixInitsM tss σ).2).2 :=
        Block.hoistLoopPrefixInitsM_genStep ess _
      rcases hx with h | h
      · have ih := Block.hoistLoopPrefixInitsM_modVars_classified hQmint tss σ h_wf h_uni_t h_sf_t x h
        rcases ih with h_o | ⟨str, he, hin, hnot, hQ⟩
        · refine Or.inl ?_
          simp only [Stmt.modifiedVars, Stmt.initVars_ite, List.mem_append] at h_o ⊢
          rcases h_o with hm | hi
          · exact Or.inl (Or.inl hm)
          · exact Or.inr (Or.inl hi)
        · exact Or.inr ⟨str, he, h_step_e.subset hin, hnot, hQ⟩
      · have ih := Block.hoistLoopPrefixInitsM_modVars_classified hQmint ess
          (Block.hoistLoopPrefixInitsM tss σ).2 h_wf_t h_uni_e h_sf_e x h
        rcases ih with h_o | ⟨str, he, hin, hnot, hQ⟩
        · refine Or.inl ?_
          simp only [Stmt.modifiedVars, Stmt.initVars_ite, List.mem_append] at h_o ⊢
          rcases h_o with hm | hi
          · exact Or.inl (Or.inr hm)
          · exact Or.inr (Or.inr hi)
        · refine Or.inr ⟨str, he, hin, ?_, hQ⟩
          intro h_in_σ; exact hnot (h_step_t.subset h_in_σ)
  | .loop g m inv body md =>
      intro x hx
      -- abbreviations: body₁ = hoist body, σ₁ its state; renames/body₂ from the lift.
      rw [Stmt.hoistLoopPrefixInitsM_loop_out, Stmt.hoistLoopPrefixInitsM_loop_state] at *
      have h_wf₁ : StringGenState.WF (Block.hoistLoopPrefixInitsM body σ).2 :=
        (Block.hoistLoopPrefixInitsM_genStep body σ).wf_mono h_wf
      have h_step_body : GenStep σ (Block.hoistLoopPrefixInitsM body σ).2 :=
        Block.hoistLoopPrefixInitsM_genStep body σ
      have h_step_lift :
          GenStep (Block.hoistLoopPrefixInitsM body σ).2
            (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).2 :=
        Block.liftInitsInLoopBodyM_genStep _ _
      have h_unique' : (Block.initVars body).Nodup := by simpa only [Stmt.initVars_loop] using h_unique
      have h_shapefree' : ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ Block.initVars body := by
        intro str hsuf; simpa only [Stmt.initVars_loop] using h_shapefree str hsuf
      -- the output's modifiedVars are exactly `modifiedVars body₃` (havocs are `.init`).
      have hx_body₃ : x ∈ Block.modifiedVars
          (Block.applyRenames
            (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1.2.1
            (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1.2.2) := by
        rw [Block.modVars_append] at hx
        rw [(LoopInitHoistLoopDriver.Block.lift_harvest_subst
              (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1,
            Block.modifiedVars_havocStmts'] at hx
        simp only [Stmt.modifiedVars, Block.modifiedVars,
          List.append_nil, List.nil_append] at hx
        exact hx
      -- rename targets are exactly `targetsOf' E`; sources `sourcesOf' E`.
      have h_subst : (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
          (Block.hoistLoopPrefixInitsM body σ).2).1.2.1
          = substOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2) :=
        (LoopInitHoistLoopDriver.Block.lift_harvest_subst _ _).2
      -- classify via applyRenames: original residual modVars or a rename target.
      rcases Block.applyRenames_modVars_mem _ _ x hx_body₃ with h_res | h_tgt
      · -- residual modVars: original body₁ modVars or a rename source (= lifted init name).
        rcases Block.liftResidual_modVars_mem _ _ x h_res with h_body₁ | h_src
        · -- x ∈ modifiedVars body₁: classify by IH on `body`.
          have ih := Block.hoistLoopPrefixInitsM_modVars_classified hQmint body σ h_wf h_unique' h_shapefree' x h_body₁
          rcases ih with h_o | ⟨str, he, hin, hnot, hQ⟩
          · refine Or.inl ?_
            simp only [Stmt.modifiedVars, Stmt.initVars_loop, List.mem_append] at h_o ⊢
            exact h_o
          · exact Or.inr ⟨str, he, h_step_lift.subset hin, hnot, hQ⟩
        · -- x ∈ renames.map .1 = sourcesOf' E ⊆ initVars body₁: classify by initVars classification.
          rw [h_subst, substOf'_map_fst] at h_src
          have h_x_in₁ : x ∈ Block.initVars (Block.hoistLoopPrefixInitsM body σ).1 :=
            Block.sourcesOf_entriesOf_subset _ _ x h_src
          have ih := (Block.hoistLoopPrefixInitsM_initVars_classified hQmint body σ h_wf
            h_unique' h_shapefree').1 x h_x_in₁
          rcases ih with h_o | ⟨str, he, hin, hnot, hQ⟩
          · refine Or.inl ?_
            simp only [Stmt.modifiedVars, Stmt.initVars_loop, List.mem_append]
            exact Or.inr h_o
          · exact Or.inr ⟨str, he, h_step_lift.subset hin, hnot, hQ⟩
      · -- x is a rename TARGET = targetsOf' E: fresh between σ₁ and σ₂, hence fresh from σ.
        rw [h_subst, ← LoopInitHoistLoopDriver.targetsOf'_eq_substOf'_snd] at h_tgt
        obtain ⟨e, he_mem, he_eq⟩ := List.mem_map.mp h_tgt
        obtain ⟨t, ht_eq, ht_in, ht_not⟩ :=
          (Block.entriesOf_targetGen (Block.hoistLoopPrefixInitsM body σ).1
            (Block.hoistLoopPrefixInitsM body σ).2 h_wf₁).1 e he_mem
        obtain ⟨t', ht'_eq, ht'_Q⟩ :=
          Block.entriesOf_target_suffix hQmint (Block.hoistLoopPrefixInitsM body σ).1
            (Block.hoistLoopPrefixInitsM body σ).2 e he_mem
        have h_t_eq : t = t' :=
          LawfulHasIdent.ident_inj (ht_eq.symm.trans ht'_eq)
        refine Or.inr ⟨t, ?_, ht_in, ?_, h_t_eq ▸ ht'_Q⟩
        · rw [← he_eq, ht_eq]
        · intro h_in_σ; exact ht_not (h_step_body.subset h_in_σ)
  | .exit lbl md =>
      intro x hx
      simp only [Stmt.hoistLoopPrefixInitsM, Block.modifiedVars, Stmt.modifiedVars,
        List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  | .funcDecl d md =>
      intro x hx
      simp only [Stmt.hoistLoopPrefixInitsM, Block.modifiedVars, Stmt.modifiedVars,
        List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  | .typeDecl t md =>
      intro x hx
      simp only [Stmt.hoistLoopPrefixInitsM, Block.modifiedVars, Stmt.modifiedVars,
        List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  termination_by sizeOf s

/-- Mutual `Block` step of the `modifiedVars` classification. -/
theorem Block.hoistLoopPrefixInitsM_modVars_classified [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] [LawfulHasIdent P] [HasVarsPure P P.Expr] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIntOrder P] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) (h_wf : StringGenState.WF σ)
    (h_unique : (Block.initVars ss).Nodup)
    (h_shapefree : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ Block.initVars ss) :
    ∀ x ∈ Block.modifiedVars (Block.hoistLoopPrefixInitsM ss σ).1,
        HoistInitClass Q (Block.modifiedVars ss ++ Block.initVars ss) σ
          (Block.hoistLoopPrefixInitsM ss σ).2 x := by
  match ss with
  | [] =>
      intro x hx
      simp only [Block.hoistLoopPrefixInitsM, Block.modifiedVars] at hx
      exact absurd hx List.not_mem_nil
  | s :: rest =>
      intro x hx
      rw [Block.hoistLoopPrefixInitsM_cons_out, Block.hoistLoopPrefixInitsM_cons_state] at *
      simp only [Block.modVars_append, List.mem_append] at hx
      have h_uni : (Stmt.initVars s ++ Block.initVars rest).Nodup := by
        simpa only [Block.initVars_cons] using h_unique
      have h_uni_s : (Stmt.initVars s).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_r : (Block.initVars rest).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_sf_s : ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ Stmt.initVars s := by
        intro str hsuf hmem
        exact h_shapefree str hsuf (by rw [Block.initVars_cons, List.mem_append]; exact Or.inl hmem)
      have h_sf_r : ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ Block.initVars rest := by
        intro str hsuf hmem
        exact h_shapefree str hsuf (by rw [Block.initVars_cons, List.mem_append]; exact Or.inr hmem)
      have h_wf_s : StringGenState.WF (Stmt.hoistLoopPrefixInitsM s σ).2 :=
        (Stmt.hoistLoopPrefixInitsM_genStep s σ).wf_mono h_wf
      have h_step_s : GenStep σ (Stmt.hoistLoopPrefixInitsM s σ).2 :=
        Stmt.hoistLoopPrefixInitsM_genStep s σ
      have h_step_r : GenStep (Stmt.hoistLoopPrefixInitsM s σ).2
          (Block.hoistLoopPrefixInitsM rest (Stmt.hoistLoopPrefixInitsM s σ).2).2 :=
        Block.hoistLoopPrefixInitsM_genStep rest _
      rcases hx with h | h
      · have ih := Stmt.hoistLoopPrefixInitsM_modVars_classified hQmint s σ h_wf h_uni_s h_sf_s x h
        rcases ih with h_o | ⟨str, he, hin, hnot, hQ⟩
        · refine Or.inl ?_
          simp only [Block.modVars_cons, Block.initVars_cons, List.mem_append] at h_o ⊢
          rcases h_o with hm | hi
          · exact Or.inl (Or.inl hm)
          · exact Or.inr (Or.inl hi)
        · exact Or.inr ⟨str, he, h_step_r.subset hin, hnot, hQ⟩
      · have ih := Block.hoistLoopPrefixInitsM_modVars_classified hQmint rest
          (Stmt.hoistLoopPrefixInitsM s σ).2 h_wf_s h_uni_r h_sf_r x h
        rcases ih with h_o | ⟨str, he, hin, hnot, hQ⟩
        · refine Or.inl ?_
          simp only [Block.modVars_cons, Block.initVars_cons, List.mem_append] at h_o ⊢
          rcases h_o with hm | hi
          · exact Or.inl (Or.inr hm)
          · exact Or.inr (Or.inr hi)
        · refine Or.inr ⟨str, he, hin, ?_, hQ⟩
          intro h_in_σ; exact hnot (h_step_s.subset h_in_σ)
  termination_by sizeOf ss
end

/-! ## Producer precondition `h_disjoint`: harvest sources ∩ targets = ∅.

`Block.bodyTransport_of_lift` needs the renaming's keys (sources) disjoint from
its values (targets): `∀ a ∈ sourcesOf' E, a ∉ targetsOf' E` for
`E = entriesOf body₁ σ₁`.  Sources are top-level inits of `body₁` (a `Sublist`
of `initVars body₁`); each such init is CLASSIFIED (by the post-order pass) as
either an ORIGINAL source init (a member of the source `initVars body`, hence
suffix-free) or a FRESH hoist name whose generator string lies in the HOIST
pass's output state `σ₁`.  Each target is a generator string of the SUBSEQUENT
lift pass, suffix-shaped and ABSENT from `σ₁`.  Both classes are therefore
disjoint from the targets: a suffix-free original can't equal a suffix-shaped
target, and a fresh source's string is in `σ₁` while a target's is not. -/
theorem Block.sourcesOf'_disjoint_targetsOf'_self [HasIdent P] [LawfulHasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (body : List (Stmt P (Cmd P))) (σ : StringGenState) (h_wf : StringGenState.WF σ)
    (h_unique : (Block.initVars body).Nodup)
    (h_shapefree : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ Block.initVars body) :
    ∀ a ∈ sourcesOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2),
      a ∉ targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2) := by
  classical
  intro a ha_src ha_tgt
  -- abbreviations
  have h_wf₁ : StringGenState.WF (Block.hoistLoopPrefixInitsM body σ).2 :=
    (Block.hoistLoopPrefixInitsM_genStep body σ).wf_mono h_wf
  -- (1) `a ∈ initVars body₁` (sources ⊆ inits).
  have h_a_in₁ : a ∈ Block.initVars (Block.hoistLoopPrefixInitsM body σ).1 :=
    Block.sourcesOf_entriesOf_subset _ _ a ha_src
  -- (2) classify `a` as original or fresh-hoist.
  have h_class :=
    (Block.hoistLoopPrefixInitsM_initVars_classified hQmint body σ h_wf h_unique h_shapefree).1
      a h_a_in₁
  -- (3) `a` is a target: `a = e.2.1` with `TargetGen σ₁ σ₂ e`, i.e. `a = ident
  -- str_b`, `str_b ∉ σ₁`, and (separately) `str_b` carries the mint kind `Q`.
  obtain ⟨e, he_mem, he_eq⟩ := List.mem_map.mp ha_tgt
  obtain ⟨str_b, h_b_eq, _, h_str_b_notσ₁⟩ :=
    (Block.entriesOf_targetGen _ _ h_wf₁).1 e he_mem
  have h_a_eq_b : a = HasIdent.ident str_b := he_eq ▸ h_b_eq
  have h_str_b_Q : Q str_b := by
    obtain ⟨str_b', h_eq', h_Q'⟩ :=
      Block.mem_targetsOf'_entriesOf_hasUnderscoreDigitSuffix hQmint _ _ ha_tgt
    have : (HasIdent.ident str_b' : P.Ident) = HasIdent.ident str_b := by
      rw [← h_eq', h_a_eq_b]
    rw [← LawfulHasIdent.ident_inj this]; exact h_Q'
  rcases h_class with h_orig | ⟨str_a, h_a_eq_a, h_str_a_inσ₁, _⟩
  · -- ORIGINAL: `a ∈ initVars body`, but `a = HasIdent.ident str_b` carries kind
    -- `Q` — contradicts `h_shapefree`.
    exact h_shapefree str_b h_str_b_Q (h_a_eq_b ▸ h_orig)
  · -- FRESH hoist: `a = HasIdent.ident str_a`, `str_a ∈ σ₁`; but
    -- `a = HasIdent.ident str_b`, `str_b ∉ σ₁`.  `str_a = str_b` ⇒ contradiction.
    have h_id : (HasIdent.ident str_a : P.Ident) = HasIdent.ident str_b := by
      rw [← h_a_eq_a, ← h_a_eq_b]
    have h_str_eq : str_a = str_b := LawfulHasIdent.ident_inj h_id
    exact h_str_b_notσ₁ (h_str_eq ▸ h_str_a_inσ₁)

/-! ## Producer precondition `h_mod_disjoint_B1`: harvest targets ∩ modifiedVars = ∅.

`Block.stepB_self_of_lift` needs `modifiedVars body₁ ∩ targetsOf' E = ∅` for
`body₁ = (hoistLoopPrefixInitsM body σ).1` and `E = entriesOf body₁ σ₁`.  Each
`x ∈ modifiedVars body₁` is CLASSIFIED (by the post-order pass) as either an
ORIGINAL source modified-or-init var (a member of `modifiedVars body ++ initVars
body`, hence suffix-free for a well-formed source) or a FRESH hoist name whose
generator string lies in the HOIST pass's output state `σ₁` (a name minted by the
inner hoist of a nested-loop init).  Each target is a
generator string of the SUBSEQUENT lift pass, suffix-shaped and ABSENT from
`σ₁`.  Both classes are therefore disjoint from the targets: a suffix-free
original can't equal a suffix-shaped target, and a fresh source's string is in
`σ₁` while a target's is not. -/
theorem Block.modifiedVars_disjoint_targetsOf'_self [HasIdent P] [LawfulHasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] [HasVarsPure P P.Expr] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIntOrder P] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (body : List (Stmt P (Cmd P))) (σ : StringGenState) (h_wf : StringGenState.WF σ)
    (h_unique : (Block.initVars body).Nodup)
    (h_iv_shapefree : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ Block.initVars body)
    (h_mod_shapefree : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ Block.modifiedVars body) :
    ∀ x ∈ Block.modifiedVars (Block.hoistLoopPrefixInitsM body σ).1,
      x ∉ targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2) := by
  classical
  intro x hx_mod hx_tgt
  -- abbreviation: σ₁ = output state of the hoist pass.
  have h_wf₁ : StringGenState.WF (Block.hoistLoopPrefixInitsM body σ).2 :=
    (Block.hoistLoopPrefixInitsM_genStep body σ).wf_mono h_wf
  -- (1) classify `x` as ORIGINAL (∈ modifiedVars body ++ initVars body) or FRESH (∈ σ₁ \ σ).
  have h_class :=
    Block.hoistLoopPrefixInitsM_modVars_classified hQmint body σ h_wf h_unique h_iv_shapefree x hx_mod
  -- (2) `x` is a target: `x = ident str_b` with `str_b ∉ σ₁`, carrying kind `Q`.
  obtain ⟨e, he_mem, he_eq⟩ := List.mem_map.mp hx_tgt
  obtain ⟨str_b, h_b_eq, _, h_str_b_notσ₁⟩ :=
    (Block.entriesOf_targetGen _ _ h_wf₁).1 e he_mem
  have h_x_eq_b : x = HasIdent.ident str_b := he_eq ▸ h_b_eq
  have h_str_b_Q : Q str_b := by
    obtain ⟨str_b', h_eq', h_Q'⟩ :=
      Block.mem_targetsOf'_entriesOf_hasUnderscoreDigitSuffix hQmint _ _ hx_tgt
    have : (HasIdent.ident str_b' : P.Ident) = HasIdent.ident str_b := by
      rw [← h_eq', h_x_eq_b]
    rw [← LawfulHasIdent.ident_inj this]; exact h_Q'
  rcases h_class with h_orig | ⟨str_a, h_x_eq_a, h_str_a_inσ₁, _⟩
  · -- ORIGINAL: `x ∈ modifiedVars body ++ initVars body`, but `x = ident str_b`
    -- carries kind `Q` — contradicts `h_mod_shapefree`/`h_iv_shapefree`.
    rcases List.mem_append.mp h_orig with h_m | h_i
    · exact h_mod_shapefree str_b h_str_b_Q (h_x_eq_b ▸ h_m)
    · exact h_iv_shapefree str_b h_str_b_Q (h_x_eq_b ▸ h_i)
  · -- FRESH hoist: `x = ident str_a`, `str_a ∈ σ₁`; but `x = ident str_b`,
    -- `str_b ∉ σ₁`.  `str_a = str_b` ⇒ contradiction.
    have h_id : (HasIdent.ident str_a : P.Ident) = HasIdent.ident str_b := by
      rw [← h_x_eq_a, ← h_x_eq_b]
    have h_str_eq : str_a = str_b := LawfulHasIdent.ident_inj h_id
    exact h_str_b_notσ₁ (h_str_eq ▸ h_str_a_inσ₁)

/-! ## §E `.loop` arm final reconciliation.

`union_entry_hinv` builds the loop-entry union `HoistInv` (ambient `A B subst`
relating `ρ_src ρ_hoist`, prelude relating `ρ_hoist ρ_pre` on the fresh
carriers, composed at the union).  `loop_arm_close` then runs the full guarded
assembly — prelude bridge → union entry → `compose_union(bridge_in_guarded)` →
two-guard loop driver → stitch (havoc prelude ++ loop run) → `stepJ_restrict`
back to the ambient carriers — producing the §E sum-typed terminal conclusion
for the residual `havocStmts' E ++ [.loop (.det g) none [] body₃ md]`. -/

open LoopInitHoistLoopDriver (BodySim BodySimUSF bodySim_is_driver_slot
  bodySimUSF_is_driver_slot compose_union compose_union_sf
  bridge_in_guarded bridge_in_guarded_undef_sf stepJ_restrict
  loopDet_lift_2g_recovers_single
  loopDet_lift_sf_undef_recovers_single loopDet_no_exit
  prelude_bridge_list_md_frame)

/-- Loop-entry union `HoistInv` builder (guarded frame). -/
theorem union_entry_hinv
    {A B As Bs : List P.Ident} {subst ss : List (P.Ident × P.Ident)}
    {ρ_src ρ_hoist ρ_pre : Env P}
    (h_hinv : HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store)
    (_h_pre  : HoistInv (P := P) A Bs ss ρ_hoist.store ρ_pre.store)
    (h_subst_wf : ∀ a b, (a, b) ∈ subst → a ∈ A ∧ b ∈ B)
    (h_ss_wf : ∀ a b, (a, b) ∈ ss → a ∈ As ∧ b ∈ Bs)
    (_h_As_notA : ∀ x ∈ As, x ∉ A) (_h_As_notB : ∀ x ∈ As, x ∉ B)
    (h_B_notBs : ∀ b ∈ B, b ∉ Bs)
    (h_src_As_undef : ∀ a ∈ As, ρ_src.store a = none)
    (h_pre_frame_off_Bs : ∀ x, x ∉ Bs → ρ_pre.store x = ρ_hoist.store x) :
    HoistInv (P := P) (A ++ As) (B ++ Bs) (subst ++ ss) ρ_src.store ρ_pre.store := by
  refine ⟨?_, ?_⟩
  · intro x hxA hxB h_x_ne
    have hxAo : x ∉ A := fun h => hxA (List.mem_append.mpr (Or.inl h))
    have hxBo : x ∉ B := fun h => hxB (List.mem_append.mpr (Or.inl h))
    have hxBs : x ∉ Bs := fun h => hxB (List.mem_append.mpr (Or.inr h))
    rw [h_hinv.1 x hxAo hxBo h_x_ne, (h_pre_frame_off_Bs x hxBs).symm]
  · intro a b h_pair h_ne
    rcases List.mem_append.mp h_pair with h_so | h_ss
    · obtain ⟨ha_A, hb_B⟩ := h_subst_wf a b h_so
      obtain ⟨h_b_ne, h_eq⟩ := h_hinv.2 a b h_so h_ne
      have h_move : ρ_pre.store b = ρ_hoist.store b := h_pre_frame_off_Bs b (h_B_notBs b hb_B)
      exact ⟨by rw [h_move]; exact h_b_ne, by rw [h_move]; exact h_eq⟩
    · obtain ⟨ha_As, hb_Bs⟩ := h_ss_wf a b h_ss
      exact absurd (h_src_As_undef a ha_As) h_ne

/-- **Step B, self-assembled at the harvest carriers.**  On the post-order body
`body₁ = (hoistLoopPrefixInitsM body σ).1`, the lift's renaming simulation holds
at `body₁`'s OWN harvest carriers `sourcesOf' E`/`targetsOf' E`/`substOf' E`
(`E = entriesOf body₁ σ₁`), producing the rewritten loop body `body₃ =
applyRenames (substOf' E) (lift residual)`.  Every producer precondition of
`Block.stepB_bodySim_of_lift` is discharged from the source body's §E arm shape
facts: the self-`EntriesIn` is `List.mem_map`, the target freshness/nodup/shape
facts come from the harvest-target generator lemmas, and the source∩target
disjointness from `sourcesOf'_disjoint_targetsOf'_self`. -/
theorem Block.stepB_self_of_lift [HasIdent P] [LawfulHasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIntOrder P] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    {extendEval : ExtendEval P}
    (body : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h_wf_σ : StringGenState.WF σ)
    (h_nd : Block.containsNondetLoop body = false)
    (h_fd : Block.containsFuncDecl body = false)
    (h_inv : Block.loopHasNoInvariants body = true)
    (h_measure : Block.loopMeasureNone body = true)
    (h_noexit : Block.noExit body = true)
    (h_unique : Block.uniqueInits body)
    (h_sf : Block.exprsShapeFree (P := P) Q body)
    (h_src_shapefree :
      ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ Block.initVars body)
    (h_mod_disjoint_B : ∀ x ∈ Block.modifiedVars (Block.hoistLoopPrefixInitsM body σ).1,
        x ∉ targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1
          (Block.hoistLoopPrefixInitsM body σ).2))
    (h_wfvar   : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval)
    (h_wfcongr : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval)
    (h_wfsubst : ∀ ρ : Env P, WellFormedSemanticEvalSubstFvar ρ.eval)
    (h_wfdef   : ∀ ρ : Env P, WellFormedSemanticEvalDef ρ.eval) :
    LoopInitHoistLoopDriver.BodySim (extendEval := extendEval)
      (sourcesOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
      (targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
      (substOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
      (Block.hoistLoopPrefixInitsM body σ).1
      (Block.applyRenames
        (substOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
        (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2).1.2.2) := by
  have h_wf₁ : StringGenState.WF (Block.hoistLoopPrefixInitsM body σ).2 :=
    (Block.hoistLoopPrefixInitsM_genStep body σ).wf_mono h_wf_σ
  have h_nd_body1 : (Block.initVars (Block.hoistLoopPrefixInitsM body σ).1).Nodup :=
    Block.hoistLoopPrefixInitsM_initVars_nodup hQmint body σ h_wf_σ h_unique h_src_shapefree
  have h_entries : LoopInitHoistStepCProducer.EntriesIn
      (sourcesOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
      (targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
      (substOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
      (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2 := by
    intro e he
    exact ⟨List.mem_map.mpr ⟨e, he, rfl⟩,
           List.mem_map.mpr ⟨e, he, rfl⟩,
           List.mem_map.mpr ⟨e, he, rfl⟩⟩
  refine LoopInitHoistStepCProducer.Block.stepB_bodySim_of_lift
    (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2
    (sourcesOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
    (targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
    (substOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
    ?_ h_entries ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h_wfvar h_wfcongr h_wfsubst h_wfdef
  · exact Block.hoistLoopPrefixInitsM_allLoopBodiesInitFree body σ
  · exact Block.hoistLoopPrefixInitsM_namesFreshInExprs_targets_of_exprsShapeFree
      hQmint body σ h_wf₁ h_sf
  · exact h_mod_disjoint_B
  · intro a b hab
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hab
    cases heq
    exact ⟨List.mem_map.mpr ⟨e, he, rfl⟩, List.mem_map.mpr ⟨e, he, rfl⟩⟩
  · exact Block.entriesOf_substOf_src_nodup_of_initVars (Block.hoistLoopPrefixInitsM body σ).1
      (Block.hoistLoopPrefixInitsM body σ).2 h_nd_body1
  · rw [show (substOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2)).map Prod.snd
        = targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2) from
      (LoopInitHoistLoopDriver.targetsOf'_eq_substOf'_snd _).symm]
    exact (Block.entriesOf_targetGen (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2 h_wf₁).2
  · rw [substOf'_map_fst, show (substOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2)).map Prod.snd
        = targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2) from
      (LoopInitHoistLoopDriver.targetsOf'_eq_substOf'_snd _).symm]
    exact Block.sourcesOf'_disjoint_targetsOf'_self hQmint body σ h_wf_σ h_unique h_src_shapefree
  · exact Block.transportShape_hoistLoopPrefixInitsM body σ h_nd h_fd h_inv h_measure h_noexit
  · rw [substOf'_map_fst]; exact fun a ha => ha
  · rw [substOf'_map_fst]; exact fun a ha => ha
  · rw [show (substOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2)).map Prod.snd
        = targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2) from
      (LoopInitHoistLoopDriver.targetsOf'_eq_substOf'_snd _).symm]
    exact fun b hb => hb

/-- **Step B residual is `noFuncDecl`.**  The rewritten loop body
`body₃ = applyRenames (substOf' E) (lift residual)` (`E = entriesOf body₁ σ₁`,
`body₁ = (hoistLoopPrefixInitsM body σ).1`) is `noFuncDecl` — the body-transport
relation that `body₁` ↝ `body₃` inhabits (`bodyTransport_of_lift`, at the same
harvest carriers `stepB_self_of_lift` uses) has a `noFuncDecl` hoist side
(`BodyTransport.noFuncDecl_h`).  The producer preconditions are discharged from
the source body's §E arm-shape facts exactly as in `stepB_self_of_lift`. -/
theorem Block.stepB_noFuncDecl_h_of_lift [HasIdent P] [LawfulHasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident] [HasVarsPure P P.Expr] [LawfulHasSubstFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIntOrder P] {Q : String → Prop}
    (hQmint : ∀ sg, Q (StringGenState.gen hoistFreshPrefix sg).1)
    (body : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h_wf_σ : StringGenState.WF σ)
    (h_nd : Block.containsNondetLoop body = false)
    (h_fd : Block.containsFuncDecl body = false)
    (h_inv : Block.loopHasNoInvariants body = true)
    (h_measure : Block.loopMeasureNone body = true)
    (h_noexit : Block.noExit body = true)
    (h_unique : Block.uniqueInits body)
    (h_sf : Block.exprsShapeFree (P := P) Q body)
    (h_src_shapefree :
      ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ Block.initVars body)
    (h_mod_disjoint_B : ∀ x ∈ Block.modifiedVars (Block.hoistLoopPrefixInitsM body σ).1,
        x ∉ targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1
          (Block.hoistLoopPrefixInitsM body σ).2)) :
    Block.noFuncDecl
      (Block.applyRenames
        (substOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
        (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2).1.2.2)
      = true := by
  have h_wf₁ : StringGenState.WF (Block.hoistLoopPrefixInitsM body σ).2 :=
    (Block.hoistLoopPrefixInitsM_genStep body σ).wf_mono h_wf_σ
  have h_nd_body1 : (Block.initVars (Block.hoistLoopPrefixInitsM body σ).1).Nodup :=
    Block.hoistLoopPrefixInitsM_initVars_nodup hQmint body σ h_wf_σ h_unique h_src_shapefree
  have h_entries : LoopInitHoistStepCProducer.EntriesIn
      (sourcesOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
      (targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
      (substOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
      (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2 := by
    intro e he
    exact ⟨List.mem_map.mpr ⟨e, he, rfl⟩,
           List.mem_map.mpr ⟨e, he, rfl⟩,
           List.mem_map.mpr ⟨e, he, rfl⟩⟩
  refine LoopInitHoistBodyTransport.BodyTransport.noFuncDecl_h
    (LoopInitHoistStepCProducer.Block.bodyTransport_of_lift
      (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2
      (sourcesOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
      (targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
      (substOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2))
      (Block.hoistLoopPrefixInitsM_allLoopBodiesInitFree body σ)
      h_entries
      (Block.hoistLoopPrefixInitsM_namesFreshInExprs_targets_of_exprsShapeFree
        hQmint body σ h_wf₁ h_sf)
      h_mod_disjoint_B
      ?_ ?_ ?_ ?_ ?_ ?_)
  · intro a b hab
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hab
    cases heq
    exact ⟨List.mem_map.mpr ⟨e, he, rfl⟩, List.mem_map.mpr ⟨e, he, rfl⟩⟩
  · rw [substOf'_map_fst]; exact fun a ha => ha
  · exact Block.entriesOf_substOf_src_nodup_of_initVars (Block.hoistLoopPrefixInitsM body σ).1
      (Block.hoistLoopPrefixInitsM body σ).2 h_nd_body1
  · rw [show (substOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2)).map Prod.snd
        = targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2) from
      (LoopInitHoistLoopDriver.targetsOf'_eq_substOf'_snd _).symm]
    exact (Block.entriesOf_targetGen (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2 h_wf₁).2
  · rw [substOf'_map_fst, show (substOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2)).map Prod.snd
        = targetsOf' (Block.entriesOf (Block.hoistLoopPrefixInitsM body σ).1 (Block.hoistLoopPrefixInitsM body σ).2) from
      (LoopInitHoistLoopDriver.targetsOf'_eq_substOf'_snd _).symm]
    exact Block.sourcesOf'_disjoint_targetsOf'_self hQmint body σ h_wf_σ h_unique h_src_shapefree
  · exact Block.transportShape_hoistLoopPrefixInitsM body σ h_nd h_fd h_inv h_measure h_noexit

/-- The full §E `.loop` arm reconciliation: given Step A (`BodySim A B subst body
body₁`) and Step B (`BodySim (sources)(targets)(substOf'E) body₁ body₃`) plus the
arm's disjointness / freshness / run facts, produce the §E sum-typed terminal
conclusion for the residual `havocStmts' E ++ [.loop (.det g) none [] body₃ md]`.
Guard `g` is UNCHANGED (the renames live inside `body₃`). -/
theorem loop_arm_close [HasIdent P] [HasFvar P] [DecidableEq P.Ident] [HasVarsPure P P.Expr] [HasBool P] [HasNot P]
    {Q : String → Prop}
    {extendEval : ExtendEval P}
    {g : P.Expr}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {Vs : List P.Ident} {σ_sf : StringGenState}
    {body body₁ body₃ : List (Stmt P (Cmd P))} {md : MetaData P}
    {entries : List (Entry P)}
    {ρ_src ρ_hoist : Env P} {cfg_src : Config P (Cmd P)}
    (stepA : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store →
       ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
       (∀ y ∈ B, ρ_h.store y ≠ none) →
       (∀ y ∈ Vs, ρ_s.store y = none) → (∀ y ∈ Vs, ρ_h.store y = none) →
       (∀ str : String, Q str →
          str ∉ StringGenState.stringGens σ_sf → ρ_s.store (HasIdent.ident (P := P) str) = none) →
       (∀ str : String, Q str →
          str ∉ StringGenState.stringGens σ_sf → ρ_h.store (HasIdent.ident (P := P) str) = none) →
       ∀ (ρ_s' : Env P),
         StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ_s) (.terminal ρ_s') →
         ∃ ρ_h' : Env P,
           StepStmtStar P (EvalCmd P) extendEval (.stmts body₁ ρ_h) (.terminal ρ_h') ∧
           HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
           ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none))
    (stepB : BodySim (extendEval := extendEval)
       (sourcesOf' entries) (targetsOf' entries) (substOf' entries) body₁ body₃)
    (h_entry_Vs : ∀ y ∈ Vs, ρ_src.store y = none)
    (h_entry_Vh : ∀ y ∈ Vs, ρ_hoist.store y = none)
    (h_arm_src_sf : ∀ str : String, Q str →
       str ∉ StringGenState.stringGens σ_sf → ρ_src.store (HasIdent.ident (P := P) str) = none)
    (h_sf_notA : ∀ str : String, Q str →
       str ∉ StringGenState.stringGens σ_sf → HasIdent.ident (P := P) str ∉ A)
    (h_sf_notB : ∀ str : String, Q str →
       str ∉ StringGenState.stringGens σ_sf → HasIdent.ident (P := P) str ∉ B)
    (h_Vs_notA : ∀ y ∈ Vs, y ∉ A) (h_Vs_notB : ∀ y ∈ Vs, y ∉ B)
    (h_Vs_notBs : ∀ y ∈ Vs, y ∉ targetsOf' entries)
    (h_subst_wf : ∀ a b, (a, b) ∈ subst → a ∈ A ∧ b ∈ B)
    (h_ss_wf : ∀ a b, (a, b) ∈ substOf' entries →
       a ∈ sourcesOf' entries ∧ b ∈ targetsOf' entries)
    (h_As_notA : ∀ x ∈ sourcesOf' entries, x ∉ A)
    (h_As_notB : ∀ x ∈ sourcesOf' entries, x ∉ B)
    (h_B_notAs : ∀ b ∈ B, b ∉ sourcesOf' entries)
    (h_B_notBs : ∀ b ∈ B, b ∉ targetsOf' entries)
    (_h_Bs_notB : ∀ b ∈ targetsOf' entries, b ∉ B)
    (h_g_A_fresh : ∀ x ∈ A, x ∉ HasVarsPure.getVars g)
    (h_g_B_fresh : ∀ x ∈ B, x ∉ HasVarsPure.getVars g)
    (h_g_As_fresh : ∀ x ∈ sourcesOf' entries, x ∉ HasVarsPure.getVars g)
    (h_g_Bs_fresh : ∀ x ∈ targetsOf' entries, x ∉ HasVarsPure.getVars g)
    (h_src_As_undef : ∀ a ∈ sourcesOf' entries, ρ_src.store a = none)
    (h_src_body_no_exit : ∀ (ρ : Env P) (lbl : String) (ρe : Env P),
       ¬ StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ) (.exiting lbl ρe))
    (h_nofd_src : Block.noFuncDecl body = true)
    (h_nofd_h : Block.noFuncDecl body₃ = true)
    (h_tgt_nodup : (targetsOf' entries).Nodup)
    (h_src_undef_h : ∀ e ∈ entries, ρ_hoist.store e.1 = none)
    (h_tgt_undef_h : ∀ e ∈ entries, ρ_hoist.store e.2.1 = none)
    (h_post_src_none : ∀ (ρ_post : Env P) (x : P.Ident),
       StepStmtStar P (EvalCmd P) extendEval
         (.stmt (.loop (.det g) none [] body md) ρ_src) (.terminal ρ_post) →
       x ∈ sourcesOf' entries → ρ_post.store x = none)
    (h_post_tgt_none : ∀ (ρ_post : Env P) (x : P.Ident),
       StepStmtStar P (EvalCmd P) extendEval
         (.stmt (.loop (.det g) none [] body md) ρ_src) (.terminal ρ_post) →
       x ∈ targetsOf' entries → ρ_post.store x = none)
    (h_wfvar : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval)
    (h_wfcongr : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval)
    (h_wfdef   : ∀ ρ : Env P, WellFormedSemanticEvalDef ρ.eval)
    (h_hinv : HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store)
    (h_eval : ρ_src.eval = ρ_hoist.eval) (h_hf : ρ_src.hasFailure = ρ_hoist.hasFailure)
    (h_bound : ∀ y ∈ B, ρ_hoist.store y ≠ none)
    (h_run_src : StepStmtStar P (EvalCmd P) extendEval
        (.stmt (.loop (.det g) none [] body md) ρ_src) cfg_src)
    (h_cfg_src : (∃ ρ_src' : Env P, cfg_src = .terminal ρ_src') ∨
                 (∃ lbl ρ_src', cfg_src = .exiting lbl ρ_src')) :
    ∃ ρ_h', ∃ cfg_hoist : Config P (Cmd P),
      StepStmtStar P (EvalCmd P) extendEval
        (.stmts (havocStmts' entries ++ [.loop (.det g) none [] body₃ md]) ρ_hoist)
          cfg_hoist
      ∧ ((∃ ρ_src' : Env P,
            cfg_src = .terminal ρ_src' ∧ cfg_hoist = .terminal ρ_h' ∧
            HoistInv (P := P) A B subst ρ_src'.store ρ_h'.store ∧
            ρ_src'.hasFailure = ρ_h'.hasFailure ∧
            (∀ y ∈ B, ρ_h'.store y ≠ none)) ∨
         (∃ lbl ρ_src',
            cfg_src = .exiting lbl ρ_src' ∧ cfg_hoist = .exiting lbl ρ_h' ∧
            HoistInv (P := P) A B subst ρ_src'.store ρ_h'.store ∧
            ρ_src'.hasFailure = ρ_h'.hasFailure ∧
            (∀ y ∈ B, ρ_h'.store y ≠ none))) := by
  classical
  obtain ⟨ρ_post, h_cfg_terminal⟩ : ∃ ρ_post, cfg_src = .terminal ρ_post := by
    rcases h_cfg_src with ⟨ρ', h⟩ | ⟨lbl, ρ', h⟩
    · exact ⟨ρ', h⟩
    · subst h
      exact (loopDet_no_exit (g := g) (md := md)
        (fun ρ hif lbl ρe => h_src_body_no_exit _ lbl ρe) h_run_src).elim
  subst h_cfg_terminal
  have h_run : StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.loop (.det g) none [] body md) ρ_src) (.terminal ρ_post) := h_run_src
  obtain ⟨ρ_pre, h_prelude_run, h_pre_hinv, h_pre_eval, h_pre_hf, h_pre_bnd,
          h_pre_frame⟩ :=
    prelude_bridge_list_md_frame (A := A) entries ρ_hoist ρ_hoist rfl rfl rfl
      h_src_undef_h h_tgt_undef_h h_tgt_nodup h_wfvar
  have composed : BodySimUSF (extendEval := extendEval) Q Vs Vs σ_sf
      (A ++ sourcesOf' entries) (B ++ targetsOf' entries) (subst ++ substOf' entries)
      body body₃ :=
    compose_union_sf stepA stepB h_subst_wf h_ss_wf h_As_notA h_As_notB h_B_notAs h_B_notBs
      (fun _ hy => hy)
      (fun ρ_s ρ_h h he hf hb hVh hsf =>
        bridge_in_guarded_undef_sf h_subst_wf h_ss_wf h_As_notA h_As_notB h_Vs_notA h_Vs_notB
          h_sf_notA h_sf_notB ρ_s ρ_h h he hf hb hVh hsf)
  have h_union_entry : HoistInv (P := P)
      (A ++ sourcesOf' entries) (B ++ targetsOf' entries) (subst ++ substOf' entries)
      ρ_src.store ρ_pre.store :=
    union_entry_hinv h_hinv h_pre_hinv h_subst_wf h_ss_wf h_As_notA h_As_notB
      h_B_notBs h_src_As_undef h_pre_frame
  have h_union_eval : ρ_src.eval = ρ_pre.eval := h_eval.trans h_pre_eval
  have h_union_hf : ρ_src.hasFailure = ρ_pre.hasFailure := h_hf.trans h_pre_hf
  have h_union_bnd : ∀ y ∈ B ++ targetsOf' entries, ρ_pre.store y ≠ none := by
    intro y hy
    rcases List.mem_append.mp hy with hyB | hyBs
    · have : ρ_pre.store y = ρ_hoist.store y := h_pre_frame y (h_B_notBs y hyB)
      rw [this]; exact h_bound y hyB
    · exact h_pre_bnd y hyBs
  have h_guard_agree : ∀ (ρ_s ρ_h : Env P),
      HoistInv (P := P) (A ++ sourcesOf' entries) (B ++ targetsOf' entries)
        (subst ++ substOf' entries) ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
      (∀ x ∈ HasVarsPure.getVars g, ρ_s.store x ≠ none) →
      ρ_s.eval ρ_s.store g = ρ_h.eval ρ_h.store g := by
    intro ρ_s ρ_h hi he h_read_def
    have h_store_agree : ∀ x ∈ HasVarsPure.getVars g, ρ_s.store x = ρ_h.store x := by
      intro x hx
      refine hi.1 x ?_ ?_ (h_read_def x hx)
      · intro h; rcases List.mem_append.mp h with h | h
        · exact h_g_A_fresh x h hx
        · exact h_g_As_fresh x h hx
      · intro h; rcases List.mem_append.mp h with h | h
        · exact h_g_B_fresh x h hx
        · exact h_g_Bs_fresh x h hx
    rw [he]; exact (h_wfcongr ρ_h) g ρ_s.store ρ_h.store h_store_agree
  have h_guard_tt : ∀ (ρ_s ρ_h : Env P),
      HoistInv (P := P) (A ++ sourcesOf' entries) (B ++ targetsOf' entries)
        (subst ++ substOf' entries) ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
      ρ_s.eval ρ_s.store g = .some HasBool.tt → ρ_h.eval ρ_h.store g = .some HasBool.tt := by
    intro ρ_s ρ_h hi he ht
    rw [← h_guard_agree ρ_s ρ_h hi he (read_vars_def_of_eval (h_wfdef ρ_s) ht)]; exact ht
  have h_guard_ff : ∀ (ρ_s ρ_h : Env P),
      HoistInv (P := P) (A ++ sourcesOf' entries) (B ++ targetsOf' entries)
        (subst ++ substOf' entries) ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
      ρ_s.eval ρ_s.store g = .some HasBool.ff → ρ_h.eval ρ_h.store g = .some HasBool.ff := by
    intro ρ_s ρ_h hi he hf
    rw [← h_guard_agree ρ_s ρ_h hi he (read_vars_def_of_eval (h_wfdef ρ_s) hf)]; exact hf
  -- The driver's hoist env is the prelude post env `ρ_pre`; transport the
  -- hoist-side `Vs`-undef seed from `ρ_hoist` to `ρ_pre` (they agree off the
  -- fresh targets, and `Vs` is disjoint from the targets).
  have h_entry_Vh_pre : ∀ y ∈ Vs, ρ_pre.store y = none := by
    intro y hy
    rw [h_pre_frame y (h_Vs_notBs y hy)]; exact h_entry_Vh y hy
  obtain ⟨ρ_post_h, h_loop_h_run, h_post_hinv, h_post_hf, h_post_bnd⟩ :=
    loopDet_lift_sf_undef_recovers_single (g := g) (md_s := md) (md_h := md)
      (A := A ++ sourcesOf' entries) (B := B ++ targetsOf' entries)
      (subst := subst ++ substOf' entries) (Vs := Vs) (Vh := Vs) (σ_sf := σ_sf)
      h_guard_tt h_guard_ff (fun _ _ he hwfb => he ▸ hwfb)
      (bodySimUSF_is_driver_slot _ _ _ _ _ _ _ _ composed)
      h_src_body_no_exit h_nofd_src h_nofd_h
      h_union_entry h_union_eval h_union_hf h_union_bnd
      h_entry_Vs h_entry_Vh_pre h_arm_src_sf h_run
  refine ⟨ρ_post_h, .terminal ρ_post_h, ?_, ?_⟩
  · have h_pfx := stmts_prefix_terminal_append P (EvalCmd P) extendEval
      (havocStmts' entries) [Stmt.loop (.det g) none [] body₃ md] ρ_hoist ρ_pre h_prelude_run
    refine ReflTrans_Transitive _ _ _ _ h_pfx ?_
    refine ReflTrans.step _ _ _ .step_stmts_cons ?_
    refine ReflTrans_Transitive _ _ _ _
      (seq_inner_star P (EvalCmd P) extendEval _ _ _ h_loop_h_run) ?_
    exact ReflTrans.step _ _ _ .step_seq_done
      (ReflTrans.step _ _ _ .step_stmts_nil (.refl _))
  · refine Or.inl ⟨ρ_post, rfl, rfl, ?_, ?_, ?_⟩
    · exact stepJ_restrict h_post_hinv
        (fun x hx => h_post_src_none ρ_post x h_run hx)
        (fun x hx => h_post_tgt_none ρ_post x h_run hx)
    · exact h_post_hf
    · intro y hy
      exact h_post_bnd y (List.mem_append.mpr (Or.inl hy))

end LoopInitHoistLoopArmWF
end Imperative

end -- public section
