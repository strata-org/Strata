/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF
public import Strata.Backends.CBMC.GOTO.BlocksFoldClosed
import all Strata.DL.Imperative.ToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline

public section

/-! # `coreCFGToGotoTransform` never emits DEAD instructions

Round-7b deliverable, refactored in L3 to use the
`BlocksFoldClosed` preservation combinator. Discharges R6a's
`h_no_dead` side hypothesis by induction on the translator's structure.

## What we prove

```
theorem no_dead_program_of_translator
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_no_dead : HasNoDead trans₀)
    ...
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀ = .ok ans) :
    ∀ {pc instr}, ⟨…ans.instructions⟩.instrAt pc = some instr →
                  instr.type ≠ .DEAD
```

## Refactor strategy (L3)

The 9 per-step preservation lemmas (steps 1-9 of the blocks-fold
chain in the L2 audit) are replaced by a single `BlocksFoldClosed`
typeclass instance for `HasNoDead'` (the array-level predicate
underlying `HasNoDead`). The `BlocksFoldClosed.of_blocks_run` theorem
exposes the post-blocks-fold preservation; the patcher chain (steps
10-12) is handled directly. -/

namespace CProverGOTO.NoDead

open Imperative
open CProverGOTO

/-! ## The `HasNoDead` predicate

Two equivalent shapes are useful: an array-level predicate
`HasNoDead' : Array Instruction → Prop` (which the combinator consumes),
and the transform-level predicate `HasNoDead : GotoTransform → Prop`
(the original public name). They are linked by definitional unfolding.
-/

/-- Array-level: every instruction in `a` has a non-DEAD type. -/
def HasNoDead' (a : Array CProverGOTO.Instruction) : Prop :=
  ∀ {pc : Nat} {instr : Instruction},
    a[pc]? = some instr → instr.type ≠ .DEAD

/-- Transform-level (legacy public name): every instruction in
`trans.instructions` has a non-DEAD type. -/
abbrev HasNoDead (trans : Imperative.GotoTransform Core.Expression.TyEnv) : Prop :=
  HasNoDead' trans.instructions

/-! ## Push/append safety primitives

These match the `ofPushSafe` API: `HasNoDead'` is closed under pushing
any non-DEAD instruction, and under appending two non-DEAD instructions. -/

private theorem hasNoDead'_push
    (a : Array CProverGOTO.Instruction) (new_instr : Instruction)
    (h : HasNoDead' a) (h_new : new_instr.type ≠ .DEAD) :
    HasNoDead' (a.push new_instr) := by
  intro pc instr h_at
  by_cases h_lt : pc < a.size
  · rw [Array.getElem?_push_lt h_lt] at h_at
    have h' : a[pc]? = some instr := by
      rw [Array.getElem?_eq_getElem h_lt]; exact h_at
    exact h h'
  · have h_ge : a.size ≤ pc := Nat.le_of_not_lt h_lt
    by_cases h_eq : pc = a.size
    · subst h_eq
      rw [Array.getElem?_push_size] at h_at
      injection h_at with h_at
      subst h_at
      exact h_new
    · have h_lt' : a.size < pc := by omega
      have h_oor : (a.push new_instr).size ≤ pc := by
        rw [Array.size_push]; omega
      rw [Array.getElem?_eq_none h_oor] at h_at
      exact absurd h_at (by simp)

private theorem hasNoDead'_append_two
    (a : Array CProverGOTO.Instruction) (i₀ i₁ : Instruction)
    (h : HasNoDead' a) (h_new0 : i₀.type ≠ .DEAD)
    (h_new1 : i₁.type ≠ .DEAD) :
    HasNoDead' (a ++ #[i₀, i₁]) := by
  intro pc instr h_at
  by_cases h_lt : pc < a.size
  · rw [Array.getElem?_append_left h_lt] at h_at
    exact h h_at
  · have h_ge : a.size ≤ pc := Nat.le_of_not_lt h_lt
    by_cases h_eq0 : pc = a.size
    · subst h_eq0
      rw [Array.getElem?_append_right (Nat.le_refl _)] at h_at
      simp at h_at
      subst h_at
      exact h_new0
    · by_cases h_eq1 : pc = a.size + 1
      · subst h_eq1
        rw [Array.getElem?_append_right (Nat.le_add_right _ _)] at h_at
        simp at h_at
        subst h_at
        exact h_new1
      · have h_oor : (a ++ #[i₀, i₁]).size ≤ pc := by
          rw [Array.size_append]
          simp; omega
        rw [Array.getElem?_eq_none h_oor] at h_at
        exact absurd h_at (by simp)

/-! ## `BlocksFoldClosed` instance for `HasNoDead'`

Every instruction the translator emits during the blocks-fold has type
DECL / ASSIGN / ASSERT / ASSUME / GOTO / LOCATION / END_FUNCTION /
FUNCTION_CALL — none of which equal DEAD. So `HasNoDead'` is closed
under each push, and the combinator's `ofPushSafe` builds the instance
from this single observation. -/

instance instBlocksFoldClosed_HasNoDead' :
    BlocksFoldClosed HasNoDead' :=
  BlocksFoldClosed.ofPushSafe
    (IsSafe := fun instr => instr.type ≠ .DEAD)
    (h_push := fun a x h h_safe => hasNoDead'_push a x h h_safe)
    (h_append := fun a x y h hx hy => hasNoDead'_append_two a x y h hx hy)
    (h_DECL := by intro instr h; rw [h]; decide)
    (h_ASSIGN := by intro instr h; rw [h]; decide)
    (h_ASSERT := by intro instr h; rw [h]; decide)
    (h_ASSUME := by intro instr h; rw [h]; decide)
    (h_FUNCTION_CALL := by intro instr h; rw [h]; decide)
    (h_LOCATION := by intro instr h; rw [h]; decide)
    (h_GOTO := by intro instr h; rw [h]; decide)
    (h_END_FUNCTION := by intro instr h; rw [h]; decide)

/-! ## Preservation through `patchGotoTargets`

The patcher only mutates `target` — A4's `patchGotoTargets_preserves_type`
says every instruction's type after patching is the type of some
pre-existing instruction. Combined with the input being no-DEAD, the
output is no-DEAD. -/

theorem patchGotoTargets_preserves_no_dead
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (patches : List (Nat × Nat))
    (h_no_dead : HasNoDead trans) :
    HasNoDead (Imperative.patchGotoTargets trans patches) := by
  intro pc instr h
  obtain ⟨instr_pre, h_pre, h_ty⟩ :=
    patchGotoTargets_preserves_type trans patches pc instr h
  rw [h_ty]
  exact h_no_dead h_pre

/-! ## Final composition

Assemble the per-step preservation lemmas to get:

> `Strata.coreCFGToGotoTransform Env functionName cfg trans₀ = .ok ans` ⊢
> if `trans₀.instructions` has no DEAD, neither does `ans.instructions`.

`coreCFGToGotoTransform` decomposes as:

1. The entry-block check (a `pure ()` or `throw`; doesn't touch the
   transform).
2. `cfg.blocks.foldlM (coreCFGToGotoBlockStep ...) initSt` — handled by
   `BlocksFoldClosed.of_blocks_run`.
3. `st.pendingPatches.foldlM (coreCFGToGotoPatchStep ...) ([], st.trans)`
   — under the no-loop-contracts assumption, the trans is unchanged
   (A4's `patchesFoldlM_no_contracts_trans_eq`).
4. Wrap with `patchGotoTargets`.

(R6a's pipeline already only invokes the bridge with no-contract
inputs, so requiring `loopContracts = ∅` is consistent with the
existing call sites.) -/

/-- **Translator never emits DEAD instructions.**

Under the assumption that the initial transform has no DEAD
instructions and the no-loop-contracts assumption (consistent with
R6a's call sites), the translator's output also has no DEAD.

This `_explicit` form takes the decomposition pieces as inputs.
For the version that takes only `h_run`, see `no_dead_of_translator`
below. -/
theorem no_dead_of_translator_no_contracts_explicit
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_no_dead : HasNoDead trans₀)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (_h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    (st_final : Strata.CoreCFGTransLoopState)
    (h_blocks_run :
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        ({ trans := trans₀, pendingPatches := #[], labelMap := {},
           loopContracts := {} } : Strata.CoreCFGTransLoopState)
      = Except.ok st_final)
    (h_loopContracts_empty : st_final.loopContracts = ∅)
    (resolved : List (Nat × Nat))
    (trans_post : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_patches_run :
      st_final.pendingPatches.foldlM
        (Strata.coreCFGToGotoPatchStep st_final.labelMap st_final.loopContracts)
        ([], st_final.trans)
      = Except.ok (resolved, trans_post))
    (h_ans_eq : ans = Imperative.patchGotoTargets trans_post resolved) :
    HasNoDead ans := by
  -- Step 1: the blocks-fold preserves no-DEAD.
  have h_blocks_run' :
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀) = Except.ok st_final := by
    have heq : coreCFGToGotoInitState trans₀ =
        ({ trans := trans₀, pendingPatches := #[], labelMap := {},
           loopContracts := {} } : Strata.CoreCFGTransLoopState) := by
      simp [coreCFGToGotoInitState]
    rw [heq]; exact h_blocks_run
  have h_init' : HasNoDead' trans₀.instructions := h_init_no_dead
  have h_after_blocks : HasNoDead' st_final.trans.instructions :=
    BlocksFoldClosed.of_blocks_run (P := HasNoDead') functionName cfg trans₀
      h_init' st_final h_blocks_run'
  -- Step 2: the patches-fold preserves trans under empty loop contracts.
  rw [h_loopContracts_empty] at h_patches_run
  have h_trans_eq : trans_post = st_final.trans :=
    patchesFoldlM_no_contracts_trans_eq st_final.labelMap st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
  have h_after_patches : HasNoDead trans_post := by
    rw [h_trans_eq]; exact h_after_blocks
  -- Step 3: patchGotoTargets preserves no-DEAD.
  rw [h_ans_eq]
  intro pc instr h
  exact patchGotoTargets_preserves_no_dead trans_post resolved h_after_patches h

/-- **Translator never emits DEAD instructions** — direct form.

Takes only `h_run` plus the no-loop-contracts side condition.
Internally invokes `coreCFGToGotoTransform_decompose` to extract
the per-stage results. The no-loop-contracts side condition is the
analog of A4's `h_loopContracts_empty_post` — it's true for any CFG
without `LoopInvariant` / `Decreases` metadata, which is the case
for the round-6 / round-7 forward-simulation pipeline. -/
theorem no_dead_of_translator
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_no_dead : HasNoDead trans₀)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans) :
    HasNoDead ans := by
  obtain ⟨st_final, resolved, trans_post, h_blocks_run, h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  have h_blocks_run' :
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        ({ trans := trans₀, pendingPatches := #[], labelMap := {},
           loopContracts := {} } : Strata.CoreCFGTransLoopState)
      = Except.ok st_final := by
    have : coreCFGToGotoInitState trans₀ =
        ({ trans := trans₀, pendingPatches := #[], labelMap := {},
           loopContracts := {} } : Strata.CoreCFGTransLoopState) := by
      simp [coreCFGToGotoInitState]
    rw [this] at h_blocks_run
    exact h_blocks_run
  intro pc instr h
  exact no_dead_of_translator_no_contracts_explicit Env functionName cfg trans₀
    h_init_no_dead ans h_run st_final h_blocks_run'
    (h_loopContracts_empty_post st_final h_blocks_run)
    resolved trans_post h_patches_run h_ans_eq h

/-! ## Wrapper at the `Program` level

R6a's `h_no_dead` field works at the `Program.instrAt` level, not
directly on `trans.instructions[pc]?`. The two are interconvertible:
`Program.instrAt pgm pc` unfolds to `pgm.instructions[pc]?`. -/

/-- The translator never emits DEAD — at the `Program` level.

This is the precise shape of R6a's `h_no_dead` side hypothesis. -/
theorem no_dead_program_of_translator
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_no_dead : HasNoDead trans₀)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans) :
    ∀ {pc : Nat} {instr : Instruction},
      ({ name := "", parameterIdentifiers := #[],
         instructions := ans.instructions } : Program).instrAt pc =
        some instr →
      instr.type ≠ .DEAD := by
  intro pc instr h
  unfold Program.instrAt at h
  exact no_dead_of_translator Env functionName cfg trans₀ h_init_no_dead
    h_loopContracts_empty_post ans h_run h

end CProverGOTO.NoDead
