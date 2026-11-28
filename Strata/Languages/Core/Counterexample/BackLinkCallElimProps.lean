/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkCallElim
import all Strata.Languages.Core.Counterexample.BackLinkCallElim

/-! # Properties of the `callElim` configuration map

`uncallElimConfig` (`BackLinkCallElim`) maps a configuration of the
call-elimination output to the source program.  It is the identity, up to dropping the
pass's fresh variables from the store, on a top-level start whose statement list contains
no expansion (`expansionFreeStmts`), and it maps the top of the call-elimination image
of a source unit (`CallElimImageStmts`) to the top of that source unit.

Key theorems: `uncallElimConfig_stmts_of_free`, `uncallElimConfig_top`.

Key definitions (`BackLinkCallElim`): `uncallElimConfig`, `expansionFreeStmts`,
`CallElimImageStmts`, `midExpansion?`, `dropFreshEnv`. -/

namespace Core

open _root_.Lambda Imperative
open Core.CallElim (CallOrigin)

public section

/-! ## Identity outside expansions -/

mutual

/-- `uncallElimStmt` is the identity on an expansion-free statement (`expansionFreeStmt`:
    no statement list nested in it starts an expansion). -/
private theorem uncallElimStmt_of_free (origins : List CallOrigin) :
    ∀ (s : Statement), expansionFreeStmt origins s → uncallElimStmt origins s = s
  | .block _ _ _, h | .loop _ _ _ _ _, h => by simp [uncallElimStmt, uncallElimStmts_of_free _ _ h]
  | .ite _ _ _ _, h => by
    simp [uncallElimStmt, uncallElimStmts_of_free _ _ h.1, uncallElimStmts_of_free _ _ h.2]
  | .cmd _, _ | .exit .., _ | .typeDecl .., _ => rfl

/-- `uncallElimStmts` is the identity on an expansion-free statement list
    (`expansionFreeStmts`: no suffix of it, and no statement list nested in it, starts an
    expansion). -/
private theorem uncallElimStmts_of_free (origins : List CallOrigin) :
    ∀ (ss : List Statement), expansionFreeStmts origins ss → uncallElimStmts origins 0 ss = ss
  | [], _ => rfl
  | _ :: _, ⟨hat, hs, hrest⟩ => by
    simp [uncallElimStmts, hat, uncallElimStmt_of_free _ _ hs, uncallElimStmts_of_free _ _ hrest]

end

/-- Dropping `skip` statements, then un-eliminating: `uncallElimStmts` with a pending
    skip of `xs.length` over `xs ++ ys` is `uncallElimStmts` of `ys`. -/
private theorem uncallElimStmts_skip (origins : List CallOrigin) :
    ∀ (xs ys : List Statement),
      uncallElimStmts origins xs.length (xs ++ ys) = uncallElimStmts origins 0 ys
  := fun xs _ => by induction xs <;> simp [uncallElimStmts, *]

/-- An expansion recognized at the head of a list (`expansionAt?`) is replaced by the
    original call, and the rest of the list is un-eliminated. -/
private theorem uncallElimStmts_expansion (origins : List CallOrigin) (o : CallOrigin)
    (post : List Statement) (hne : o.expansion ≠ [])
    (hat : expansionAt? origins (o.expansion ++ post) = some o) :
    uncallElimStmts origins 0 (o.expansion ++ post)
      = o.source :: uncallElimStmts origins 0 post := by
  obtain ⟨s, t, hexp⟩ := List.exists_cons_of_ne_nil hne
  simp_all [uncallElimStmts, uncallElimStmts_skip]

/-- **Identity outside expansions** for a top-level start: a statement list that is
    expansion-free (`expansionFreeStmts`: no suffix of it, and no statement list nested in
    it, starts an expansion) and does not start strictly inside an expansion
    (`midExpansion?` is `none`) maps to itself, with the pass's fresh variables dropped
    from the store. -/
theorem uncallElimConfig_stmts_of_free (origins : List CallOrigin) (ss : List Statement)
    (env : IEnv Expression) (hfree : expansionFreeStmts origins ss)
    (hmid : midExpansion? origins ss = none) :
    uncallElimConfig origins (.stmts ss env)
      = some (.stmts ss (dropFreshEnv (callElimFreshVars origins) env)) := by
  simp [uncallElimConfig, hmid, uncallElimStmts_of_free _ _ hfree]

/-! ## The top-level downstream start

On a call-elimination image `uncallElimStmts` recovers the source, so the top-level
downstream start maps to the top of the source unit. -/

mutual

/-- `uncallElimStmt` recovers a source statement from its call-elimination image. -/
private theorem uncallElimStmt_of_image (origins : List CallOrigin) :
    ∀ {s s' : Statement}, CallElimImageStmt origins s s' → uncallElimStmt origins s' = s
  | _, _, .block _ _ _ _ h | _, _, .loop _ _ _ _ _ _ h => by
    simp [uncallElimStmt, uncallElimStmts_of_image _ h]
  | _, _, .ite _ _ _ _ _ _ ht he => by
    simp [uncallElimStmt, uncallElimStmts_of_image _ ht, uncallElimStmts_of_image _ he]
  | _, _, .cmd _ | _, _, .exit .. | _, _, .typeDecl .. => rfl

/-- `uncallElimStmts` recovers a source statement list from its call-elimination image. -/
private theorem uncallElimStmts_of_image (origins : List CallOrigin) :
    ∀ {ss ss' : List Statement}, CallElimImageStmts origins ss ss' →
      uncallElimStmts origins 0 ss' = ss
  | _, _, .nil => rfl
  | _, _, .call _ _ _ hne hat h => by
    rw [uncallElimStmts_expansion _ _ _ hne hat, uncallElimStmts_of_image _ h]
  | _, _, .stmt _ _ _ _ hat hs h => by
    simp [uncallElimStmts, hat, uncallElimStmt_of_image _ hs, uncallElimStmts_of_image _ h]

end

/-- **Downstream top => source top.**  The top-level downstream start `.stmts st' env`, for
    `st'` the call-elimination image of the source unit `st` (`CallElimImageStmts`: `st`
    with each eliminated call replaced by its recorded expansion) not starting strictly
    inside an expansion (`midExpansion?` is `none`), maps to the top of the source unit
    `.stmts st env'`, where `env'` is `env` without the pass's fresh variables. -/
theorem uncallElimConfig_top (origins : List CallOrigin) (st st' : List Statement)
    (env : IEnv Expression) (himg : CallElimImageStmts origins st st')
    (hmid : midExpansion? origins st' = none) :
    uncallElimConfig origins (.stmts st' env)
      = some (.stmts st (dropFreshEnv (callElimFreshVars origins) env)) := by
  simp [uncallElimConfig, hmid, uncallElimStmts_of_image _ himg]

end -- public section

end Core
