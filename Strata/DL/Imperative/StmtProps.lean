/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt

namespace Imperative

public section

/-! ## Properties of `Stmt.exitsCoveredByBlocks` -/

theorem block_exitsCoveredByBlocks_append
    {P : PureExpr} {CmdT : Type}
    (labels : List String) (ss₁ ss₂ : List (Stmt P CmdT))
    (h₁ : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss₁)
    (h₂ : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss₂) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels (ss₁ ++ ss₂) := by
  induction ss₁ with
  | nil => exact h₂
  | cons s ss ih => exact ⟨h₁.1, ih h₁.2⟩

/-- `exitsCoveredByBlocks` is monotone in the label list: more covering labels
    can only help. -/
theorem exitsCoveredByBlocks_weaken
    {P : PureExpr} {CmdT : Type}
    (labels₁ labels₂ : List String)
    (hsub : ∀ l, l ∈ labels₁ → l ∈ labels₂) :
    (∀ (s : Stmt P CmdT),
      s.exitsCoveredByBlocks labels₁ → s.exitsCoveredByBlocks labels₂) ∧
    (∀ (ss : List (Stmt P CmdT)),
      Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels₁ ss →
      Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels₂ ss) := by
  suffices hstmt : ∀ (s : Stmt P CmdT),
      ∀ labels₁ labels₂, (∀ l, l ∈ labels₁ → l ∈ labels₂) →
        s.exitsCoveredByBlocks labels₁ → s.exitsCoveredByBlocks labels₂ by
    constructor
    · exact fun s => hstmt s labels₁ labels₂ hsub
    · intro ss
      induction ss with
      | nil => intros; trivial
      | cons s ss ih =>
        exact fun h => ⟨hstmt s _ _ hsub h.1, ih h.2⟩
  intro s
  induction s using Stmt.rec (motive_2 := fun ss =>
    ∀ labels₁ labels₂, (∀ l, l ∈ labels₁ → l ∈ labels₂) →
      Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels₁ ss →
      Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels₂ ss) with
  | cmd _ => intros; trivial
  | block l ss _ ih =>
    intro labels₁ labels₂ hsub h
    show Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (l :: labels₂) ss
    exact ih (l :: labels₁) (l :: labels₂)
      (fun x hx => by cases hx with
        | head => exact .head _
        | tail _ hm => exact .tail _ (hsub x hm))
      h
  | ite _ tss ess _ ih_t ih_e =>
    intro labels₁ labels₂ hsub h
    exact ⟨ih_t labels₁ labels₂ hsub h.1, ih_e labels₁ labels₂ hsub h.2⟩
  | loop _ _ _ body _ ih =>
    intro labels₁ labels₂ hsub h
    exact ih labels₁ labels₂ hsub h
  | exit l _ =>
    intro labels₁ labels₂ hsub h
    exact hsub l h
  | funcDecl _ _ => intros; trivial
  | typeDecl _ _ => intros; trivial
  | nil => intros; trivial
  | cons s ss ih_s ih_ss =>
    rename_i labels₁ labels₂ hsub h
    exact ⟨ih_s labels₁ labels₂ hsub h.1, ih_ss labels₁ labels₂ hsub h.2⟩

/-- If every statement in a list is a `.cmd`, then `exitsCoveredByBlocks` holds
    for any labels (since `.cmd` has no exit statements). -/
theorem all_cmd_exitsCoveredByBlocks
    {P : PureExpr} {CmdT : Type}
    (labels : List String) (ss : List (Stmt P CmdT))
    (h : ∀ s ∈ ss, ∃ c, s = Stmt.cmd c) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss := by
  induction ss with
  | nil => trivial
  | cons hd tl ih =>
    constructor
    · obtain ⟨c, hc⟩ := h hd (.head _)
      subst hc; exact True.intro
    · exact ih (fun s hs => h s (.tail _ hs))

end -- public section
end Imperative
