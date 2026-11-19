/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify.SimpRun
public import Strata.Transform.Simplify.SweepRun
import all Strata.Transform.Simplify.SimpRun
import all Strata.Transform.Simplify.SweepRun
import all Strata.Transform.Simplify.StmtSim
import all Strata.Transform.Simplify.Precondition
import all Strata.Transform.Simplify.Entry

/-! # Composing the two passes of a Simplify body

The simplification pass relates events by `Event.WeakensAssume evalInterp`; the
dead-definition sweep replays them (`EvReplay`), keeping each condition's value. The two
compose into `Event.WeakensAssume evalInterp` (`weakensAssume_replay`). The entry
environment of a body satisfying the precondition satisfies the run invariant
(`inv_entry`).
-/

namespace Core.Simplify

open Imperative Imperative.BigStep

/-- An identifier of a body is touched by it or defined in it. -/
private theorem mem_touched_or_defined {ss : List Statement} {y : CoreIdent}
    (hy : y ∈ Block.idents ss) :
    y ∈ Block.touchedVars (P := Expression) (C := Command) ss ∨
      y ∈ Block.definedVars (P := Expression) (C := Command) ss false := by
  rcases Block.idents_subset_vars ss y hy with h | h | h
  · exact .inl (by simp [Block.touchedVars, h])
  · exact .inl (by simp [Block.touchedVars, Block.modifiedOrDefinedVars, h])
  · exact .inr h


/-! ## Composing the event relations -/

/-- A replaying event's condition holds where the replayed one's does. -/
private theorem holds_of_argReplay {M : Expression.Factory} (hE : EvCongr M)
    {a a' : EventArg Expression}
    (h : ArgReplay M a a') (w : (evalInterp (P := Expression)).World) :
    (evalInterp (P := Expression)).holds w a' ↔ (evalInterp (P := Expression)).holds w a := by
  obtain ⟨hf, hf', -, hx, -, hA, hC⟩ := h
  show Expression.eval a'.factory a'.store a'.expr = _ ↔
    Expression.eval a.factory a.store a.expr = _
  rw [hf', hx, ev_agree hE hC hA fun _ hy => hy, hf]

/-- **The two passes compose**: an event related to a second by `Event.WeakensAssume
    evalInterp`, the second replayed by a third, is related to the third. -/
theorem weakensAssume_replay {M : Expression.Factory} (hE : EvCongr M) {e₁ e₂ e₃ : Event Expression}
    (h₁ : Event.WeakensAssume (evalInterp (P := Expression)) e₁ e₂) (h₂ : EvReplay M e₂ e₃) :
    Event.WeakensAssume (evalInterp (P := Expression)) e₁ e₃ := by
  rcases e₁ with a₁ | a₁ | a₁ <;> rcases e₂ with a₂ | a₂ | a₂ <;> rcases e₃ with a₃ | a₃ | a₃ <;>
    simp only [Event.WeakensAssume, EvReplay] at h₁ h₂ ⊢
  all_goals first
    | (obtain ⟨hl, hm, hh⟩ := h₁
       obtain ⟨-, -, hl', -, hm', -, -⟩ := id h₂
       exact ⟨hl.trans hl'.symm, hm.trans hm'.symm,
         fun w => (hh w).trans (holds_of_argReplay hE h₂ w).symm⟩)
    | (obtain ⟨hl, hm, hh⟩ := h₁
       obtain ⟨-, -, hl', -, hm', -, -⟩ := id h₂
       exact ⟨hl.trans hl'.symm, hm.trans hm'.symm,
         fun w hw => (holds_of_argReplay hE h₂ w).mpr (hh w hw)⟩)

/-- Event lists related pointwise, the first two by `Event.WeakensAssume evalInterp` and the
    last two by `EvReplay` (replaying keeps each condition's value), make the first and the
    last related pointwise by `Event.WeakensAssume evalInterp`. -/
theorem rel₂_weakensAssume_replay {M : Expression.Factory} (hE : EvCongr M) :
    ∀ {l₁ l₂ l₃ : List (Event Expression)},
      List.Rel₂ (Event.WeakensAssume (evalInterp (P := Expression))) l₁ l₂ →
      List.Rel₂ (EvReplay M) l₂ l₃ →
      List.Rel₂ (Event.WeakensAssume (evalInterp (P := Expression))) l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h hs, .cons h' hs' =>
    .cons (weakensAssume_replay hE h h') (rel₂_weakensAssume_replay hE hs hs')

/-! ## The entry environment -/

/-- **The run invariant holds at entry**, in an environment the gate admits whose store
    gives the body's entry variables their `Γ` types, when `Γ` types no variable the body
    declares. -/
theorem inv_entry {base : Ctx} {M : Expression.Factory} {Γ : VarTyping Expression}
    {ss : List Statement} {σ : SemanticStore Expression} (hfresh : base.Fresh)
    (hst : StoreTypedBy M Γ ss σ) (hwf : WellFormedStore σ M)
    (hrw : ∀ x ∈ Block.touchedVars (P := Expression) (C := Command) ss,
      x ∉ Block.definedVars (P := Expression) (C := Command) ss false → (σ x).isSome)
    (hdu : ∀ x ∈ Block.definedVars (P := Expression) (C := Command) ss false, (σ x).isNone)
    (hΓ : ∀ x ∈ Block.definedVars (P := Expression) (C := Command) ss false, Γ x = none) :
    Inv base M (Block.idents ss) (typeList Γ ss) Γ base σ := by
  have hentry : ∀ y ∈ Block.idents ss, ∀ v, σ y = some v →
      y ∈ Block.entryVars ss ∧ ∃ ty, Γ y = some ty ∧ HasVal.valueOfTy M v ty := by
    intro y hy v hv
    have hnd : y ∉ Block.definedVars (P := Expression) (C := Command) ss false := fun h => by
      have := hdu y h; rw [hv] at this; cases this
    have hy' : y ∈ Block.entryVars ss := by
      rcases mem_touched_or_defined hy with h | h
      · exact List.mem_filter.mpr ⟨h, by simpa using hnd⟩
      · exact absurd h hnd
    obtain ⟨hT, hb⟩ := storeTypedBy_iff.mp hst
    obtain ⟨ty, ht⟩ := Option.isSome_iff_exists.mp (hb y hy' (by simp [hv]))
    exact ⟨hy', ty, ht, hT y hy' ty v ht hv⟩
  refine ⟨Ctx.Fixed.refl base, fun x r hm => ?_, fun x r hm => ?_, fun y hy t v ht hv => ?_,
    fun y hy v hv => ?_, hwf, fun y hy ht => ?_⟩
  · rw [hfresh.2] at hm; cases hm
  · rw [hfresh.2] at hm; cases hm
  · obtain ⟨-, ty, hty, hval⟩ := hentry y hy v hv
    rw [ht] at hty; cases hty; exact hval
  · obtain ⟨hy', ty, hty, hval⟩ := hentry y hy v hv
    refine List.mem_append_left _ (List.mem_filterMap.mpr ⟨y, hy', ?_⟩)
    rw [hty, ← ty_eq_of_valueOfTy hval]; rfl
  · have hnd : y ∉ Block.definedVars (P := Expression) (C := Command) ss false := fun h => by
      rw [hΓ y h] at ht; cases ht
    rcases mem_touched_or_defined hy with h | h
    · exact hrw y h hnd
    · exact absurd h hnd

end Core.Simplify
