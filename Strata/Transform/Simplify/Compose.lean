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
import all Strata.Transform.Simplify.SimpWF

/-! # Composing the two passes of a Simplify body

The simplification pass relates events by `Event.WeakensAssume evalInterp`; the
dead-definition sweep replays them (`EvReplay`), keeping each condition's value. The two
compose into `Event.WeakensAssume evalInterp` (`weakensAssume_replay`). The entry
environment of a body satisfying the precondition satisfies the run invariant
(`inv_entry`), once the entry typing is restricted to the entry variables
(`restrictTyping`): a body def-use well-formed from the entry store reads no variable it
declares before declaring it, so the restriction keeps the precondition
(`Block.exprsOKIn_congr`, `BodyWF.restrict`).
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
    Inv base M (Block.idents ss) Γ base σ := by
  have hentry : ∀ y ∈ Block.idents ss, ∀ v, σ y = some v →
      ∃ ty, Γ y = some ty ∧ HasVal.valueOfTy M v ty := by
    intro y hy v hv
    have hnd : y ∉ Block.definedVars (P := Expression) (C := Command) ss false := fun h => by
      have := hdu y h; rw [hv] at this; cases this
    have hy' : y ∈ Block.entryVars ss := by
      rcases mem_touched_or_defined hy with h | h
      · exact List.mem_filter.mpr ⟨h, by simpa using hnd⟩
      · exact absurd h hnd
    obtain ⟨hT, hb⟩ := storeTypedBy_iff.mp hst
    obtain ⟨ty, ht⟩ := Option.isSome_iff_exists.mp (hb y hy' (by simp [hv]))
    exact ⟨ty, ht, hT y hy' ty v ht hv⟩
  refine ⟨Ctx.Fixed.refl base, fun x r hm => ?_, fun x r hm => ?_, fun y hy t v ht hv => ?_,
    hwf, fun y hy ht => ?_⟩
  · rw [hfresh.2] at hm; cases hm
  · rw [hfresh.2] at hm; cases hm
  · obtain ⟨ty, hty, hval⟩ := hentry y hy v hv
    rw [ht] at hty; cases hty; exact hval
  · have hnd : y ∉ Block.definedVars (P := Expression) (C := Command) ss false := fun h => by
      rw [hΓ y h] at ht; cases ht
    rcases mem_touched_or_defined hy with h | h
    · exact hrw y h hnd
    · exact absurd h hnd

/-! ## Restricting the entry typing to the entry variables -/

/-- `Γ` restricted to the body's entry variables (`Block.entryVars`): the variables it declares,
    and those it does not mention, are left untyped. -/
def restrictTyping (Γ : VarTyping Expression) (ss : List Statement) : VarTyping Expression :=
  fun x => if x ∈ Block.entryVars ss then Γ x else none

/-- The restricted typing types no variable the body declares. -/
theorem restrictTyping_declsUntyped (Γ : VarTyping Expression) (ss : List Statement) :
    ∀ x ∈ Block.definedVars (P := Expression) (C := Command) ss false,
      restrictTyping Γ ss x = none :=
  fun _ hx => by simp [restrictTyping, Block.entryVars, hx]

/-- The restricted typing agrees with `Γ` on the body's entry variables. -/
private theorem restrictTyping_entry {Γ : VarTyping Expression} {ss : List Statement}
    {x : CoreIdent} (hx : x ∈ Block.entryVars ss) : restrictTyping Γ ss x = Γ x := by
  simp [restrictTyping, hx]

/-- A store gives the entry variables their restricted types when it gives them their `Γ`
    types. -/
theorem StoreTypedBy.restrict {M : Expression.Factory} {Γ : VarTyping Expression}
    {ss : List Statement} {σ : CoreStore} (h : StoreTypedBy M Γ ss σ) :
    StoreTypedBy M (restrictTyping Γ ss) ss σ := fun x hx v hv => by
  rw [restrictTyping_entry hx]; exact h x hx v hv

/-- A store that binds the body's entry variables at their `Γ` types conforms to the restricted
    typing. -/
theorem restrictTyping_storeHasTyping {M : Expression.Factory} {Γ : VarTyping Expression}
    {ss : List Statement} {σ : CoreStore} (h : StoreTypedBy M Γ ss σ)
    (hb : ∀ x ∈ Block.entryVars ss, (σ x).isSome) :
    StoreHasTyping M σ (restrictTyping Γ ss) := by
  intro x ty hx
  simp only [restrictTyping] at hx
  split at hx
  · rename_i he
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hb x he)
    obtain ⟨ty', h1, h2⟩ := h x he v hv
    rw [hx] at h1; cases h1
    exact ⟨v, hv, h2⟩
  · cases hx

/-- Under such a store the restricted typing gives monotypes only. -/
theorem restrictTyping_mono {M : Expression.Factory} {Γ : VarTyping Expression}
    {ss : List Statement} {σ : CoreStore} (h : StoreTypedBy M Γ ss σ)
    (hb : ∀ x ∈ Block.entryVars ss, (σ x).isSome) : MonoTyping (restrictTyping Γ ss) := by
  intro y t hy
  obtain ⟨v, -, -, hm⟩ := restrictTyping_storeHasTyping h hb y t hy
  exact ⟨_, Option.some.inj (eq_forAll_of_bind (t? := some t) hm)⟩

/-- Typings that agree on the variables of `e` make it `ExprOK` alike. -/
private theorem ExprOK.congr {F : Lambda.Factory CoreLParams} {Γ₁ Γ₂ : VarTyping Expression}
    {e : Expression.Expr} {ty : Expression.Ty} (h : ExprOK F Γ₁ e ty)
    (hag : ∀ x ∈ Lambda.LExpr.LExpr.getVars e, Γ₂ x = Γ₁ x) : ExprOK F Γ₂ e ty := by
  obtain ⟨⟨τ, hτ, hg, hdef, hT⟩, hops, hann⟩ := h
  have hA : e.annotateFvars (fun x => (Γ₂ x).bind Lambda.LTy.toMonoType?) =
      e.annotateFvars (fun x => (Γ₁ x).bind Lambda.LTy.toMonoType?) :=
    Lambda.LExpr.annotateFvars_congr e fun x _ hx => by
      rw [hag x (Lambda.LExpr.mem_getVars_of_mem_freeVars hx)]
  exact ⟨⟨τ, hτ, hg, fun x hx => (hag x hx) ▸ hdef x hx, hA ▸ hT⟩, hops, hA.trans hann⟩

/-- A variable a statement declares in its own scope is among its typed definitions. -/
private theorem mem_typedDefinedVars (s : Statement) :
    ∀ y ∈ Stmt.definedVars (P := Expression) (C := Command) s true,
      y ∈ (Stmt.typedDefinedVars (P := Expression) s).map Prod.fst := by
  rcases s with ((x | _ | _ | _ | _) | _) | _ | _ | _ | _ | _ <;>
    simp [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars, CmdExt.typedDefinedVars,
      Cmd.typedDefinedVars, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars]

/-- Extending two typings with the same definitions makes them agree at the defined names
    and wherever they agreed. -/
private theorem extend_agree {Γ₁ Γ₂ : VarTyping Expression} (d : List (CoreIdent × Expression.Ty))
    {y : CoreIdent} (h : y ∈ d.map Prod.fst ∨ Γ₂ y = Γ₁ y) : Γ₂.extend d y = Γ₁.extend d y := by
  rcases h with h | h
  · simp only [VarTyping.extend]
    split
    · rfl
    · rename_i hf
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
      exact absurd (List.find?_eq_none.1 hf e he) (by simp)
  · exact VarTyping.extend_congr (Γ := Γ₁) (Γ' := Γ₂) d h

mutual
/-- **The typing of a statement depends only on its defined names.** Two typings that agree
    on the names of the statement that `D` counts as defined make a statement that is def-use
    well-formed from `D` `exprsOKIn` alike. -/
private theorem Stmt.exprsOKIn_congr {F : Lambda.Factory CoreLParams} {fs : CoreIdent → Bool}
    (s : Statement) {D : CoreIdent → Bool} {Γ₁ Γ₂ : VarTyping Expression}
    (hdu : Stmt.defUseWellFormed (P := Expression) (C := Command) D fs s = true)
    (hag : ∀ x, D x = true → x ∈ Stmt.idents s → Γ₂ x = Γ₁ x) (h : Stmt.exprsOKIn F Γ₁ s) :
    Stmt.exprsOKIn F Γ₂ s := by
  match s with
  | .cmd (.cmd (.init x ty (.det e) md)) =>
    simp only [Stmt.exprsOKIn] at h ⊢
    simp only [Stmt.defUseWellFormed, HasVarsImp.readVars, CmdExt.readVars, Cmd.getVars,
      ExprOrNondet.getVars, Bool.and_eq_true, List.all_eq_true] at hdu
    exact ExprOK.congr h fun y hy => hag y (hdu.1.1.1 y hy) (List.mem_cons_of_mem _ hy)
  | .cmd (.cmd (.init x ty .nondet md)) => simp [Stmt.exprsOKIn]
  | .cmd (.cmd (.set x (.det e) md)) =>
    simp only [Stmt.exprsOKIn] at h ⊢
    simp only [Stmt.defUseWellFormed, HasVarsImp.readVars, CmdExt.readVars, Cmd.getVars,
      ExprOrNondet.getVars, HasVarsImp.modifiedVars, CmdExt.modifiedVars, Cmd.modifiedVars,
      Bool.and_eq_true, List.all_eq_true, List.mem_singleton, forall_eq] at hdu
    obtain ⟨ty, hty, hok⟩ := h
    exact ⟨ty, (hag x hdu.1.1.2 (by simp [Stmt.idents])).trans hty,
      ExprOK.congr hok fun y hy => hag y (hdu.1.1.1 y hy) (List.mem_cons_of_mem _ hy)⟩
  | .cmd (.cmd (.set x .nondet md)) =>
    simp only [Stmt.defUseWellFormed, HasVarsImp.modifiedVars, CmdExt.modifiedVars,
      Cmd.modifiedVars, Bool.and_eq_true, List.all_eq_true, List.mem_singleton,
      forall_eq] at hdu
    simp only [Stmt.exprsOKIn] at h ⊢
    rw [hag x hdu.1.1.2 (by simp [Stmt.idents])]; exact h
  | .cmd (.cmd (.assert l e md)) | .cmd (.cmd (.assume l e md))
  | .cmd (.cmd (.cover l e md)) =>
    simp only [Stmt.exprsOKIn] at h ⊢
    simp only [Stmt.defUseWellFormed, HasVarsImp.readVars, CmdExt.readVars, Cmd.getVars,
      Bool.and_eq_true, List.all_eq_true] at hdu
    exact ExprOK.congr h fun y hy => hag y (hdu.1.1.1 y hy) (by
      first | exact hy | (simp only [Stmt.idents]; exact hy))
  | .cmd (.call ..) => simp [Stmt.exprsOKIn]
  | .block l ss md =>
    simp only [Stmt.exprsOKIn] at h ⊢
    simp only [Stmt.defUseWellFormed] at hdu
    exact Block.exprsOKIn_congr ss hdu hag h
  | .ite (.det g) ts es md =>
    simp only [Stmt.exprsOKIn] at h ⊢
    simp only [Stmt.defUseWellFormed, ExprOrNondet.getVars, Bool.and_eq_true,
      List.all_eq_true] at hdu
    exact ⟨ExprOK.congr h.1 fun y hy => hag y (hdu.1.1.1 y hy)
        (List.mem_append_left _ (List.mem_append_left _ hy)),
      Block.exprsOKIn_congr ts hdu.1.2 (fun y hy hm => hag y hy (by simp [Stmt.idents, hm]))
        h.2.1,
      Block.exprsOKIn_congr es hdu.2 (fun y hy hm => hag y hy (by simp [Stmt.idents, hm])) h.2.2⟩
  | .ite .nondet ts es md =>
    simp only [Stmt.exprsOKIn] at h ⊢
    simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
    exact ⟨Block.exprsOKIn_congr ts hdu.1.2 (fun y hy hm => hag y hy (by simp [Stmt.idents, hm]))
        h.1,
      Block.exprsOKIn_congr es hdu.2 (fun y hy hm => hag y hy (by simp [Stmt.idents, hm])) h.2⟩
  | .loop g m invs body md =>
    simp only [Stmt.exprsOKIn] at h ⊢
    simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
    exact Block.exprsOKIn_congr body hdu.2 (fun y hy hm => hag y hy (by simp [Stmt.idents, hm])) h
  | .exit l md => simp [Stmt.exprsOKIn]
  | .typeDecl tc md => simp [Stmt.exprsOKIn]
  termination_by sizeOf s

/-- **The typing of a list depends only on its defined names.** Two typings that agree on the
    names of the list that `D` counts as defined make a list that is def-use well-formed from
    `D` `exprsOKIn` alike. -/
private theorem Block.exprsOKIn_congr {F : Lambda.Factory CoreLParams} {fs : CoreIdent → Bool}
    (ss : List Statement) {D : CoreIdent → Bool} {Γ₁ Γ₂ : VarTyping Expression}
    (hdu : Block.defUseWellFormed (P := Expression) (C := Command) D fs ss = true)
    (hag : ∀ x, D x = true → x ∈ Block.idents ss → Γ₂ x = Γ₁ x) (h : Block.exprsOKIn F Γ₁ ss) :
    Block.exprsOKIn F Γ₂ ss := by
  match ss with
  | [] => simp [Block.exprsOKIn]
  | s :: rest =>
    simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
    simp only [Block.exprsOKIn] at h ⊢
    refine ⟨Stmt.exprsOKIn_congr s hdu.1 (fun x hx hm => hag x hx (by simp [Block.idents, hm]))
      h.1, Block.exprsOKIn_congr rest hdu.2 (fun x hx hr => extend_agree _ ?_) h.2⟩
    rcases Bool.or_eq_true_iff.1 hx with hD | hm
    · exact .inr (hag x hD (by simp [Block.idents, hr]))
    · exact .inl (mem_typedDefinedVars s x (of_decide_eq_true hm))
  termination_by sizeOf ss
end

/-- **The precondition holds of the restricted typing**, for a body def-use well-formed from
    the names bound in a store that binds none of the variables the body declares. -/
theorem BodyWF.restrict {F : Lambda.Factory CoreLParams} {Γ : VarTyping Expression}
    {ss : List Statement} {σ : CoreStore} {fs : CoreIdent → Bool} (h : BodyWF F Γ ss)
    (hdu : Block.defUseWellFormed (P := Expression) (C := Command) (fun x => (σ x).isSome) fs ss
      = true)
    (hdef : ∀ x ∈ Block.definedVars (P := Expression) (C := Command) ss false,
      (σ x).isNone = true) :
    BodyWF F (restrictTyping Γ ss) ss :=
  ⟨h.1, Block.exprsOKIn_congr ss hdu (fun x hx hi => by
    have hm : x ∉ Block.definedVars (P := Expression) (C := Command) ss false := fun hm => by
      have := hdef x hm; simp_all
    have he : x ∈ Block.entryVars ss := by
      rcases mem_touched_or_defined hi with h | h
      · exact List.mem_filter.mpr ⟨h, by simpa using hm⟩
      · exact absurd h hm
    exact restrictTyping_entry he) h.2⟩

end Core.Simplify
