/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPCoreDefs
public import Strata.Transform.Passive.CoreTyped
public import Strata.Transform.WP.WPOutTyping
import Strata.Transform.WP.WPOutTypingWalk

/-! # The output of the WP phase is well typed

The WP phase keeps a well-typed Core statement list well typed: when `ss` is well typed under
the types `tys` of its free variables (`Statements.WellTyped`), so is its guarded program `w.lay`,
under the typing of the free variables of `ss` by `tys` (`fvTyping`) (`wpEntry_wellTyped`).

Core expressions with ground monomorphic types have the typing laws the proof needs
(`typingLaws`).

Key definitions: `fvTyping`.

Key theorems: `typingLaws`, `wpEntry_wellTyped`. -/

namespace Core
namespace WP

open Imperative Imperative.WP

public section

/-- The typing of the free variables of `ss` by the types `tys`: the free variables of `ss` have
    their types in `tys`, no other name has a type. -/
@[expose] def fvTyping (tys : Tys Expression) (ss : Statements) : VarTyping Expression :=
  fun x => if x ∈ Block.freeVars ss then tys.get? x else none

/-- **The typing laws of Core expressions with ground monomorphic types**: those of
    `Core.typedLaws`, the Boolean literals are Boolean, a typed expression has a ground
    monomorphic type, and a variable annotated with a ground monomorphic type has that type. -/
theorem typingLaws : TypingLaws (P := Expression) Expression.Typed
    (fun ty => ∃ τ, ty.toMonoType? = some τ ∧ τ.IsGround) where
  toTypedLaws := typedLaws
  tt := ⟨.bool, boolTy_toMonoType, rfl, fun _ _ h => by
    simp [Imperative.WP.tt, HasBool.tt, Core.true, Lambda.LExpr.boolConst,
      Lambda.LExpr.freeVars] at h, .const rfl⟩
  ff := ⟨.bool, boolTy_toMonoType, rfl, fun _ _ h => by
    simp [Imperative.WP.ff, HasBool.ff, Core.false, Lambda.LExpr.boolConst,
      Lambda.LExpr.freeVars] at h, .const rfl⟩
  ground h := let ⟨τ, h1, h2, _⟩ := h; ⟨τ, h1, h2⟩
  mkVar x ty h := by
    obtain ⟨τ, h1, h2⟩ := h
    refine ⟨τ, h1, h2, fun z τz hz => ?_, ?_⟩
    · simp only [HasFvar.mkVar, HasFvar.mkTypedFvar, h1, Lambda.LExpr.freeVars,
        List.mem_singleton, Prod.mk.injEq] at hz
      exact ⟨τ, hz.2, h2⟩
    · simp only [HasFvar.mkVar, HasFvar.mkTypedFvar, h1]
      exact .fvar

/-- **The WP phase keeps a statement list well typed.**  For a Core statement list `ss` meeting
    the syntactic precondition `WPPre tys ss`, well typed under the types `tys` of its free
    variables, the guarded program `w.lay` of its WP phase is well typed under the typing of the
    free variables of `ss` by `tys`. -/
theorem wpEntry_wellTyped {G : IdSet Expression} {tys : Tys Expression} {ss : Statements}
    {w : WOut Expression} (h : wpEntry G tys ss = .ok w) (hpre : WPPre tys ss)
    (htyp : Statements.WellTyped (fun x => tys.get? x) ss) :
    Statements.WellTyped (fvTyping tys ss) w.lay :=
  wpEntry_wellTyped_of typingLaws h hpre.2.1 hpre.1 htyp

end -- public section

end WP
end Core
