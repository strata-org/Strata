/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BigStep.Sem

/-! # Properties of the big-step semantics of loop-free and obligation programs

Inversions of the command semantics `EvalE` for `init`, `assume`, `assert` and `cover`, and the
effect of a store update.

Key theorems: `evalE_init_det_inv`, `evalE_init_nondet_inv`, `evalE_assume_inv`,
`evalE_assert_inv`, `evalE_cover_inv`, `update_facts`. -/

namespace Imperative
namespace BigStep

public section

variable {P : PureExpr} [HasBool P] [HasFvar P]

section
variable [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
  [LawfulHasVal P]

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [LawfulHasVal P] in
/-- A deterministic `init x : ty := e` step evaluates `e` to a value `v` of type `ty`
    (`HasVal.valueOfTy F v ty`), defines the undefined `x` as `v`, leaves the other
    variables unchanged and emits no event. -/
theorem evalE_init_det_inv_typed {F : P.Factory} {σ σ1 : SemanticStore P}
    {x : P.Ident} {ty : P.Ty} {e : P.Expr} {md : MetaData P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.init x ty (.det e) md)) σ1 evs) :
    ∃ v, P.eval F σ e = some v ∧ σ x = none ∧ σ1 x = some v ∧ (∀ y, x ≠ y → σ1 y = σ y) ∧
      evs = [] ∧ HasVal.valueOfTy F v ty :=
  match h with | .eval_init hev (.init h0 h1 hfr) hty _ => ⟨_, hev, h0, h1, hfr, rfl, hty⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [LawfulHasVal P] in
/-- A nondeterministic `init x : ty` step defines the undefined `x` as some value `v` of
    type `ty`, leaves the other variables unchanged and emits no event. -/
private theorem evalE_init_nondet_inv_typed {F : P.Factory} {σ σ1 : SemanticStore P}
    {x : P.Ident} {ty : P.Ty} {md : MetaData P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.init x ty .nondet md)) σ1 evs) :
    ∃ v, HasVal.valueOfTy F v ty ∧ σ x = none ∧ σ1 x = some v ∧
      (∀ y, x ≠ y → σ1 y = σ y) ∧ evs = [] :=
  match h with | .eval_init_unconstrained (.init h0 h1 hfr) hty _ => ⟨_, hty, h0, h1, hfr, rfl⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [LawfulHasVal P] in
/-- A deterministic `init x := e` step evaluates `e` to a value `v`, defines the
    undefined `x` as `v`, leaves the other variables unchanged and emits no event. -/
theorem evalE_init_det_inv {F : P.Factory} {σ σ1 : SemanticStore P}
    {x : P.Ident} {ty : P.Ty} {e : P.Expr} {md : MetaData P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.init x ty (.det e) md)) σ1 evs) :
    ∃ v, P.eval F σ e = some v ∧ σ x = none ∧ σ1 x = some v ∧ (∀ y, x ≠ y → σ1 y = σ y) ∧
      evs = [] :=
  (evalE_init_det_inv_typed h).imp fun _ ⟨hev, h0, h1, hfr, he, _⟩ => ⟨hev, h0, h1, hfr, he⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    in
/-- A nondeterministic `init x` step defines the undefined `x` as some value `v`,
    leaves the other variables unchanged and emits no event. -/
theorem evalE_init_nondet_inv {F : P.Factory} {σ σ1 : SemanticStore P}
    {x : P.Ident} {ty : P.Ty} {md : MetaData P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.init x ty .nondet md)) σ1 evs) :
    ∃ v, HasVal.value F v ∧ σ x = none ∧ σ1 x = some v ∧
      (∀ y, x ≠ y → σ1 y = σ y) ∧ evs = [] :=
  (evalE_init_nondet_inv_typed h).imp fun _ ⟨hty, hrest⟩ =>
    ⟨LawfulHasVal.valueOfTy_isVal _ _ _ hty, hrest⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [LawfulHasVal P] in
/-- An `assume` step keeps the store and emits its assumption event. -/
theorem evalE_assume_inv {F : P.Factory} {σ σ1 : SemanticStore P}
    {l : String} {e : P.Expr} {md : MetaData P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.assume l e md)) σ1 evs) :
    σ1 = σ ∧
      evs = [.assume { factory := F, store := σ, label := l, expr := e, metadata := md }] :=
  match h with | .eval_assume => ⟨rfl, rfl⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [LawfulHasVal P] in
/-- An `assert` step keeps the store and emits its assertion event. -/
theorem evalE_assert_inv {F : P.Factory} {σ σ1 : SemanticStore P}
    {l : String} {e : P.Expr} {md : MetaData P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.assert l e md)) σ1 evs) :
    σ1 = σ ∧
      evs = [.assert { factory := F, store := σ, label := l, expr := e, metadata := md }] :=
  match h with | .eval_assert => ⟨rfl, rfl⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [LawfulHasVal P] in
/-- A `cover` step keeps the store and emits its cover event. -/
theorem evalE_cover_inv {F : P.Factory} {σ σ1 : SemanticStore P}
    {l : String} {e : P.Expr} {md : MetaData P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.cover l e md)) σ1 evs) :
    σ1 = σ ∧
      evs = [.cover { factory := F, store := σ, label := l, expr := e, metadata := md }] :=
  match h with | .eval_cover => ⟨rfl, rfl⟩

omit [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P] [HasFvar P]
    [LawfulHasVal P] in
/-- Updating `x` to `v` maps `x` to `v` and leaves the other variables unchanged. -/
theorem update_facts (σ : SemanticStore P) (x : P.Ident) (v : P.Expr) :
    Imperative.SemanticStore.update σ x v x = some v ∧
      (∀ y, x ≠ y → Imperative.SemanticStore.update σ x v y = σ y) :=
  ⟨by simp [SemanticStore.update], fun y hy => by simp [SemanticStore.update, Ne.symm hy]⟩

end

end -- public section

end BigStep
end Imperative
