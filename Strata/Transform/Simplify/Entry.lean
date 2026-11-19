/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify.DeadDefsShape
public import Strata.Languages.Core.InstWellFormedSemanticsEval

/-! # The relations the Simplify simulation is stated over

The simulation of a simplified body relates a run of the original body to a run of the
simplified one. Both runs start in the same environment (`EntryRel`), and finish in
environments that agree on every live name (`EnvAgreeOnLive`).

`Γ` types the variables the body reads or writes without declaring them, which are the
ones whose values come from the entry store (`Block.entryVars`). The body's locals are typed
as they are declared, scope by scope, so sibling scopes may declare the same name at
different types.
-/

namespace Core.Simplify

open Imperative

public section

/-- Every entry variable of the body `ss` that the store `σ` binds holds a value of the type
    `Γ` gives it, under the factory `f`.

    Only bound variables are constrained. Only entry variables are constrained, so the store
    may bind anything else (a name the body never mentions, or one it declares, which the
    gate requires to be unbound anyway) whatever `Γ` says about it. -/
@[expose] def StoreTypedBy (f : Expression.Factory) (Γ : VarTyping Expression)
    (ss : List Statement) (σ : CoreStore) : Prop :=
  ∀ x ∈ Block.entryVars ss, ∀ v, σ x = some v →
    ∃ ty, Γ x = some ty ∧ HasVal.valueOfTy f v ty

/-- **The entry relation.** Both runs start in the same environment. Its factory is a model
    of the factory `F` that Simplify folds against, and its store gives the variables of
    `ss` their `Γ` types. -/
@[expose] def EntryRel (F : Lambda.Factory CoreLParams) (Γ : VarTyping Expression)
    (ss : List Statement) (ρ ρ' : Imperative.Env Expression) : Prop :=
  ρ' = ρ ∧ ρ.factory.factory = F ∧ StoreTypedBy ρ.factory Γ ss ρ.store

/-- **The output relation.** The two final stores agree at every live name, bound or not,
    and the two factories are the same. -/
@[expose] def EnvAgreeOnLive (live : Std.HashSet String)
    (ρ ρ' : Imperative.Env Expression) : Prop :=
  (∀ x : CoreIdent, Live live x → ρ'.store x = ρ.store x) ∧ ρ'.factory = ρ.factory

/-- `EntryRel` admits environments: one that binds none of the body's entry variables is
    related to itself. -/
private theorem EntryRel.of_untouched {F : Lambda.Factory CoreLParams} {Γ : VarTyping Expression}
    {ss : List Statement} {ρ : Imperative.Env Expression} (hF : ρ.factory.factory = F)
    (hσ : ∀ x ∈ Block.entryVars ss, ρ.store x = none) : EntryRel F Γ ss ρ ρ :=
  ⟨rfl, hF, fun x hx v hv => by rw [hσ x hx] at hv; cases hv⟩

end

end Core.Simplify
