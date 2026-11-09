/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Expressions
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.NamePrefixes

/-! ## Conditions kept while registering functions and datatypes

`FactorySigsAllowed`: every factory signature names only type constructors
without a reserved prefix. `AliasNamesFresh`: no type-alias name is a
registered type. -/

namespace Core

open Lambda

public section

/-- Every input and output type of every function in the factory of `C` names
    only type constructors whose names start with no reserved prefix. -/
@[expose] def FactorySigsAllowed (C : Expression.TyContext) : Prop :=
  ∀ f ∈ C.functions.toArray, ∀ ty ∈ f.output :: f.inputs.values,
    mtyAllTyConsNames isAllowedName ty = true

/-- No alias name of `Γ` is a registered type of `C`. -/
@[expose] def AliasNamesFresh (C : Expression.TyContext)
    (Γ : TContext Unit) : Prop :=
  ∀ al ∈ Γ.aliases, al.name ∉ C.knownTypes

end -- public section

end Core
