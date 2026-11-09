/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Env
public import Strata.DL.Lambda.TypeFactoryProps
import all Strata.Languages.Core.Env
import all Strata.DL.Lambda.LState

/-! # Properties of the Core evaluation environment

Registering datatypes in an environment adds only constructors of those datatypes, so it
keeps the property that no constructor of the environment's factory produces a Boolean,
when no registered datatype is named `bool`.

Key theorem: `Env.addDatatypes_constrsNotBool`. -/

namespace Core

public section

/-- Registering a block of datatypes, none named `bool`, keeps `ConstrsNotBool` of the
    environment's factory. -/
private theorem Env.addMutualDatatype_constrsNotBool {E E' : Env}
    {block : Lambda.MutualDatatype Unit}
    (hE : E.factory.ConstrsNotBool) (hname : ∀ d ∈ block, d.name ≠ "bool")
    (h : E.addMutualDatatype block = .ok E') : E'.factory.ConstrsNotBool := by
  simp only [Env.addMutualDatatype, Env.addFactory, Lambda.LState.addFactory, bind,
    Except.bind, pure, Except.pure] at h
  cases hG : Lambda.genBlockFactory (T := CoreLParams) block with
  | error => simp [hG] at h
  | ok G =>
    cases hF : E.factory.addFactory G with
    | error => simp_all [Env.factory]
    | ok F =>
      simp only [hG, Env.factory] at h hF
      simp only [hF, Except.ok.injEq] at h
      subst h
      exact hE.addFactory_genBlockFactory hname hG hF

/-- **Registering datatypes keeps `ConstrsNotBool`.**  If `E`'s factory has no
    Boolean-producing constructor and no datatype in `blocks` is named `bool`, the
    environment `E'` that `Env.addDatatypes` returns has a factory with none either. -/
theorem Env.addDatatypes_constrsNotBool {E E' : Env} {blocks : List (Lambda.MutualDatatype Unit)}
    (hE : E.factory.ConstrsNotBool) (hname : ∀ b ∈ blocks, ∀ d ∈ b, d.name ≠ "bool")
    (h : E.addDatatypes blocks = .ok E') : E'.factory.ConstrsNotBool := by
  induction blocks generalizing E with
  | nil => cases h; exact hE
  | cons b bs ih =>
    simp only [Env.addDatatypes, List.foldlM_cons, bind, Except.bind] at h ih
    split at h
    · cases h
    · rename_i E1 h1
      exact ih (Env.addMutualDatatype_constrsNotBool hE (hname b (by simp)) h1)
        (fun b' hb' => hname b' (by simp [hb'])) h

end -- public section

end Core
