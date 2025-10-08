/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Lambda.LTy
import Strata.DL.Util.Map

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)

section Identifiers

/--
Identifiers, optionally with their inferred monotype.
-/
abbrev IdentT (Identifier : Type) (ExtraRestrict : Type := Empty) := Identifier × Option (LMonoTy ExtraRestrict)
abbrev IdentTs (Identifier ExtraRestrict : Type) := List (IdentT Identifier ExtraRestrict)

instance {Identifier ExtraRestrict : Type} [ToFormat Identifier] : ToFormat (IdentT Identifier ExtraRestrict) where
  format i := match i.snd with
    | none => f!"{i.fst}"
    | some ty => f!"({i.fst} : {ty})"

def IdentT.ident (x : (IdentT Identifier ExtraRestrict)) : Identifier :=
  x.fst

def IdentT.monoty? (x : (IdentT Identifier ExtraRestrict)) : Option (LMonoTy ExtraRestrict) :=
  x.snd

def IdentTs.idents (xs : (IdentTs Identifier ExtraRestrict)) : List Identifier :=
  xs.map Prod.fst

def IdentTs.monotys? (xs : (IdentTs Identifier ExtraRestrict)) : List (Option (LMonoTy ExtraRestrict)) :=
  xs.map Prod.snd

---------------------------------------------------------------------

end Identifiers
end Lambda
