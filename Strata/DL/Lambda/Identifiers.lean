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
abbrev IdentT (Identifier : Type) := Identifier × Option LMonoTy
abbrev IdentTs (Identifier : Type) := Map Identifier (Option LMonoTy)

instance {Identifier : Type} [ToFormat Identifier] : ToFormat (IdentT Identifier) where
  format i := match i.snd with
    | none => f!"{i.fst}"
    | some ty => f!"({i.fst} : {ty})"

def IdentT.ident (x : (IdentT Identifier)) : Identifier :=
  x.fst

def IdentT.monoty? (x : (IdentT Identifier)) : Option LMonoTy :=
  x.snd

def IdentTs.idents (xs : (IdentTs Identifier)) : List Identifier :=
  xs.keys

def IdentTs.monotys? (xs : (IdentTs Identifier)) : List (Option LMonoTy) :=
  xs.values

---------------------------------------------------------------------

end Identifiers
end Lambda
