/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Util.Map

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)

section Identifiers

/--
Identifiers, optionally with their type.
-/
abbrev IdentT (Identifier : Type) (TypeType : Type) := Identifier × Option TypeType
abbrev IdentTs (Identifier : Type) (TypeType : Type) := List (IdentT Identifier TypeType)

instance {Identifier : Type} [ToFormat Identifier]
         {TypeType : Type} [ToFormat TypeType]:
    ToFormat (IdentT Identifier TypeType) where
  format i := match i.snd with
    | none => f!"{i.fst}"
    | some ty => f!"({i.fst} : {ty})"

def IdentT.ident {Identifier TypeType} (x : (IdentT Identifier TypeType)) : Identifier :=
  x.fst

def IdentT.type? {Identifier TypeType} (x : (IdentT Identifier TypeType)) :
    Option TypeType :=
  x.snd

def IdentTs.idents {Identifier TypeType} (xs : (IdentTs Identifier TypeType)) :
    List Identifier :=
  xs.map Prod.fst

def IdentTs.types? {Identifier TypeType} (xs : (IdentTs Identifier TypeType)) :
    List (Option TypeType) :=
  xs.map Prod.snd

---------------------------------------------------------------------

end Identifiers
end Lambda
