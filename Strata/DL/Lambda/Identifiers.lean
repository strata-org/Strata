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
structure Identifier (IDMeta : Type) : Type where
  name : String
  metadata : IDMeta
deriving Repr, DecidableEq, Inhabited

instance : ToFormat (Identifier IDMeta) where
  format i := i.name

instance : ToString (Identifier IDMeta) where
  toString i := i.name

instance {IDMeta} [Inhabited IDMeta] : Coe String (Identifier IDMeta) where
  coe s := ⟨s, Inhabited.default⟩

abbrev IdentT (IDMeta : Type) := (Identifier IDMeta) × Option LMonoTy
abbrev IdentTs (IDMeta : Type) := List (IdentT IDMeta)

instance {IDMeta : Type} : ToFormat (IdentT IDMeta) where
  format i := match i.snd with
    | none => f!"{i.fst}"
    | some ty => f!"({i.fst} : {ty})"

def IdentT.ident (x : (IdentT IDMeta)) : Identifier IDMeta :=
  x.fst

def IdentT.monoty? (x : (IdentT IDMeta)) : Option LMonoTy :=
  x.snd

def IdentTs.idents (xs : (IdentTs IDMeta)) : List (Identifier IDMeta) :=
  xs.map Prod.fst

def IdentTs.monotys? (xs : (IdentTs IDMeta)) : List (Option LMonoTy) :=
  xs.map Prod.snd

---------------------------------------------------------------------

end Identifiers
end Lambda
