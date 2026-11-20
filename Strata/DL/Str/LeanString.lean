/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Str.Predicates

/-! # Lean strings as code-point strings

A Lean `String` is a sequence of scalar values, so it is exactly a code-point string
satisfying `scalar`: `ofLeanString` reads one as its code points, and
`toLeanString?` reads a code-point string back when every element is a scalar value.
The two are inverse (proved in `Strata.DL.Str.LeanStringProps`: `toLeanString?_ofLeanString`, `ofLeanString_of_toLeanString?`),
which lets an interactive proof state its lemmas over Lean strings. -/

@[expose] public section

namespace Strata.Str

/-- The code points of a Lean string. -/
def ofLeanString (s : String) : List Nat := s.toList.map Char.toNat

/-- The Lean string whose code points are `cs`, when every one is a scalar value. -/
def toLeanString? (cs : List Nat) : Option String :=
  if scalar cs then some (String.ofList (cs.map Char.ofNat)) else none

end Strata.Str

end
