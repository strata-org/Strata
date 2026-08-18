/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Init.Data.Repr

public section

/-! ## String / Nat Utilities

General-purpose definitions and lemmas for parsing and printing natural numbers
as decimal strings, and for `List.isPrefixOf` on `Char` lists.

These are used by the Lambda type-inference machinery (`LExprTypeEnv.lean`,
`LExprTypeSpec.lean`) but are not Lambda-specific.
-/

/-! ### Parsing: `listCharToNatAux` and `listCharToNat?` -/

/-- Parse a `List Char` of decimal digits as a natural number.
    Returns `none` for empty or non-digit input. -/
def listCharToNatAux : Nat → List Char → Option Nat
  | acc, [] => some acc
  | acc, c :: cs =>
    if '0' ≤ c ∧ c ≤ '9' then
      listCharToNatAux (acc * 10 + (c.toNat - '0'.toNat)) cs
    else none


/-- Parse a non-empty `List Char` of decimal digits as a natural number. -/
def listCharToNat? (cs : List Char) : Option Nat :=
  match cs with
  | [] => none
  | _ => listCharToNatAux 0 cs


/-! ### Printing: structurally recursive digit generation

`Nat.toDigitsCore` uses `brecOn` (bounded recursion on Nat), which is hard to
reason about directly. We define an equivalent structurally recursive version
and prove it equal to `Nat.toDigitsCore`. -/

def digitLoop : Nat → Nat → List Char → List Char
  | 0, _, ds => ds
  | fuel + 1, n, ds =>
    let d := (n % 10).digitChar
    let n' := n / 10
    if n' = 0 then d :: ds else digitLoop fuel n' (d :: ds)


end
