/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Lean.ToExpr

import Lean.ToExpr
import all Strata.DDM.Util.Lean
import all Strata.DDM.Util.String

public section
namespace Strata

structure Decimal where
  mantissa : Int
  exponent : Int
deriving DecidableEq, Inhabited, Repr

namespace Decimal

def zero : Decimal := { mantissa := 0, exponent := 0 }

protected def ofInt (x : Int) : Decimal := { mantissa := x, exponent := 0 }

private opaque maxPrettyExponent : Int := 5

private opaque minPrettyExponent : Int := -5

def toString (d : Decimal) : String :=
  let m := d.mantissa
  let e := d.exponent
  if m = 0 then
    s!"0.0"
  else if e == 0 then
    s!"{m}.0"
  else if e > 0 ∧ e ≤ maxPrettyExponent then
    s!"{m}{String.replicate e.natAbs '0'}.0"
  else if e < 0 ∧ e ≥ minPrettyExponent then
    let ms := if m < 0 then "-" else ""
    let ma := m.natAbs
    let ne := 10^(-e).natAbs
    let md := ma % ne
    s!"{ms}{ma / ne}.{md}"
  else
    s!"{m}e{e}"

instance : ToString Decimal where
  toString := private Decimal.toString

section

open _root_.Lean

instance : ToExpr Decimal where
  toTypeExpr := mkConst ``Decimal
  toExpr d :=
    mkApp2 (mkConst ``Decimal.mk) (toExpr d.mantissa) (toExpr d.exponent)

private instance : Quote Decimal where
  quote d := Syntax.mkCApp ``Decimal.mk #[quote d.mantissa, quote d.exponent]

end

end Decimal

end Strata
