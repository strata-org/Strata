/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.DDM.Util.Decimal

namespace Strata

namespace Decimal


def toRat (d: Decimal) : Rat :=
  if d.exponent < 0 then mkRat d.mantissa (10 ^ (d.exponent).natAbs) else
  Rat.ofInt (d.mantissa * 10 ^ (d.exponent).natAbs)

/-- Check if a natural number has only factors of 2 and 5.-/
private def isTerminatingDenominator (d : Nat) : Bool :=
  let rec divideOut (n : Nat) (factor : Nat) (f_pos: 1 < factor) : Nat :=
    if h_n: n == 0 then n else
    if n % factor == 0 then
      have n_pos: 0 < n := by grind
      have: n / factor < n := Nat.div_lt_self n_pos f_pos
      divideOut (n / factor) factor f_pos else n
    termination_by n

  let afterDiv2 := divideOut d 2 (by omega)
  let afterDiv5 := divideOut afterDiv2 5 (by omega)
  afterDiv5 == 1

/-- Normalize a decimal representation by removing trailing zeros from the mantissa. -/
private def normalize (m : Int) (e : Int) : Decimal :=
  let rec removeTrailingZeros (mantissa : Int) (exponent : Int) : Decimal :=
    if hz: mantissa == 0 then
      { mantissa := 0, exponent := 0 }
    else if h_mod: mantissa % 10 == 0 then
      have : (mantissa / 10).natAbs < mantissa.natAbs := by grind
      removeTrailingZeros (mantissa / 10) (exponent + 1)
    else
      { mantissa := mantissa, exponent := exponent }
  termination_by mantissa.natAbs
  removeTrailingZeros m e

/-- Convert a rational number to a decimal representation.
    Returns `some` if the rational can be exactly represented as a terminating decimal, `none` otherwise (denominator has factors other than 2 and 5). -/
def fromRat (r : Rat) : Option Decimal :=
  if r.num == 0 then
    some zero
  else
    let n := r.num
    let d := r.den

    -- Check if denominator has only factors of 2 and 5
    if !isTerminatingDenominator d then
      none
    else
      -- Count factors of 2 and 5 in denominator
      let rec countFactor (num : Nat) (factor : Nat) (f_pos: 1 < factor) : Nat :=
        if h_n: num == 0 then 0 else
        if num % factor == 0 then
          have num_pos: 0 < num := by grind
          have: num / factor < num := Nat.div_lt_self num_pos f_pos
          1 + countFactor (num / factor) factor f_pos
        else 0
      termination_by num

      let count2 := countFactor d 2 (by omega)
      let count5 := countFactor d 5 (by omega)

      -- We need to multiply by 10^k where k = max(count2, count5)
      -- This makes the denominator divide evenly into 10^k
      let k := max count2 count5
      let powerOf10 := 10 ^ k
      let mantissa := (n * powerOf10) / d
      let exponent := -(k : Int)
      some (normalize mantissa exponent)

#guard Decimal.fromRat (5 : Rat) = some (Decimal.mk 5 0)
#guard Decimal.fromRat (0 : Rat) = some Decimal.zero
#guard Decimal.fromRat (-3 : Rat) = some (Decimal.mk (-3) 0)
#guard Decimal.fromRat (1/2 : Rat) = some (Decimal.mk 5 (-1))
#guard Decimal.fromRat (1/4 : Rat) = some (Decimal.mk 25 (-2))
#guard Decimal.fromRat (7/20 : Rat) = some (Decimal.mk 35 (-2))
#guard Decimal.fromRat (-1/2 : Rat) = some (Decimal.mk (-5) (-1))
#guard Decimal.fromRat (-7/8 : Rat) = some (Decimal.mk (-875) (-3))
#guard Decimal.fromRat (5/2 : Rat) = some (Decimal.mk 25 (-1))
#guard Decimal.fromRat (15/8 : Rat) = some (Decimal.mk 1875 (-3))
#guard Decimal.fromRat (1/3 : Rat) = none
#guard Decimal.fromRat (1/7 : Rat) = none

#guard Decimal.fromRat (Decimal.mk 5 0).toRat = some (Decimal.mk 5 0)
#guard Decimal.fromRat (Decimal.mk 25 (-1)).toRat = some (Decimal.mk 25 (-1))
#guard Decimal.fromRat (Decimal.mk 375 (-3)).toRat = some (Decimal.mk 375 (-3))
#guard Decimal.fromRat (Decimal.mk (-75) (-2)).toRat = some (Decimal.mk (-75) (-2))
#guard Decimal.fromRat (Decimal.mk 100 (-2)).toRat = some (Decimal.mk 1 0)
#guard (Decimal.fromRat (5 : Rat)).get!.toRat = (5 : Rat)
#guard (Decimal.fromRat (1/2 : Rat)).get!.toRat = (1/2 : Rat)
#guard (Decimal.fromRat (22/5 : Rat)).get!.toRat = (22/5 : Rat)

end Decimal
end Strata
