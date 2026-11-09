/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.RegexMatch
import all Strata.DL.SMT.RegexMatch

/-! # Properties of the SMT-LIB regex matcher

Key theorem: `derivNullable_snd`. -/

public section

namespace Strata.SMT.Regex.Re

/-- The flag `derivNullable c r` returns is `r.nullable`, for every
    character `c`. -/
theorem derivNullable_snd (c : Char) (r : Re) :
    (derivNullable c r).2 = r.nullable := by
  induction r with
  | str s => cases s <;> rfl
  | cat a b iha ihb | union a b iha ihb | inter a b iha ihb =>
    simp only [derivNullable, nullable, ← iha, ← ihb]
  | comp a ih | loop a lo hi ih => simp only [derivNullable, nullable, ← ih]
  | _ => rfl

end Strata.SMT.Regex.Re

end
