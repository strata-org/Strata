/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

def beq_eq_DecidableEq
  {T : Type}
  (beq : T → T → Bool)
  (beq_eq : (x1 x2 : T) → beq x1 x2 = true ↔ x1 = x2) :
  DecidableEq T :=
  fun x1 x2 =>
    let eq := beq_eq x1 x2
    if h: beq x1 x2 then
      isTrue (eq.mp h)
    else
      isFalse (fun heq => h (eq.mpr heq))
