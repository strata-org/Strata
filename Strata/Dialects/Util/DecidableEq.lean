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

/--
Solves goals of the form `beq e1 e2 = true ↔ e1 = e2` if `beq` is
marked with `@[grind]`.
-/
syntax "solve_beq" ident ident  : tactic
macro_rules
  | `(tactic|solve_beq $e1:ident $e2:ident) =>
  `(tactic|
    constructor <;> intro h <;>
    try (induction $e1:ident generalizing $e2 <;> cases $e2:ident <;> grind) <;>
    (subst_vars; induction $e2:ident <;> grind)
  )
