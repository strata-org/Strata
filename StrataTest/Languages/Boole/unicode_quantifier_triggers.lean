import Strata.Languages.Boole.Verify

open Strata

private def unicode_quantifier_program :=
#strata
program Boole;

function f(x : int): int;

axiom [ax_no_trigger]: ∀ x : int . f(x) > 0;
axiom [ax_with_trigger]: ∀ x : int . { f(x) } f(x) > 0;
axiom [ax_exists_no_trigger]: ∃ y : int . y == y;
axiom [ax_exists_with_trigger]: ∃ y : int . { f(y) } y == y;
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: function f (x : int) : int;
axiom [ax_no_trigger]: forall __q0 : int :: f(__q0) > 0;
axiom [ax_with_trigger]: forall __q0 : int ::  { f(__q0) }
  f(__q0) > 0;
axiom [ax_exists_no_trigger]: exists __q0 : int :: __q0 == __q0;
axiom [ax_exists_with_trigger]: exists __q0 : int ::  { f(__q0) }
  __q0 == __q0;
-/
#guard_msgs in
#eval Strata.Boole.typeCheck unicode_quantifier_program
