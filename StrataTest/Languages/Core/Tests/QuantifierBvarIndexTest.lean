/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate

open Core
open Strata

def translate (t : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

/-! ## Regression test for #1038 (https://github.com/strata-org/Strata/issues/1038)

`translateQuantifier` assigned placeholder bvar indices left-to-right via
`mapIdx` (0, 1, …), but `foldr` nests quantifiers right-to-left, so the de
Bruijn indices ended up reversed.
-/

-- Axiom-level quantifier with bound variable application
def axiomApplyBoundVar :=
#strata
program Core;

function apply(f : int -> int, x : int) : int;
axiom forall f : int -> int, x : int :: apply(f, x) == f(x);
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function apply (f : int -> int, x : int) : int;
axiom [axiom_0]: forall __q0 : int -> int :: forall __q1 : int :: apply(__q0, __q1) == __q0(__q1);
-/
#guard_msgs in
#eval (Std.format ((Core.typeCheck .default (translate axiomApplyBoundVar).stripMetaData)))

-- Expression-level quantifier with bound variable application (no axiom needed)
def quantifierApplyBoundVar :=
#strata
program Core;

function apply(f : int -> int, x : int) : int
{
  f(x)
}

procedure Check(out result: bool)
spec {
  ensures result == (forall f : int -> int, x : int :: apply(f, x) == f(x));
}
{
  result := true;
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function apply (f : int -> int, x : int) : int {
  f(x)
}
procedure Check (out result : bool)
spec {
  ensures [Check_ensures_0]: result == forall __q0 : int -> int :: forall __q1 : int :: apply(__q0, __q1) == __q0(__q1);
  } {
  result := true;
};
-/
#guard_msgs in
#eval (Std.format ((Core.typeCheck .default (translate quantifierApplyBoundVar).stripMetaData)))
