/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Core
meta import Strata.Languages.Core.DDMTransform.Translate
import Strata.DDM.Integration.Lean.HashCommands

meta section

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
axiom [axiom_0]: forall f : int -> int :: forall x : int :: apply(f, x) == f(x);
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
  ensures [Check_ensures_0]: result == forall f : int -> int :: forall x : int :: apply(f, x) == f(x);
  } {
  result := true;
};
-/
#guard_msgs in
#eval (Std.format ((Core.typeCheck .default (translate quantifierApplyBoundVar).stripMetaData)))

end
