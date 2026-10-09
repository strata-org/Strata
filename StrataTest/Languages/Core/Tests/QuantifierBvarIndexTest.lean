/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
import StrataDDM.Integration.Lean.HashCommands

meta section

open Core
open Strata

def translate (t : StrataDDM.Program) : Core.Program :=
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
axiom [axiom_0]: forall f : (int -> int) :: forall x : int :: apply(f, x) == f(x);
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
  ensures [Check_ensures_0]: result == forall f : (int -> int) :: forall x : int :: apply(f, x) == f(x);
  } {
  result := true;
};
-/
#guard_msgs in
#eval (Std.format ((Core.typeCheck .default (translate quantifierApplyBoundVar).stripMetaData)))

/-! ## Applied local-function parameters under nested binders

Local-function parameters are stored as placeholder bvars while translating the
body. An applied parameter must be re-indexed to its current DDM binder index,
just like a zero-argument parameter reference. Otherwise, a binder introduced
by `have`, `fun`, or a quantifier can make an application select a later
parameter instead.
-/

def localFunctionAppliedBvar :=
#strata
program Core;

procedure Check()
{
  function underHave(g : int -> int, h : int -> int, x : int) : int
    { have c : int = x in g(c) }
  function underLambda(g : int -> int, h : int -> int, x : int) : int
    { (fun c : int => g(c))(x) }
  function underQuantifier(p : int -> bool, q : int -> bool) : bool
    { forall x : int :: p(x) }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure Check ()
{
  var underHave : (int -> int) -> (int -> int) -> int -> int := fun g : (int -> int) => fun h : (int -> int) => fun x : int => (fun c : int => g(c))(x);
  var underLambda : (int -> int) -> (int -> int) -> int -> int := fun g : (int -> int) => fun h : (int -> int) => fun x : int => (fun c : int => g(c))(x);
  var underQuantifier : (int -> bool) -> (int -> bool) -> bool := fun p : (int -> bool) => fun q : (int -> bool) => forall x : int :: p(x);
};
-/
#guard_msgs in
#eval (Std.format ((Core.typeCheck .default (translate localFunctionAppliedBvar).stripMetaData)))

end
