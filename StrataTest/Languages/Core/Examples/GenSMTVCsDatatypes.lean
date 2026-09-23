/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.MetaVerifier

/-!
`gen_smt_vcs` on programs with datatypes: each SMT datatype becomes a Lean
inductive `Strata.SMT.DT.<name>`, with testers `is_<ctor>` and selectors
defined by `casesOn`, so constructor applications, testers and selectors in
the VCs translate to ordinary Lean terms.
-/

namespace Strata

def dtPgm :=
#strata
program Core;

datatype Option () { None(), Some(val: int) };
datatype IntList () { Nil(), Cons(head: int, tail: IntList) };
datatype Wrap () { W(inner: Option) };

procedure Test(o : Option, l : IntList, out y : int)
spec {
  requires [pre]: Option..isSome(o) && IntList..isCons(l);
  ensures [ens]: y == int.add(Option..val(o), IntList..head(l));
}
{
  var o2 : Option;
  o2 := Some(Option..val(o));
  assert [roundtrip]: o2 == o;
  assert [nested]: IntList..isCons(Cons(Option..val(o), IntList..tail(l)));
  y := int.add(Option..val(o2), IntList..head(l));
};

// `Option` is already declared by the goals of `Test` when this procedure's
// goal is created; the selector `inner : Wrap → Option` still needs a default
// element of `Option`.
procedure Unwrap(w : Wrap, out y : int)
spec {
  requires [pre]: Option..isSome(Wrap..inner(w));
  ensures [ens]: y == Option..val(Wrap..inner(w));
}
{
  y := Option..val(Wrap..inner(w));
};
#end

theorem dtPgm_correct : smtVCsCorrect dtPgm := by
  gen_smt_vcs
  case roundtrip =>
    intro l o h
    cases o with
    | None => simp [dtPgm_correct.DT.Option.is_Some] at h
    | Some v => rfl
  all_goals (intros; trivial)

end Strata
