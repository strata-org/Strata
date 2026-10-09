/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.MetaVerifier

/-!
`gen_smt_vcs` on programs with datatypes. `#strata_datatypes prog` declares each
datatype of `prog` as a Lean inductive `prog.DT.<name>`, with testers
`is_<ctor>` and selectors defined by `casesOn`, so constructor applications,
testers and selectors in the VCs translate to ordinary Lean terms.
-/

namespace Strata

def dtPgm :=
#strata
program Core;

datatype Option () { None(), Some(val: int) };
datatype IntList () { Nil(), Cons(head: int, tail: IntList) };
datatype Wrap () { W(inner: Option) };
datatype MyNat () { Zero(), Succ(pred: MyNat) };
// Used by no VC; `#strata_datatypes` declares it all the same.
datatype Color () { Red(), Green() };

// A recursive function over a datatype: its termination and selector
// well-formedness VCs become goals about the inductive itself.
rec function depth(@[cases] n : MyNat) : int
  decreases n
{
  if MyNat..isZero(n) then 0 else int.add(1, depth(MyNat..pred(n)))
};

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

procedure Depth(n : MyNat, out d : int)
spec {
  ensures [ens]: d == depth(n);
}
{
  d := depth(n);
};

procedure Unwrap(w : Wrap, out y : int)
spec {
  requires [pre]: Option..isSome(Wrap..inner(w));
  ensures [ens]: y == Option..val(Wrap..inner(w));
}
{
  y := Option..val(Wrap..inner(w));
};
#end

#strata_datatypes dtPgm

/-- info: Strata.dtPgm.DT.Color.Green : dtPgm.DT.Color -/
#guard_msgs in
#check dtPgm.DT.Color.Green

/-- The goals are ordinary statements about the generated inductives.  For the
    recursive function the two are that the constructors are exhaustive and that
    a selector's result ranks below the constructor it came from; elsewhere a
    hypothesis already carries the tester a selector needs, or a constructor's
    own selector round-trips. -/
theorem dtPgm_correct : smtVCsCorrect dtPgm := by
  gen_smt_vcs
  case «depth_body_calls_MyNat..pred_0» =>
    intro n; intros
    cases n <;> simp_all [dtPgm.DT.MyNat.is_Zero, dtPgm.DT.MyNat.is_Succ]
  case depth_terminates_0 =>
    intro n; intros
    cases n <;> simp_all [dtPgm.DT.MyNat.is_Zero, dtPgm.DT.MyNat.pred]
  case roundtrip =>
    intro _ o; intros
    cases o with
    | None => simp_all [dtPgm.DT.Option.is_Some]
    | Some v => rfl
  all_goals (intros; simp_all [dtPgm.DT.Option.is_Some, dtPgm.DT.IntList.is_Cons])

/-- A program whose VCs use a datatype that `#strata_datatypes` has not declared. -/
def undeclaredPgm :=
#strata
program Core;

datatype Box () { B(v: int) };

procedure Get(b : Box)
{
  assert [eta]: B(Box..v(b)) == b;
};
#end

/-- error: gen_smt_vcs: datatype 'Box' is not declared; run `#strata_datatypes Strata.undeclaredPgm` before this proof -/
#guard_msgs in
example : smtVCsCorrect undeclaredPgm := by
  gen_smt_vcs

end Strata
