/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def regexPgm :=
#strata
program Boogie;

function cannot_end_with_period () : regex {
  re.comp(re.concat (re.* (re.all()), str.to.re(".")))
}

procedure main() returns () {

    assert (!(str.in.re("hello.", cannot_end_with_period())));
    assert (!(str.in.re(".",      cannot_end_with_period())));
    assert   (str.in.re("bye!",   cannot_end_with_period()));

};
#end

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: assert_0
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #hello.) ~cannot_end_with_period))

Label: assert_1
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #.) ~cannot_end_with_period))

Label: assert_2
Assumptions:


Proof Obligation:
((~Str.InRegEx #bye!) ~cannot_end_with_period)

Wrote problem to vcs/assert_0.smt2.
Wrote problem to vcs/assert_1.smt2.
Wrote problem to vcs/assert_2.smt2.
---
info:
Obligation: assert_0
Result: verified

Obligation: assert_1
Result: verified

Obligation: assert_2
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" regexPgm

---------------------------------------------------------------------
