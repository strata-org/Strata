/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def blockLabelUniqueTestPgm1 :=
#strata
program Core;

procedure test () {
  foo: {
    if (true) {
      foo: { exit foo; }   // ambiguous: inner or outer foo?
      exit foo;            // exits outer foo
    } else {
      foo: { exit foo; }   // ambiguous: (different) inner or outer foo?
    }
  }
};
#end

/--
error:  ❌ Type checking error.
Block label "foo" shadows an enclosing block.
-/
#guard_msgs in
#eval verify blockLabelUniqueTestPgm1

---------------------------------------------------------------------

def blockLabelUniqueTestPgm2 :=
#strata
program Core;

procedure test () {
  foo: { exit foo; }
  foo: { exit foo; }
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:

---
info:
-/
#guard_msgs in
#eval verify blockLabelUniqueTestPgm2
