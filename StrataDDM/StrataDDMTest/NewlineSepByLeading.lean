/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean

/-!
# Test for NewlineSepBy as leading argument

Regression test for issue #1245: `checkLeftRec` panics when the leading
argument of an op is `NewlineSepBy`.
-/

#dialect
dialect NewlineSepByLeadingTest;

category Item;
op item (n : Num) : Item => n;

// NewlineSepBy as the leading (first) argument in the syntax
op items (xs : NewlineSepBy Item) : Command => xs ";";
#end

#guard_msgs in
private def test_newline_sep_by_leading := #strata
program NewlineSepByLeadingTest;
1
2
3;
#end
