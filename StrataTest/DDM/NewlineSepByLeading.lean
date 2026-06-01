/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DDM.Integration.Lean

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

abbrev testItems := #strata
program NewlineSepByLeadingTest;
1
2
3;
#end

/--
info: program NewlineSepByLeadingTest;
1
2
3;
-/
#guard_msgs in
#eval testItems.format

-- Assert the parsed AST contains a seq with newline separator and three items
#guard
  let cmd := testItems.commands[0]!
  match cmd.args[0]? with
  | some (Strata.ArgF.seq _ .newline items) => items.size == 3
  | _ => false

-- Negative test: left-recursive NewlineSepBy (inner category = op's own category) is rejected
/--
error: Leading symbol cannot be recursive call to Item
-/
#guard_msgs in
#dialect
dialect NewlineSepByLeftRecTest;

category Item;
op item (n : Num) : Item => n;

// Left-recursive: NewlineSepBy of the op's own category as leading argument
op badItems (xs : NewlineSepBy Item) : Item => xs;
#end
