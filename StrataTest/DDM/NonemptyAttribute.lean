/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean

/-!
# Tests for @[nonempty] attribute on list constructs

This file tests that the @[nonempty] attribute properly enforces non-empty lists
for CommaSepBy, SpaceSepBy, and SpacePrefixSepBy constructs.
-/

#dialect
dialect NonemptyTest;

category Item;
op item (n : Num) : Item => n;

// Operations with @[nonempty] - require at least one element
op comma1 (@[nonempty] items : CommaSepBy Item) : Command => "comma1(" items ")";
op space1 (@[nonempty] items : SpaceSepBy Item) : Command => "space1(" items ")";
op prefixed1 (@[nonempty] items : SpacePrefixSepBy Item) : Command => "prefixed1(" items ")";
op seq1 (@[nonempty] items : Seq Item) : Command => "seq1(" items ")";

// Operations without @[nonempty] - allow zero elements
op comma0 (items : CommaSepBy Item) : Command => "comma0(" items ")";
op space0 (items : SpaceSepBy Item) : Command => "space0(" items ")";
op seq0 (items : Seq Item) : Command => "seq0(" items ")";

#end

namespace NonemptyTest

#strata_gen NonemptyTest

end NonemptyTest

namespace NonemptyTest.Tests

-- Test that @[nonempty] CommaSepBy accepts non-empty lists
#guard_msgs in
private def test_nonempty_comma_success := #strata
program NonemptyTest;
comma1(1, 2, 3)
#end

-- Test that @[nonempty] CommaSepBy rejects empty lists
/-- error: expected expected at least one element -/
#guard_msgs in
private def test_nonempty_comma_empty := #strata
program NonemptyTest;
comma1()
#end

-- Test that @[nonempty] SpaceSepBy accepts non-empty lists
#guard_msgs in
private def test_nonempty_space_success := #strata
program NonemptyTest;
space1(1 2 3)
#end

-- Test that @[nonempty] SpaceSepBy rejects empty lists
/-- error: expected expected at least one element -/
#guard_msgs in
private def test_nonempty_space_empty := #strata
program NonemptyTest;
space1()
#end

-- Test that @[nonempty] SpacePrefixSepBy accepts non-empty lists
#guard_msgs in
private def test_nonempty_prefixed_success := #strata
program NonemptyTest;
prefixed1(1 2 3)
#end

-- Test that @[nonempty] SpacePrefixSepBy rejects empty lists
/-- error: expected expected at least one element -/
#guard_msgs in
private def test_nonempty_prefixed_empty := #strata
program NonemptyTest;
prefixed1()
#end

-- Test that regular (non-@[nonempty]) CommaSepBy allows empty lists
#guard_msgs in
private def test_maybe_empty_comma := #strata
program NonemptyTest;
comma0()
#end

-- Test that regular (non-@[nonempty]) SpaceSepBy allows empty lists
#guard_msgs in
private def test_maybe_empty_space := #strata
program NonemptyTest;
space0()
#end

end NonemptyTest.Tests

-- Test that @[nonempty] Seq accepts non-empty lists
#guard_msgs in
private def test_nonempty_seq_success := #strata
program NonemptyTest;
seq1(1 2 3)
#end

-- Test that @[nonempty] Seq rejects empty lists
/-- error: expected expected at least one element -/
#guard_msgs in
private def test_nonempty_seq_empty := #strata
program NonemptyTest;
seq1()
#end

-- Test that regular (non-@[nonempty]) Seq allows empty lists
#guard_msgs in
private def test_maybe_empty_seq := #strata
program NonemptyTest;
seq0()
#end
