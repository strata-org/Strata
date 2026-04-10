/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Util.Profile

namespace Strata.Util.Profile.Tests

/-! # FFI statistics / timer tests

These tests must be run as a compiled executable since the FFI symbols
are not available to the interpreter. Build and run with:

    lake build TestProfile && .lake/build/bin/TestProfile
-/

private def assert (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.Error.userError s!"FAIL: {msg}")

public def runTests : IO Unit := do
  IO.println "--- Profile FFI tests ---"

  -- Basic increment and read back
  let v :=
    increment_stat "a";
    increment_stat "a";
    increment_stat "a" 3;
    get_stat "a" v;
    v
  assert (v == 5) s!"increment_stat: expected 5, got {v}"
  IO.println "  [pass] increment_stat / get_stat"

  -- Unset counter returns 0
  let v :=
    get_stat "nonexistent" v;
    v
  assert (v == 0) s!"unset counter: expected 0, got {v}"
  IO.println "  [pass] unset counter returns 0"

  -- Multiple independent counters
  let (vx, vy) :=
    increment_stat "x";
    increment_stat "y" 10;
    get_stat "x" vx;
    get_stat "y" vy;
    (vx, vy)
  assert (vx == 1) s!"counter x: expected 1, got {vx}"
  assert (vy == 10) s!"counter y: expected 10, got {vy}"
  IO.println "  [pass] multiple independent counters"

  -- get_stat_keys returns all registered keys
  let ks :=
    get_stat_keys ks;
    ks
  assert (ks.contains "a") "get_stat_keys missing 'a'"
  assert (ks.contains "x") "get_stat_keys missing 'x'"
  assert (ks.contains "y") "get_stat_keys missing 'y'"
  IO.println s!"  [pass] get_stat_keys ({ks.size} keys)"

  -- print_stat / print_stat_all (output goes to stdout via dbgTrace)
  let sentinel : Nat :=
    print_stat "a";
    print_stat_all;
    42
  assert (sentinel == 42) "print_stat round-trip"
  IO.println "  [pass] print_stat / print_stat_all"

  -- Timer round-trip
  let sentinel : Nat :=
    start_timer "test_timer";
    finish_timer;
    42
  assert (sentinel == 42) "timer round-trip"
  IO.println "  [pass] start_timer / finish_timer"

  -- Nested timers
  let sentinel : Nat :=
    start_timer "outer";
    start_timer "inner";
    finish_timer;
    finish_timer;
    42
  assert (sentinel == 42) "nested timers round-trip"
  IO.println "  [pass] nested timers"

  IO.println "--- All tests passed ---"

end Strata.Util.Profile.Tests
