/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Util.Profile

namespace Strata.Util.Profile.Tests

/-! # Statistics / timer tests -/

private def assert (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.Error.userError s!"FAIL: {msg}")

public def runTests : IO Unit := do
  IO.println "--- Profile tests ---"

  -- Basic increment and read back
  reset_stats
  increment_stat "a"
  increment_stat "a"
  increment_stat "a" 3
  let v := getStatistics "a"
  assert (v == 5) s!"increment_stat: expected 5, got {v}"
  IO.println "  [pass] increment_stat / get_stat"

  -- Unset counter returns 0
  let v := getStatistics "nonexistent"
  assert (v == 0) s!"unset counter: expected 0, got {v}"
  IO.println "  [pass] unset counter returns 0"

  -- Multiple independent counters
  increment_stat "x"
  increment_stat "y" 10
  let vx := getStatistics "x"
  let vy := getStatistics "y"
  assert (vx == 1) s!"counter x: expected 1, got {vx}"
  assert (vy == 10) s!"counter y: expected 10, got {vy}"
  IO.println "  [pass] multiple independent counters"

  -- get_stat_keys returns all registered keys
  let ks := getStatKeys ()
  assert (ks.contains "a") "get_stat_keys missing 'a'"
  assert (ks.contains "x") "get_stat_keys missing 'x'"
  assert (ks.contains "y") "get_stat_keys missing 'y'"
  IO.println s!"  [pass] get_stat_keys ({ks.size} keys)"

  -- print_stat / print_stat_all
  print_stat "a"
  print_stat_all
  IO.println "  [pass] print_stat / print_stat_all"

  -- Timer round-trip
  start_timer "test_timer"
  finish_timer
  IO.println "  [pass] start_timer / finish_timer"

  -- Nested timers
  start_timer "outer"
  start_timer "inner"
  finish_timer
  finish_timer
  IO.println "  [pass] nested timers"

  -- Reset clears everything
  reset_stats
  let v := getStatistics "a"
  let ks := getStatKeys ()
  assert (v == 0) s!"reset: expected 0, got {v}"
  assert ks.isEmpty "reset: expected empty keys"
  IO.println "  [pass] reset_stats clears all counters"

  IO.println "--- All tests passed ---"

end Strata.Util.Profile.Tests
