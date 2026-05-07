/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Util.Profile

def measureNanos_nonzero : BaseIO Bool := do
  let (_, ns) ← measureNanos fun () =>
    -- Large enough to comfortably exceed monoNanosNow resolution on any host.
    (List.range 200000).foldl (· + ·) 0
  pure (ns > 0)

#eval show IO Unit from do
  unless (← measureNanos_nonzero.toIO) do
    throw <| IO.userError "measureNanos regressed to 0 ns"
