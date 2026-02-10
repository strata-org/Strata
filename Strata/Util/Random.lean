/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

namespace Strata.Util

/--
This sets the StdGenRef to a specific seed to eliminate one source
of non-determinism.

N.B. This could be made a private once files that import it are
modules.
-/
public def withStdGenSeed {α} (seed : Nat) (act : IO α) : IO α := do
  let oldStdGen ← IO.stdGenRef.get
  IO.stdGenRef.set (mkStdGen seed)
  try
    act
  finally
    IO.stdGenRef.set oldStdGen

end Strata.Util
