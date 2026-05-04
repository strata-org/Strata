/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.DDM.Ion
public import Strata.DDM.Util.Ion.DeriveFromIon

public section

-- Test 1: Simple structure
structure TestPoint where
  x : Nat
  y : Nat

derive_FromIon TestPoint

-- Verify the instance was created
#check (inferInstance : Strata.FromIon TestPoint)

end
