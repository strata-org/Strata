/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
-- Constrained primitive type
constrained nat = x: int where x >= 0

-- Something analogous to an algebriac datatype
composite OptionBase {}
composite Some extends OptionBase { 
  value: int
}
composite None extends OptionBase
constrained Option = x: OptionBase where x is Some || x is None