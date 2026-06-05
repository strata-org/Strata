/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/--
Extract `Decidable` instance from typeclass inference.
-/
def decideProp (p : Prop) [h : Decidable p] : Decidable p := h
