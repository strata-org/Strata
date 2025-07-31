/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

structure Options where
  verbose : Bool

def Options.default : Options := { verbose := true }

def Options.quiet : Options := { verbose := false }
