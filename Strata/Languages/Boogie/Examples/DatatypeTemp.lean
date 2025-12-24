/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

/-!
# Simple Datatype Example: Option

This example demonstrates basic datatype usage with the Option type,
including constructors, testers, and destructors.
-/

def optionPgm : Program :=
#strata
program Boogie;

datatype Option (α : Type) {
  None(),
  Some(value: α)
};

procedure testOption(x: int) returns (r: Option int)
{
  r := Some(x);
};

#end
