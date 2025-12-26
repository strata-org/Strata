/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/

composite ImmutableContainer {
  val value: int // val indicates immutability of field
}

procedure valueReader(c: ImmutableContainer): int
  { c.value } // no reads clause needed because value is immutable

/*
Translation towards SMT:

type Composite;
function ImmutableContainer_value(c: Composite): int

function valueReader(c: Composite): int {
  ImmutableContainer_value(c)
}

proof valueReader_body { 
}
*/