/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/

// Constrained primitive type
constrained nat = x: int where x >= 0 witness 0

// Something analogous to an algebriac datatype
composite Option {}
composite Some extends Option { 
  value: int
}
composite None extends Option
constrained SealedOption = x: Option where x is Some || x is None witness None

procedure foo() returns (r: nat) {
  // no assign to r. 
  // this is accepted. there is no definite-asignment checking since types may never be empty
}