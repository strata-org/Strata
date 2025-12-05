/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/
procedure foo() {
  assert true; // pass
  assert false; // error
  assert false; // TODO: decide if this has an error
}

procedure bar() {
  assume false; // pass
  assert true; // pass
}