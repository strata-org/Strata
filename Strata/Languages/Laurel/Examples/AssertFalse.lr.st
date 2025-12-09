/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/
procedure foo() {
    assert true;
    assert false;
//  ^^^^^^^^^^^^^ error: assertion does not hold
    assert false; // TODO: decide if this has an error
//  ^^^^^^^^^^^^^ error: assertion does not hold
}

procedure bar() {
    assume false;
    assert true;
}