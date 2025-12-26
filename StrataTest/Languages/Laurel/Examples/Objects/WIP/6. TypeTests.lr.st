/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/

/*
WIP
*/
composite Base {
  var x: int
}

composite Extended1 extends Base {
  var y: int
}

composite Extended2 extends Base {
  var z: int
}

procedure typeTests(e: Extended1) {
  var b: Base = e as Base; // even upcasts are not implicit, but they pass statically
  var e2 = e as Extended2;
//           ^^ error: could not prove 'e' is of type 'Extended2'
  if (e is Extended2) {
    // unreachable, but that's OK
    var e2pass = e as Extended2; // no error
  }
}