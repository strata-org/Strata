/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/
composite Base {
  procedure foo(): int
    ensures result > 3
    { abstract }
}

composite Extender1 extends Base {
  procedure foo(): int
    ensures result > 4
//  ^^^^^^^ error: could not prove ensures clause guarantees that of extended method 'Base.foo'
    { abstract }
}

composite Extender2 extends Base {
  value: int
  procedure foo(): int
    ensures result > 2
  {
    this.value + 2 // 'this' is an implicit variable inside instance callables
  }
}

val foo = procedure(b: Base) {
  var x = b.foo();
  assert x > 3; // pass
}