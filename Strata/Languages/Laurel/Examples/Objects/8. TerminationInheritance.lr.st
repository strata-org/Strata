/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/
trait Base {
  predicate foo()
}

trait Extender extends Base {
  // Commenting this method in or out should not change the result of termination checking
  // predicate foo()
}

datatype AnotherExtender extends Base = AnotherExtender(e: Extender) {

  predicate foo() 
  {
    e.foo()
  }
}