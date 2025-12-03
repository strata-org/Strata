/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Create immutable composite
composite Immutable {
  val x: int
  val y: int

  invariant x + y >= 5

  procedure construct()
    constructor
    requires this in Immutable.contructing
    ensures this !in Immutable.constructing
  {
    x = 3; -- we can assign to an immutable field, while the target is in the constructing set.
    this.constructorHelper();
    construct this; -- checks that all fields of 'this' have been assigned
  }

  procedure constructorHelper() 
    constructor
    requires this in Immutable.constructing
    ensures assigned(this.y)
  {
    y = 2;
  }
}

procedure foo() {
  val immutable = Immutable.construct(); -- constructor instance method can be called as a static.
}