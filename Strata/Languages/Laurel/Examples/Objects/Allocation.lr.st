/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
-- WIP. needs further design

-- Create immutable composite
composite Immutable {
  val x: int
  val y: int

  invariant x + y >= 5

  val construct = procedure()
    constructor
    requires contructing == {this}
    ensures constructing == {}
  {
    x = 3; -- we can assign to an immutable field, while the target is in the constructing set.
    y = 2;
    construct this; -- checks that all fields of 'this' have been assigned
  }
}

val foo = procedure() {
  val immutable = Immutable.construct(); -- constructor instance method can be called as a static.
}

-- Create immutable circle
composite ImmutableChainOfTwo {
  val other: ChainOfTwo -- note the field is immutable

  invariant other.other == this -- reading other.other is allowed because the field is immutable

  val construct = constructor() 
    requires contructing == {this}
    ensures constructing == {}
  {
    var second = allocate();
    assert constructing == {this, second};

    second.other = first; -- we can assign to a mutable field because second is in the constructing set
    first.other = second;
    construct first;
    construct second;
  }

  -- only used privately
  val allocate = constructor()
    ensures constructing = {this} {    
    -- empty body
  }
}

val foo2 = procedure() {
  val immutable = ImmutableChainOfTwo.construct();
  val same = immutable.other.other;
  assert immutable =&= same;
}

-- Helper constructor
composite UsesHelperConstructor {
  val x: int
  val y: int

  val setXhelper = constructor() 
    requires constructing == {this}
    ensures constructing == {this} && assigned(this.x)
  {
    this.x = 3;
  }

  val construct = constructor() 
    requires contructing == {this}
    ensures constructing == {}
  {
    this.setXhelper();
    y = 2;
    construct this;
  }
}