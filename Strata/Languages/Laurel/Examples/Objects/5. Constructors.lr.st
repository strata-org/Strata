/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
-- WIP. needs further design
composite Immutable {
  val x: int

  procedure construct(): Immutable
    constructor
    requires constructing = {this}
    ensures constructing == {}
  {
    this.x = 3; // while this is being constructed, 
    // its immutable fields can be assigned to

    construct this; // 'this' is no longer being constructed
    this
  }
}

procedure pureCompositeAllocator(): boolean {
  // can be called in a determinstic context
  var i: Immutable = Immutable.construct(); 
  var j: Immutable = Immutable.construct();
  assert i =&= j; // error: structural equality 
}