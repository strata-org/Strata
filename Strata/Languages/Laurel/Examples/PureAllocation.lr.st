/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
-- WIP. needs further design
composite Immutable {
  val x: int

  val construct = function(): pure Immutable
    constructor
    requires constructing = {this}
    ensures constructing == {}
  {
    this.x = 3;
    construct this;
    this
  }
}

val pureCompositeAllocator = function(): boolean {
  var i: pure Empty = Immutable.construct(); -- can be called in a pure construct, because it is a function
  var j: pure Empty = Immutable.construct();
  i =&= j
--  ^^^ reference equality operator '=&=' can not be used on pure types
}