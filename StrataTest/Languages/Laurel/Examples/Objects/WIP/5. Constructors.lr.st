/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/

/*
WIP
*/
composite Immutable {
  val x: int
  val y: int
  var z: int

  invariant x + y == 6

  procedure construct(): Immutable
  // fields of Immutable are considered mutable inside this procedure
  // and invariants of Immutable are not visible
  // can only call procedures that are also constructing Immutable
    opaque
    constructs Immutable
    modifies this
  {
    this.x = 3;
    assignToY();
    // implicit: assert modifiesOf(construct()).forall(x -> x.invariant());
  };

  procedure assignToY() 
    opaque
    constructs Immutable
  {
    this.y = 3;
  };
}

procedure foo()
  opaque
{
  var c = new Immutable.construct();
  var temp = c.x;
  c.z = 1;
  assert c.x + c.y == 6; // pass
  assert temp == c.x; // pass
};

procedure pureCompositeAllocator(): boolean
  opaque
{
  // can be called in a determinstic context
  var i: Immutable = Immutable.construct(); 
  var j: Immutable = Immutable.construct();
  assert i =&= j; // error: refernce equality is not available on deterministic types
};