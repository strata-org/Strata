/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/

/*
A decreases clause CAN be added to a procedure to prove that it terminates.
A procedure with a decreases clause may be called in an erased context.
*/

procedure noDecreases(x: int): boolean
procedure caller(x: int)
  requires noDecreases(x) // error: noDecreases can not be called from a contract, because ...

// Non-recursive procedures can use an empty decreases list and still prove termination
procedure noCyclicCalls() 
  decreases []
{
  leaf(); // call passes since leaf is lower in the SCC call-graph.
}

procedure leaf() decreases [1] { }

// Decreases clauses are needed for recursive procedure calls.

// Decreases clauses take a list of arguments
procedure mutualRecursionA(x: nat)
  decreases [x, 1]
{
  mutualRecursionB(x);
}

procedure mutualRecursionB(x: nat)
  decreases [x, 0]
{
  if x != 0 { mutualRecursionA(x-1); }
}

/*
Translation towards SMT:

proof foo_body {
  var x: nat;
  assert decreases([x, 1], [x, 0]);
}

proof bar_body {
  var x: nat;
  if (x != 0) {
    assert decreases([x, 0], [x - 1, 1]);
  }
}

*/